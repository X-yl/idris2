
module Compiler.CIL.Passes.LambdaInstantiation

import Compiler.CIL.CIL
import Compiler.Common
import Compiler.Common
import Core.Context
import Core.Core
import Core.Name
import Data.List
import Data.SortedMap
import Data.Vect

%default covering


lambda_instantiate_expr : SortedMap Name Name -> SortedMap Name CILDef -> CILExpr -> Core CILExpr
lambda_instantiate_expr lamstr defs (CILExprOp fc f xs x) = do
  xs' <- traverseVect (lambda_instantiate_expr lamstr defs) xs
  pure $ CILExprOp fc f xs' x
lambda_instantiate_expr lamstr defs (CILExprConstant fc cst x) = pure $ CILExprConstant fc cst x
lambda_instantiate_expr lamstr defs (CILExprLocal fc n x) = pure $ CILExprLocal fc n x
lambda_instantiate_expr lamstr defs (CILExprStruct fc n x xs) = do
  xs' <- traverse (lambda_instantiate_expr lamstr defs) xs
  pure $ CILExprStruct fc n x xs'
lambda_instantiate_expr lamstr defs (CILExprRef fc n x) = pure $ CILExprRef fc n x
lambda_instantiate_expr lamstr defs (CILExprField fc x y n) = do
  x' <- lambda_instantiate_expr lamstr defs x
  pure $ CILExprField fc x' y n
lambda_instantiate_expr lamstr defs (CILExprTaggedUnion fc n x i xs) = do
  xs' <- traverse (lambda_instantiate_expr lamstr defs) xs
  pure $ CILExprTaggedUnion fc n x i xs'
lambda_instantiate_expr lamstr defs (CILExprSizeof fc x) = do
  x' <- lambda_instantiate_expr lamstr defs x
  pure $ CILExprSizeof fc x'
lambda_instantiate_expr lamstr defs (CILExprAddrof fc x) = do
  x' <- lambda_instantiate_expr lamstr defs x
  pure $ CILExprAddrof fc x'
lambda_instantiate_expr lamstr defs c@(CILExprCall fc callee ty args argTys) = assert_total $
  case !(inferExprType callee) of
    CILStruct n x => do
      args <- traverse (lambda_instantiate_expr lamstr defs) args
      let Just fnName = lookup n lamstr
      let Just fn = lookup fnName defs
      lamType@(CILFn lamArgs return) <- fnType fn
      let callee' = CILExprRef fc fnName lamType
      stType : Maybe CILType <- case lamArgs of
        ((st@(CILStruct _ _)) :: xs) => pure $ Just st
        _ => pure Nothing
      let args = case stType of
                  Just st => callee :: args
                  Nothing => args
      pure $ CILExprCall fc callee' lamType args argTys
    _ => do
      callee' <- lambda_instantiate_expr lamstr defs callee
      args' <- traverse (lambda_instantiate_expr lamstr defs) args
      pure $ CILExprCall fc callee' ty args' argTys
    where fnType : CILDef -> Core CILType
          fnType (MkCILFun _ _ args return _) = pure $ CILFn (snd <$> args) return
          fnType _ = throw $ InternalError "Non Fun cannot be called"

lambda_instantiate_def : SortedMap Name Name -> SortedMap Name CILDef -> CILDef -> Core CILDef
lambda_instantiate_def lamstr defs (MkCILFun fc n args return body) = do
  body' <- traverseCIL (lambda_instantiate_expr lamstr defs) body
  pure $ MkCILFun fc n args return body'
lambda_instantiate_def _ _ struct@(MkCILStruct fc n members) = pure struct
lambda_instantiate_def _ _ etc = pure etc

public export
lambda_instantiate : SortedMap Name Name -> List CILDef -> Core (List CILDef)
lambda_instantiate lamstr defs = do
  let defMap = fromList (zip (getName <$> defs) defs)
  traverse (lambda_instantiate_def lamstr defMap) defs
