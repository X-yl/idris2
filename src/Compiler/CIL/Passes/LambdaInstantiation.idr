
module Compiler.CIL.Passes.LambdaInstantiation

import Compiler.CIL.CIL
import Compiler.Common
import Compiler.Common
import Core.Context
import Core.Core
import Core.Name
import Data.List
import Data.SortedMap
import Debug.Trace

%default covering


lambda_instantiate_expr : SortedMap Name Name -> SortedMap Name CILDef -> CILExpr -> Core CILExpr
lambda_instantiate_expr lamstr defs c@(CILExprCall fc callee ty args argTys) = assert_total $ 
  case !(inferExprType callee) of
    CILStruct n x => do
      let Just fnName = lookup n lamstr 
      let Just fn = lookup fnName defs
      lamType@(CILFn lamArgs return) <- fnType fn
      let callee' = CILExprRef fc fnName lamType
      pure $ CILExprCall fc callee' lamType args argTys
    _ => pure c
    where fnType : CILDef -> Core CILType
          fnType (MkCILFun _ _ args return _) = pure $ CILFn (snd <$> args) return
          fnType (MkCILStruct _ _ _) = throw $ InternalError "Structs cannot be called"
-- lambda_instantiate_expr lamstr defs c@(CILExprCall fc callee ty args argTys) = assert_total $ do
--   ty <- inferExprType callee
--   _ <- pure $ traceVal $ "!!!!!! " ++ show callee ++ " : " ++ show ty
--   pure c
lambda_instantiate_expr lamstr defs c = pure c

lambda_instantiate_def : SortedMap Name Name -> SortedMap Name CILDef -> CILDef -> Core CILDef
lambda_instantiate_def lamstr defs (MkCILFun fc n args return body) = do
  body' <- traverseCIL (lambda_instantiate_expr lamstr defs) body
  pure $ MkCILFun fc n args return body'
lambda_instantiate_def _ _ struct@(MkCILStruct fc n members) = pure struct

public export
lambda_instantiate : SortedMap Name Name -> List CILDef -> Core (List CILDef)
lambda_instantiate lamstr defs = do
  let defMap = fromList (zip (getName <$> defs) defs)
  traverse (lambda_instantiate_def lamstr defMap) defs
  where getName : CILDef -> Name
        getName (MkCILFun _ n _ _ _) = n
        getName (MkCILStruct _ n _) = n
