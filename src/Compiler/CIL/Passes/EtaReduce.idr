module Compiler.CIL.Passes.EtaReduce

import Compiler.CIL.CIL
import Data.List
import Compiler.Common
import Core.Core
import Data.SortedMap
import Core.Name
import Compiler.Common
import Core.Context
import Data.Vect

%default covering

eta_reduce_expr : SortedMap Name CILDef -> CILExpr -> Core CILExpr
eta_reduce_expr defs c@(CILExprCall fc callee (CILFn xs x) args arg_tys) = do
  callee' <- eta_reduce_expr defs callee
  args' <- traverse (eta_reduce_expr defs) args
  if length xs < length args then
    let (args', _) = splitAt (length xs) args in
    let (arg_tys', _) = splitAt (length xs) arg_tys
    in pure $ CILExprCall fc callee (CILFn xs x) args' arg_tys'
    else pure c
eta_reduce_expr defs c@(CILExprCall fc callee t args arg_tys) = do
  callee' <- eta_reduce_expr defs callee
  args' <- traverse (eta_reduce_expr defs) args
  pure $ CILExprCall fc callee' t args' arg_tys
eta_reduce_expr defs (CILExprOp fc f xs x) = do
  xs' <- traverseVect (eta_reduce_expr defs) xs
  pure $ CILExprOp fc f xs' x
eta_reduce_expr defs (CILExprConstant fc cst x) = pure $ CILExprConstant fc cst x
eta_reduce_expr defs (CILExprLocal fc n x) = pure $ CILExprLocal fc n x
eta_reduce_expr defs (CILExprStruct fc n x xs) = do
  xs' <- traverse (eta_reduce_expr defs) xs
  pure $ CILExprStruct fc n x xs'
eta_reduce_expr defs (CILExprRef fc n x) = pure $ CILExprRef fc n x
eta_reduce_expr defs (CILExprField fc x y n) = do
  x' <- eta_reduce_expr defs x
  pure $ CILExprField fc x' y n
eta_reduce_expr defs (CILExprTaggedUnion fc n x i xs) = do
  xs' <- traverse (eta_reduce_expr defs) xs
  pure $ CILExprTaggedUnion fc n x i xs'
eta_reduce_expr defs (CILExprSizeof fc x) = do
  x' <- eta_reduce_expr defs x
  pure $ CILExprSizeof fc x'
eta_reduce_expr defs (CILExprAddrof fc x) = do
  x' <- eta_reduce_expr defs x
  pure $ CILExprAddrof fc x'


eta_reduce_defs : SortedMap Name CILDef -> CILDef -> Core CILDef
eta_reduce_defs defs (MkCILFun fc n args return body) = do
  body' <- traverseCIL (eta_reduce_expr defs) body
  pure $ MkCILFun fc n args return body'
eta_reduce_defs _ struct = pure struct

public export
eta_reduce : List CILDef -> Core (List CILDef)
eta_reduce defs = do
  let defMap = fromList (zip (getName <$> defs) defs)
  traverse (eta_reduce_defs defMap) defs
