module Compiler.CIL.Passes.EtaReduce

import Compiler.CIL.CIL
import Data.List
import Compiler.Common
import Core.Core
import Data.SortedMap
import Core.Name
import Compiler.Common
import Core.Context

%default covering

eta_reduce_expr : SortedMap Name CILDef -> CILExpr -> Core CILExpr
eta_reduce_expr defs c@(CILExprCall fc callee (CILFn xs x) args arg_tys) =
  if length xs < length args then
    let (args', _) = splitAt (length xs) args in
    let (arg_tys', _) = splitAt (length xs) arg_tys
    in pure $ CILExprCall fc callee (CILFn xs x) args' arg_tys'
  else pure c
eta_reduce_expr defs ex = pure ex


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
