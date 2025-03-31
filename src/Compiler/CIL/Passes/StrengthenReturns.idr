module Compiler.CIL.Passes.StrengthenReturns

import Compiler.CIL.CIL
import Data.Vect
import Data.List
import Compiler.Common
import Core.Core
import Data.SortedMap
import Core.Name
import Compiler.Common
import Core.Context
import Compiler.CIL.Passes.FixAssignmentTypes

%default covering

fixup : SortedMap Name CILType -> CILExpr -> Core CILExpr
fixup changes (CILExprCall fc x y xs ys) = do
    x' <- fixup changes x
    xs' <- traverse (fixup changes) xs
    pure $ CILExprCall fc x' y xs' ys
fixup changes (CILExprOp fc f xs x) = do
    _ <- traverseVect (fixup changes) xs
    pure $ CILExprOp fc f xs x
fixup changes (CILExprStruct fc n x xs) = do
    xs' <- traverse (fixup changes) xs
    pure $ CILExprStruct fc n x xs'
fixup changes ref@(CILExprRef fc n x) = do
    case lookup n changes of
        Just t => do
          pure $ CILExprRef fc n t
        Nothing => pure ref
fixup changes (CILExprField fc x y n) = do
    x' <- fixup changes x
    pure $ CILExprField fc x' y n
fixup changes (CILExprTaggedUnion fc n x i xs) = do
    xs' <- traverse (fixup changes) xs
    pure $ CILExprTaggedUnion fc n x i xs'
fixup _ x = pure x

fixupCalls : SortedMap Name CILType -> CILDef -> Core CILDef
fixupCalls fixes (MkCILFun fc n args return body)  = pure $ MkCILFun fc n args return !(traverseCIL (fixup fixes) body)
fixupCalls fixes other  = pure other

strengthenDef : CILDef -> Core CILDef
strengthenDef fn@(MkCILFun fc n args return body) = do
    computedReturn <- inferType body
    if return == CILDyn then do
        case computedReturn of
            CILFn _ _ => pure fn
            _ => pure $ MkCILFun fc n args computedReturn body
      else pure fn
strengthenDef x = pure x

public export
strengthenReturns : List CILDef -> Core (List CILDef)
strengthenReturns defs = do
  strengthened <- traverse (strengthenDef) defs
  let changed = filter (\x => case x of
            ((MkCILFun fc _ _ return _), (MkCILFun _ _ _ return' _)) => return' /= return
            _ => False
        ) (zip defs strengthened)
  let changed = catMaybes $ map (\(_, def) => case def of
        (MkCILFun fc n args return body) => Just (n, CILFn (snd <$> args) return)
        _ => Nothing) changed
  if length changed > 0 then do
    fixed <- traverse (fixupCalls (fromList changed)) strengthened
    fixed <- traverse (\def => case def of
        (MkCILFun fc n args return body) => pure $ MkCILFun fc n args return (fst !(fix_assign_types body))
        _ => pure def) fixed
    strengthenReturns fixed
    else pure strengthened
