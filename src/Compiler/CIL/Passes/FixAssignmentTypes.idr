module Compiler.CIL.Passes.FixAssignmentTypes

import Compiler.CIL.CIL
import Data.Vect
import Compiler.Common
import Compiler.Common
import Core.Context
import Core.Core
import Core.Name
import Data.List
import Data.SortedMap
import Debug.Trace
import Data.List1

%default covering
data FixedDecls : Type where

mutual
  public export
  ||| Checks if the second list of types is stricter than the first list of types,
  ||| i.e if the first list contains any CILDyn types that are not in the second list.
  stricter : List CILType -> List CILType -> Bool
  stricter [] [] = False
  stricter (x :: xs) (y :: ys) = (stricter' x y) || stricter xs ys
  stricter _ _ = False

  public export
  stricter' : CILType -> CILType -> Bool
  stricter' CILDyn CILDyn = False
  stricter' CILDyn _      = True
  stricter' (CILPtr x) (CILPtr y) = stricter' x y
  stricter' (CILFn zs x) (CILFn ys y) = stricter zs ys || stricter' x y
  stricter' (CILFn _ _) (CILStruct _ _) = True -- This is a lambda and so can be monomorphised
  stricter' (CILStruct n x) (CILStruct m y) = n /= m || stricter (snd <$> toList x) (snd <$> toList y)
  stricter' _ _ = False

public export
combineStrictest : List CILType -> List CILType -> List CILType
combineStrictest [] [] = []
combineStrictest (x :: xs) (y :: ys) = 
  let stricter = if stricter' x y then y else x
  in stricter :: (combineStrictest xs ys)
combineStrictest [] ys = ys
combineStrictest xs [] = xs


fix_assign_types_expr : { auto _ : Ref FixedDecls (SortedMap Name CILType)} -> CILExpr -> Core CILExpr
fix_assign_types_expr (CILExprLocal fc n x) = do
  -- _ <- pure $ traceVal $ "Fixing local"
  fixedDecls <- get FixedDecls
  case lookup n fixedDecls of
    Just t => pure $ CILExprLocal fc n t
    Nothing => pure $ CILExprLocal fc n x
fix_assign_types_expr exp@(CILExprCall fc x y xs ys) = do
  -- _ <- pure $ traceVal $ "Fixing call"
  x' <- fix_assign_types_expr x
  xs' <- traverse fix_assign_types_expr xs
  strict <- pure $ combineStrictest !(traverse inferExprType xs')  ys
  pure $ CILExprCall fc x' !(inferExprType x') xs' strict
fix_assign_types_expr (CILExprOp fc f xs x) = do 
  -- _ <- pure $ traceVal $ "Fixing op"
  xs' <- traverseVect fix_assign_types_expr xs
  pure $ CILExprOp fc f xs' x
fix_assign_types_expr (CILExprStruct fc n x xs) = do
  -- _ <- pure $ traceVal $ "Fixing struct"
  xs' <- traverse fix_assign_types_expr xs
  pure $ CILExprStruct fc n x xs'
fix_assign_types_expr (CILExprField fc x y n) = do 
  -- _ <- pure $ traceVal $ "Fixing field"
  x' <- fix_assign_types_expr x
  pure $ CILExprField fc x' y n
fix_assign_types_expr (CILExprTaggedUnion fc n t k xs) = do
  -- _ <- pure $ traceVal $ "Fixing tagged union"
  xs' <- traverse fix_assign_types_expr xs
  pure $ CILExprTaggedUnion fc n t k xs'
fix_assign_types_expr c =  pure c




fix_assign_types' : { auto _ : Ref FixedDecls (SortedMap Name CILType)} -> CIL e  -> Core (CIL e, Bool)
fix_assign_types' (CILConstCase x fc sc xs y) = do
  -- _ <- pure $ traceVal $ "Fixing CILConstCase"
  sc' <- fix_assign_types_expr sc
  (xscil, changed) <- unzip <$> traverseList1 fix_assign_types' (map (\(MkCILConstAlt _ _ c) => c) xs)
  let xs' = zipWith (\(MkCILConstAlt e n _), x => MkCILConstAlt e n x) xs xscil
  -- _ <- pure $ traceVal $ "Fixing default"
  y' <- traverseOpt fix_assign_types' y
  case y' of
    Just (y'', changed2) => pure $ (CILConstCase x fc sc' xs' (Just y''), changed2 || (any id changed))
    Nothing => pure $ (CILConstCase x fc sc' xs' Nothing, any id changed)
fix_assign_types' (CILBlock fc xs x) = do
  -- _ <- pure $ traceVal $ "Fixing block"
  (xs', changed) <- unzip <$> traverse fix_assign_types' xs
  (x', changed2) <- fix_assign_types' x
  pure $ (CILBlock fc xs' x', (changed2 || (any id changed)))
fix_assign_types' (CILDeclare fc x n y) = do
  -- _ <- pure $ traceVal $ "Fixing declare"
  (y', c1) <- fix_assign_types' y
  x' <- inferType y'
  update FixedDecls (insert n x')
  -- _ <- if x /= x' then pure $ traceVal $ "Changed " ++ show x ++ " to " ++ show x' else pure ""
  pure $ (CILDeclare fc x' n y, x /= x' || c1)
fix_assign_types' (CILReturn fc ex) =  pure ((CILReturn fc !(fix_assign_types_expr ex)), False)
fix_assign_types' (CILAssign fc n x) =  pure ((CILAssign fc n !(fix_assign_types_expr x)), False)
fix_assign_types' (CILConCase fc e sc xs) = do
  -- _ <- pure $ traceVal $ "Fixing concase"
  sc' <- fix_assign_types_expr sc
  (xscil, changed) <- unzip <$> traverseList1 fix_assign_types' (map (\(MkCILConAlt _ _ c) => c) xs)
  let xs' = zipWith (\(MkCILConAlt e n _), x => MkCILConAlt e n x) xs xscil
  pure $ (CILConCase fc e sc' xs', any id changed)

public export
fix_assign_types : CIL e -> Core (CIL e, Bool)
fix_assign_types cil = do 
  _ <- newRef FixedDecls empty
  fix_assign_types' cil