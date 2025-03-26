||| This file implements the monomorphisation pass.
||| A function with uninferred arguments is monomorphised by replacing the
||| uninferred arguments with the actual arguments.

module Compiler.CIL.Passes.Monomorphise

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

data LambdaStructEquiv : Type where
data MonoDefs : Type where

data FixedDecls : Type where

assign_types_expr : { auto _ : Ref FixedDecls (SortedMap Name CILType)} -> CILExpr -> Core CILExpr
assign_types_expr (CILExprLocal fc n x) = do
  fixedDecls <- get FixedDecls
  case lookup n fixedDecls of
    Just t => pure $ CILExprLocal fc n t
    Nothing => pure $ CILExprLocal fc n x
assign_types_expr (CILExprCall fc x y xs ys) = do
  x' <- assign_types_expr x
  xs' <- traverse assign_types_expr xs
  pure $ CILExprCall fc x' !(inferExprType x') xs' !(traverse inferExprType xs')
assign_types_expr (CILExprOp fc f xs x) = do 
  xs' <- traverseVect assign_types_expr xs
  pure $ CILExprOp fc f xs' x
assign_types_expr (CILExprStruct fc n x xs) = do
  xs' <- traverse assign_types_expr xs
  pure $ CILExprStruct fc n x xs'
assign_types_expr (CILExprField fc x y n) = do 
  x' <- assign_types_expr x
  pure $ CILExprField fc x' y n
assign_types_expr (CILExprTaggedUnion fc n t k xs) = do
  xs' <- traverse assign_types_expr xs
  pure $ CILExprTaggedUnion fc n t k xs'
assign_types_expr c = pure c

assign_types : { auto _ : Ref FixedDecls (SortedMap Name CILType)} -> CIL e  -> Core (CIL e, Bool)
assign_types (CILConstCase x fc sc xs y) = do
  sc' <- assign_types_expr sc
  (xscil, changed) <- unzip <$> traverseList1 assign_types (map (\(MkCILConstAlt _ _ c) => c) xs)
  let xs' = zipWith (\(MkCILConstAlt e n _), x => MkCILConstAlt e n x) xs xscil
  y' <- traverseOpt assign_types y
  case y' of
    Just (y'', changed2) => pure $ (CILConstCase x fc sc' xs' (Just y''), changed2 || (any id changed))
    Nothing => pure $ (CILConstCase x fc sc' xs' Nothing, any id changed)
assign_types (CILBlock fc xs x) = do
  (xs', changed) <- unzip <$> traverse assign_types xs
  (x', changed2) <- assign_types x
  pure $ (CILBlock fc xs' x', (changed2 || (any id changed)))
assign_types (CILDeclare fc x n y) = do
  x' <- inferType y
  update FixedDecls (insert n x')
  _ <- if x /= x' then pure $ traceVal $ "Changed " ++ show x ++ " to " ++ show x' else pure ""
  pure $ (CILDeclare fc x' n y, x /= x')
assign_types (CILReturn fc ex) = pure ((CILReturn fc !(assign_types_expr ex)), False)
assign_types (CILAssign fc n x) = pure ((CILAssign fc n !(assign_types_expr x)), False)
assign_types (CILConCase fc e sc xs) = do
  sc' <- assign_types_expr sc
  (xscil, changed) <- unzip <$> traverseList1 assign_types (map (\(MkCILConAlt _ _ c) => c) xs)
  let xs' = zipWith (\(MkCILConAlt e n _), x => MkCILConAlt e n x) xs xscil
  pure $ (CILConCase fc e sc' xs', any id changed)

mutual 
  recompile_def : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> (SortedMap Name CILDef) -> CILDef -> List CILType -> Core CILDef
  recompile_def defs fn@(MkCILFun fc n fnArgs return body) actualArgs =
    if (snd <$> fnArgs) /= actualArgs then do
      _ <- pure $ traceVal $ "Recompiling function: " ++ show n ++ " ! " ++ show (snd <$> fnArgs) ++ " vs. " ++ show actualArgs 
      let fnArgMap = fromList fnArgs
      let actualArgMap = fromList (zip (fst <$> fnArgs) actualArgs)
      body' <- traverseCIL (recompile_expr defs fnArgMap actualArgMap) body
      let name' = MN (show n) (cast $ length !(get MonoDefs))
      pure $ MkCILFun fc name' (toList actualArgMap) return body'
    else pure fn
      where recompile_expr : (SortedMap Name CILDef) -> SortedMap Name CILType -> SortedMap Name CILType -> CILExpr -> Core CILExpr
            recompile_expr defs fnArgMap actualArgMap (CILExprLocal fc1 n1 x) = assert_total $ do
              pure $ case lookup n1 actualArgMap of
                      Just t' => (CILExprLocal fc1 n1 t')
                      Nothing => (CILExprLocal fc1 n1 x)
            recompile_expr defs fnArgMap actualArgMap (CILExprCall fc1 callee ty args argTys) = assert_total $ do
              callee' <- recompile_expr defs fnArgMap actualArgMap callee
              args' <- traverse (recompile_expr defs fnArgMap actualArgMap) args
              call' <- monomorphise_expr defs (CILExprCall fc1 callee' !(inferExprType callee') args' !(traverse inferExprType args'))
              pure call'
            recompile_expr defs fnArgMap actualArgMap (CILExprStruct fc1 n1 (CILStruct _ ty) members) = assert_total $ do
              members' <- traverse (recompile_expr defs fnArgMap actualArgMap) members
              pure (CILExprStruct fc1 n1 (CILStruct n1 (fromList $ zip (keys ty) !(traverse inferExprType members'))) members')
            recompile_expr defs fnArgMap actualArgMap (CILExprField fc x ty f) = assert_total $ do
              x' <- recompile_expr defs fnArgMap actualArgMap x
              pure (CILExprField fc x' !(inferExprType x') f)
            recompile_expr defs fnArgMap actualArgMap ex = pure ex
  recompile_def defs st@(MkCILStruct fc n members) args =
    if (values members) /= args then do
      let members' = zip (keys members) args
      let name' = MN (show n) (cast $ length !(get MonoDefs))
      pure $ MkCILStruct fc name' (fromList members')
    else pure st
  recompile_def defs d args = pure d
            

  monomorphise_expr : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> SortedMap Name CILDef -> CILExpr -> Core CILExpr
  monomorphise_expr defs call@(CILExprCall fc (CILExprRef fc1 n y) ty args arg_types) = assert_total $ do
      _ <- pure $ traceVal $ "expr" ++ show call
      monoDefs <- get MonoDefs
      let monoDefMap = fromList $ (\x => (getName x, x)) <$> monoDefs
      let Just fn = lookup n (mergeLeft defs monoDefMap)
          | _ => throw $ InternalError $ "Function"  ++ show n ++  "not found in " ++ show  (mergeLeft defs monoDefMap)
      case fn of
        fn@(MkCILFun _ _ _ _ _) => do
          _ <- pure $ traceVal $ "args " ++ show args
          args <- traverse (monomorphise_expr defs) args
          _ <- pure $ traceVal $ "finished args"
          fn'@(MkCILFun fc n' args' return' body') <- recompile_def defs fn arg_types
          if n /= n' then do
              _ <- pure $ traceVal $ "Changed " ++ show n ++ " to " ++ show n'
              update MonoDefs (fn' ::)
              pure (CILExprCall fc (CILExprRef fc1 n' y) ty args arg_types) 
            else pure call
        _ => pure call -- Foreign functions are not monomorphised
  monomorphise_expr defs s@(CILExprStruct fc n ty members) = assert_total $ do
      monoDefs <- get MonoDefs
      let monoDefMap = fromList $ (\x => (getName x, x)) <$> monoDefs
      let Just struct = traceVal (lookup n (mergeLeft defs monoDefMap))
          | _ => throw $ InternalError $ "Struct " ++ show n ++ " not found in " ++ show (mergeLeft defs monoDefMap)
      actualTypes <- traverse inferExprType members
      struct'@(MkCILStruct fc n' members') <- recompile_def defs struct actualTypes
      if n' /= n then do
        lamstr <- get LambdaStructEquiv
        let Just lambdaName = lookup n lamstr
            | _ => throw $ InternalError "Lambda not found"
        let mdefMap = traceVal $ fromList (zip (getName <$> !(get MonoDefs)) !(get MonoDefs))
        let Just lambdaFn@(MkCILFun _ _ lamargs return body) = lookup lambdaName (mergeLeft defs mdefMap)
            | _ => throw $ InternalError $ "Lambda function " ++ show lambdaName ++ " not found"
        lambdaFn'@(MkCILFun _ lamName' _ _ _) <- recompile_def defs lambdaFn (CILStruct n' members' ::  (snd <$> drop 1 lamargs))
        update MonoDefs (\x => struct' :: lambdaFn' :: x)
        update LambdaStructEquiv (insert n' lamName')

        pure (CILExprStruct fc n' (CILStruct n' members') members) else pure s
  monomorphise_expr defs x = pure x

monomorphise_def : {auto _ : Ref MonoDefs (List CILDef)} -> {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> SortedMap Name CILDef -> CILDef -> Core CILDef
monomorphise_def defs (MkCILFun fc n args return body) = do
  _ <- pure $ traceVal $ "Monomorphising function: " ++ show n ++ " !"
  body' <- traverseCIL (monomorphise_expr defs) body
  _ <- newRef FixedDecls empty
  (body',changed) <- assign_types body'
  -- fixme: This is a hack to recompile the definition after fixing assign_types.
  --        Instead of vaguely recompiling we should pass through the types that changed.
  monodefs <- get MonoDefs
  let monodefmap = fromList $ (\x => (getName x, x)) <$> monodefs
  if changed 
    then do _ <- pure $ traceVal $ "Remonorphising function: " ++ show n ++ " !"
            assert_total $ monomorphise_def (mergeLeft defs monodefmap) (MkCILFun fc n args return body')
    else pure $ MkCILFun fc n args return body'
monomorphise_def _ struct = pure struct

public export
monomorphise : SortedMap Name Name -> List CILDef -> Core (List CILDef, SortedMap Name Name) 
monomorphise = repeat_monomorphisation empty
    where repeat_monomorphisation : SortedMap Name CILDef -> SortedMap Name Name -> List CILDef -> Core (List CILDef, SortedMap Name Name)
          repeat_monomorphisation otherdefs lamstr defs = do
            _ <- pure $ traceVal $ "Monomorphising " ++ show (getName <$> defs)
            monoDefs <- newRef MonoDefs []
            lamRef <- newRef LambdaStructEquiv lamstr
            let defMap = mergeLeft otherdefs $ fromList (zip (getName <$> defs) defs)
            defs' <- traverse (monomorphise_def defMap) defs
            lamstr' <- get LambdaStructEquiv
            monoDefs <- get MonoDefs
            if length monoDefs == 0
              then pure (defs', lamstr')
              else do
                let newDefMap = mergeLeft defMap $ fromList (zip (getName <$> defs') defs')
                (moreDefs, moreLamStr) <- repeat_monomorphisation newDefMap lamstr' (monoDefs)
                pure (defs' ++ moreDefs, moreLamStr)
            