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

getName : CILDef -> Name
getName (MkCILFun _ n _ _ _) = n
getName (MkCILStruct _ n _) = n


assign_types : CIL e  -> Core (CIL e)
assign_types (CILConstCase x fc sc xs y) = do
  xscil <- traverseList1 assign_types (map (\(MkCILConstAlt _ _ c) => c) xs)
  let xs' = zipWith (\(MkCILConstAlt e n _), x => MkCILConstAlt e n x) xs xscil
  y' <- traverseOpt assign_types y
  pure $ CILConstCase x fc sc xs' y'
assign_types (CILBlock fc xs x) = do
  xs' <- traverse assign_types xs
  x' <- assign_types x
  pure $ CILBlock fc xs' x'
assign_types (CILDeclare fc x n y) = do
  x' <- inferType y
  pure $ CILDeclare fc x' n y 
assign_types c = pure c

mutual 
  recompile_def : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> (SortedMap Name CILDef) -> CILDef -> List CILType -> Core CILDef
  recompile_def defs fn@(MkCILFun fc n fnArgs return body) actualArgs =
    if (snd <$> fnArgs) /= actualArgs then do
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
            

  monomorphise_expr : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> SortedMap Name CILDef -> CILExpr -> Core CILExpr
  monomorphise_expr defs call@(CILExprCall fc (CILExprRef fc1 n y) ty args arg_types) = assert_total $ do
      _ <- pure $ traceVal $ "expr" ++ show call
      monoDefs <- get MonoDefs
      let monoDefMap = fromList $ (\x => (getName x, x)) <$> monoDefs
      let Just fn = lookup n (mergeLeft defs monoDefMap)
          | _ => throw $ InternalError $ "Function"  ++ show n ++  "not found in " ++ show  (mergeLeft defs monoDefMap)
      args <- traverse (monomorphise_expr defs) args
      fn'@(MkCILFun fc n' args' return' body') <- recompile_def defs fn arg_types
      if n /= n' then do
          update MonoDefs (fn' ::)
          pure (CILExprCall fc (CILExprRef fc1 n' y) ty args arg_types) 
        else pure call
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
  body' <- traverseCIL (monomorphise_expr defs) body
  body' <- assign_types body'
  pure $ (MkCILFun fc n args return body')
monomorphise_def _ struct = pure struct

public export
monomorphise : SortedMap Name Name -> List CILDef -> Core (List CILDef, SortedMap Name Name) 
monomorphise = repeat_monomorphisation empty
    where repeat_monomorphisation : SortedMap Name CILDef -> SortedMap Name Name -> List CILDef -> Core (List CILDef, SortedMap Name Name)
          repeat_monomorphisation otherdefs lamstr defs = do
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
            