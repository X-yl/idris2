||| This file implements the monomorphisation pass.
||| A function with uninferred arguments is monomorphised by replacing the
||| uninferred arguments with the actual arguments.

module Compiler.CIL.Passes.Monomorphise

import Compiler.CIL.CIL
import Compiler.CIL.Passes.FixAssignmentTypes
import Data.Vect
import Compiler.Common
import Compiler.Common
import Core.Context
import Core.Core
import Core.Name
import Data.List
import Data.SortedMap
import Data.List1
import Compiler.RefC.RefC

%default covering

data LambdaStructEquiv : Type where
data MonoDefs : Type where

mutual 
  recompile_def : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> (SortedMap Name CILDef) -> CILDef -> List CILType -> Core CILDef
  recompile_def defs fn@(MkCILFun fc n fnArgs return body) actualArgs =
    if stricter (snd <$> fnArgs) actualArgs then do
      let actualArgs = combineStrictest (snd <$> fnArgs) actualArgs 
      let fnArgMap = fromList fnArgs
      let actualArgMap = fromList (zip (fst <$> fnArgs) actualArgs)
      let name' = MN (cName n) (cast $ length !(get MonoDefs))
      update MonoDefs ((MkCILFun fc name' (toList actualArgMap) return body) ::) -- Add the new function with the old 
                                                                                 -- body so we can monomorphise recursion 
      body' <- recompile_cil name' defs fnArgMap actualArgMap body
      mdefs <- get MonoDefs
      let fn' = MkCILFun fc name' (toList actualArgMap) return body'
      let mdefs' = filter (\x => getName x /= name') mdefs
      update MonoDefs (const (fn' :: mdefs'))
      pure fn'
    else pure fn
      where recompile_expr : Name
                             -> (SortedMap Name CILDef) 
                             -> SortedMap Name CILType 
                             -> SortedMap Name CILType 
                             -> CILExpr 
                             -> Core (List (CIL Nothing), CILExpr)
            recompile_expr _ defs fnArgMap actualArgMap (CILExprLocal fc1 n1 x) = assert_total $ do
              pure $ ([], case lookup n1 actualArgMap of
                      Just t' => (CILExprLocal fc1 n1 t')
                      Nothing => (CILExprLocal fc1 n1 x))
            recompile_expr name' defs fnArgMap actualArgMap (CILExprCall fc1 callee ty args argTys) = assert_total $ do
              (calleeLifted, callee') <- recompile_expr name' defs fnArgMap actualArgMap callee 
              (argsLifted, args') <- unzip <$> traverse (recompile_expr name' defs fnArgMap actualArgMap) args
              inferredArgTypes <- (traverse inferExprType args') -- otherwise we may throw away inferred types of the caller
              (monoLifted, call') <- monomorphise_expr defs (CILExprCall fc1 callee' !(inferExprType callee') args' (combineStrictest inferredArgTypes argTys))
              pure (calleeLifted ++ concat argsLifted ++ monoLifted, call')
            recompile_expr name' defs fnArgMap actualArgMap (CILExprStruct fc1 n1 (CILStruct _ ty) members) = assert_total $ do
              (memLifted, members') <- unzip <$> traverse (recompile_expr name' defs fnArgMap actualArgMap) members
              let stType' = (CILStruct n1 (fromList $ zip (keys ty) !(traverse inferExprType members')))
              pure (concat memLifted, CILExprStruct fc1 n1 stType' members')
            
            recompile_expr name' defs fnArgMap actualArgMap (CILExprStruct fc1 n1 other members) = 
              throw $ InternalError $ "Expected struct type, got " ++ show other
              
            recompile_expr name' defs fnArgMap actualArgMap (CILExprField fc x ty f) = assert_total $ do
              (lifted, x') <- recompile_expr name' defs fnArgMap actualArgMap x
              pure (lifted, CILExprField fc x' !(inferExprType x') f)
            recompile_expr name' defs fnArgMap actualArgMap r@(CILExprRef fc refn _) = assert_total $ do
              if n == refn
                then pure ([], CILExprRef fc name' (CILFn actualArgs return))
                else pure ([], r)
            recompile_expr name' defs fnArgMap actualArgMap (CILExprOp fc1 f xs x) = do
              (lifted, xs') <- unzip <$> traverseVect (recompile_expr name' defs fnArgMap actualArgMap) xs
              pure (concat lifted, CILExprOp fc1 f xs' x)
            recompile_expr name' defs fnArgMap actualArgMap (CILExprConstant fc1 cst x) = pure ([], CILExprConstant fc1 cst x)
            recompile_expr name' defs fnArgMap actualArgMap (CILExprTaggedUnion fc1 n1 x i xs) = do
              (lifted, xs') <- unzip <$> traverse (recompile_expr name' defs fnArgMap actualArgMap) xs
              pure (concat lifted, CILExprTaggedUnion fc1 n1 x i xs')
            recompile_expr name' defs fnArgMap actualArgMap (CILExprSizeof fc1 x) = do
              (lifted, x') <- recompile_expr name' defs fnArgMap actualArgMap x
              pure (lifted, CILExprSizeof fc1 x')
            recompile_expr name' defs fnArgMap actualArgMap (CILExprAddrof fc1 x) = do
              (lifted, x') <- recompile_expr name' defs fnArgMap actualArgMap x
              pure (lifted, CILExprAddrof fc1 x')

            
            recompile_cil : Name
                             -> (SortedMap Name CILDef) 
                             -> SortedMap Name CILType 
                             -> SortedMap Name CILType 
                             -> CIL e 
                             -> Core (CIL e)
            recompile_cil name' defs fnArgMap actualArgMap (CILConstCase e fc sc xs y) = do
              (scLifted, sc') <- recompile_expr name' defs fnArgMap actualArgMap sc
              xs' <- traverseList1 (\(MkCILConstAlt e c cil) =>  MkCILConstAlt e c <$> recompile_cil name' defs fnArgMap actualArgMap cil) xs
              y' <- traverseOpt (recompile_cil name' defs fnArgMap actualArgMap) y
              pure $ prepend scLifted (CILConstCase e fc sc' xs' y')
            recompile_cil name' defs fnArgMap actualArgMap (CILConCase x fc sc xs) = do
              (scLifted, sc') <- recompile_expr name' defs fnArgMap actualArgMap sc
              xs' <- traverseList1 (\(MkCILConAlt e c cil) => MkCILConAlt e c <$> recompile_cil name' defs fnArgMap actualArgMap cil) xs
              pure $ prepend scLifted $ CILConCase x fc sc' xs'
            recompile_cil name' defs fnArgMap actualArgMap (CILBlock fc xs x) = do
              xs' <- traverse (recompile_cil name' defs fnArgMap actualArgMap) xs
              x' <- recompile_cil name' defs fnArgMap actualArgMap x
              pure $ CILBlock fc xs' x'
            recompile_cil name' defs fnArgMap actualArgMap (CILAssign fc n x) = do
              (lifted, x') <- recompile_expr name' defs fnArgMap actualArgMap x
              pure $ prepend lifted $ CILAssign fc n x'
            recompile_cil name' defs fnArgMap actualArgMap (CILReturn fc x) = do
              (lifted, x') <- recompile_expr name' defs fnArgMap actualArgMap x
              pure $ prepend lifted $ CILReturn fc x'
            recompile_cil name' defs fnArgMap actualArgMap (CILDeclare fc x n y) = do
              y' <- recompile_cil name' defs fnArgMap actualArgMap y
              pure $ CILDeclare fc x n y'
  recompile_def defs st@(MkCILStruct fc n members) args =
    if stricter (values members) args then do
      let members' = zip (keys members) args
      let name' = MN (cName n) (cast $ length !(get MonoDefs))
      pure $ MkCILStruct fc name' (fromList members')
    else pure st
  recompile_def defs d args = pure d
            

  monomorphise_expr : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> SortedMap Name CILDef -> CILExpr -> Core (List (CIL Nothing), CILExpr)
  monomorphise_expr defs call@(CILExprCall fc (CILExprRef fc1 n y) ty args arg_types) = assert_total $ do
      monoDefs <- get MonoDefs
      let monoDefMap = Data.SortedMap.fromList $ (\x => (getName x, x)) <$> monoDefs
      let Just fn = lookup n (mergeLeft defs monoDefMap)
          | _ => throw $ InternalError $ "Function"  ++ show n ++  "not found in " ++ show  (mergeLeft defs monoDefMap)
      case fn of
        fn@(MkCILFun _ _ _ _ _) => do
          (lifted, args) <- unzip <$> traverse (monomorphise_expr defs) args
          actualArgTypes <- traverse inferExprType args
          fn'@(MkCILFun fc n' args' return' body') <- recompile_def defs fn actualArgTypes
          if n /= n' then do
              pure (concat lifted, CILExprCall fc (CILExprRef fc1 n' (CILFn (snd <$> args') return')) ty args actualArgTypes) 
            else pure (concat lifted, call)
        _ => pure ([], call) -- Foreign functions are not monomorphised
  monomorphise_expr defs s@(CILExprStruct fc n ty members) = assert_total $ do
      monoDefs <- get MonoDefs
      let monoDefMap = fromList $ (\x => (getName x, x)) <$> monoDefs
      let Just struct = (lookup n (mergeLeft defs monoDefMap))
          | _ => throw $ InternalError $ "Struct " ++ show n ++ " not found in " ++ show (mergeLeft defs monoDefMap)
      actualTypes <- traverse inferExprType members
      struct'@(MkCILStruct fc n' members') <- recompile_def defs struct actualTypes
      if n' /= n then do
        lamstr <- get LambdaStructEquiv
        let Just lambdaName = lookup n lamstr
            | _ => throw $ InternalError "Lambda not found"
        let mdefMap = fromList (zip (getName <$> !(get MonoDefs)) !(get MonoDefs))
        let Just lambdaFn@(MkCILFun _ _ lamargs return body) = lookup lambdaName (mergeLeft defs mdefMap)
            | _ => throw $ InternalError $ "Lambda function " ++ show lambdaName ++ " not found"
        lambdaFn'@(MkCILFun _ lamName' _ _ _) <- recompile_def defs lambdaFn (CILStruct n' members' ::  (snd <$> drop 1 lamargs))
        update MonoDefs (\x => struct' :: x)
        update LambdaStructEquiv (insert n' lamName')

        pure ([], CILExprStruct fc n' (CILStruct n' members') members) else pure ([], s)
  monomorphise_expr defs call@(CILExprCall fc callee stType@(CILStruct stName stMembers) args arg_types) = assert_total $ do

      (lifted, args) <- unzip <$> traverse (monomorphise_expr defs) args
      actualArgTypes <- traverse inferExprType args

      lamstr <- get LambdaStructEquiv
      let Just lambdaName = lookup stName lamstr
          | _ => throw $ InternalError $ "Lambda " ++ show stName ++ " not found in " ++ show lamstr

      let mdefMap = fromList $ (\x => (getName x, x)) <$> !(get MonoDefs)
      let Just lambdaFn@(MkCILFun _ _ lamargs _ _) = lookup lambdaName (mergeLeft defs mdefMap)
          | _ => throw $ InternalError $ "Lambda function " ++ show lambdaName ++ " not found"

      let lamargsNoStruct = case lamargs of
                          ((_, (CILStruct _ _)) :: xs) => xs
                          _ => lamargs

      if stricter (snd <$> lamargsNoStruct) actualArgTypes then do
          stName' <- pure $ MN (cName stName) (cast $ length !(get MonoDefs))
          let lamArgs' = case lamargs of
                          ((_, (CILStruct _ _)) :: xs) => (CILStruct stName' stMembers ::  (actualArgTypes))
                          _ => actualArgTypes
          lambdaFn'@(MkCILFun _ lamName' _ _ _) <- recompile_def defs lambdaFn lamArgs'
          
          let structDef' = MkCILStruct EmptyFC stName' stMembers
          update MonoDefs (\x => structDef' :: x)
          update LambdaStructEquiv (insert stName' lamName')
          let stType' = (CILStruct stName' stMembers)

          let argExprs = map (\(n, _) => CILExprField EmptyFC callee stType n) (Data.SortedMap.toList stMembers)
          let structExpr = (CILExprStruct EmptyFC stName' stType' argExprs)
          let stVarName = MN "st" (cast $ length !(get MonoDefs))
          let def = CILDeclare EmptyFC stType' stVarName (CILAssign EmptyFC stVarName structExpr)
          pure (concat lifted ++ [def], CILExprCall fc (CILExprLocal EmptyFC stVarName stType') stType' args actualArgTypes) -- fixme: hack, should properly lift a new struct definition
        else pure $ ([], CILExprCall fc callee (CILStruct stName stMembers) args arg_types)
  monomorphise_expr defs x = pure ([], x)

monomorphise_cil : {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> {auto _ : Ref MonoDefs (List CILDef)} -> SortedMap Name CILDef -> CIL e -> Core (CIL e)
monomorphise_cil defs (CILConstCase e fc sc xs y) = do
  (scLifted, sc') <- monomorphise_expr defs sc
  xs' <- traverseList1 (\(MkCILConstAlt e c cil) =>  MkCILConstAlt e c <$> monomorphise_cil defs cil) xs
  y' <- traverseOpt (monomorphise_cil defs) y
  pure $ prepend scLifted (CILConstCase e fc sc' xs' y')
monomorphise_cil defs (CILConCase x fc sc xs) = do
  (scLifted, sc') <- monomorphise_expr defs sc
  xs' <- traverseList1 (\(MkCILConAlt e c cil) => MkCILConAlt e c <$> monomorphise_cil defs cil) xs
  pure $ prepend scLifted $ CILConCase x fc sc' xs'
monomorphise_cil defs (CILBlock fc xs x) = do
  xs' <- traverse (monomorphise_cil defs) xs
  x' <- monomorphise_cil defs x
  pure $ CILBlock fc xs' x'
monomorphise_cil defs (CILAssign fc n x) = do
  (lifted, x') <- monomorphise_expr defs x
  pure $ prepend lifted $ CILAssign fc n x'
monomorphise_cil defs (CILReturn fc x) = do
  (lifted, x') <- monomorphise_expr defs x
  pure $ prepend lifted $ CILReturn fc x'
monomorphise_cil defs (CILDeclare fc x n y) = do
  y' <- monomorphise_cil defs y
  pure $ CILDeclare fc x n y'

monomorphise_def : {auto _ : Ref MonoDefs (List CILDef)} -> {auto _ : Ref LambdaStructEquiv (SortedMap Name Name)} -> SortedMap Name CILDef -> CILDef -> Core CILDef
monomorphise_def defs (MkCILFun fc n args return body) = do
  body' <- monomorphise_cil defs body
  (body',changed) <- fix_assign_types body'
  -- fixme: This is a hack to recompile the definition after fixing assign_types.
  --        Instead of vaguely recompiling we should pass through the types that changed.
  monodefs <- get MonoDefs
  let monodefmap = fromList $ (\x => (getName x, x)) <$> monodefs
  if changed 
    then assert_total $ monomorphise_def (mergeLeft defs monodefmap) (MkCILFun fc n args return body')
    else pure $ MkCILFun fc n args return body'
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
            