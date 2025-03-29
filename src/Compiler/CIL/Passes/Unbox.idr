module Compiler.CIL.Passes.Unbox

import Compiler.CIL.CIL
import Data.List
import Data.List1
import Compiler.Common
import Core.Core
import Data.SortedMap
import Core.Name
import Compiler.Common
import Core.Context
import Data.Vect
import Debug.Trace

%default covering

data CDefs  : Type where
data Unboxers : Type where

BoxMap : Type
BoxMap = SortedMap CILType CILDef

DefMap : Type
DefMap = SortedMap Name CILDef

constant : Constant -> CILType -> CILExpr
constant = CILExprConstant EmptyFC

makeInitializer : CILType -> CILExpr
makeInitializer CILU8 = constant (B8 0) CILU8
makeInitializer CILU16 = constant (B16 0) CILU16
makeInitializer CILU32 = constant (B32 0) CILU32
makeInitializer CILU64 = constant (B64 0) CILU64
makeInitializer CILI8 = constant (I8 0) CILI8
makeInitializer CILI16 = constant (I16 0) CILI16
makeInitializer CILI32 = constant (I32 0) CILI32
makeInitializer CILI64 = constant (I64 0) CILI64
makeInitializer CILF32 = constant (B32 0) CILF32
makeInitializer CILF64 = constant (B64 0) CILF64
makeInitializer (CILPtr x) = constant (B64 0) (CILPtr x)
makeInitializer CILWorld = constant (WorldVal) CILWorld
makeInitializer CILDyn = constant (B64 0) CILDyn
makeInitializer (CILFn xs x) = constant (B64 0) (CILFn xs x)
makeInitializer (CILStruct n x) = CILExprStruct EmptyFC n (CILStruct n x) [constant (B64 0) (CILU64)]
makeInitializer (CILTaggedUnion n xs) = do
  CILExprStruct EmptyFC n (CILStruct n (empty)) [constant (B64 0) CILU64]

getUnboxer : {auto _ : Ref CDefs DefMap} -> {auto _ : Ref Unboxers BoxMap} ->  CILType -> Core Name
getUnboxer to = do
  boxers <- get Unboxers
  case Data.SortedMap.lookup to boxers of
    Just (MkCILFun _ n _ _ _) => pure n
    Just _ => throw (InternalError "Unboxer is not a function")
    Nothing => do
      let n = MN "unbox" (cast $ length $ Data.SortedMap.toList boxers)
      let mallocType = CILFn [CILU64] CILDyn
      let memcpyType = CILFn [CILDyn, CILDyn, CILU64] CILDyn
      let body : CIL (Just Return) = CILBlock EmptyFC 
            [ CILDeclare EmptyFC to (MN "p" 0) (
                   CILAssign EmptyFC (MN "p" 0) (makeInitializer to))
            , CILDeclare EmptyFC CILDyn (MN "p" 1) (
                  CILAssign EmptyFC (MN "p" 1) (
                      CILExprCall EmptyFC (
                        CILExprRef EmptyFC (UN $ mkUserName "memcpy") memcpyType) 
                        memcpyType
                        [ CILExprAddrof EmptyFC (CILExprLocal EmptyFC (MN "p" 0) to)
                        , CILExprLocal EmptyFC (MN "arg" 0) CILDyn
                        , CILExprSizeof EmptyFC (CILExprLocal EmptyFC (MN "p" 0) to)] 
                        [CILDyn, CILDyn, CILU64]))
            ] (CILReturn EmptyFC (CILExprLocal EmptyFC (MN "p" 0) to))
      let def = MkCILFun (EmptyFC) n [((MN "arg" 0, CILDyn))] to body
      _ <- update Unboxers (insert to def)
      pure n

-- Like unboxExpr, but skips the first level
mutual
  deeper : {auto _ : Ref CDefs DefMap} -> {auto _ : Ref Unboxers BoxMap} -> CILExpr -> Core CILExpr
  deeper (CILExprCall fc ex fnt args argTys) = do
    ex' <- unboxExpr fnt ex
    case ex of 
      CILExprRef _ name _ => do
          defs <- get CDefs
          case (Data.SortedMap.lookup name defs) of
            (Just (MkCILFun _ _ realArgs _ _)) => do
                let argTys' = snd <$> realArgs 
                args' <- traverse (uncurry unboxExpr) (zip argTys' args) 
                -- _ <- pure $ traceVal $ "Call to " ++ show ex ++ " with args " ++ show (zip argTys args)
                fixedArgs <- traverse inferExprType args'
                pure $ CILExprCall fc ex' fnt args' fixedArgs
            _ => pure $ CILExprCall fc ex' fnt args argTys
      _ => pure $ CILExprCall fc ex' fnt args argTys
  deeper (CILExprOp fc f xs x) = pure $ CILExprOp fc f xs x
  deeper (CILExprConstant fc cst x) = pure $ CILExprConstant fc cst x
  deeper (CILExprLocal fc n x) = pure $ CILExprLocal fc n x
  deeper (CILExprStruct fc n ty args) = do
    (CILStruct _ membs) <- pure ty
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    args' <- traverse (uncurry unboxExpr) (zip argTys args)
    pure $ CILExprStruct fc n ty args'
  deeper (CILExprRef fc n x) = pure $ CILExprRef fc n x
  deeper (CILExprField fc x y n) = do
    x' <- unboxExpr y x
    pure $ CILExprField fc x' y n
  deeper (CILExprTaggedUnion fc n ty i xs) = do
    (CILTaggedUnion _ kinds) <- pure ty
      | _ => throw (InternalError "Expected tagged union type")
    Just tagIdx <- pure $ natToFin (cast i) (length kinds) 
      | _ => throw (InternalError "Invalid tag")
    let argTy = index' kinds tagIdx 
    (CILStruct _ membs) <- pure argTy
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    args' <- traverse (uncurry unboxExpr) (zip argTys xs)
    pure $ CILExprTaggedUnion fc n ty i args'
  deeper (CILExprSizeof fc x) = pure $ CILExprSizeof fc x
  deeper (CILExprAddrof fc x) = pure $ CILExprAddrof fc x


  unboxExpr : {auto _ : Ref CDefs DefMap} -> {auto _ : Ref Unboxers BoxMap} -> CILType -> CILExpr -> Core CILExpr
  unboxExpr t x = unboxExpr' t !(inferExprType x) x
    where unboxExpr' : CILType -> CILType -> CILExpr -> Core CILExpr
          unboxExpr' exp CILDyn expr = if exp == CILWorld 
            then pure expr
              else if exp == CILDyn 
                then deeper expr
                else do
                _ <- pure $ traceVal $ "Unboxing " ++ show expr ++ " to type " ++ show exp
                convertDef <- getUnboxer exp
                let unboxerType = CILFn [CILDyn] exp
                -- expr' <- unboxExpr from expr
                pure $ traceVal $ CILExprCall EmptyFC (CILExprRef EmptyFC convertDef unboxerType) unboxerType [expr] [exp]
          unboxExpr' _ _ (CILExprCall fc ex fnt args argTys) = do
            ex' <- unboxExpr fnt ex
            case ex of 
              CILExprRef _ name _ => do
                  defs <- get CDefs
                  case (Data.SortedMap.lookup name defs) of
                    (Just (MkCILFun _ _ realArgs _ _)) => do
                        let argTys' = snd <$> realArgs 
                        args' <- traverse (uncurry unboxExpr) (zip argTys' args) 
                        -- _ <- pure $ traceVal $ "Call to " ++ show ex ++ " with args " ++ show (zip argTys args)
                        fixedArgs <- traverse inferExprType args'
                        pure $ CILExprCall fc ex' fnt args' fixedArgs
                    _ => pure $ CILExprCall fc ex' fnt args argTys
              _ => pure $ CILExprCall fc ex' fnt args argTys
          unboxExpr' exp _ (CILExprOp fc f xs x) = do
            xs' <- traverseVect (unboxExpr exp) xs
            pure $ CILExprOp fc f xs' x
          unboxExpr' _ _ expr@(CILExprLocal fc n x) = pure expr
          unboxExpr' _ _ (CILExprStruct fc n ty args) = do 
            (CILStruct _ membs) <- pure ty
              | _ => throw (InternalError "Expected struct type")
            let argTys = snd <$> toList membs
            args' <- traverse (uncurry unboxExpr) (zip argTys args)
            pure $ CILExprStruct fc n ty args'
          unboxExpr' _ _ expr@(CILExprRef fc n x) = pure expr
          unboxExpr' _ _ (CILExprField fc ex ty n) = do
            ex' <- unboxExpr ty ex
            pure $ CILExprField fc ex' ty n
          unboxExpr' exp _ (CILExprTaggedUnion fc n ty tag args) = do
            (CILTaggedUnion _ kinds) <- pure ty
              | _ => throw (InternalError "Expected tagged union type")
            Just tagIdx <- pure $ natToFin (cast tag) (length kinds) 
              | _ => throw (InternalError "Invalid tag")
            let argTy = index' kinds tagIdx 
            (CILStruct _ membs) <- pure argTy
              | _ => throw (InternalError "Expected struct type")
            let argTys = snd <$> toList membs
            args' <- traverse (uncurry unboxExpr) (zip argTys args)
            pure $ CILExprTaggedUnion fc n ty tag args'
          unboxExpr' _ _ (CILExprConstant fc cst x) = pure (CILExprConstant fc cst x)
          unboxExpr' _ _ (CILExprSizeof fc x) = pure (CILExprSizeof fc x)
          unboxExpr' _ _ (CILExprAddrof fc x) = pure (CILExprAddrof fc x)


unboxCIL :  {auto _ : Ref CDefs DefMap} -> {auto _ : Ref Unboxers BoxMap} -> CILType -> CIL e -> Core (CIL e)
unboxCIL ty (CILConstCase e fc sc xs y) = do
  xs' <- traverseList1 (\(MkCILConstAlt e n c) => pure $ MkCILConstAlt e n !(unboxCIL ty c)) xs
  let (MkCILConstAlt _ c _) = head xs'
  sc' <- unboxExpr !(inferConstType c) sc
  def' <- traverseOpt (unboxCIL ty) y
  pure $ CILConstCase e fc sc xs' def'
unboxCIL ty (CILConCase e fc sc xs) = do
  sc' <- unboxExpr (CILI64) sc
  xs' <- traverseList1 (\(MkCILConAlt e t cil) => pure $ MkCILConAlt e t !(unboxCIL ty cil)) xs
  pure $ CILConCase e fc sc' xs'
unboxCIL ty (CILBlock fc xs x) = do
  xs' <- traverse (unboxCIL CILDyn) xs
  x' <- unboxCIL ty x
  pure $ CILBlock fc xs' x'
unboxCIL ty (CILAssign fc n x) = pure $ CILAssign fc n !(unboxExpr ty x)
unboxCIL ty (CILReturn fc x) =  pure $ CILReturn fc !(unboxExpr ty x)
unboxCIL _  (CILDeclare fc ty n cil) = pure $ CILDeclare fc ty n !(unboxCIL ty cil)

unboxDef : {auto _ : Ref CDefs DefMap} -> {auto _ : Ref Unboxers BoxMap} -> CILDef -> Core CILDef
unboxDef (MkCILFun fc n args return body) = do
    _ <- pure $ traceVal $ "---------- Unboxing function " ++ show n
    body <- unboxCIL return body
    pure $ MkCILFun fc n args return body
unboxDef x = pure x

public export
unboxDefs : List CILDef -> Core (List CILDef)
unboxDefs defs = do 
    let defMap = (fromList (zip (getName <$> defs) defs))
    _ <- newRef CDefs defMap
    _ <- newRef Unboxers empty
    defs <- traverse unboxDef defs
    pure (defs ++ (snd <$> toList !(get Unboxers)))