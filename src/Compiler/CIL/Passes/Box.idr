||| This pass boxes values of known types where a boxed value is expected.
module Compiler.CIL.Passes.Box

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

%default covering

data Boxers : Type where

BoxMap : Type
BoxMap = SortedMap CILType CILDef

getBoxer : {auto _ : Ref Boxers BoxMap} ->  CILType -> Core Name
getBoxer from = do
  boxers <- get Boxers
  case lookup from boxers of
    Just (MkCILFun _ n _ _ _) => pure n
    Just _ => throw (InternalError "Boxer is not a function")
    Nothing => do
      let n = MN "box" (cast $ length $ Data.SortedMap.toList boxers)
      let mallocType = CILFn [CILU64] CILDyn
      let memcpyType = CILFn [CILDyn, CILDyn, CILU64] CILDyn
      let body = CILBlock EmptyFC
            [CILDeclare EmptyFC CILDyn (MN "p" 0) (
                  CILAssign EmptyFC (MN "p" 0) (
                      CILExprCall EmptyFC (
                        CILExprRef EmptyFC (UN $ mkUserName "malloc") mallocType)
                        mallocType
                        [CILExprSizeof EmptyFC (CILExprLocal EmptyFC (MN "arg" 0) from)]
                        [CILU64])),
             CILDeclare EmptyFC CILDyn (MN "p" 1) (
                  CILAssign EmptyFC (MN "p" 1) (
                      CILExprCall EmptyFC (
                        CILExprRef EmptyFC (UN $ mkUserName "memcpy") memcpyType)
                        memcpyType
                        [CILExprLocal EmptyFC (MN "p" 0) CILDyn
                        , CILExprAddrof EmptyFC (CILExprLocal EmptyFC (MN "arg" 0) from)
                        , CILExprSizeof EmptyFC (CILExprLocal EmptyFC (MN "arg" 0) from)]
                        [CILDyn, CILDyn, CILU64]))
            ] (CILReturn EmptyFC (CILExprLocal EmptyFC (MN "p" 1) CILDyn))
      let def = MkCILFun (EmptyFC) n [((MN "arg" 0, from))] CILDyn body
      _ <- update Boxers (insert from def)
      pure n

mutual
  ||| Like `boxExpr`, but one level deeper.
  deeper : {auto _ : Ref Boxers BoxMap} -> CILExpr -> Core CILExpr
  deeper (CILExprCall fc x y xs ys) = do
    x' <- boxExpr y x
    xs' <- traverse (boxExpr y) xs
    pure $ CILExprCall fc x' y xs' ys
  deeper (CILExprOp fc f xs x) = do
    xs' <- traverseVect (boxExpr CILDyn) xs
    pure $ CILExprOp fc f xs' x
  deeper (CILExprConstant fc cst x) = pure $ CILExprConstant fc cst x
  deeper (CILExprLocal fc n x) = pure $ CILExprLocal fc n x
  deeper (CILExprStruct fc n x xs) = do
    (CILStruct _ membs) <- pure x
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    xs' <- traverse (uncurry boxExpr) (zip argTys xs)
    pure $ CILExprStruct fc n x xs'
  deeper (CILExprRef fc n x) = pure $ CILExprRef fc n x
  deeper (CILExprField fc x y n) = do
    x' <- boxExpr y x
    pure $ CILExprField fc x' y n
  deeper (CILExprTaggedUnion fc n x i xs) = do
    (CILTaggedUnion _ kinds) <- pure x
      | _ => throw (InternalError "Expected tagged union type")
    Just tagIdx <- pure $ natToFin (cast i) (length kinds)
      | _ => throw (InternalError "Invalid tag")
    let argTy = index' kinds tagIdx
    (CILStruct _ membs) <- pure argTy
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    xs' <- traverse (uncurry boxExpr) (zip argTys xs)
    pure $ CILExprTaggedUnion fc n x i xs'
  deeper (CILExprSizeof fc x) = do
    x' <- boxExpr CILDyn x
    pure $ CILExprSizeof fc x'
  deeper (CILExprAddrof fc x) = do
    x' <- boxExpr CILDyn x
    pure $ CILExprAddrof fc x'

  boxExpr : {auto _ : Ref Boxers BoxMap} -> CILType -> CILExpr -> Core CILExpr
  boxExpr CILDyn expr = if !(inferExprType expr) == CILDyn then deeper expr
    else do
      from <- inferExprType expr
      convertDef <- getBoxer from
      let boxerType = CILFn [from] CILDyn
      expr' <- boxExpr from expr
      pure $ CILExprCall EmptyFC (CILExprRef EmptyFC convertDef boxerType) boxerType [expr'] [from]
  boxExpr exp call@(CILExprCall fc ex fnt args argTys) = do
    ex' <- boxExpr fnt ex
    let argTys = case fnt of
          (CILFn argTys _) => argTys
          _ => argTys
    args' <- traverse (uncurry boxExpr) (zip argTys args)
    pure $ CILExprCall fc ex' fnt args' argTys
  boxExpr exp (CILExprOp fc f xs x) = do
    xs' <- traverseVect (boxExpr exp) xs
    pure $ CILExprOp fc f xs' x
  boxExpr _ expr@(CILExprLocal fc n x) = pure expr
  boxExpr _ (CILExprStruct fc n ty args) = do
    (CILStruct _ membs) <- pure ty
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    args' <- traverse (uncurry boxExpr) (zip argTys args)
    pure $ CILExprStruct fc n ty args'
  boxExpr _ expr@(CILExprRef fc n x) = pure expr
  boxExpr _ (CILExprField fc ex ty n) = do
    ex' <- boxExpr ty ex
    pure $ CILExprField fc ex' ty n
  boxExpr exp (CILExprTaggedUnion fc n ty tag args) = do
    (CILTaggedUnion _ kinds) <- pure ty
      | _ => throw (InternalError "Expected tagged union type")
    Just tagIdx <- pure $ natToFin (cast tag) (length kinds)
      | _ => throw (InternalError "Invalid tag")
    let argTy = index' kinds tagIdx
    (CILStruct _ membs) <- pure argTy
      | _ => throw (InternalError "Expected struct type")
    let argTys = snd <$> toList membs
    args' <- traverse (uncurry boxExpr) (zip argTys args)
    pure $ CILExprTaggedUnion fc n ty tag args'
  boxExpr _ (CILExprConstant fc cst x) = pure (CILExprConstant fc cst x)
  boxExpr _ (CILExprSizeof fc x) = do
    x' <- boxExpr CILDyn x
    pure $ CILExprSizeof fc x'
  boxExpr _ (CILExprAddrof fc x) = do
    x' <- boxExpr CILDyn x
    pure $ CILExprAddrof fc x'


boxCIL : {auto _ : Ref Boxers BoxMap} -> CILType -> CIL e -> Core (CIL e)
boxCIL ty (CILConstCase e fc sc xs y) = do
  xs' <- traverseList1 (\(MkCILConstAlt e n c) => pure $ MkCILConstAlt e n !(boxCIL ty c)) xs
  let (MkCILConstAlt _ c _) = head xs'
  sc' <- boxExpr !(inferConstType c) sc
  def' <- traverseOpt (boxCIL ty) y
  pure $ CILConstCase e fc sc' xs' def'
boxCIL ty (CILConCase e fc sc xs) = do
  sc' <- boxExpr (CILI64) sc
  xs' <- traverseList1 (\(MkCILConAlt e t cil) => pure $ MkCILConAlt e t !(boxCIL ty cil)) xs
  pure $ CILConCase e fc sc' xs'
boxCIL ty (CILBlock fc xs x) = do
  xs' <- traverse (boxCIL CILDyn) xs
  x' <- boxCIL ty x
  pure $ CILBlock fc xs' x'
boxCIL ty (CILAssign fc n x) = pure $ CILAssign fc n !(boxExpr ty x)
boxCIL ty (CILReturn fc x) =  pure $ CILReturn fc !(boxExpr ty x)
boxCIL _  (CILDeclare fc ty n cil) = pure $ CILDeclare fc ty n !(boxCIL ty cil)

boxDef : {auto _ : Ref Boxers BoxMap} -> CILDef -> Core CILDef
boxDef (MkCILFun fc n args return body) = do
    body <- boxCIL return body
    pure $ MkCILFun fc n args return body
boxDef x = pure x

public export
boxDefs : List CILDef -> Core (List CILDef)
boxDefs defs = do
    _ <- newRef Boxers empty
    defs <- traverse boxDef defs
    pure (defs ++ (snd <$> toList !(get Boxers)))
