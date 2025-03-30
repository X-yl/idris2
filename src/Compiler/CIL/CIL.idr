||| C intermediate language compiler backend

module Compiler.CIL.CIL

import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Env
import Core.FC
import Core.Name
import Core.TT.Binder
import Core.TT.Term
import Data.List1
import Data.SnocList
import Data.SortedMap
import Data.Vect
import Idris.Syntax

%default covering

mutual
  public export
    data Effect : Type where
      Assign : Name -> Effect
      Return : Effect

  public export
    data CIL : (e: Maybe Effect) -> Type where
      CILConstCase : (e: Effect) -> FC -> (sc: CILExpr) -> List1 (CILConstAlt e) -> Maybe (CIL (Just e)) -> CIL (Just e)
      CILConCase   : (e: Effect) -> FC -> (sc: CILExpr) -> List1 (CILConAlt e)  -> CIL (Just e)
      CILBlock : FC -> List (CIL Nothing) -> CIL e -> CIL e
      CILAssign : FC -> (n: Name) -> CILExpr -> CIL (Just (Assign n))
      CILReturn : FC -> CILExpr -> CIL (Just Return)
      CILDeclare : FC -> CILType -> (n: Name) -> CIL (Just (Assign n)) -> CIL Nothing

  public export
    Show Effect where
      show (Assign n) = "Assign " ++ show n
      show Return = "Return"

  public export
    data CILExpr : Type where
      CILExprCall : FC -> CILExpr -> CILType -> List CILExpr -> List CILType -> CILExpr
      CILExprOp : {arity: _} -> FC -> PrimFn arity -> Vect arity CILExpr -> CILType -> CILExpr
      CILExprConstant : FC -> Constant -> CILType -> CILExpr
      CILExprLocal : FC -> Name -> CILType -> CILExpr
      CILExprStruct : FC -> Name -> CILType -> List CILExpr -> CILExpr
      CILExprRef : FC -> Name -> CILType -> CILExpr
      CILExprField : FC -> CILExpr -> CILType -> Name -> CILExpr
      CILExprTaggedUnion : FC -> Name -> CILType -> Int -> List CILExpr -> CILExpr
      CILExprSizeof : FC -> CILExpr -> CILExpr
      CILExprAddrof : FC -> CILExpr -> CILExpr

  public export
    data CILConstAlt : (e: Effect) -> Type where
      MkCILConstAlt : (e: Effect) -> Constant -> CIL (Just e) -> CILConstAlt e

  public export
    data CILConAlt  : (e: Effect) -> Type where
      MkCILConAlt   : (e: Effect) -> (tag: Int) -> CIL (Just e) -> CILConAlt e

  covering
  public export
    Show (CILConstAlt e) where
      show (MkCILConstAlt e c b) = assert_total $ "MkCILConstAlt (" ++ show e ++ " " ++ show c ++ " " ++ show b ++ ")"

  covering
  public export
    Show (CILConAlt e) where
      show (MkCILConAlt e t b) = assert_total $ "MkCILConAlt (" ++ show e ++ " " ++ show t ++ " " ++ show b ++ ")"

  covering
  public export
    Show (CIL e) where
      show (CILConstCase e fc sc alts def) = assert_total $ "CILConstCase (" ++ show e ++ " " ++ show sc ++ " " ++ show alts ++ " " ++ show def ++ ")"
      show (CILBlock fc stmts target) = assert_total $ "CILBlock (" ++ show stmts ++ " " ++ show target ++ ")"
      show (CILAssign fc n expr) = assert_total $ "CILAssign (" ++ show n ++ " " ++ show expr ++ ")"
      show (CILReturn fc expr) = assert_total $ "CILReturn (" ++ show expr ++ ")"
      show (CILDeclare fc ty name sc) = assert_total $ "CILDeclare (" ++ show ty ++ show name ++ " " ++ show sc ++ ")"
      show (CILConCase e fc sc alts) = assert_total $ "CILConCase (" ++ show e ++ " " ++ show sc ++ " " ++ show alts ++ ")"

  public export
    Show CILExpr where
      show (CILExprCall fc name ty1 args ty2) = assert_total $ "CILCall (" ++ show name ++ " " ++ show args ++ " : " ++ show ty2 ++  ")"
      show (CILExprOp fc fn args ty) = assert_total $ "CILOp (" ++ show fn ++ " " ++ (show args) ++ ")"
      show (CILExprLocal fc name ty) = "CILExprLocal (" ++ show name ++ " : " ++ show ty ++ ")"
      show (CILExprConstant fc c ty) = "CILConstant (" ++ show c ++ ")"
      show (CILExprRef fc name ty) = "CILRef (" ++ show name ++ " : " ++ show ty  ++ ")"
      show (CILExprStruct fc name ty args) = assert_total $ "CILStruct (" ++ show name ++ " " ++ show args ++ " : " ++ show ty ++ ")"
      show (CILExprField fc name ty field) = assert_total $ "CILField (" ++ show name ++ " " ++ show field ++ " : " ++ show ty ++ ")"
      show (CILExprTaggedUnion fc name ty kind args) = assert_total $ "CILTaggedUnion (" ++ show name ++ " " ++ show kind ++ " " ++ show args ++ ")"
      show (CILExprSizeof fc expr) = assert_total $ "sizeof (" ++ show expr ++ ")"
      show (CILExprAddrof fc expr) = assert_total $ "&(" ++ show expr ++ ")"

  public export
    data CILDef : Type where
      MkCILFun : FC -> Name -> (args: List (Name, CILType)) -> (return: CILType) -> (body: CIL (Just Return)) -> CILDef
      MkCILStruct : FC -> Name -> (members: SortedMap Name CILType) -> CILDef
      MkCILTaggedUnion : FC -> Name -> (datacons: List Name) -> (kinds: List (CILType)) -> CILDef -- a tagged union is a union of structs
      MkCILForeign : FC -> Name -> (args: List CILType) -> (return: CILType) -> (external: String) -> CILDef

  covering
  public export
    Show CILDef where
      show (MkCILFun fc name args ret body) = assert_total $ "MkCILFun (" ++ show name ++ " " ++ show args ++ " " ++ show ret ++ " " ++ show body ++ ")"
      show (MkCILStruct fc name members) = assert_total $ "MkCILStruct (" ++ show name ++ " " ++ show members ++ ")"
      show (MkCILTaggedUnion fc name datacons kinds) = assert_total $ "MkCILTaggedUnion (" ++ show name ++ " " ++ show datacons ++ " " ++ show kinds ++ ")"
      show (MkCILForeign fc name args external ret) = assert_total $ "MkCILForeign (" ++ show name ++ " " ++ show args ++ " " ++ show ret ++ " : " ++ show external ++ ") "

  public export
    data CILType : Type where
      CILU8 : CILType
      CILU16 : CILType
      CILU32 : CILType
      CILU64 : CILType
      CILI8 : CILType
      CILI16 : CILType
      CILI32 : CILType
      CILI64 : CILType
      CILF32 : CILType
      CILF64 : CILType
      CILPtr : CILType -> CILType
      CILWorld : CILType
      CILDyn : CILType -- Dynamic type, not known at compile time
      CILFn : List CILType -> CILType -> CILType
      CILStruct : Name -> SortedMap Name CILType -> CILType
      CILTaggedUnion : Name -> List (CILType) -> CILType -- the inner CILType should be CILStruct

  public export
  Eq CILType where
    CILU8 == CILU8 = True
    CILU16 == CILU16 = True
    CILU32 == CILU32 = True
    CILU64 == CILU64 = True
    CILI8 == CILI8 = True
    CILI16 == CILI16 = True
    CILI32 == CILI32 = True
    CILI64 == CILI64 = True
    CILF32 == CILF32 = True
    CILF64 == CILF64 = True
    CILWorld == CILWorld = True
    CILDyn == CILDyn = True
    CILFn args ret == CILFn args' ret' = assert_total $ args == args' && ret == ret'
    CILPtr t == CILPtr t' = assert_total $ t == t'
    CILStruct name members == CILStruct name' members' = assert_total $ name == name' && members == members'
    CILTaggedUnion name kinds == CILTaggedUnion name' kinds' = assert_total $ name == name' && kinds == kinds'
    _ == _ = False

  typeTag : CILType -> Int
  typeTag CILU8 = 0
  typeTag CILU16 = 1
  typeTag CILU32 = 2
  typeTag CILU64 = 3
  typeTag CILI8 = 4
  typeTag CILI16 = 5
  typeTag CILI32 = 6
  typeTag CILI64 = 7
  typeTag CILF32 = 8
  typeTag CILF64 = 9
  typeTag CILWorld = 10
  typeTag CILDyn = 11
  typeTag (CILFn _ _) = 12
  typeTag (CILPtr _) = 13
  typeTag (CILStruct _ _) = 14
  typeTag (CILTaggedUnion _ _) = 15

  public export
  Ord CILType where
    compare x y = if x == y then EQ else compare' x y
      where
        compare' : CILType -> CILType -> Ordering
        compare' (CILFn args ret) (CILFn args' ret') = assert_total $ compare (args, ret) (args', ret')
        compare' (CILPtr t) (CILPtr t') = assert_total $ compare t t'
        compare' (CILStruct name members) (CILStruct name' members') =
          assert_total $ case compare name name' of
            EQ => compare (Data.SortedMap.toList members) (toList members')
            x => x
        compare' (CILTaggedUnion name kinds) (CILTaggedUnion name' kinds') =
          assert_total $ case compare name name' of
            EQ => compare kinds kinds'
            x => x
        compare' x y = assert_total $ compare (typeTag x) (typeTag y)


  public export
  Show CILType where
    show CILU8 = "u8"
    show CILU16 = "u16"
    show CILU32 = "u32"
    show CILU64 = "u64"
    show CILI8 = "i8"
    show CILI16 = "i16"
    show CILI32 = "i32"
    show CILI64 = "i64"
    show CILF32 = "f32"
    show CILF64 = "f64"
    show CILWorld = "void*" -- World type
    show (CILPtr t) = show t ++ "*"
    show CILDyn = "dyn"
    show (CILFn args ret) = assert_total $ "(" ++ show args ++ " -> " ++ show ret ++ ")"
    show ((CILStruct name members)) = assert_total $ "{" ++ show name ++ show members ++ "}"
    show (CILTaggedUnion name kinds) = assert_total $ "TaggedUnion " ++ show name ++ " " ++ show kinds

public export
inferPrimType : PrimType -> CILType
inferPrimType IntType = CILI32
inferPrimType Int8Type = CILI8
inferPrimType Int16Type = CILI16
inferPrimType Int32Type =  CILI32
inferPrimType Int64Type = CILI64
inferPrimType IntegerType = CILI64
inferPrimType Bits8Type = CILU8
inferPrimType Bits16Type = CILU16
inferPrimType Bits32Type = CILU32
inferPrimType Bits64Type = CILU64
inferPrimType StringType = CILPtr CILI8
inferPrimType CharType = CILI8
inferPrimType DoubleType = CILF64
inferPrimType WorldType = CILWorld

public export
getName : CILDef -> Name
getName (MkCILFun _ n _ _ _) = n
getName (MkCILStruct _ n _) = n
getName (MkCILTaggedUnion _ n _ _) = n
getName (MkCILForeign _ n _ _ _) = n

record DataCon where
  constructor MkDataCon
  name  : Name
  tag   : Int
  arity : Nat
  type  : ClosedTerm
  flags : List DefFlag

Show DataCon where
  show (MkDataCon n t a ty flags) = assert_total $  "MkDataCon " ++ show n ++ " " ++ show t ++ " " ++ show a ++ " " ++ show ty ++ show flags

getCons :
          Defs -> Name -> Core (List DataCon)
getCons defs tn
    = case !(lookupDefExact tn (gamma defs)) of
           Just (TCon _ _ _ _ _ _ cons _) =>
                do cs' <- traverse addTy cons
                   pure (catMaybes cs')
           _ => throw (InternalError "Called `getCons` on something that is not a Type constructor")
  where
    addTy : Name -> Core (Maybe DataCon)
    addTy cn
        = do Just gdef <- lookupCtxtExact cn (gamma defs)
                  | _ => pure Nothing
             case (gdef.definition, gdef.type) of
                  (DCon t arity _, ty) =>
                        pure . Just $ MkDataCon gdef.fullname t arity ty gdef.flags
                  _ => pure Nothing

isNat : List DefFlag -> Bool
isNat [] = False
isNat ((ConType ZERO) :: xs) = True
isNat ((ConType SUCC) :: xs) = True
isNat ((ConType _) :: xs) = False
isNat (_ :: xs) = isNat xs

isUnit : List DefFlag -> Bool
isUnit [] = False
isUnit ((ConType UNIT) :: xs) = True
isUnit ((ConType _) :: xs) = False
isUnit (_ :: xs) = isUnit xs

mutual
  public export
  inferConstType : Constant -> Core CILType
  inferConstType (I i) = pure CILI64
  inferConstType (I8 i) = pure CILI8
  inferConstType (I16 i) = pure CILI16
  inferConstType (I32 i) = pure CILI32
  inferConstType (I64 i) = pure CILI64
  inferConstType (BI i) = pure CILI64
  inferConstType (B8 m) = pure CILU8
  inferConstType (B16 m) = pure CILU16
  inferConstType (B32 m) = pure CILU32
  inferConstType (B64 m) = pure CILU64
  inferConstType (Str str) = pure (CILPtr CILU8)
  inferConstType (Ch c) = pure CILU8
  inferConstType (Db dbl) = pure CILF64
  inferConstType (PrT ty) = pure $ inferPrimType ty
  inferConstType WorldVal = pure CILWorld

  fnType : {auto c : Ref Ctxt Defs} -> Term _ -> Core (List CILType, CILType)
  fnType = fnType' []

  fnType' : {auto c : Ref Ctxt Defs} -> (seen: List Name) -> Term _ -> Core (List CILType, CILType)
  fnType' _ (Local fc isLet idx p) = pure ([], CILDyn)
  fnType' _ (Meta fc n i ts)       = pure ([], CILDyn)
  fnType' seen (Bind fc x b scope)    = do
    t <- (case b of
              Pi fc rc info type  => termToCILType seen type
              _                   => pure CILDyn)
    _ <- pure $ "Bind " ++ show t
    (rest, rtn) <- fnType' seen scope
    pure (t::rest, rtn)
  fnType' _ (App fc fn arg)        = do
    let isIO = case fn of
            Ref _ _ n => (show n) == "PrimIO.IO" || (show n) == "PrimIO.PrimIO"
            _ => False
    if isIO
      then pure ([CILWorld], CILDyn)
      else pure ([], CILDyn)
  fnType' _ (As fc side as pat)    =  pure ([], CILDyn)
  fnType' seen (TDelayed fc lz t)  =  pure ([], !(termToCILType seen t))
  fnType' _ (TDelay fc lz ty arg)  =  pure ([], CILDyn)
  fnType' _ (TForce fc lz t)       =  pure ([], CILDyn)
  fnType' seen (t@(PrimVal fc c))  =  pure ([], !(termToCILType seen t))
  fnType' seen r@(Ref fc (TyCon tag arity) n) =  pure ([], !(termToCILType seen r))
  fnType' _ (Ref fc (DataCon t a) name) = do
    pure ([], CILDyn)
  fnType' _ (Ref fc nt name)       =  pure ([], CILDyn)
  fnType' _ (Erased fc why)        =  pure ([], CILDyn)
  fnType' _ (TType fc n)           =  pure ([], CILDyn)

  termToCILType : {auto c : Ref Ctxt Defs} -> (seen: List Name) -> Term _ -> Core CILType
  termToCILType _ (PrimVal fc (PrT x)) =  pure $  inferPrimType x
  termToCILType _ (PrimVal fc x) =  inferConstType (x)
  termToCILType seen term@(Bind _ _ _ _) = do (args, ret) <- (fnType' seen term)
                                              pure $ CILFn args ret
  termToCILType seen (Ref fc (TyCon tag arity) n) = do
    defs <- get Ctxt
    n' <- case !(lookupCtxtExact n (gamma defs)) of
            Just x => pure $ fullname x
            _ => throw $ InternalError $ "Type constructor " ++ show n ++ " not found"
    if n' `elem` seen
      then pure CILDyn -- Recursion detected, so use a boxed type.
      else do
        defs <- get Ctxt
        cons <- getCons defs n'
        if all (\(MkDataCon _ _ _ _ flags) => isUnit flags) cons
          then pure CILWorld
          else if (all (\(MkDataCon _ _ a _ _) => a == 0) cons) || (all (\(MkDataCon _ _ _ _ flags) => isNat flags) cons)
            then pure CILU64 -- Enum type or Nat
            else do
              (consArgs, _) <- unzip <$> traverse (\(MkDataCon _ _ _ ty _) => fnType' (n' :: seen) ty) cons
              let indexes = allFins (length consArgs)
              asStructs <- traverse (\(i,members) => do
                  let indexes = (cast . finToInteger) <$> allFins (length members)
                  let memMap = fromList $ zip (map (MN "arg") indexes) members
                  pure $ CILStruct (MN ("tag") (cast $ finToInteger i)) memMap
                ) (zip indexes consArgs)
              let tagUnionType = CILTaggedUnion n' asStructs
              pure tagUnionType
  termToCILType seen x = pure CILDyn


data Locals : Type where
data Lambdas : Type where
data Structs : Type where
data TagUnions : Type where
data ConstructorMap : Type where
data Refs : Type where
data LambdaStructEquiv : Type where

nextLocal : {auto _ : Ref Locals (SortedMap Name CILType)} -> Core Name
nextLocal = do
  ns <- get Locals
  let next = cast $ 1 + length (Data.SortedMap.toList ns)
  update Locals $ insert (MN "local" next) CILDyn
  pure $ MN "local" next

updateLocalType : {auto _ : Ref Locals (SortedMap Name CILType)} -> Name -> CILType -> Core ()
updateLocalType n t = update Locals $ insert n t

lookupLocalType : {auto _ : Ref Locals (SortedMap Name CILType)} -> Name -> Core CILType
lookupLocalType t = do ns <- get Locals
                       Just ty <- pure $ lookup t ns
                         | _ => throw $ InternalError $ "Local " ++ show t ++ " not found in" ++ show ns
                       pure ty
nextStruct : {auto _ : Ref Structs (SortedMap Name (SortedMap Name CILType))} -> SortedMap Name CILType -> Core Name
nextStruct membs = do
  ns <- get Structs
  let next = cast $ 1 + length (Data.SortedMap.toList ns)
  update Structs $ insert (MN "struct" next) membs
  pure $ MN "struct" next

inferOpArgType : PrimFn a -> CILType
inferOpArgType (Add ty) = inferPrimType ty
inferOpArgType (Sub ty) = inferPrimType ty
inferOpArgType (Mul ty) = inferPrimType ty
inferOpArgType (Div ty) = inferPrimType ty
inferOpArgType (Mod ty) = inferPrimType ty
inferOpArgType (Neg ty) = inferPrimType ty
inferOpArgType (ShiftL ty) = inferPrimType ty
inferOpArgType (ShiftR ty) = inferPrimType ty
inferOpArgType (BAnd ty) = inferPrimType ty
inferOpArgType (BOr ty) = inferPrimType ty
inferOpArgType (BXOr ty) = inferPrimType ty
inferOpArgType (LT ty) = inferPrimType ty
inferOpArgType (LTE ty) = inferPrimType ty
inferOpArgType (EQ ty) = inferPrimType ty
inferOpArgType (GTE ty) = inferPrimType ty
inferOpArgType (GT ty) = inferPrimType ty
inferOpArgType StrLength = CILPtr CILU8
inferOpArgType StrHead = CILPtr CILU8
inferOpArgType StrTail = CILPtr CILU8
inferOpArgType StrIndex = CILPtr CILU8
inferOpArgType StrCons = CILPtr CILU8
inferOpArgType StrAppend = CILPtr CILU8
inferOpArgType StrReverse = CILPtr CILU8
inferOpArgType StrSubstr = CILPtr CILU8
inferOpArgType DoubleExp = CILF64
inferOpArgType DoubleLog = CILF64
inferOpArgType DoublePow = CILF64
inferOpArgType DoubleSin = CILF64
inferOpArgType DoubleCos = CILF64
inferOpArgType DoubleTan = CILF64
inferOpArgType DoubleASin = CILF64
inferOpArgType DoubleACos = CILF64
inferOpArgType DoubleATan = CILF64
inferOpArgType DoubleSqrt = CILF64
inferOpArgType DoubleFloor = CILF64
inferOpArgType DoubleCeiling = CILF64
inferOpArgType (Cast pty pty1) = inferPrimType pty1
inferOpArgType BelieveMe = CILDyn
inferOpArgType Crash = CILDyn


public export
inferExprType : CILExpr -> Core CILType
inferExprType (CILExprCall fc x ty1 xs ty2) = do
  case ty1 of
    CILFn args ret => if length args == length xs || length args == 0
                      then pure ret
                      else pure $ CILFn (drop (length xs) args) ret
    _              => pure CILDyn
inferExprType (CILExprOp fc f xs ty) = pure ty
inferExprType (CILExprConstant fc cst ty) = pure ty
inferExprType (CILExprLocal fc n ty) = pure ty
inferExprType (CILExprRef fc n ty) = pure ty
inferExprType (CILExprStruct fc n ty _) = pure ty
inferExprType exp@(CILExprField fc n ty f) = do
  case ty of
    CILStruct name members => maybe (pure CILDyn) pure (lookup f members)
    CILTaggedUnion _ kinds =>
      case f of
        (UN (Basic "tag")) => pure CILI64
        (MN "tag" tag) => do
          Just i <- pure $ natToFin (cast tag) (length kinds)
            | _ => throw $ InternalError $ "tag out of bounds " ++ show tag
          pure (index' kinds i)
        _ => throw $ InternalError $ "Tag union field access on non-tag field " ++ show f
    _           => throw $ InternalError $ "Field access on non-struct " ++ show exp
inferExprType (CILExprTaggedUnion fc n ty k xs) = pure ty
inferExprType (CILExprSizeof fc expr) = pure CILU64
inferExprType (CILExprAddrof fc expr) = pure $ CILPtr !(inferExprType expr)

public export
inferType : CIL (Just e) -> Core CILType
inferType (CILConstCase e fc sc xs y) = do altsTypes <- traverseList1 (\(MkCILConstAlt _ _ x) => inferType x) xs
                                           if all (== head altsTypes) altsTypes
                                             then pure $ head altsTypes
                                             else pure CILDyn
inferType (CILBlock fc xs x) = inferType x
inferType (CILAssign fc n x) = inferExprType x
inferType (CILReturn fc x) = inferExprType x
inferType (CILConCase e fc sc xs) = do altsTypes <- traverseList1 (\(MkCILConAlt _ _ x) => inferType x) xs
                                       if all (== head altsTypes) altsTypes
                                         then pure $ head altsTypes
                                         else pure CILDyn

public export
declare : {auto _: Ref Locals (SortedMap Name CILType)} ->
          {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} ->
          {auto _: Ref Ctxt Defs} ->
          {auto _ : Ref TagUnions (SortedMap Name CILType)} ->
          {auto _ : Ref Syn SyntaxInfo} ->
          {v : _} ->
          CIL (Just $ Assign v) ->
          Core $ CIL Nothing
declare (CILBlock fc ss s)              = pure $ CILBlock fc ss $ !(declare s)
declare s                               = pure $ CILDeclare EmptyFC !(inferType s) v s

public export
prepend : (List (CIL Nothing)) -> CIL (Just e) -> CIL (Just e)
prepend [] x = x
prepend xs x = CILBlock EmptyFC xs x

assign : {auto _: Ref Locals (SortedMap Name CILType)} ->
         {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} ->
         {auto _: Ref Ctxt Defs} ->
         {auto _ : Ref TagUnions (SortedMap Name CILType)} ->
         {auto _ : Ref Syn SyntaxInfo} ->
         (e: Effect) ->
         CILExpr ->
         Core (CIL (Just e))
assign (Assign n) expr = pure $ CILAssign EmptyFC n expr
assign Return expr@(CILExprStruct _ _ _ _) = do
  local <- nextLocal
  updateLocalType local !(inferExprType expr)
  let assignment = CILAssign EmptyFC local expr
  pure $ prepend [!(declare assignment)] $ CILReturn EmptyFC (CILExprLocal EmptyFC local !(inferExprType expr))
assign Return expr@(CILExprTaggedUnion _ _ _ _ _) = do
  local <- nextLocal
  updateLocalType local !(inferExprType expr)
  let assignment = CILAssign EmptyFC local expr
  pure $ prepend [!(declare assignment)] $ CILReturn EmptyFC (CILExprLocal EmptyFC local !(inferExprType expr))
assign Return expr = pure $ CILReturn EmptyFC expr

mutual
  lift : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto _: Ref Refs (SortedMap Name CILType)}
         -> {auto _ : Ref Ctxt Defs}
         -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
         -> {auto _: Ref LambdaStructEquiv (SortedMap  Name Name)}
         -> {auto _ : Ref TagUnions (SortedMap Name CILType)}
         -> {auto _: Ref ConstructorMap (SortedMap Name Name)}
         -> {auto _ : Ref Syn SyntaxInfo}
         -> {auto _ : Ref Lambdas (List CILDef)}
         -> NamedCExp
         -> Core (List (CIL Nothing), CILExpr)
  lift cexp = do
    local <- nextLocal
    st <- stmt (Assign local) cexp
    updateLocalType local !(inferType st)
    def <- pure ([!(declare st)], CILExprLocal EmptyFC local !(inferType st))
    pure $ case st of
      CILAssign _ _ expr => ([], expr)
      _                  => def

  lambda : {auto _: Ref Locals (SortedMap Name CILType)}
           -> {auto _: Ref Refs (SortedMap Name CILType)}
           -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
           -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
           -> {auto _ : Ref TagUnions (SortedMap Name CILType)}
           -> {auto _: Ref ConstructorMap (SortedMap Name Name)}
           -> {auto c: Ref Ctxt Defs}
           -> {auto s: Ref Syn SyntaxInfo}
           -> {auto _ : Ref Lambdas (List CILDef) }
           -> Name
           -> NamedCExp
           -> Core (CILExpr, CILDef)
  lambda name cexp = go [name] cexp
    where go : List Name -> NamedCExp -> Core (CILExpr, CILDef)
          go ns (NmLam fc n x) = go (n :: ns) x
          go ns x = do
            let args = reverse ns
            let argTypes = map (const CILDyn) args
            captures <- extractCaptures args x
            struct <-  nextStruct captures
            let structType = CILStruct struct captures
            let args = if null captures then args else (UN $ mkUserName "c") :: args
            let argTypes = if null captures then argTypes else (structType) :: argTypes
            update Locals (mergeLeft (fromList $ zip args argTypes))
            body <- traverseCIL (pure . rewriteCaptures structType (keys captures) (UN $ mkUserName "c")) =<< stmt Return x
            update Locals (\x => foldr delete x (keys (fromList $ zip args argTypes)))
            let nextLambda = cast $ 1 + length !(get Lambdas)
            let fnName = MN "lambda" nextLambda
            update LambdaStructEquiv (insert struct fnName)
            let fn = MkCILFun EmptyFC fnName (zip args argTypes) (!(inferType body)) (body)
            let captureExprs: List CILExpr = map (\(k,v) => CILExprLocal EmptyFC k v) (Data.SortedMap.toList captures)
            pure (CILExprStruct EmptyFC struct structType captureExprs, fn)

  public export
  traverseCIL : (CILExpr -> Core CILExpr) -> CIL e -> Core (CIL e)
  traverseCIL f (CILConstCase e fc sc xs y) = do sc <- f sc
                                                 xs <- traverseList1 (\(MkCILConstAlt e c cexp) =>
                                                                    (MkCILConstAlt e c) <$> traverseCIL f cexp) xs
                                                 y <- traverseOpt (\x => traverseCIL f x) y
                                                 pure $ CILConstCase e fc sc xs y
  traverseCIL f (CILBlock fc xs x) = do xs <- traverse (\x => traverseCIL f x) xs
                                        x <- traverseCIL f x
                                        pure $ CILBlock fc xs x
  traverseCIL f (CILAssign fc n x) = CILAssign fc n <$> f x
  traverseCIL f (CILReturn fc x) = CILReturn fc <$> f x
  traverseCIL f (CILDeclare fc x n y) = CILDeclare fc x n <$> traverseCIL f y
  traverseCIL f (CILConCase e fc sc xs) = do sc <- f sc
                                             xs <- traverseList1 (\(MkCILConAlt e t cexp) =>
                                                                (MkCILConAlt e t) <$> traverseCIL f cexp) xs
                                             pure $ CILConCase e fc sc xs


  rewriteCaptures : CILType -> List Name -> Name -> CILExpr -> CILExpr
  rewriteCaptures structType ns rw (CILExprCall fc x ty1 xs ty2) = CILExprCall fc (rewriteCaptures structType ns rw x) ty1 (map (\x => rewriteCaptures structType ns rw x) xs) ty2
  rewriteCaptures structType ns rw (CILExprOp fc f xs ty) = CILExprOp fc f (map (\x => rewriteCaptures structType ns rw x) xs) ty
  rewriteCaptures structType ns rw c@(CILExprConstant _ _ _) = c
  rewriteCaptures structType ns rw (CILExprLocal fc n ty) = if n `elem` ns then CILExprField fc (CILExprLocal EmptyFC rw ty) structType n else CILExprLocal fc n ty
  rewriteCaptures structType ns rw (CILExprStruct fc n ty xs) = CILExprStruct fc n ty (map (\x => rewriteCaptures structType ns rw x) xs)
  rewriteCaptures structType ns rw (CILExprRef fc n ty) = CILExprRef fc n ty
  rewriteCaptures structType ns rw (CILExprField fc x ty n1) = CILExprField fc (rewriteCaptures structType ns rw x) ty n1
  rewriteCaptures structType ns rw (CILExprTaggedUnion fc n ty k xs) = CILExprTaggedUnion fc n ty k (map (\x => rewriteCaptures structType ns rw x) xs)
  rewriteCaptures structType ns rw (CILExprSizeof fc expr) = CILExprSizeof fc (rewriteCaptures structType ns rw expr)
  rewriteCaptures structType ns rw (CILExprAddrof fc expr) = CILExprAddrof fc (rewriteCaptures structType ns rw expr)

  extractCaptures : {auto _ : Ref Locals (SortedMap Name CILType)}
                    -> {auto _ : Ref Ctxt Defs}
                    -> {auto _ : Ref Syn SyntaxInfo}
                    -> (args: List Name) -> NamedCExp -> Core (SortedMap Name CILType)
  extractCaptures ns (NmLocal fc n) = do if n `elem` ns then pure empty else pure $ fromList [(n, !(lookupLocalType n))]
  extractCaptures ns (NmRef fc n) = pure empty
  extractCaptures ns (NmLam fc n y) = extractCaptures (n :: ns) y
  extractCaptures ns (NmLet fc n y z) = do a <- (extractCaptures ns y)
                                           b <- (extractCaptures (n :: ns) z)
                                           pure $ mergeLeft a b
  extractCaptures ns (NmApp fc x xs) = do a <- extractCaptures ns x
                                          b <- foldl mergeLeft empty <$> traverse (extractCaptures ns) xs
                                          pure $ mergeLeft a b
  extractCaptures ns (NmCon fc n x tag xs) = foldl mergeLeft empty <$> traverse (extractCaptures ns) xs
  extractCaptures ns (NmOp fc f xs) = foldl mergeLeft empty <$> traverse (extractCaptures ns) (toList xs)
  extractCaptures ns (NmExtPrim fc p xs) = ?extractCaptures_rhs_7
  extractCaptures ns (NmForce fc lz x) = ?extractCaptures_rhs_8
  extractCaptures ns (NmDelay fc lz x) = ?extractCaptures_rhs_9
  extractCaptures ns (NmConCase fc sc xs x) = do a <- extractCaptures ns sc
                                                 b <- foldl mergeLeft empty <$> traverse (\(MkNConAlt _ _ _ args cexp) => extractCaptures (args ++ ns) cexp) xs
                                                 pure $ mergeLeft a b
  extractCaptures ns (NmConstCase fc sc xs x) = do a <- extractCaptures ns sc
                                                   b <- foldl mergeLeft empty <$> traverse (\(MkNConstAlt c cexp) => extractCaptures ns cexp) xs
                                                   c <- foldl mergeLeft empty <$> traverseOpt (extractCaptures ns) x
                                                   pure $ mergeLeft a (mergeLeft b c)
  extractCaptures ns (NmPrimVal fc cst) = pure empty
  extractCaptures ns (NmErased fc) = pure empty
  extractCaptures ns (NmCrash fc str) = pure empty

  public export
  stmt : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto _: Ref Refs (SortedMap Name CILType)}
         -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
         -> {auto _: Ref TagUnions (SortedMap Name CILType)}
         -> {auto _: Ref ConstructorMap (SortedMap Name Name)}
         -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
         -> {auto c: Ref Ctxt Defs}
         -> {auto s: Ref Syn SyntaxInfo}
         -> {auto _ : Ref Lambdas (List CILDef)}
         -> (e: Effect)
         -> NamedCExp
         -> Core (CIL (Just e))
  stmt e (NmRef fc n) = do refs <- get Refs
                           case lookup n refs of
                             Just ty => assign e (CILExprRef fc n ty)
                             _       => throw $ InternalError $ "Reference " ++ show n ++ " not found in" ++ show refs
  stmt e (NmLam fc x y) = do
    (expr, fn) <- lambda x y
    update Lambdas (fn ::)
    assign e expr
  stmt e (NmLet fc name val sc) = do
    val <- stmt (Assign name) val
    _ <- updateLocalType name !(inferType val)
    sc <- stmt e sc
    pure $ prepend [!(declare val)] sc
  stmt e (NmApp fc x xs) = do
    (calleeStmts, callee) <- lift x
    (argStmts, args) <- unzip <$> traverse lift xs

    ignore $ pure $ (argStmts, args)

    pure (prepend (calleeStmts ++ (concat argStmts)) !(assign e $ CILExprCall fc callee !(inferExprType callee) args !(traverse inferExprType args)))
  stmt e (NmCon fc n x tag xs) = do
    case tag of
      Just t => do
        consMap <- get ConstructorMap
        Just tuName <- pure $ lookup n consMap
          | _ => throw $ InternalError $ "Constructor " ++ show n ++ " not found in" ++ show consMap
        (argStmts, args) <- unzip <$> traverse lift xs
        tu <- get TagUnions
        ty' <- case (Data.SortedMap.lookup tuName tu) of
                Just ty => pure ty
                _       => throw $ InternalError $ "Tagged union " ++ show tuName ++ " not found in" ++ show tu
        let expr = CILExprTaggedUnion EmptyFC tuName ty' t args
        pure $ prepend (concat argStmts) !(assign e expr)
      Nothing => do
        pure $ ?nontaggedstruct
  stmt e (NmOp fc f xs) = do
    (argStmts, args) <- unzip <$> traverseVect lift xs
    pure $ prepend (concat argStmts) $ !(assign e $ CILExprOp fc f args (inferOpArgType f))
  stmt e (NmExtPrim fc p xs) = ?stmt_rhs_7
  stmt e (NmForce fc lz x) = ?stmt_rhs_8
  stmt e (NmDelay fc lz x) = ?stmt_rhs_9
  stmt e (NmConCase fc sc xs x) = do
    tu <- get TagUnions
    Just (MkNConAlt n _ _ _ _) <- pure $ head' xs
      | _ => throw $ InternalError "Empty list of alternatives"
    consMap <- get ConstructorMap
    Just tuName <- pure $ lookup n consMap
      | _ => throw $ InternalError $ "Constructor " ++ show n ++ " not found in" ++ show consMap
    Just tuType <- pure $ Data.SortedMap.lookup tuName tu
      | _ => throw $ InternalError $ "Tagged union " ++ show tuName ++ " not found in " ++ show tu
    (CILTaggedUnion _ kinds) <- pure tuType
      | _ => throw $ InternalError "impossible: non tagged union in TagUnions"

    local <- nextLocal
    st <- stmt (Assign local) sc
    updateLocalType local !(inferType st)
    scStmt <- declare st
    let scExpr = CILExprLocal EmptyFC local !(inferType st)

    let scExpr' = CILExprField EmptyFC scExpr tuType (UN $ mkUserName "tag")
    Just alts <- Data.List1.fromList <$> traverse (\(MkNConAlt n ci tag args cexp) => do
        case tag of
          Just t => do
            if length kinds == 0
              then do
                (stmts, expr) <- lift cexp
                tail <- assign e expr
                let cil = prepend stmts tail
                pure $  MkCILConAlt e t cil
              else do
                let indexes  = allFins (length args)
                argAssigns <- traverse (\(iarg,name) => do
                    let args = CILExprField EmptyFC scExpr tuType (MN "tag" t)
                    Just ikind <- pure $ natToFin (cast t) (length kinds)
                      | _ => throw $ InternalError "impossible: tag out of bounds"
                    let argsType = index' kinds ikind
                    let arg  = CILExprField EmptyFC args (argsType) (MN "arg" (cast $ finToInteger iarg))
                    assignment <- assign (Assign name) arg
                    _ <- updateLocalType name !(inferExprType arg)

                    (declare assignment)
                  ) (zip indexes args)

                (stmts, expr) <- lift cexp
                tail <- assign e expr
                let cil = prepend (argAssigns ++ stmts) tail
                pure $ MkCILConAlt e t cil
          Nothing => throw $ InternalError "Non-tagged union"
        ) xs
      | _ => throw $ InternalError "Empty list of alternatives"
    pure $ prepend [scStmt] $ CILConCase e fc scExpr' alts
  stmt e (NmConstCase fc sc xs def) = do
    (scStmts, scExpr) <- lift sc
    altCILs <- traverse (\(MkNConstAlt c cexp) => do (stmts, expr) <- lift cexp
                                                     tail <- assign e expr
                                                     pure $ prepend stmts tail) xs
    Just alts <- pure $ Data.List1.fromList $ map (\(cil, MkNConstAlt c _) => MkCILConstAlt e c cil) (zip altCILs xs)
      | _ => throw $ InternalError "Empty list of alternatives"
    def <- traverseOpt (stmt e) def
    pure $ prepend scStmts $ CILConstCase e fc scExpr alts def
  stmt e (NmPrimVal fc cst) = assign e $ CILExprConstant fc cst !(inferConstType cst)
  stmt e (NmErased fc) = assign e $ CILExprConstant fc (I32 0) CILI32
  stmt e (NmCrash fc str) = ?stmt_rhs_14
  stmt e (NmLocal fc n) = do
    assign e $ CILExprLocal fc n !(lookupLocalType n)

  compileStructs : {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} -> Core (List CILDef)
  compileStructs = do
    structs <- get Structs
    traverse (\(n, m) => pure $ MkCILStruct EmptyFC n m) (Data.SortedMap.toList structs)

foreignToCIL : CFType -> CILType
foreignToCIL CFUnit = CILWorld
foreignToCIL CFInt = CILI32
foreignToCIL CFInteger = CILI64
foreignToCIL CFInt8 = CILI8
foreignToCIL CFInt16 = CILI16
foreignToCIL CFInt32 = CILI32
foreignToCIL CFInt64 = CILI64
foreignToCIL CFUnsigned8 = CILU8
foreignToCIL CFUnsigned16 = CILU16
foreignToCIL CFUnsigned32 = CILU32
foreignToCIL CFUnsigned64 = CILU64
foreignToCIL CFString = CILPtr CILI8
foreignToCIL CFDouble = CILF64
foreignToCIL CFChar = CILU8
foreignToCIL CFPtr = CILPtr CILU8
foreignToCIL CFGCPtr = CILPtr CILU8
foreignToCIL CFBuffer = CILPtr CILU8
foreignToCIL CFForeignObj = CILPtr CILU8
foreignToCIL CFWorld = CILWorld
foreignToCIL (CFFun x y) = CILFn ([foreignToCIL x]) (foreignToCIL y)
foreignToCIL (CFIORes x) = foreignToCIL x
foreignToCIL (CFStruct str xs) = CILStruct (UN $ mkUserName str) (fromList $ map (\(n, t) => ((UN $ mkUserName n), foreignToCIL t)) xs)
foreignToCIL (CFUser n xs) = ?idk

%hide Libraries.Data.PosMap.infixl.(|>)
public export compileDefs : {auto c: Ref Ctxt Defs}
                             -> {auto s: Ref Syn SyntaxInfo}
                             -> List (Name, (FC, NamedDef), ClosedTerm)
                             -> Core (List CILDef, SortedMap Name Name)
compileDefs xs = do
  let nmap = fromList $ !(traverse (\(n, _, ty) => do pure (n, (uncurry CILFn) !(fnType ty))) xs)
  lamdas <- newRef Lambdas []
  structs <- newRef Structs empty
  ls <- newRef LambdaStructEquiv empty
  tu <- newRef TagUnions empty
  consmap <- newRef ConstructorMap empty
  let (structDefs,others ) = partition (\(_, (_, def), _) => case def of
                                                                MkNmCon _ _ _ => True

                                                                _ => False) xs
  compiledDefs <- catMaybes <$> traverse (compileDef nmap) (structDefs ++ others)
  pure $ (compiledDefs ++ !(get Lambdas) ++ !(compileStructs), !(get LambdaStructEquiv))
  where
    compileDef : {auto _ : Ref Lambdas (List CILDef)}
      -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
      -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
      -> {auto _: Ref ConstructorMap (SortedMap Name Name)}
      -> {auto _: Ref TagUnions (SortedMap Name CILType)}
      -> SortedMap Name CILType
      -> (Name, (FC, NamedDef), ClosedTerm)
      -> Core (Maybe CILDef)
    compileDef types (name, (fc, (MkNmFun args cexp)), type) = do
      (argTypes, ret) <- fnType type
      locals <- newRef Locals empty
      zip args argTypes |> traverse_ (\(n, t) => updateLocalType (n) t)
      refs <- newRef Refs types
      body <- stmt Return (cexp)
      pure $ Just (MkCILFun fc (name) (zip args argTypes) ret body)
    compileDef _ (name, (fc, ((MkNmForeign ccs fargs ftype))), type) = do
      Just (_, (ext :: otherOpts)) <- pure $ parseCC ["RefC", "C"] ccs
        | _ => throw $ InternalError $ "Foreign function " ++ show name ++ " not in C: " ++ show ccs
      pure $ Just (MkCILForeign fc name (map foreignToCIL fargs) (foreignToCIL ftype) ext)
    compileDef _ (name, (fc, (MkNmCon tag arity nt)), type) = do
      (_, tuType) <- fnType type
      CILTaggedUnion tuName kinds <- pure tuType
        | _ => throw $ InternalError $ "impossible: Inferred type not a tagged union " ++ show tuType ++ " " ++ show name
      update ConstructorMap (insert name tuName)
      tus <- get TagUnions
      defs <- get Ctxt
      tyconName <- case !(lookupCtxtExact tuName (gamma defs)) of
            Just x => pure $ fullname x
            _ => throw $ InternalError $ "impossible: Already checked " ++ show tuName
      case lookup tuName tus of
        Just _ => pure $ Nothing
        Nothing => do
          update TagUnions (insert tuName tuType)
          datacons <- map (DataCon.name) <$> getCons defs tyconName
          pure $ Just (MkCILTaggedUnion fc tuName datacons kinds)
    compileDef _ _ = do
      pure $ Nothing

