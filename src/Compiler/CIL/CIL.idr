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
import Data.Vect
import Data.List1
import Data.SnocList
import Debug.Trace
import Idris.Syntax
import Data.SortedMap

%default covering

mutual
  public export
    data Effect : Type where
      Assign : Name -> Effect
      Return : Effect

  public export
    data CIL : (e: Maybe Effect) -> Type where
      CILConstCase : (e: Effect) -> FC -> (sc: CILExpr) -> List1 (CILConstAlt e) -> Maybe (CIL (Just e)) -> CIL (Just e)
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
      CILExprCall : FC -> CILExpr -> List CILExpr -> CILExpr
      CILExprOp : {arity: _} -> FC -> PrimFn arity -> Vect arity CILExpr -> CILExpr
      CILExprConstant : FC -> Constant -> CILExpr
      CILExprLocal : FC -> Name -> CILExpr
      CILExprRef : FC -> Name -> CILExpr

  public export
    data CILConstAlt : (e: Effect) -> Type where
      MkCILConstAlt : (e: Effect) -> Constant -> CIL (Just e) -> CILConstAlt e

  covering
  public export
    Show (CILConstAlt e) where
      show (MkCILConstAlt e c b) = assert_total $ "MkCILConstAlt (" ++ show e ++ " " ++ show c ++ " " ++ show b ++ ")"

  covering
  public export
    Show (CIL e) where
      show (CILConstCase e fc sc alts def) = assert_total $ "CILConstCase (" ++ show e ++ " " ++ show sc ++ " " ++ show alts ++ " " ++ show def ++ ")"
      show (CILBlock fc stmts target) = assert_total $ "CILBlock (" ++ show stmts ++ " " ++ show target ++ ")"
      show (CILAssign fc n expr) = assert_total $ "CILAssign (" ++ show n ++ " " ++ show expr ++ ")"
      show (CILReturn fc expr) = assert_total $ "CILReturn (" ++ show expr ++ ")"
      show (CILDeclare fc ty name sc) = assert_total $ "CILDeclare (" ++ show ty ++ show name ++ " " ++ show sc ++ ")"

  public export
    Show CILExpr where
      show (CILExprCall fc name args) = assert_total $ "CILCall (" ++ show name ++ " " ++ show args ++ ")"
      show (CILExprOp fc fn args) = assert_total $ "CILOp (" ++ show fn ++ " " ++ (show args) ++ ")"
      show (CILExprLocal fc name) = "CILExorLocal (" ++ show name ++ ")"
      show (CILExprConstant fc c) = "CILConstant (" ++ show c ++ ")"
      show (CILExprRef fc name) = "CILRef (" ++ show name ++ ")"

  public export
    data CILDef : Type where
      MkCILFun : FC -> Name -> (args: List (Name, CILType)) -> (return: CILType) -> (body: CIL (Just Return)) -> CILDef

  covering
  public export
    Show CILDef where
      show (MkCILFun fc name args ret body) = assert_total $ "MkCILFun (" ++ show name ++ " " ++ show args ++ " " ++ show ret ++ " " ++ show body ++ ")"

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
inferPrimType StringType = CILPtr CILU8
inferPrimType CharType = CILI32
inferPrimType DoubleType = CILF64
inferPrimType WorldType = CILWorld

mutual
  fnType : {auto c : Ref Ctxt Defs} -> Term _ -> Core (List CILType, CILType)
  fnType (Local fc isLet idx p) = pure ([], CILDyn)
  fnType (Meta fc n i ts)       = pure ([], CILDyn)
  fnType (Bind fc x b scope)    = do
    t <- (case b of
              Pi fc rc info type  => termToCILType type
              _                   => pure CILDyn)
    (rest, rtn) <- fnType scope
    pure (t::rest, rtn)
  fnType (App fc fn arg)        = pure ([], CILDyn)
  fnType (As fc side as pat)    = pure ([], CILDyn)
  fnType (TDelayed fc lz t)     = pure ([], CILDyn)
  fnType (TDelay fc lz ty arg)  = pure ([], CILDyn)
  fnType (TForce fc lz t)       = pure ([], CILDyn)
  fnType (t@(PrimVal fc c))     = pure ([], !(termToCILType t))
  fnType (Ref fc (TyCon _ 0) _) = pure ([], CILU32) -- Enum type
  fnType (Ref fc nt name)       = pure ([], CILDyn)
  fnType (Erased fc why)        = pure ([], CILDyn)
  fnType (TType fc n)           = pure ([], CILDyn)

  termToCILType : {auto c : Ref Ctxt Defs} -> Term _ -> Core CILType
  termToCILType (PrimVal fc (PrT x)) = pure $ inferPrimType x
  termToCILType (Ref fc (TyCon _ 0) _) = pure CILU32 -- Enum type
  termToCILType term@(Bind _ _ _ _) = do (args, ret) <- (fnType term)
                                         pure $ CILFn args ret
  termToCILType _ = pure CILDyn

  typeLookup : {auto _: Ref Ctxt Defs} -> {auto _ : Ref Syn SyntaxInfo} -> Name -> Core CILType
  typeLookup name = do
    defs <- get Ctxt
    ty <- (type<$>) <$> lookupCtxtExact name (gamma defs)
    maybe (pure CILDyn) termToCILType ty

assign : (e: Effect) -> CILExpr -> CIL (Just e)
assign (Assign n) = (CILAssign EmptyFC n)
assign Return = CILReturn EmptyFC

prepend : (List (CIL Nothing)) -> CIL (Just e) -> CIL (Just e)
prepend [] x = x
prepend xs x = CILBlock EmptyFC xs x

data Locals : Type where
data Lambdas : Type where

nextLocal : {auto _ : Ref Locals (SortedMap Name CILType)} -> Core Name
nextLocal = do
  ns <- get Locals
  let next = cast $ 1 + length (Data.SortedMap.toList ns)
  update Locals $ insert (MN "local" next) CILDyn
  pure $ MN "local" next

updateLocalType : {auto _ : Ref Locals (SortedMap Name CILType)} -> Name -> CILType -> Core ()
updateLocalType n t = update Locals $ insert n t



inferConstType : {auto _: Ref Ctxt Defs} -> Constant -> Core CILType
inferConstType (I i) = pure CILI64
inferConstType (I8 i) = pure CILI8
inferConstType (I16 i) = pure CILI16
inferConstType (I32 i) = pure CILI32
inferConstType (I64 i) = pure CILI64
inferConstType (BI i) = pure CILU64
inferConstType (B8 m) = pure CILU8
inferConstType (B16 m) = pure CILU16
inferConstType (B32 m) = pure CILU32
inferConstType (B64 m) = pure CILU64
inferConstType (Str str) = pure (CILPtr CILU8)
inferConstType (Ch c) = pure CILU8
inferConstType (Db dbl) = pure CILF64
inferConstType a@(PrT _) = let q: ClosedTerm = (PrimVal EmptyFC a) in pure . CILPtr $ !(termToCILType q)
inferConstType WorldVal = pure CILWorld

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


inferExprType :  {auto _: Ref Locals (SortedMap Name CILType)} -> {auto _: Ref Ctxt Defs} -> {auto _ : Ref Syn SyntaxInfo} -> CILExpr -> Core CILType
inferExprType (CILExprCall fc x xs) = do
  defs <- get Ctxt
  ty <- inferExprType x
  case ty of
    CILFn args ret => if length args == length xs
                      then pure ret
                      else pure $ CILFn (drop (length xs) args) ret
    _              => pure CILDyn
inferExprType (CILExprOp fc f xs) = pure $ inferOpArgType f
inferExprType (CILExprConstant fc cst) = inferConstType cst
inferExprType (CILExprLocal fc n) = do
  locals <- get Locals
  maybe (pure CILDyn) pure (lookup n locals)
inferExprType (CILExprRef fc n) = typeLookup n

inferType : {auto _: Ref Locals (SortedMap Name CILType)} -> {auto _: Ref Ctxt Defs} -> {auto _ : Ref Syn SyntaxInfo} -> CIL (Just e) -> Core CILType
inferType (CILConstCase e fc sc xs y) = let altsTypes = map (\MkCILConstAlt _ _ x => x) xs in
                                          if all (== head altsTypes) altsTypes
                                          then pure $ head altsTypes
                                          else pure CILDyn
inferType (CILBlock fc xs x) = inferType x
inferType (CILAssign fc n x) = inferExprType x
inferType (CILReturn fc x) = inferExprType x

export
declare : {auto _: Ref Locals (SortedMap Name CILType)} -> {auto _: Ref Ctxt Defs} -> {auto _ : Ref Syn SyntaxInfo} -> {v : _} -> CIL (Just $ Assign v) -> Core $ CIL Nothing
declare (CILBlock fc ss s)              = pure $ CILBlock fc ss $ !(declare s)
declare s                               = pure $ CILDeclare EmptyFC !(inferType s) v s

mutual
  lift : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto _ : Ref Ctxt Defs}
         -> {auto _ : Ref Syn SyntaxInfo}
         -> {auto _ : Ref Lambdas (List CILDef)}
         -> NamedCExp
         -> Core (List (CIL Nothing), CILExpr)
  lift cexp = do
    local <- nextLocal
    st <- stmt (Assign local) cexp
    updateLocalType local !(inferType st)
    let def= ([!(declare st)], CILExprLocal EmptyFC local)
    pure $ case st of
      CILAssign _ _ expr => ([], expr)
      _                  => def

  lambda : {auto _: Ref Locals (SortedMap Name CILType)}
           -> {auto c: Ref Ctxt Defs}
           -> {auto s: Ref Syn SyntaxInfo}
           -> {auto _ : Ref Lambdas (List CILDef)}
           -> Name
           -> NamedCExp
           -> Core (CILExpr, CILDef)
  lambda name cexp = go [name] cexp
    where go : List Name -> NamedCExp -> Core (CILExpr, CILDef)
          go ns (NmLam fc n x) = go (n :: ns) x
          go ns x = do
            body <- stmt Return x
            let args = reverse ns
            argTypes <- traverse typeLookup args
            let nextLambda = cast $ 1 + length !(get Lambdas)
            let fnName = MN "lambda" nextLambda
            let fn = MkCILFun EmptyFC fnName (zip args argTypes) !(inferType body) body
            pure (CILExprLocal EmptyFC fnName, fn)


  stmt : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto c: Ref Ctxt Defs}
         -> {auto s: Ref Syn SyntaxInfo}
         -> {auto _ : Ref Lambdas (List CILDef)}
         -> (e: Effect)
         -> NamedCExp
         -> Core (CIL (Just e))
  stmt e (NmRef fc n) = pure $ assign e (CILExprRef fc n)
  stmt e (NmLam fc x y) = do
    (expr, fn) <- lambda x y
    update Lambdas (fn ::)
    pure $ assign e expr
  stmt e (NmLet fc name val sc) = do
    sc <- stmt e sc
    val <- stmt (Assign name) val
    pure $ prepend [!(declare val)] sc
  stmt e (NmApp fc x xs) = do
    (calleeStmts, callee) <- lift x
    (argStmts, args) <- unzip <$> traverse lift xs

    ignore $ pure $ traceVal (argStmts, args)

    pure (prepend (calleeStmts ++ (concat argStmts)) (assign e $ CILExprCall fc callee args))
  stmt e (NmCon fc n x tag xs) = do ignore $ pure $ (traceVal n)
                                    pure ?ficxme
  stmt e (NmOp fc f xs) = do
    (argStmts, args) <- unzip <$> traverseVect lift xs
    pure $ prepend (concat argStmts) $ assign e $ CILExprOp fc f args
  stmt e (NmExtPrim fc p xs) = ?stmt_rhs_7
  stmt e (NmForce fc lz x) = ?stmt_rhs_8
  stmt e (NmDelay fc lz x) = ?stmt_rhs_9
  stmt e (NmConCase fc sc xs x) = ?stmt_rhs_10
  stmt e (NmConstCase fc sc xs def) = do
    (scStmts, scExpr) <- lift sc
    Just alts <- fromList <$> traverse (\(MkNConstAlt c cexp) => pure $ MkCILConstAlt e c !(stmt e cexp)) xs
      | _ => throw $ InternalError "Empty list of alternatives"
    def <- traverseOpt (stmt e) def
    pure $ prepend scStmts $ CILConstCase e fc scExpr alts def
  stmt e (NmPrimVal fc cst) = pure $ assign e $ CILExprConstant fc cst
  stmt e (NmErased fc) = pure $ assign e $ CILExprConstant fc (I32 0)
  stmt e (NmCrash fc str) = ?stmt_rhs_14
  stmt e (NmLocal fc n) = do
    pure $ assign e $ CILExprLocal fc n

public export compileDefs : {auto c: Ref Ctxt Defs} -> {auto s: Ref Syn SyntaxInfo} -> List (Name, (FC, NamedDef), ClosedTerm) -> Core (List CILDef)
compileDefs xs = (traceVal . concat) <$> traverse compileDef (traceVal xs)
  where
    compileDef : (Name, (FC, NamedDef), ClosedTerm) -> Core $ List CILDef
    compileDef (name, (fc, (MkNmFun args cexp)), type) = do
      (argTypes, ret) <- fnType type
      _ <- pure $ (argTypes, ret)
      locals <- newRef Locals empty
      lamdas <- newRef Lambdas []
      body <- stmt Return (traceVal cexp)
      pure $ (MkCILFun fc (traceVal name) (zip args argTypes) ret body) :: !(get Lambdas)
    compileDef (name, (fc, _), type) = pure ?unimplemented
