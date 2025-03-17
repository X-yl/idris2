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
import Debug.Trace
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
      show (CILExprCall fc name ty1 args ty2) = assert_total $ "CILCall (" ++ show name ++ " " ++ show args ++ " : " ++ show ty2 ++  ")"
      show (CILExprOp fc fn args ty) = assert_total $ "CILOp (" ++ show fn ++ " " ++ (show args) ++ ")"
      show (CILExprLocal fc name ty) = "CILExprLocal (" ++ show name ++ " : " ++ show ty ++ ")"
      show (CILExprConstant fc c ty) = "CILConstant (" ++ show c ++ ")"
      show (CILExprRef fc name ty) = "CILRef (" ++ show name ++ " : " ++ show ty  ++ ")"
      show (CILExprStruct fc name ty args) = assert_total $ "CILStruct (" ++ show name ++ " " ++ show args ++ " : " ++ show ty ++ ")"
      show (CILExprField fc name ty field) = assert_total $ "CILField (" ++ show name ++ " " ++ show field ++ ")"

  public export
    data CILDef : Type where
      MkCILFun : FC -> Name -> (args: List (Name, CILType)) -> (return: CILType) -> (body: CIL (Just Return)) -> CILDef
      MkCILStruct : FC -> Name -> (members: SortedMap Name CILType) -> CILDef

  covering
  public export
    Show CILDef where
      show (MkCILFun fc name args ret body) = assert_total $ "MkCILFun (" ++ show name ++ " " ++ show args ++ " " ++ show ret ++ " " ++ show body ++ ")"
      show (MkCILStruct fc name members) = assert_total $ "MkCILStruct (" ++ show name ++ " " ++ show members ++ ")"

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
    _ == _ = False

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
  fnType (TDelayed fc lz t)     = pure ([], !(termToCILType t))
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

assign : (e: Effect) -> CILExpr -> CIL (Just e)
assign (Assign n) = (CILAssign EmptyFC n)
assign Return = CILReturn EmptyFC

prepend : (List (CIL Nothing)) -> CIL (Just e) -> CIL (Just e)
prepend [] x = x
prepend xs x = CILBlock EmptyFC xs x

data Locals : Type where
data Lambdas : Type where
data Structs : Type where
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
inferExprType (CILExprField fc n ty f) = do
  case ty of
    CILStruct name members => maybe (pure CILDyn) pure (lookup f members)
    _           => throw $ InternalError $ "Field access on non-struct type " ++ show ty

inferType : {auto _: Ref Locals (SortedMap Name CILType)} ->
            {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} ->
            {auto _: Ref Ctxt Defs} -> {auto _ : Ref Syn SyntaxInfo} -> CIL (Just e) -> Core CILType
inferType (CILConstCase e fc sc xs y) = do altsTypes <- traverseList1 (\(MkCILConstAlt _ _ x) => inferType x) xs
                                           if all (== head altsTypes) altsTypes
                                             then pure $ head altsTypes
                                             else pure CILDyn
inferType (CILBlock fc xs x) = inferType x
inferType (CILAssign fc n x) = inferExprType x
inferType (CILReturn fc x) = inferExprType x

export
declare : {auto _: Ref Locals (SortedMap Name CILType)} ->
          {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} ->
          {auto _: Ref Ctxt Defs} ->
          {auto _ : Ref Syn SyntaxInfo} ->
          {v : _} ->
          CIL (Just $ Assign v) ->
          Core $ CIL Nothing
declare (CILBlock fc ss s)              = pure $ CILBlock fc ss $ !(declare s)
declare s                               = pure $ CILDeclare EmptyFC !(inferType s) v s

mutual
  lift : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto _: Ref Refs (SortedMap Name CILType)}
         -> {auto _ : Ref Ctxt Defs}
         -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
         -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
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
      CILAssign _ _ (CILExprStruct _ _ _ _) => def -- Structs must be lifted.
      CILAssign _ _ expr => ([], expr)
      _                  => def

  lambda : {auto _: Ref Locals (SortedMap Name CILType)}
           -> {auto _: Ref Refs (SortedMap Name CILType)}
           -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
           -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
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
            let fn = MkCILFun EmptyFC fnName (zip args argTypes) (traceVal !(inferType body)) (traceVal body)
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


  rewriteCaptures : CILType -> List Name -> Name -> CILExpr -> CILExpr
  rewriteCaptures structType ns rw (CILExprCall fc x ty1 xs ty2) = CILExprCall fc (rewriteCaptures structType ns rw x) ty1 (map (\x => rewriteCaptures structType ns rw x) xs) ty2
  rewriteCaptures structType ns rw (CILExprOp fc f xs ty) = CILExprOp fc f (map (\x => rewriteCaptures structType ns rw x) xs) ty
  rewriteCaptures structType ns rw c@(CILExprConstant _ _ _) = c
  rewriteCaptures structType ns rw (CILExprLocal fc n ty) = if n `elem` ns then CILExprField fc (CILExprLocal EmptyFC rw ty) structType n else CILExprLocal fc n ty
  rewriteCaptures structType ns rw (CILExprStruct fc n ty xs) = CILExprStruct fc n ty (map (\x => rewriteCaptures structType ns rw x) xs)
  rewriteCaptures structType ns rw (CILExprRef fc n ty) = CILExprRef fc n ty
  rewriteCaptures structType ns rw (CILExprField fc x ty n1) = CILExprField fc (rewriteCaptures structType ns rw x) ty n1

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
  extractCaptures ns (NmCon fc n x tag xs) = ?extractCaptures_rhs_5
  extractCaptures ns (NmOp fc f xs) = foldl mergeLeft empty <$> traverse (extractCaptures ns) (toList xs)
  extractCaptures ns (NmExtPrim fc p xs) = ?extractCaptures_rhs_7
  extractCaptures ns (NmForce fc lz x) = ?extractCaptures_rhs_8
  extractCaptures ns (NmDelay fc lz x) = ?extractCaptures_rhs_9
  extractCaptures ns (NmConCase fc sc xs x) = ?extractCaptures_rhs_10
  extractCaptures ns (NmConstCase fc sc xs x) = ?extractCaptures_rhs_11
  extractCaptures ns (NmPrimVal fc cst) = pure empty
  extractCaptures ns (NmErased fc) = pure empty
  extractCaptures ns (NmCrash fc str) = pure empty

  public export
  stmt : {auto _: Ref Locals (SortedMap Name CILType)}
         -> {auto _: Ref Refs (SortedMap Name CILType)}
         -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
         -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
         -> {auto c: Ref Ctxt Defs}
         -> {auto s: Ref Syn SyntaxInfo}
         -> {auto _ : Ref Lambdas (List CILDef)}
         -> (e: Effect)
         -> NamedCExp
         -> Core (CIL (Just e))
  stmt e (NmRef fc n) = do refs <- get Refs
                           case lookup n refs of
                             Just ty => pure $ assign e (CILExprRef fc n ty)
                             _       => throw $ InternalError $ "Reference " ++ show n ++ " not found in" ++ show refs
  stmt e (NmLam fc x y) = do
    (expr, fn) <- lambda x y
    update Lambdas (fn ::)
    pure $ assign e expr
  stmt e (NmLet fc name val sc) = do
    sc <- stmt e sc
    val <- stmt (Assign name) val
    _ <- updateLocalType name !(inferType val)
    pure $ prepend [!(declare val)] sc
  stmt e (NmApp fc x xs) = do
    (calleeStmts, callee) <- lift x
    (argStmts, args) <- unzip <$> traverse lift xs

    ignore $ pure $ (argStmts, args)

    pure (prepend (calleeStmts ++ (concat argStmts)) (assign e $ CILExprCall fc callee !(inferExprType callee) args !(traverse inferExprType args)))
  stmt e (NmCon fc n x tag xs) = do ignore $ pure $ (n)
                                    pure ?ficxme
  stmt e (NmOp fc f xs) = do
    (argStmts, args) <- unzip <$> traverseVect lift xs
    pure $ prepend (concat argStmts) $ assign e $ CILExprOp fc f args (inferOpArgType f)
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
  stmt e (NmPrimVal fc cst) = pure $ assign e $ CILExprConstant fc cst !(inferConstType cst)
  stmt e (NmErased fc) = pure $ assign e $ CILExprConstant fc (I32 0) CILI32
  stmt e (NmCrash fc str) = ?stmt_rhs_14
  stmt e (NmLocal fc n) = do
    pure $ assign e $ CILExprLocal fc n !(lookupLocalType n)

  compileStructs : {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))} -> Core (List CILDef)
  compileStructs = do
    structs <- get Structs
    traverse (\(n, m) => pure $ MkCILStruct EmptyFC n m) (Data.SortedMap.toList structs)

%hide Libraries.Data.PosMap.infixl.(|>)
public export compileDefs : {auto c: Ref Ctxt Defs} -> {auto s: Ref Syn SyntaxInfo} -> List (Name, (FC, NamedDef), ClosedTerm) -> Core (List CILDef, SortedMap Name Name)
compileDefs xs = do
  let nmap = fromList $ !(traverse (\(n, _, ty) => do pure (n, (uncurry CILFn) !(fnType ty))) xs)
  lamdas <- newRef Lambdas []
  structs <- newRef Structs empty
  ls <- newRef LambdaStructEquiv empty
  compiledDefs <- traverse (compileDef nmap) (xs)
  pure $ (compiledDefs ++ !(get Lambdas) ++ !(compileStructs), !(get LambdaStructEquiv))
  where
    compileDef : {auto _ : Ref Lambdas (List CILDef)}
      -> {auto _: Ref Structs (SortedMap Name (SortedMap Name CILType))}
      -> {auto _: Ref LambdaStructEquiv (SortedMap Name Name)}
      -> SortedMap Name CILType
      -> (Name, (FC, NamedDef), ClosedTerm)
      -> Core CILDef
    compileDef types (name, (fc, (MkNmFun args cexp)), type) = do
      _ <- pure $ traceVal name
      (argTypes, ret) <- fnType type
      _ <- pure $ traceVal (argTypes, ret)
      locals <- newRef Locals empty
      zip args argTypes |> traverse_ (\(n, t) => updateLocalType (traceVal n) t)
      refs <- newRef Refs types
      body <- stmt Return (traceVal cexp)
      pure $ (MkCILFun fc (traceVal name) (zip args argTypes) ret body)
    compileDef _ (name, (fc, _), type) = pure ?unimplemented
