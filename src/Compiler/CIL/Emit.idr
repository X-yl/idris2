module Compiler.CIL.Emit

import Compiler.CIL.CIL
import Compiler.RefC.RefC
import Core.Context
import Data.List1
import Data.List
import Data.SortedMap
import Data.Vect
import Protocol.Hex

%default covering

cType : CILType -> String
cType CILU8 = "uint8_t"
cType CILU16 = "uint16_t"
cType CILU32 = "uint32_t"
cType CILU64 = "uint64_t"
cType CILI8 = "char"
cType CILI16 = "int16_t"
cType CILI32 = "int32_t"
cType CILI64 = "int64_t"
cType CILF32 = "float"
cType CILF64 = "double"
cType (CILPtr x) = cType x ++ "*"
cType CILWorld = "void*"
cType CILDyn = "Value*"
cType (CILFn args ret) = cType ret ++ " (*)(" ++ concat (intersperse ", " (cType <$> args)) ++ ")"
cType (CILStruct name members) = "struct " ++ cName name
cType (CILTaggedUnion name kinds) = "struct " ++ cName name

data OutputRef : Type where
data ConstructorNames : Type where

ConsMap : Type
ConsMap = SortedMap Name (List Name)

emit : {auto p: Ref OutputRef String} -> (s: String) -> Core ()
emit s = update OutputRef (\a => a ++ s)

emitField : {auto p: Ref OutputRef String} -> (Name, CILType) -> Core ()
emitField (name, ty) = do
  emit (cType ty)
  emit " "
  emit (cName name)

emitConstructorDefine : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> Name -> Name -> CILType -> Int ->  Core ()
emitConstructorDefine tu cons argTy index = do
  emit "#define "
  emit (cName cons)
  emit "("
  CILStruct tagname fields <- pure argTy
    | _ => throw $ InternalError "argTy is not a struct"
  let argNames = map (\i => MN "arg" (cast $ finToInteger i)) (allFins (length $ Data.SortedMap.toList fields))
  traverse_ emit $ intersperse ", " (cName <$> argNames)
  emit ") "
  emit "((struct "
  emit (cName tu)
  emit "){ "
  emit " .tag = "
  emit (show index)
  emit ", ."
  emit (cName tagname)
  emit " = { "
  traverse_ emit $ intersperse ", " (cName <$> argNames)
  emit " } })\n"
  update ConstructorNames (update (Just . (maybe [cons] (++ [cons]))) tu)

emitArgs : {auto _: Ref OutputRef String} -> List (Name, CILType) -> Core ()
emitArgs xs = emit . concat $ intersperse ", " (emitArg <$> xs)
  where emitArg : (Name, CILType) -> String
        emitArg (name, t) = cType t ++ " " ++ cName name

emitHeaders : {auto _: Ref OutputRef String} -> CILDef -> Core ()
emitHeaders (MkCILFun fc n args return body) = do
  emit (cType return)
  emit " "
  emit (cName n)
  emit "("
  emitArgs args
  emit ");\n"
emitHeaders (MkCILStruct fc n members) = pure () -- Struct defs emitted elsewhere
emitHeaders _ = pure ()

cStringQuoted : String -> String
cStringQuoted cs = strCons '"' (showCString (unpack cs) "\"")
where
    showCChar : Char -> String -> String
    showCChar '\\' = ("\\\\" ++)
    showCChar c
      = if c < chr 32
            then (("\\x" ++ leftPad '0' 2 (asHex (cast c))) ++ "\"\"" ++)
            else if c < chr 127 then strCons c
            else if c < chr 65536 then (("\\u" ++ leftPad '0' 4 (asHex (cast c))) ++ "\"\"" ++)
            else (("\\U" ++ leftPad '0' 8 (asHex (cast c))) ++ "\"\"" ++)
    showCString : List Char -> String -> String
    showCString [] = id
    showCString ('"'::cs) = ("\\\"" ++) . showCString cs
    showCString (c ::cs) = (showCChar c) . showCString cs

emitConst : {auto _: Ref OutputRef String} -> Constant -> Core ()
emitConst (I i) = emit (show i)
emitConst (I8 i) = emit (show i)
emitConst (I16 i) = emit (show i)
emitConst (I32 i) = emit (show i)
emitConst (I64 i) = emit (show i)
emitConst (BI i) = emit (show i)
emitConst (B8 i) = emit (show i)
emitConst (B16 i) = emit (show i)
emitConst (B32 i) = emit (show i)
emitConst (B64 i) = emit (show i)
emitConst (Str str) = emit (cStringQuoted str)
emitConst (Ch c) = do emit $ show c
emitConst (Db dbl) = emit (show dbl)
emitConst (PrT pty) = emit "FIXME"
emitConst WorldVal = emit "NULL"

mutual

  emitDef : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> CILDef -> Core ()
  emitDef (MkCILFun fc name args ret body) = do
      emit (cType ret)
      emit " "
      emit (cName name)
      emit "("
      emitArgs args
      emit ") {\n"
      emitStmt body
      emit "}\n"
  emitDef (MkCILStruct fc name fields) = do
      emit "struct "
      emit (cName name)
      emit " { "
      traverse_ (\x => emitField x >> emit "; ") (Data.SortedMap.toList fields)
      emit " };\n"
  emitDef (MkCILTaggedUnion fc name datacons kinds) = do
      emit "struct "
      emit (cName name)
      emit " { \n"
      emit "  int64_t tag; \n"
      emit "  union { \n"
      ignore . sequence $ ((\kind => do
          (CILStruct tagname fields) <- pure kind
            | _ => throw $ InternalError "kind is not a struct"
          emit "  struct "
          emit " { "
          _ <- traverse_ (\x => emitField x >> emit "; ") (Data.SortedMap.toList fields)
          emit " } "
          emit (cName tagname)
          emit "; \n"
        ) <$> kinds)
      emit "  };\n"
      emit "};\n\n"
      ignore . sequence $ (\(a,b,c) => emitConstructorDefine name a b (cast $ finToInteger c))
                            <$> (zip3 datacons kinds (allFins (length datacons)))
      emit "\n"

  emitDef (MkCILForeign fc name args ret external) = do
      emit (cType ret)
      emit " "
      emit (cName name)
      emit "("
      let argNames = map (\i => MN "arg" (cast $ finToInteger i)) (allFins (length args))
      let fullArgs = (zip argNames args)
      emitArgs fullArgs
      emit ") {\n"
      if ret == CILWorld
        then do
          Just realArgs <- pure $ init' argNames
            | _ => throw $ InternalError "empty list"
          emitCall realArgs
          emit "return NULL;\n"
        else do
          emit "  return "
          emitCall argNames
      emit "}\n"
    where emitCall : List Name -> Core ()
          emitCall argNames = do
            emit external
            emit "("
            ignore . sequence $ intersperse (emit ", ") (emit . cName <$> argNames)
            emit ");\n"

  emitBinOp : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> String -> Vect 2 CILExpr -> Core ()
  emitBinOp op (a::b::Nil) = do
    emit "("
    ignore . sequence $ intersperse (emit " ") [emitExpr a, emit op, emitExpr b]
    emit ")"


  emitOp : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> PrimFn arit -> Vect arit CILExpr -> Core ()
  emitOp (Add ty)         = emitBinOp "+"
  emitOp (Sub ty)         = emitBinOp "-"
  emitOp (Mul ty)         = emitBinOp "*"
  emitOp (Div ty)         = emitBinOp "/"
  emitOp (Mod ty)         = emitBinOp "%"
  emitOp (Neg ty)         = ?emitOp_rhs_5
  emitOp (ShiftL ty)      = emitBinOp "<<"
  emitOp (ShiftR ty)      = emitBinOp ">>"
  emitOp (BAnd ty)        = emitBinOp "&"
  emitOp (BOr ty)         = emitBinOp "|"
  emitOp (BXOr ty)        = emitBinOp "^"
  emitOp (LT ty)          = emitBinOp "<"
  emitOp (LTE ty)         = emitBinOp "<="
  emitOp (EQ ty)          = emitBinOp "=="
  emitOp (GTE ty)         = emitBinOp ">="
  emitOp (GT ty)          = emitBinOp ">"
  emitOp StrLength        = ?emitOp_rhs_14
  emitOp StrHead          = \(x :: Nil) => do
    emit "("
    emitExpr x
    emit ")[0]"
  emitOp StrTail          = ?emitOp_rhs_18
  emitOp StrIndex         = ?emitOp_rhs_19
  emitOp StrCons          = ?emitOp_rhs_20
  emitOp StrAppend        = \(x :: y :: Nil) => do
    emit "idris2AppendString("
    emitExpr x
    emit ", "
    emitExpr y
    emit ")"
  emitOp StrReverse       = ?emitOp_rhs_22
  emitOp StrSubstr        = ?emitOp_rhs_23
  emitOp DoubleExp        = \(x :: Nil) => do
    emit "exp("
    emitExpr x
    emit ")"
  emitOp DoubleLog        = ?emitOp_rhs_25
  emitOp DoublePow        = ?emitOp_rhs_26
  emitOp DoubleSin        = \(x :: Nil) => do
    emit "sin("
    emitExpr x
    emit ")"
  emitOp DoubleCos        = \(x :: Nil) => do
    emit "cos("
    emitExpr x
    emit ")"
  emitOp DoubleTan        = ?emitOp_rhs_29
  emitOp DoubleASin       = ?emitOp_rhs_30
  emitOp DoubleACos       = ?emitOp_rhs_31
  emitOp DoubleATan       = ?emitOp_rhs_32
  emitOp DoubleSqrt       = ?emitOp_rhs_33
  emitOp DoubleFloor      = ?emitOp_rhs_34
  emitOp DoubleCeiling    = ?emitOp_rhs_35
  emitOp (Cast pty w)    = \(x :: Nil) => do
    emit "("
    emit (cType (inferPrimType w))
    emit ") "
    emitExpr x
  emitOp BelieveMe        = ?emitOp_rhs_37
  emitOp Crash            = \_ =>  emit "abort()"

  emitExpr : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> CILExpr -> Core ()
  emitExpr (CILExprCall fc x ty1 xs ty2) = do
                                      emit "("
                                      emitExpr x
                                      emit ")("
                                      ignore . sequence $ intersperse (emit ", ") (emitExpr <$> xs)
                                      emit ")"
  emitExpr (CILExprOp fc f xs ty) = emitOp f xs
  emitExpr (CILExprConstant fc cst ty) = emitConst cst
  emitExpr (CILExprLocal fc n ty) = emit $ cName n
  emitExpr (CILExprRef fc n ty) = emit $ cName n
  emitExpr (CILExprStruct fc n ty args) = do emit "(struct "
                                             emit (cName n)
                                             emit "){ "
                                             ignore . sequence $ intersperse (emit ", ") (emitExpr <$> args)
                                             emit " } "
  emitExpr (CILExprField fc n ty f) = do emit "("
                                         emitExpr n
                                         emit ")."
                                         emit $ cName f
  emitExpr (CILExprTaggedUnion fc n ty k args) = do
    consMap <- get ConstructorNames
    let Just allcons = lookup n consMap
      | _ => throw $ InternalError "No constructor found for tagged union"

    -- Note the constructor names are stored in reverse order.
    let Just i = natToFin (cast k) (length allcons)
      | _ => throw $ InternalError "Invalid constructor index"

    let cons = index' allcons i
    emit (cName cons)
    emit "("
    ignore . sequence $ intersperse (emit ", ") (emitExpr <$> args)
    emit ")"
  emitExpr (CILExprSizeof fc expr) = do
    emit "sizeof("
    emitExpr expr
    emit ")"
  emitExpr (CILExprAddrof fc expr) = do
    emit "&"
    emitExpr expr

  emitConstAlt : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> CILConstAlt e -> Core ()
  emitConstAlt (MkCILConstAlt e x y) = do emit "case "
                                          emitConst x
                                          emit ":\n"
                                          emitStmt y
                                          case e of
                                            Return => pure ()
                                            _ => emit "break;\n"
  emitConstCase : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> (e: Effect) -> CILExpr -> List1 (CILConstAlt e) -> Maybe (CIL (Just e)) -> Core ()
  emitConstCase e x xs def = do emit "switch ("
                                emitExpr x
                                emit ") {\n"
                                traverse_ emitConstAlt (toList xs)
                                case def of
                                  Just x => do emit "default:\n"
                                               emitStmt x
                                               emit "break;\n"
                                  _ => pure ()
                                emit "}\n"


  emitStmt : {auto _ : Ref ConstructorNames ConsMap} -> {auto _: Ref OutputRef String} -> CIL e -> Core ()
  emitStmt (CILConstCase e fc sc xs y) = emitConstCase e sc xs y
  emitStmt (CILBlock fc xs x) = traverse emitStmt xs *> emitStmt x
  emitStmt (CILAssign fc n x) = do emit (cName n)
                                   emit " = "
                                   emitExpr x
                                   emit ";\n"
  emitStmt (CILReturn fc x) = do emit "return "
                                 emitExpr x
                                 emit ";\n"
  emitStmt (CILDeclare fc ty n (CILAssign _ _ assignee)) = do
    emit (cType ty)
    emit " "
    emit (cName n)
    emit " = "
    emitExpr assignee
    emit ";\n"
  emitStmt (CILDeclare fc ty n x) = do
    emit (cType ty)
    emit " "
    emit (cName n)
    emit ";\n"
    emitStmt x
  emitStmt (CILConCase e fc sc xs) = do
    emit "switch ("
    emitExpr sc
    emit ") {\n"
    traverseList1_ emitConAlt xs
    emit "}\n"
    where emitConAlt : CILConAlt e -> Core ()
          emitConAlt (MkCILConAlt _ tag body) = do
            emit "case "
            emit (show tag)
            emit ":\n"
            emitStmt body
            emit "break;\n"

public export
emitDefs : List CILDef -> Core String
emitDefs xs = do
  _ <- newRef OutputRef ""
  _ <- newRef ConstructorNames empty
  -- Sort structs first
  let (priority, fns) = partition isPriority xs
  emit "#include <stdint.h>\n"
  emit "#include <stdbool.h>\n"
  emit "#include <stddef.h>\n\n"
  emit "#include <string.h>\n"
  emit "#include <math.h>\n"
  emit "#include <stdlib.h>\n"
  emit "#include <idris_support.h>\n"
  emit "typedef struct Value {} Value;\n\n"
  traverse_ (emitDef) priority
  traverse_ emitHeaders xs
  traverse_ (emitDef) fns
  emit "int main() {\n"
  emit "  __main_0();\n";
  emit "  return 0;\n"
  emit "}\n"
  get OutputRef
  where isPriority : CILDef -> Bool
        isPriority (MkCILStruct _ _ _) = True
        isPriority (MkCILTaggedUnion _ _ _ _) = True
        isPriority (MkCILForeign _ _ _ _ _) = True
        isPriority _ = False