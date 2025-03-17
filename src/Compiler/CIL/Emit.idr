module Compiler.CIL.Emit

import Compiler.CIL.CIL
import Compiler.RefC.RefC
import Core.Context
import Data.List1
import Data.SortedMap
import Data.Vect

cType : CILType -> String
cType CILU8 = "uint8_t"
cType CILU16 = "uint16_t"
cType CILU32 = "uint32_t"
cType CILU64 = "uint64_t"
cType CILI8 = "int8_t"
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

data OutputRef : Type where

mutual
  emit : {auto p: Ref OutputRef String} -> (s: String) -> Core ()
  emit s = update OutputRef (\a => a ++ s)

  public export
  emitDef : CILDef -> Core String
  emitDef def = do
    p <- newRef OutputRef ""
    emitDef' def
    p <- get OutputRef
    pure $ p
    where emitDef' : {auto _: Ref OutputRef String} -> CILDef -> Core ()
          emitDef' (MkCILFun fc name args ret body) = do
              emit (cType ret)
              emit " "
              emit (cName name)
              emit "("
              emitArgs args
              emit ") {\n"
              emitStmt body
              emit "}\n"
          emitDef' (MkCILStruct fc name fields) = do
              emit "struct "
              emit (cName name)
              emit " { "
              ignore . sequence $ intersperse (emit ", ") (emitField <$> Data.SortedMap.toList fields)
              emit " };\n"
              where emitField : (Name, CILType) -> Core ()
                    emitField (name, ty) = do
                      emit (cType ty)
                      emit " "
                      emit (cName name)


  -- cast : {auto _: Ref OutputRef String} -> CILType ->  CILExpr -> Core ()
  -- cast to expr = do cast' !(inferExprType expr) to expr
  -- where cast' : CILType -> CILType -> CILExpr -> Core ()
  --       cast' from to x with (from == to)
  --         _                   | True =  emitExpr x
  --         cast' from CILU8 x  | _ = do emit "(uint8_t) "
  --                                      emitExpr x
  --         cast' from CILU16 x | _ = do emit "(uint16_t) "
  --                                      emitExpr x
  --         cast' from CILU32 x | _ = do emit "(uint32_t) "
  --                                      emitExpr x
  --         cast' from CILU64 x | _ = do emit "(uint64_t) "
  --                                      emitExpr x
  --         cast' from CILI8 x  | _ = do emit "(int8_t) "
  --                                      emitExpr x
  --         cast' from CILI16 x | _ = do emit "(int16_t) "
  --                                      emitExpr x
  --         cast' from CILI32 x | _ = do emit "(int32_t) "
  --                                      emitExpr x
  --         cast' from CILI64 x | _ = do emit "(int64_t) "
  --                                      emitExpr x
  --         cast' from CILF32 x | _ = do emit "(float) "
  --                                      emitExpr x
  --         cast' from CILF64 x | _ = do emit "(double) "
  --                                      emitExpr x
  --         cast' from (CILPtr y) x | _ = do emit "("
  --                                          emit (cType (CILPtr y))
  --                                          emit ") "
  --                                          emitExpr x
  --         cast' from CILWorld x | _ = do emit "(void*) "
  --                                        emitExpr x
  --         cast' from CILDyn x | _ = ?
  --         cast' CILDyn (CILFn xs y) x | _ = ?
  --         cast' (CILFn ys z) (CILFn xs y) x | _ = ?
  --         cast' (CILStruct n z) (CILFn xs y) x | _ = ?
  --         cast' from (CILStruct n y) x | _ = do emit "("
  --                                               emit (cType (CILStruct n y))
  --                                               emit ") "
  --                                               emitExpr x
  --         cast' from to x | _ = throw $ InternalError "unhandled cast"



  emitArgs : {auto _: Ref OutputRef String} -> List (Name, CILType) -> Core ()
  emitArgs xs = emit . concat $ intersperse ", " (emitArg <$> xs)
    where emitArg : (Name, CILType) -> String
          emitArg (name, t) = cType t ++ " " ++ cName name


  emitBinOp : {auto _: Ref OutputRef String} -> String -> Vect 2 CILExpr -> Core ()
  emitBinOp op (a::b::Nil) = do
    emit "("
    ignore . sequence $ intersperse (emit " ") [emitExpr a, emit op, emitExpr b]
    emit ")"


  emitOp : {auto _: Ref OutputRef String} -> PrimFn arity -> Vect arity CILExpr -> Core ()
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
  emitOp StrHead          = ?emitOp_rhs_17
  emitOp StrTail          = ?emitOp_rhs_18
  emitOp StrIndex         = ?emitOp_rhs_19
  emitOp StrCons          = ?emitOp_rhs_20
  emitOp StrAppend        = ?emitOp_rhs_21
  emitOp StrReverse       = ?emitOp_rhs_22
  emitOp StrSubstr        = ?emitOp_rhs_23
  emitOp DoubleExp        = ?emitOp_rhs_24
  emitOp DoubleLog        = ?emitOp_rhs_25
  emitOp DoublePow        = ?emitOp_rhs_26
  emitOp DoubleSin        = ?emitOp_rhs_27
  emitOp DoubleCos        = ?emitOp_rhs_28
  emitOp DoubleTan        = ?emitOp_rhs_29
  emitOp DoubleASin       = ?emitOp_rhs_30
  emitOp DoubleACos       = ?emitOp_rhs_31
  emitOp DoubleATan       = ?emitOp_rhs_32
  emitOp DoubleSqrt       = ?emitOp_rhs_33
  emitOp DoubleFloor      = ?emitOp_rhs_34
  emitOp DoubleCeiling    = ?emitOp_rhs_35
  emitOp (Cast pty pty1)  = ?emitOp_rhs_36
  emitOp BelieveMe        = ?emitOp_rhs_37
  emitOp Crash            = ?emitOp_rhs_38

  emitExpr : {auto _: Ref OutputRef String} -> CILExpr -> Core ()
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
  emitExpr (CILExprStruct fc n ty args) = do emit " { "
                                             ignore . sequence $ intersperse (emit ", ") (emitExpr <$> args)
                                             emit " } "
  emitExpr (CILExprField fc n ty f) = do emit "("
                                         emitExpr n
                                         emit ")."
                                         emit $ cName f

  covering
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
  emitConst (Str str) = do emit "\""
                           emit str
                           emit "\""
  emitConst (Ch c) = do emit "'"
                        emit $ show c
                        emit "'"
  emitConst (Db dbl) = emit (show dbl)
  emitConst (PrT pty) = emit "FIXME"
  emitConst WorldVal = emit "NULL"

  emitConstAlt : {auto _: Ref OutputRef String} -> CILConstAlt e -> Core ()
  emitConstAlt (MkCILConstAlt e x y) = do emit "case "
                                          emitConst x
                                          emit ":\n"
                                          emitStmt y
                                          case e of
                                            Return => pure ()
                                            _ => emit "break;\n"
  emitConstCase : {auto _: Ref OutputRef String} -> (e: Effect) -> CILExpr -> List1 (CILConstAlt e) -> Maybe (CIL (Just e)) -> Core ()
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


  emitStmt : {auto _: Ref OutputRef String} -> CIL e -> Core ()
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

