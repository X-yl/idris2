module Compiler.CIL.Compile

import Compiler.CIL.CIL
import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Env
import Core.FC
import Data.Vect
import Debug.Trace
import Idris.Syntax
import Compiler.CIL.Emit

export
compileExpr : Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> (outputDir : String)
           -> ClosedTerm
           -> (outfile : String)
           -> Core (Maybe String)
compileExpr defs s tmpDir outputDir tm outfile = do
  cdata <- getCompileData False Cases tm
  let namedDefs = cdata.namedDefs
  defs <- get Ctxt
  types <- traverse (\(n, _) => lookupCtxtExact n (gamma defs)) namedDefs
  let types = map (type<$>) types
  prettyTypes : List (ClosedTerm) <- mapMaybeM (\ty =>
    case ty of
      Nothing => pure $ Nothing
      Just ty => do
        defs <- get Ctxt
        ty <- normaliseHoles defs [] ty
        ty <- toFullNames ty
        -- ty <- resugar [] ty
        pure $ Just ty) types

  _ <- pure $ traceVal prettyTypes

  let fnDefs = (\((a, (b,c)), d) => (a, (b,c), d)) <$> zip namedDefs prettyTypes
  compiledDefs <- compileDefs fnDefs
  code: List String <-  traverse emitDef $ compiledDefs
  traverse_ (coreLift . putStrLn) code
  pure Nothing

executeExpr : Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> ClosedTerm
           -> Core ()
executeExpr _ _ _ _ = pure ()

public export
codegenCIL : Codegen
codegenCIL = MkCG compileExpr executeExpr Nothing Nothing