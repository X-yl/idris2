module Compiler.CIL.Compile

import Compiler.CIL.CIL
import Compiler.CIL.Emit
import Compiler.CIL.Passes.EtaReduce
import Compiler.CIL.Passes.StrengthenReturns
import Compiler.CIL.Passes.DeadCodeElim
import Compiler.CIL.Passes.LambdaInstantiation
import Compiler.CIL.Passes.Monomorphise
import Compiler.CIL.Passes.Box
import Compiler.CIL.Passes.Unbox
import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Env
import Core.FC
import Data.SortedMap
import Data.Vect
import Debug.Trace
import Idris.Syntax
import Libraries.Utils.Path

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
  let mainNamed = ((MN "__main" 0), (EmptyFC, MkNmFun [] (forget cdata.mainExpr)))
  let mainType = TDelayed EmptyFC LLazy (Erased EmptyFC Placeholder)
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

  let fnDefs = (\((a, (b,c)), d) => (a, (b,c), d)) <$> zip (mainNamed :: namedDefs) (mainType :: prettyTypes)
  (compiledDefs, lamstr) <- compileDefs fnDefs
  etaReducedDefs <- eta_reduce compiledDefs
  strengthenedDefs <- strengthenReturns etaReducedDefs
  -- (coreLift . putStrLn) (show strengthenedDefs)
  _ <- pure $ traceVal "-----------------------"
  (monomorphisedDefs, lamstr) <- monomorphise lamstr strengthenedDefs
  lambdaInstantitatedDefs <- lambda_instantiate lamstr monomorphisedDefs
  -- (coreLift . putStrLn) (show lambdaInstantitatedDefs)
  reStrengthenedDefs <- strengthenReturns lambdaInstantitatedDefs
  deadCodeElimd <- elimDeadCode lamstr reStrengthenedDefs
  (coreLift . putStrLn) (show deadCodeElimd)
  boxd <- boxDefs deadCodeElimd
  unboxd <- unboxDefs boxd
  code: String <-  emitDefs unboxd
  (coreLift . putStrLn) code
  let cfile = outputDir </> outfile ++ ".c"
  coreLift $ putStrLn $ "Writing to " ++ cfile
  writeFile cfile code
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