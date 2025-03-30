module Compiler.CIL.Compile

import Compiler.CIL.CIL
import Compiler.CIL.Emit
import Compiler.CIL.Passes.Box
import Compiler.CIL.Passes.DeadCodeElim
import Compiler.CIL.Passes.EtaReduce
import Compiler.CIL.Passes.LambdaInstantiation
import Compiler.CIL.Passes.Monomorphise
import Compiler.CIL.Passes.StrengthenReturns
import Compiler.CIL.Passes.Unbox
import Compiler.Common
import Core.CompileExpr
import Core.Context
import Core.Directory
import Core.Env
import Core.FC
import Data.SortedMap
import Data.String
import Data.Vect
import Idris.Env
import Idris.Syntax
import Libraries.Utils.Path
import System
import System.Escape
import System.File

findFlags : {default "" d : String}
             -> (search : String) 
             -> {auto 0 known : IsJust (find (search ==) Env.envNames)} 
             -> {auto 0 known2 : IsJust (find (("IDRIS2_" ++ search) ==) Env.envNames)} 
             -> IO String
findFlags s
    = do Nothing <- idrisGetEnv $ "IDRIS2_" ++ s
           | Just cc => pure cc
         Nothing <- idrisGetEnv s
           | Just cc => pure cc 
         pure d

findCC : IO String
findCC = findFlags {d = "cc"} "CC" 

findCFLAGS : IO String
findCFLAGS = findFlags "CFLAGS"

findCPPFLAGS : IO String
findCPPFLAGS = findFlags "CPPFLAGS"

findLDFLAGS : IO String
findLDFLAGS = findFlags "LDFLAGS"

findLDLIBS : IO String
findLDLIBS = findFlags "LDLIBS"

export
compileCObjectFile : {auto c : Ref Ctxt Defs}
                  -> {default False asLibrary : Bool}
                  -> (sourceFile : String)
                  -> (objectFile : String)
                  -> Core (Maybe String)
compileCObjectFile {asLibrary} sourceFile objectFile =
  do cc <- coreLift findCC
     cFlags <- coreLift findCFLAGS
     cppFlags <- coreLift findCPPFLAGS

     refcDir <- findDataFile "refc"
     cDir <- findDataFile "c"

     let libraryFlag = if asLibrary then ["-fpic"] else []

     let runccobj = (escapeCmd $
         [cc, "-Werror", "-c", "-O3", "-g", "-Wl,-z,stack-size=1677721600"] ++ libraryFlag ++ [sourceFile,
              "-o", objectFile,
              "-I" ++ refcDir,
              "-I" ++ cDir])
              ++ " " ++ cppFlags ++ " " ++ cFlags

     0 <- coreLift $ system runccobj
       | _ => pure Nothing

     pure (Just objectFile)

export
compileCFile : {auto c : Ref Ctxt Defs}
            -> {default False asShared : Bool}
            -> (objectFile : String)
            -> (outFile : String)
            -> Core (Maybe String)
compileCFile {asShared} objectFile outFile =
  do cc <- coreLift findCC
     cFlags <- coreLift findCFLAGS
     ldFlags <- coreLift findLDFLAGS
     ldLibs <- coreLift findLDLIBS

     dirs <- getDirs
     refcDir <- findDataFile "refc"
     supportFile <- findLibraryFile "libidris2_support.a"

     let sharedFlag = if asShared then ["-shared"] else []

     let runcc = (escapeCmd $
         [cc, "-Werror"] ++ sharedFlag ++ [objectFile,
              "-o", outFile,
              supportFile,
              "-lidris2_refc",
              "-L" ++ refcDir
              ] ++ map (\d => "-L" ++ d) (lib_dirs dirs) ++ [
              "-lgmp", "-lm"])
              ++ " " ++ (unwords [cFlags, ldFlags, ldLibs])

     0 <- coreLift $ system runcc
       | _ => pure Nothing

     pure (Just outFile)

optimize : List CILDef -> SortedMap Name Name -> Core (List CILDef)
optimize defs lamstr = do
  etaReducedDefs              <- eta_reduce defs
  strengthenedDefs            <- strengthenReturns etaReducedDefs
  (monomorphisedDefs, lamstr) <- monomorphise lamstr strengthenedDefs
  lambdaInstantitatedDefs     <- lambda_instantiate lamstr monomorphisedDefs
  reStrengthenedDefs          <- strengthenReturns lambdaInstantitatedDefs
  deadCodeElimd               <- elimDeadCode lamstr reStrengthenedDefs
  boxd                        <- boxDefs deadCodeElimd
  unboxd                      <- unboxDefs boxd
  pure unboxd

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
        pure $ Just ty) types

  let fnDefs = (\((a, (b,c)), d) => (a, (b,c), d)) <$> zip (mainNamed :: namedDefs) (mainType :: prettyTypes)
  compiled <- compileDefs fnDefs

  code: String <-  emitDefs !(uncurry optimize compiled)

  let cfile = outputDir </> outfile ++ ".c"
  let outobj = outputDir </> outfile ++ ".o"
  let outexec = outputDir </> outfile

  coreLift_ $ mkdirAll outputDir

  writeFile cfile code

  Just _ <- compileCObjectFile cfile outobj
         | Nothing => pure Nothing
  ignore $ compileCFile outobj outexec
  pure (Just outexec)

executeExpr : Ref Ctxt Defs
           -> Ref Syn SyntaxInfo
           -> (tmpDir : String)
           -> ClosedTerm
           -> Core ()
executeExpr _ _ _ _ = pure ()

public export
codegenCIL : Codegen
codegenCIL = MkCG compileExpr executeExpr Nothing Nothing