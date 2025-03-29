module Compiler.CIL.Passes.DeadCodeElim

import Compiler.CIL.CIL
import Data.List
import Compiler.Common
import Core.Core
import Data.SortedMap
import Core.Name
import Compiler.Common
import Core.Context
import Data.Vect

%default covering

data Refs : Type where
data Seen : Type where
data Lambdas : Type where

mutual
    goExpr : {auto _ : Ref Seen (SortedMap Name Bool)} 
            -> {auto _ : Ref Refs (SortedMap Name CILDef)}
            -> {auto _ : Ref Lambdas (SortedMap Name Name)}
            -> CILExpr 
            -> Core CILExpr
    goExpr expr@(CILExprCall fc x y xs ys) = do
        _ <- goExpr x
        _ <- traverse goExpr xs
        pure expr
    goExpr expr@(CILExprOp fc f xs x) = do
        _ <- traverseVect goExpr xs
        pure expr
    goExpr expr@(CILExprConstant fc cst x) = pure expr
    goExpr expr@(CILExprLocal fc n x) = pure expr
    goExpr expr@(CILExprStruct fc n x xs) = do
        _ <- traverse goExpr xs
        Just str <- pure (lookup n !(get Refs))
            | _ => throw (InternalError "Struct not found")
        go str
        pure expr
    goExpr expr@(CILExprRef fc n x) = do
        refs <- get Refs
        Just ref <- pure (lookup n refs)
            | _ => throw (InternalError "Ref not found")
        go ref
        
        pure expr
    goExpr expr@(CILExprField fc x y n) = do
        _ <- goExpr x
        pure expr
    goExpr expr@(CILExprTaggedUnion fc n t k xs) = do
        _ <- traverse goExpr xs
        Just str <- pure (lookup n !(get Refs))
            | _ => throw (InternalError "Struct not found")
        go str
        pure expr
    goExpr expr@(CILExprSizeof fc x) = do
        _ <- goExpr x
        pure expr
    goExpr expr@(CILExprAddrof fc x) = do
        _ <- goExpr x
        pure expr

    go : {auto _ : Ref Seen (SortedMap Name Bool)} 
        -> {auto _ : Ref Refs (SortedMap Name CILDef)}
        -> {auto _ : Ref Lambdas (SortedMap Name Name)}
        -> CILDef 
        -> Core ()
    go (MkCILFun fc n args return body) = do
        if lookup n !(get Seen) == Just True 
            then pure ()
            else do
                update Seen (insert n True)
                ignore $ traverseCIL goExpr body
    go (MkCILStruct fc n members) = do
        if lookup n !(get Seen) == Just True 
            then pure ()
            else do update Seen (insert n True)
    go (MkCILTaggedUnion fc n kinds) = do
        update Seen (insert n True)
        pure ()
    go (MkCILForeign fc n _ _ _) = do
        update Seen (insert n True)
        pure ()

public export
elimDeadCode : SortedMap Name Name -> List CILDef -> Core (List CILDef)
elimDeadCode lambdas defs = do 
    let defMap = (fromList (zip (getName <$> defs) defs))
    refs <- newRef Refs defMap
    seen <- newRef Seen empty
    Just main <- pure $ Data.SortedMap.lookup (MN "__main" 0) defMap
                  | _ => throw (InternalError "No main function found") 
    lambdas <- newRef Lambdas lambdas
    _ <-  go main
    seen <- get Seen
    let defs = filter (\def => lookup (getName def) seen == Just True) defs
    pure defs
        
