{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore #-}

module Main where

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.QuickCheck.Test (quickCheck)
import Test.Tasty.HUnit

import Compiler
import qualified Data.Map as M
import Control.Monad
import Data.List (transpose, nubBy)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [ testCase "Exemplo merge" $
      compilationScheme (M.fromList [("List", [exConstr1, exConstr2]), ("Unit", [exConstr3])]) [exVal2, exVal2] exClause1 
      `compare` 
      Switch (ValConstr (Constr {name = "cons", arity = 2, ty = "List"}) [ValConstr (Constr {name = "Unit", arity = 0, ty = "Unit"}) [],ValConstr (Constr {name = "nil", arity = 0, ty = "List"}) []]) [(Constr {name = "nil", arity = 0, ty = "List"},Leaf 1),(Constr {name = "cons", arity = 2, ty = "List"},Swap 3 (Switch (ValConstr (Constr {name = "Unit", arity = 0, ty = "Unit"}) []) [(Constr {name = "nil", arity = 0, ty = "List"},Leaf 2),(Constr {name = "cons", arity = 2, ty = "List"},Leaf 3)]))]
      @?= EQ
  ]

genChar :: Gen Char
genChar = elements ['a'..'z']

genConstr :: String -> Gen Constr
genConstr typeName = 
  do
    nameSize <- choose (3, 7)
    constrName <- vectorOf nameSize genChar
    a <- choose (0, 7)
    return (Constr constrName a typeName)

genType :: Gen (String, [Constr])
genType =
  do 
    nameSize <- choose (3, 7)
    typeName <- vectorOf nameSize genChar
    constrNumber <- choose (1, 7)
    constrs <- vectorOf constrNumber (genConstr typeName)
    return (typeName, constrs)

genCtx :: Gen Ctx
genCtx = 
  do 
    n <- choose (1,10)
    ts <- vectorOf n (genType)
    return (M.fromList ts)

genPatConstrCtx :: Ctx -> Int -> Gen Pat
genPatConstrCtx ctx n =
  do
    (_, cs) <- elements (M.toList ctx)
    c <- elements cs
    let a = arity c
    ps <- replicateM a (genPatCtx ctx (n-1))
    return (PatConstr c ps)

genPatOrCtx :: Ctx -> Int -> Gen Pat
genPatOrCtx ctx n =
  do
    p1 <- genPatCtx ctx (n-1)
    p2 <- genPatCtx ctx (n-1)
    return (PatOr p1 p2)

genPatCtx :: Ctx -> Int -> Gen Pat
genPatCtx _ 0 = return PatWild
genPatCtx ctx n = frequency [(30, return PatWild), (60, genPatConstrCtx ctx n), (10, genPatOrCtx ctx n)]

genPatCtx' :: Gen Pat
genPatCtx' =
  do
    ctx <- genCtx
    n <- choose (1, 4)
    genPatCtx ctx n

genMatCtx :: Ctx -> Int -> Int -> Int -> Gen [[Pat]]
genMatCtx ctx lin col patSize =
  do
    vectorOf lin $ vectorOf col $ genPatCtx ctx patSize

genMatCtx' :: Gen [[Pat]]
genMatCtx' =
  do
    ctx <- genCtx
    lin <- choose (1, 5)
    col <- choose (1, 5)
    maxPatSize <- choose (1, 4)
    genMatCtx ctx lin col maxPatSize


genPatConstr :: [Constr] -> Int -> Gen Pat
genPatConstr t n =
  do
    c <- elements t
    let a = arity c
    ps <- replicateM a (genPat t (n-1))
    return (PatConstr c ps)

genPatOr :: [Constr] -> Int -> Gen Pat
genPatOr t n =
  do
    p1 <- genPat t (n-1)
    p2 <- genPat t (n-1)
    return (PatOr p1 p2)

genPat :: [Constr] -> Int -> Gen Pat
genPat _ 0 = return PatWild
genPat t n = frequency [(30, return PatWild), (60, genPatConstr t n), (10, genPatOr t n)]

genPat' :: Gen Pat
genPat' =
  do
    (_, cs) <- genType
    n <- choose (1, 4)
    genPat cs n

genListPat :: [[Constr]] -> Int -> Int -> Gen [Pat]
genListPat cs col patSize = 
  do
    cs' <- elements cs
    vectorOf col (genPat cs' patSize) 

genMat :: Ctx -> Int -> Int -> Int -> Gen [[Pat]]
genMat ctx lin col patSize =
  do
    ts <- vectorOf col (elements (M.toList ctx))
    let cs = map snd ts
    m <- vectorOf col (genListPat cs lin patSize)
    return (transpose m)

genMat' :: Gen [[Pat]]
genMat' =
  do
    ctx <- genCtx
    lin <- choose (1, 5)
    col <- choose (1, 5)
    maxPatSize <- choose (1, 4)
    genMat ctx lin col maxPatSize


-- Todos os padrões pertencem ao contexto

patInCtx :: Ctx -> Pat -> Bool
patInCtx _ PatWild = True
patInCtx ctx (PatOr p1 p2) = patInCtx ctx p1 && patInCtx ctx p2
patInCtx ctx (PatConstr c _) = c `elem` cs
  where
    cs = concatMap snd (M.toList ctx)

matInCtx :: Ctx -> [[Pat]] -> Bool
matInCtx ctx m = and $ map (patInCtx ctx) (concat m)

prop_patInCtx :: Property
prop_patInCtx =
  forAll (choose (1,5)) $
    \lin -> forAll (choose (1,5)) $
    \col -> forAll (choose (1,4)) $
    \maxPatSize -> forAll genCtx $
    \ctx -> forAll (genMat ctx lin col maxPatSize) $
    \m -> matInCtx ctx m


-- Todos os padrões em uma coluna são do mesmo tipo

patType :: Pat -> [String]
patType PatWild = []
patType (PatConstr c _) = [ty c]
patType (PatOr p1 p2) = patType p1 ++ patType p2

patType' :: [Pat] -> Bool
patType' ps = allEqual $ concatMap patType ps
  where
    allEqual = \xs -> all (== head xs) xs

allColSameType :: [[Pat]] -> Bool
allColSameType m = all patType' (transpose m)

prop_allColSameType :: Property
prop_allColSameType =
  forAll (choose (1,5)) $
    \lin -> forAll (choose (1,5)) $
    \col -> forAll (choose (1,4)) $
    \maxPatSize -> forAll genCtx $
    \ctx -> forAll (genMat ctx lin col maxPatSize) $
    \m -> allColSameType m


-- número de padrões depois da especialização é menor que o número antes

genCM :: Ctx -> Int -> Int -> Int -> Gen ClauseMatrix
genCM ctx lin col patSize =
  do
    m <- genMat ctx lin col patSize
    let a = take lin [1..]
    return (m, a)

genCM' :: Gen ClauseMatrix
genCM' =
  do
    ctx <- genCtx
    lin <- choose (1, 5)
    col <- choose (1, 5)
    maxPatSize <- choose (1, 4)
    genCM ctx lin col maxPatSize

chooseConstr :: Ctx -> Gen Constr
chooseConstr ctx =
  do
    (_, cs) <- elements (M.toList ctx)
    elements cs

countPat :: Pat -> Int
countPat PatWild = 0
countPat (PatConstr _ ps) = 1 + countPatLine ps
countPat (PatOr p1 p2) = countPat p1 + countPat p2

countPatLine :: [Pat] -> Int
countPatLine [] = 0
countPatLine (p:ps) = countPat p + countPatLine ps

countPatMat :: ClauseMatrix -> Int
countPatMat ([], []) = 0
countPatMat (l:ls, _:as) = countPatLine l + countPatMat (ls, as)
countPatMat _ = 0

countPatCMUnique :: ClauseMatrix -> Int
countPatCMUnique (m, a) = countPatMat uniqueM
  where
    uniqueLine = nubBy (\x y -> snd x == snd y) (zip m a)
    uniqueM = unzip uniqueLine


countOr :: Pat -> Int
countOr PatWild = 0
countOr (PatConstr _ ps) = foldr (+) 0 (map countOr ps)
countOr (PatOr p1 p2) = 1 + countOr p1 + countOr p2

countPatCM :: ClauseMatrix -> (Int, Int)
countPatCM (m, _) = (nPat, nOr)
  where
    nPat = foldr (+) 0 (map countPat (concat m))
    nOr = foldr (+) 0 (map countOr (concat m))


lineProcOr :: [Pat] -> Action -> ClauseMatrix
lineProcOr [] _ = ([], [])
lineProcOr ((PatOr p1 p2):ps) a = lineProcOr (p1:ps) a <> lineProcOr (p2:ps) a
lineProcOr ps a = ([ps], [a])

procOr :: ClauseMatrix -> ClauseMatrix
procOr (l:ls, a:as) = (lineProcOr l a) <> procOr (ls, as)
procOr _ = ([], [])


{- 
-- Teste para processar Or em toda a matriz

toList :: Pat -> [Pat]
toList (PatOr p1 p2) = toList p1 ++ toList p2
toList p = [p]

addPat :: Pat -> ClauseMatrix -> ClauseMatrix
addPat p (m, a) = (m', a)
  where
    ps = replicate (length m) p
    m' = transpose (ps : transpose m)

addListPat :: [Pat] -> ClauseMatrix -> ClauseMatrix
addListPat ps (m, a) = (m', a)
  where
    ps' = map (replicate (length m)) ps
    m' = transpose (transpose ps' ++ transpose m)

addListPat' :: [Pat] -> ClauseMatrix -> ClauseMatrix
addListPat' ps m = foldr addPat m ps

teste :: [Pat] -> Action -> ClauseMatrix
teste ps a = foldr addListPat ([[]], [a]) ps'
  where
    ps' = map toList ps
-}

prop_specReduces :: Property
prop_specReduces =
  forAll (choose (1,7)) $
    \lin -> forAll (choose (1,7)) $
    \col -> forAll (choose (1,5)) $
    \maxPatSize -> forAll genCtx $
    \ctx -> forAll (chooseConstr ctx) $
    \c -> forAll (genCM ctx lin col maxPatSize) $
    \m -> not (allWild (head (transpose (fst m)))) ==> countPatMat (spec c m) < countPatMat (procOr m)


-- pré processar Or preserva semântica

genValConstr :: [Constr] -> Int -> Gen Val
genValConstr t n =
  do
    c <- elements t
    let a = arity c
    ps <- replicateM a (genVal t (n-1))
    return (ValConstr c ps)

genVal :: [Constr] -> Int -> Gen Val
genVal _ 0 = return (ValConstr (Constr "Unit" 0 "Unit") [])
genVal t n = frequency [(30, return (ValConstr (Constr "Unit" 0 "Unit") [])), (70, genValConstr t n)]

genVal' :: Gen Val
genVal' =
  do
    (_, cs) <- genType
    n <- choose (1, 4)
    genVal cs n

genListVal :: [[Constr]] -> Int -> Gen Val
genListVal cs valSize = 
  do
    cs' <- elements cs
    genVal cs' valSize

genOccurrence :: Ctx -> Int -> Int -> Gen Occurrence
genOccurrence ctx n valSize =
  do
    ts <- vectorOf n (elements (M.toList ctx))
    let cs = map snd ts
    vectorOf n (genListVal cs valSize)

genOccurrence' :: Gen Occurrence
genOccurrence' =
  do
    ctx <- genCtx
    n <- choose (1, 5)
    maxValSize <- choose (1, 4)
    genOccurrence ctx n maxValSize

prop_procOrPreserves :: Property
prop_procOrPreserves = 
  forAll (choose (1,2)) $
    \lin -> forAll (choose (1,2)) $
    \col -> forAll (choose (1,2)) $
    \maxPatSize -> forAll genCtx $
    \ctx -> forAll (genCM ctx lin col maxPatSize) $
    \m -> forAll (genOccurrence ctx col maxPatSize) $
    \o -> mlMatch o m == mlMatch o (procOr m)