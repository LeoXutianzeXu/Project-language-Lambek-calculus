{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Lambek where

import LTypes

-- Step 1
-- do we have [LTp] -> LTp?
dec_rinv :: [LTp] -> LTp -> Bool
dec_rinv [] _ = False
dec_rinv gamma (DivL c d) = dec_rinv (c:gamma) d
dec_rinv gamma (DivR d c) = dec_rinv (gamma++[c]) d
dec_rinv gamma (Atm p) = split [] gamma -- try all possible splits of gamma
    where
        split _ [] = False
        split gammaL1 (g:ammaR2) = if dec_lfoc gammaL1 g ammaR2 p
                                   then True
                                   else split (gammaL1++[g]) ammaR2

-- Step 2
dec_lfoc :: [LTp] -> LTp -> [LTp] -> Atm -> Bool
dec_lfoc gammaL (DivL a b) gammaR p = split [] gammaL -- split function: I try all the possible splits of gammaL
    where
        split _ [] = False
        split gammaL1 (g:ammaL2) = if dec_rinv (g:ammaL2) a && dec_lfoc gammaL1 b gammaR p
                                   then True
                                   else split (gammaL1++[g]) ammaL2 
dec_lfoc gammaL (DivR b a) gammaR p = split [] gammaR
    where 
        split _ [] = False
        split gammaR1 (g:ammaR2) = if dec_rinv (gammaR1 ++ [g]) a && dec_lfoc gammaL b ammaR2 p
                                   then True
                                   else split (gammaR1++[g]) ammaR2
dec_lfoc [] (Atm p1) [] p2 = if p1 == p2 
                             then True
                             else False 
dec_lfoc gammaL (Atm a) gammaR p = False

-- Step 3
-- make appropriate calls to dec_rinv.
-- main challenge: each word w in ws can have multiple lexical entries (w, A, _) in lex.
isGrammatical :: Lexicon sem -> [String] -> Bool
isGrammatical lex ws = undefined

