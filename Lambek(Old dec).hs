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
-- 1. Given a word, retrieve all its possible types.
-- 2. Given a list of words, consider the combinations of types available for those words, and check the resulting type lists using dec_rinv.

isGrammatical :: Lexicon sem -> [String] -> Bool
isGrammatical _ [] = False -- empty sentence is nongrammatical.
-- stp: the type that the entire sequence of words has to derive to, to count as grammatical. 
isGrammatical (Lexicon items stp) words = checkRinvs (combinations (wordTypes items words)) 
    where
        -- helper function that gives you a nested list representing which types each word can be e.g. [[NP], [NP, S], [NP]]
        wordTypes _ [] = []
        -- this list comprehension gives list of types for one word
        wordTypes items (w:ws) = [ltp | (str, ltp, _ ) <- items, str == w] : (wordTypes items ws) 

        -- helper function that gives a nested list with all type combinations, taking one type from each word's possible types list.
        combinations [] = [[]]
        -- idea: take one type for the first word, t, and prepend it to all later possible combinations.  
        combinations (types:rest) = [t:combo | t <- types, combo <- combinations rest]

        -- helper function that checks whether at least 1 combination passes the previous rinv function check.
        checkRinvs [] = False
        checkRinvs (gamma:gammas) = (dec_rinv gamma stp) || (checkRinvs gammas)

