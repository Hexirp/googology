module Bashicu where
 import Prelude

 type Matrix = [Sequence]

 type Sequence = [Integer]

 data PIndex = IsRoot | HasParent Integer

 parent :: Matrix -> Integer -> Integer -> PIndex
 parent s y x = go (x + 1) where
  go p = if is_ancestor s p y x && s ! p ! y < s ! x ! y then HasParent p else if p == mlength s - 1 then IsRoot else go (p + 1)

 is_ancestor :: Matrix -> Integer -> Integer -> Integer -> Bool
 is_ancestor s p 0 x = True
 is_ancestor s p y x = p `elem` ancestor s (y - 1) x

 ancestor :: Matrix -> Integer -> Integer -> [Integer]
 ancestor s y x = go x where
  go p = p : let nu = parent s y x in case nu of
   IsRoot -> []
   HasParent p' -> go p'

 level :: Sequence -> Integer
 level e = fromMaybe undefined $ go e where
  go [] = Nothing
  go (x : xs) = let nu = go xs in case nu of
   Nothing -> if x == 0 then Nothing else Just 0
   Just n -> Just (n + 1)

 (!) :: [a] -> Integer -> a
 [] ! _ = undefined
 (x : xs) ! 0 = x
 (x : xs) ! n = xs ! (n - 1)

 infixl 9 !

 ilength :: [a] -> Integer
 ilength [] = 0
 ilength (_ : xs) = ilength xs + 1

 mlength :: Matrix -> Integer
 mlength = ilength

 slength :: Matrix -> Integer
 slength [] = undefined
 slength (x : _) = ilength x
