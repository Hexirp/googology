module Bashicu where
 import Prelude

 type Matrix = [Sequence]

 type Sequence = [Integer]

 data PIndex = IsRoot | HasParent Integer

 parent :: Matrix -> Integer -> Integer -> PIndex
 parent s y x = go (x + 1) where
  go p = if is_ancestor s p y x && s ! p ! y < s ! x ! y then HasParent p else if p == length s - 1 then IsRoot else go (p + 1)

 is_ancestor :: Matrix -> Integer -> Integer -> Integer -> Bool
 is_ancestor s p 0 x = True
 is_ancestor s p y x = p `elem` ancestor s (y - 1) x

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
