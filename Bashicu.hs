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
 level e = case go e of
   Nothing -> undefined
   Just n -> n
  where
   go [] = Nothing
   go (x : xs) = let nu = go xs in case nu of
    Nothing -> if x == 0 then Nothing else Just 0
    Just n -> Just (n + 1)

 badroot :: Sequence -> Matrix -> Integer
 badroot e s = case parent (e : s) (level e) 0 of
  IsRoot -> undefined
  PIndex n -> n

 split :: Sequence -> Matrix -> (Matrix, Matrix)
 split e s = splitAt (badroot e s + 1) s

 goodpart :: Sequence -> Matrix -> Matrix
 goodpart e s = snd $ split e s

 badpart :: Sequence -> Matrix -> Matrix
 badpart e s = fst $ split e s

 apper :: Sequence -> Matrix -> Integer -> Integer -> Integer
 apper e s x y = if badroot e s `elem` ancestor s y x then 1 else 0

 delta :: Sequence -> Matrix -> Integer -> Integer
 delta e b y = if y > level e then e ! y - b ! (mlength b - 1) ! y else 0

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
