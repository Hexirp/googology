module Bashicu where
 import Prelude

 type Matrix = [Sequence]

 type Sequence = [Integer]

 data PIndex = IsRoot | HasParent Integer deriving (Eq, Ord, Show)

 parent :: Matrix -> Integer -> Integer -> PIndex
 parent s y x = go x where
  go p = if is_ancestor s p y x && s ! p ! y < s ! x ! y
   then HasParent p
   else if p == mlength s - 1
    then IsRoot
    else go (p + 1)

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
  HasParent n -> n

 -- isplitAt (badroot e s + 1) (e : s) = isplitAt (badroot e s) s
 split :: Sequence -> Matrix -> (Matrix, Matrix)
 split e s = isplitAt (badroot e s) s

 goodpart :: Sequence -> Matrix -> Matrix
 goodpart e s = snd $ split e s

 badpart :: Sequence -> Matrix -> Matrix
 badpart e s = fst $ split e s

 apper :: Sequence -> Matrix -> Integer -> Integer -> Integer
 apper e s x y = if badroot e s `elem` ancestor (e : s) y (x + 1) then 1 else 0

 delta :: Sequence -> Matrix -> Integer -> Integer
 delta e b y = if y < level e then e ! y - b ! (mlength b - 1) ! y else 0

 ecopies
  :: Sequence -> (Matrix, Matrix) -> Integer -> Integer -> Integer
  -> Integer
 ecopies e (b, g) a x y = b ! x ! y + a * delta e b y * apper e (b ++ g) x y

 scopies :: Sequence -> (Matrix, Matrix) -> Integer -> Integer -> Sequence
 scopies e (b, g) a x =
  map (\y -> ecopies e (b, g) a x y) [ 0 .. elength e - 1 ]

 mcopies :: Sequence -> (Matrix, Matrix) -> Integer -> Matrix
 mcopies e (b, g) a = map (\x -> scopies e (b, g) a x) [ 0 .. mlength b - 1 ]

 copies :: Sequence -> (Matrix, Matrix) -> Integer -> Matrix
 copies e (b, g) n = go n where
  go m = mcopies e (b, g) m ++ if m == 0 then g else go (m - 1)

 expand :: Sequence -> Matrix -> Integer -> Matrix
 expand e s n = copies e (split e s) n


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

 elength :: Sequence -> Integer
 elength = ilength

 isplitAt :: Integer -> [a] -> ([a], [a])
 isplitAt n xs = (itake n xs, idrop n xs)

 itake :: Integer -> [a] -> [a]
 itake 0 _ = []
 itake n [] = undefined
 itake n (x : xs) = x : itake (n - 1) xs

 idrop :: Integer -> [a] -> [a]
 idrop 0 x = x
 idrop n [] = undefined
 idrop n (x : xs) = idrop (n - 1) xs
