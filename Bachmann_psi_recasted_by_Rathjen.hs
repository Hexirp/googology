module Oridnal where

  import Prelude

  data Sequence = Sequence [Unary]

  data Unary = Omega Sequence | Psi Sequence | Cardinal

  lt :: Sequence -> Sequence -> Ordering
  lt (Sequence a) (Sequence b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       (b : bs) = LT
    go (a : as) []       = GT
    go (a : as) (b : bs) = case uo a b of
      LT -> LT
      EQ -> go as bs
      GT -> GT
    uo :: Unary -> Unary -> Ordering
    uo (Omega a) (Omega b) = lt a b
    uo (Omega a) (Psi b)   = lt a (Sequence [Psi b])
    uo (Omega a) Cardinal  = LT
    uo (Psi a)   (Omega b) = lt (Sequence [Psi a]) b
    uo (Psi a)   (Psi b)   = lt a b
    uo (Psi a)   Cardinal  = LT
    uo Cardinal  (Omega b) = GT
    uo Cardinal  (Psi b)   = GT
    uo Cardinal  Cardinal  = EQ

  st :: Sequence -> Bool
  st (Sequence x) = go x
   where
    go :: [Unary] -> Bool
    go [] = True
    go (x : xs) = stu x && go xs
    stu :: Unary -> Bool
    stu (Omega x) = case x of
      [] -> True
      [x'] -> case x' of
        Omega x'' -> st (Sequence [Omega x''])
        Psi x'' -> False
        Cardinal -> False
      (x' : xs') -> True
    stu (Psi x) = st x && stug x
    stu Cardinal = True
    stug :: Sequence -> Bool
    stug x@(Sequence x') = go x x'
     where
      go :: Sequence -> [Unary] -> Bool
      go x [] = True
      go x (x' : xs') = stugu x x' && go x xs'
      stugu :: Sequence -> Unary -> Bool
      stugu x (Omega (Sequence y)) = go x y
      stugu x y@(Psi (Sequence y')) = lt
