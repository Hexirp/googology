module Oridnal where

  import Prelude

  data Sequence = Sequence [Unary]

  data Unary = Omega Sequence | Psi Sequence | Cardinal

  lt_seq :: Sequence -> Sequence -> Ordering
  lt_seq (Sequence a) (Sequence b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       (b : bs) = LT
    go (a : as) []       = GT
    go (a : as) (b : bs) = case lt_u a b of
      LT -> LT
      EQ -> go as bs
      GT -> GT

  lt_u :: Unary -> Unary -> Ordering
  lt_u (Omega a) (Omega b) = lt_seq a b
  lt_u (Omega a) (Psi b)   = lt_seq a (Sequence [Psi b])
  lt_u (Omega a) Cardinal  = LT
  lt_u (Psi a)   (Omega b) = lt_seq (Sequence [Psi a]) b
  lt_u (Psi a)   (Psi b)   = lt_seq a b
  lt_u (Psi a)   Cardinal  = LT
  lt_u Cardinal  (Omega b) = GT
  lt_u Cardinal  (Psi b)   = GT
  lt_u Cardinal  Cardinal  = EQ

  st_seq :: Sequence -> Bool
  st_seq (Sequence x) = go x
   where
    go :: [Unary] -> Bool
    go []       = True
    go (x : xs) = st_u x && dec x xs && go xs

  dec :: Unary -> Sequence -> Bool
  dec x []       = True
  dex x (y : ys) = lt_u x y && ys

  st_u :: Unary -> Bool
  st_u (Omega x) = case x of
    [] -> True
    [x'] -> case x' of
      Omega x'' -> st_seq (Sequence [Omega x''])
      Psi x'' -> False
      Cardinal -> False
    (x' : xs') -> True
  st_u (Psi x) = g_u x && st_seq x
  st_u Cardinal = True

  g_u :: Sequence -> Bool
  g_u x = go x x
   where
    --
    go_seq :: Sequence -> Sequence -> Bool
    go_seq x (Sequence y) = go x y
    --
    go_us :: Sequence -> [Unary] -> Bool
    go_us x []       = True
    go_us x (y : ys) = go_u x y && go x xs'
    --
    go_u :: Sequence -> Unary -> Bool
    go_u x (Omega y) = lt_seq y x && 
    go_u x y@(Psi (Sequence y')) = lt
