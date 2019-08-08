module Oridnal where

  import Prelude

  data Sequence = Sequence [Unary]

  data Unary = Omega Sequence | Psi Sequence | Cardinal

  lt :: Sequence -> Sequence -> Ordering
  lt (Sequence a) (Sequence b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go [] [] = EQ
    go [] (b : bs) = LT
    go (a : as) [] = GT
    go (a : as) (b : bs) = case uo a b of
      LT -> LT
      EQ -> go as bs
      GT -> GT
    uo :: Unary -> Unary -> Ordering
    uo (Omega a) (Omega b) = lt a b
    uo (Omega a) (Psi b) = lt a (Sequence [Psi b])
    uo (Omega a) Cardinal = LT
    uo (Psi a) (Omega b) = lt (Sequence [Psi a]) b
    uo (Psi a) (Psi b) = lt a b
    uo (Psi a) Cardinal = LT
    uo Cardinal (Omega b) = GT
    uo Cardinal (Psi b) = GT
    uo Cardinal Cardinal = EQ
