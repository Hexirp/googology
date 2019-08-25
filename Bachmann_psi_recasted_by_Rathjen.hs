module Oridnal where

  import Prelude
  import System.IO

  data Seq = Seq [Unary] deriving Show

  data Unary = Omega Seq | Psi Seq | Card deriving Show

  isUnary :: Seq -> Bool
  isUnary (Sequence x) = case x of
    []     -> False
    _ : [] -> True
    _ : _  -> False

  comp_s :: Seq -> Seq -> Ordering
  comp_s (Seq a) (Seq b) = go a b
   where
    go :: [Unary] -> [Unary] -> Ordering
    go []       []       = EQ
    go []       _        = LT
    go _        []       = GT
    go (a : as) (b : bs) = comp_u a b <> go as bs

  comp_u :: Unary -> Unary -> Ordering
  comp_u (Omega a) (Omega b) = comp_s a b
  comp_u (Omega a) (Psi b)   = comp_s a (Seq [Psi b])
  comp_u (Omega a) Card      = comp_s a (Seq [Card])
  comp_u (Psi a)   (Omega b) = comp_s (Seq [Psi a]) b
  comp_u (Psi a)   (Psi b)   = comp_s a b
  comp_u (Psi _)   Card      = LT
  comp_u Card      (Omega b) = comp_s (Seq [Card]) b
  comp_u Card      (Psi _)   = GT
  comp_u Card      Card      = EQ

  st_s :: Seq -> Bool
  st_s (Seq x) = go x
   where
    go :: [Unary] -> Bool
    go []       = True
    go (x : xs) = st_u x && dec x xs && go xs

  dec :: Unary -> [Unary] -> Bool
  dec x []       = True
  dec x (y : ys) = comp_u x y /= LT && dec x ys

  st_u :: Unary -> Bool
  st_u (Omega x) = st_o x && st_s x
  st_u (Psi x)   = st_p x && st_s x
  st_u Card      = True

  st_o :: Seq -> Bool
  st_o (Seq x) = case x of
    []       -> True
    x' : []  -> case x' of
      Omega _  -> True
      Psi _    -> False
      Card     -> False
    _        -> True

  st_p :: Seq -> Bool
  st_p x = all (\x' -> comp_s x' x == LT) (g1 x)

  col_s :: Seq -> [Seq]
  col_s (Seq x) = go x
   where
    go :: [Unary] -> [Seq]
    go x = case x of
      []      -> [Seq x]
      xv : [] -> col_u xv
      xv : xs -> [Seq x] ++ col_u xv ++ go xs

  col_u :: Unary -> [Seq]
  col_u x = [Seq [x]] ++ case x of
    Omega x' -> col_s x'
    Psi x'   -> col_s x'
    Card     -> []


  main :: IO ()
  main = do
    put $ comp_s (Seq []) (Seq []) == EQ
    put $ comp_s (Seq [Psi (Seq [])]) (Seq [Psi (Seq [Card])]) == LT
    put $ st_s (Seq []) == True
    put $ st_s (Seq [Psi (Seq [])]) == True
    put $ st_s (Seq [Psi (Seq [Card])]) == True
    put $ st_s (Seq [Omega (Seq [])]) == True
    put $ st_s (Seq [Omega (Seq []), Omega (Seq [])]) == True
    put $ st_s (Seq [Psi (Seq []), Psi (Seq [])]) == True
    put $ st_s (Seq [Omega (Seq [Psi (Seq [])])]) == False
    put $ st_s (Seq [Omega (Seq [Psi (Seq []), Omega (Seq [])])]) == True
    put $ st_s (Seq [Psi (Seq [Card, Omega (Seq [])])]) == True
    put $ st_s (Seq [Psi (Seq [Card, Psi (Seq [Card])])]) == True
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card])])]) == False
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Psi (Seq [Card]), Omega (Seq [])])])]) == False
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Card, Omega (Seq [])])])]) == True
    put $ g1 (Seq [Omega (Seq [Card, Omega (Seq [])])])
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Omega (Seq [Card, Card])])])]) == True
    put $ g1 (Seq [Omega (Seq [Omega (Seq [Card, Card])])])
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card])])]) == True
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card]), Omega (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card, Card, Card])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Psi (Seq [Card])]), Psi (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card, Card])])]) == False
    put $ g1 (Seq [Psi (Seq [Card, Card])])
    put $ st_s (Seq [Omega (Seq []), Omega (Seq [Omega (Seq [])])]) == False
   where
    put :: Show a => a -> IO ()
    put a = print a >> hFlush stdout
