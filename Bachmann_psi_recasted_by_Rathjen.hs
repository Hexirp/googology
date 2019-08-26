module Oridnal where

  import Prelude
  import System.IO

  rep :: Integer -> a -> [a]
  rep 0 _ = []
  rep n x = x : rep (n - 1) x

  data Seq = Seq [Unary] deriving Show

  data Unary = Omega Seq | Psi Seq | Card deriving Show

  isUnary :: Seq -> Bool
  isUnary (Seq x) = case x of
    []     -> False
    _ : [] -> True
    _ : _  -> False

  to_i :: Seq -> Integer
  to_i (Seq x) = go x
   where
    go :: [Unary] -> Integer
    go []       = 0
    go (_ : xs) = 1 + go xs

  from_i :: Integer -> Seq
  from_i n = Seq (go n)
   where
    go :: Integer -> [Unary]
    go 0 = []
    go n = Omega (Seq []) : from_i (n - 1)

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
  st_p x = all (\x' -> comp_s x' x == LT) (col1_s x)

  col1_s :: Seq -> [Seq]
  col1_s (Seq x) = go x
   where
    go :: [Unary] -> [Seq]
    go x = case x of
      []      -> []
      xv : [] -> col1_u xv
      xv : xs -> col_u xv ++ go xs

  col1_u :: Unary -> [Seq]
  col1_u x = case x of
    Omega x' -> col_s x'
    Psi x'   -> col_s x'
    Card     -> []

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

  cof_s :: Seq -> Seq
  cof_s (Seq x) = go x
   where
    go :: [Unary] -> Seq
    go x = case x of
      []      -> Seq []
      xv : [] -> cof_u xv
      _  : xs -> go xs

  cof_u :: Unary -> Seq
  cof_u x = case x of
    Omega x' -> case cof_s x' of
      Seq []                             -> Seq [Omega (Seq [])]
      Seq [Omega (Seq [])]               -> Seq [Omega (Seq [Omega (Seq [])])]
      Seq [Omega (Seq [Omega (Seq [])])] -> Seq [Omega (Seq [Omega (Seq [])])]
      Seq [Card]                         -> Seq [Card]
      _                                  -> error "impossible"
    Psi x'   -> case cof_s x' of
      Seq []                             -> Seq [Omega (Seq [Omega (Seq [])])]
      Seq [Omega (Seq [])]               -> Seq [Omega (Seq [Omega (Seq [])])]
      Seq [Omega (Seq [Omega (Seq [])])] -> Seq [Omega (Seq [Omega (Seq [])])]
      Seq [Card]                         -> Seq [Omega (Seq [Omega (Seq [])])]
      _                                  -> error "impossible"
    Card     -> Seq [Card]

  fun :: Seq -> Seq -> Seq
  fun x n = if comp_s n (cof_s x) == LT then f x n else x
   where
    f :: Seq -> Seq -> Seq
    f (Seq x) n = case x of
      []      -> error "impossible"
      xv : [] -> fun_u xv n
      xv : xs -> fun_s (Seq (xv : xs)) n

  fun_s :: Seq -> Seq -> Seq
  fun_s x n = case cof_s x of
    Seq []                             -> error "impossible"
    Seq [Omega (Seq [])]               -> fun_s_S x
    Seq [Omega (Seq [Omega (Seq [])])] -> fun_s_L x n
    Seq [Card]                         -> fun_s_L x n
    _                                  -> error "impossible"

  fun_s_S :: Seq -> Seq
  fun_s_S (Seq x) = Seq (go x)
   where
    go :: [Unary] -> [Unary]
    go x = case x of
      []      -> error "impossible"
      xv : [] -> []
      xv : xs -> xv : go xs

  fun_s_L :: Seq -> Seq -> Seq
  fun_s_L (Seq x) n = Seq (go x n)
   where
    go :: [Unary] -> Seq -> [Unary]
    go x n = case x of
      []      -> error "impossible"
      xv : [] -> let Seq x' = fun_u xv n in x'
      xv : xs -> xv : go xs n

  fun_u :: Unary -> Seq -> Seq
  fun_u x n = case x of
    Omega x' -> fun_u_w x' n
    Psi x'   -> fun_u_p x' n
    Card     -> n

  fun_u_w :: Seq -> Seq -> Seq
  fun_u_w x n = case cof_s x of
    Seq []                             -> error "impossible"
    Seq [Omega (Seq [])]               -> Seq (rep (to_i n) (Omega (fun_s_S x)))
    Seq [Omega (Seq [Omega (Seq [])])] -> Seq [Omega (fun_s_L x n)]
    Seq [Card]                         -> Seq [Omega (fun_s_L x n)]
    _                                  -> error "impossible"

  fun_u_p :: Seq -> Seq -> Seq
  fun_u_p x n = case cof_s x of
    Seq []                             -> go_o (to_i n)
    Seq [Omega (Seq [])]               -> go_s x (to_i n)
    Seq [Omega (Seq [Omega (Seq [])])] -> Seq [Psi (fun_s_L x n)]
    Seq [Card]                         -> Seq [Psi (fun_s_L x (go_W x (to_i n)))]
    _                                  -> error "impossible"
   where
    go_o :: Integer -> Seq
    go_o 0 = Seq []
    go_o n = Seq [Omega (go_o (n - 1))]
    --
    go_s :: Seq -> Integer -> Seq
    go_s x 0 = Seq [Psi (fun_s_S x), Omega (Seq [])]
    go_s x n = Seq [Omega (go_s x (n - 1))]
    --
    go_W :: Seq -> Integer -> Seq
    go_W x 0 = Seq []
    go_W x n = Seq [Psi (fun_s_L x (go_W x (n - 1)))]

  pretty_s :: Seq -> String
  pretty_s (Seq x) = go x
   where
    go :: [Unary] -> String
    go x = case x of
      []      -> "0"
      xv : [] -> pretty_u xv
      xv : xs -> pretty_u xv ++ " + " ++ go xs

  pretty_u :: Unary -> String
  pretty_u x = case x of
    Omega x' -> "\\w ^ { " ++ pretty_s x' ++ " }"
    Psi   x' -> "\\pw ( " ++ pretty_s x' ++ " )"
    Card     -> "\\W"


  main :: IO ()
  main = do
    --
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
    put $ col1_s (Seq [Omega (Seq [Card, Omega (Seq [])])])
    put $ st_s (Seq [Psi (Seq [Omega (Seq [Omega (Seq [Card, Card])])])]) == True
    put $ col1_s (Seq [Omega (Seq [Omega (Seq [Card, Card])])])
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card])])]) == True
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card]), Omega (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Card, Card, Psi (Seq [Card, Card, Card])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Psi (Seq [Card])]), Psi (Seq [])])]) == False
    put $ st_s (Seq [Psi (Seq [Psi (Seq [Card, Card])])]) == False
    put $ col1_s (Seq [Psi (Seq [Card, Card])])
    put $ st_s (Seq [Omega (Seq []), Omega (Seq [Omega (Seq [])])]) == False
    --
    fundamental 10 $ Seq [Psi (Seq [Omega (Seq [Omega (Seq [Card, Card])])])]
   where
    --
    put :: Show a => a -> IO ()
    put a = print a >> hFlush stdout
    --
    fundamental :: Integer -> Seq -> IO ()
    fundamental n t = forM_ [ 0 .. n ] $ put . pretty_s . fun t . from_i
