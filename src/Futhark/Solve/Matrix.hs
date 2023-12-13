module Futhark.Solve.Matrix
  ( Matrix (..),
    toList,
    toLists,
    fromVector,
    fromLists,
    (@),
    (!),
    sliceCols,
    getColM,
    getCol,
    setCol,
    sliceRows,
    getRowM,
    getRow,
    (<|>),
    (<->),
    addRow,
    addRows,
    imap,
    generate,
    identity,
    diagonal,
    (<.>),
    (.*),
    (*.),
    (.+.),
    (.-.),
  )
where

import Data.Vector.Unboxed (Unbox, Vector)
import Data.Vector.Unboxed qualified as V

-- A matrix represented as a 1D 'Vector'.
data Matrix a = Matrix
  { elems :: Vector a,
    nrows :: Int,
    ncols :: Int
  }
  deriving (Eq)

instance (Show a, Unbox a) => Show (Matrix a) where
  show =
    unlines . map show . toLists

toList :: (Unbox a) => Matrix a -> [Vector a]
toList m =
  map (\r -> V.slice (r * ncols m) (nrows m) (elems m)) [0 .. nrows m - 1]

toLists :: (Unbox a) => Matrix a -> [[a]]
toLists m =
  map (\r -> V.toList $ V.slice (r * ncols m) (ncols m) (elems m)) [0 .. nrows m - 1]

fromVector :: (Unbox a) => Vector a -> Matrix a
fromVector v =
  Matrix
    { elems = v,
      nrows = 1,
      ncols = V.length v
    }

fromLists :: (Unbox a) => [[a]] -> Matrix a
fromLists xss =
  Matrix
    { elems = V.concat $ map V.fromList xss,
      nrows = length xss,
      ncols = length $ head xss
    }

class SelectCols a where
  select :: Vector Int -> a -> a
  (@) :: a -> Vector Int -> a
  (@) = flip select

infix 9 @

instance (Unbox a) => SelectCols (Vector a) where
  select s v = V.map (v V.!) s

instance (Unbox a) => SelectCols (Matrix a) where
  select = sliceCols

(!) :: (Unbox a) => Matrix a -> (Int, Int) -> a
m ! (r, c) = elems m V.! (ncols m * r + c)

sliceCols :: (Unbox a) => Vector Int -> Matrix a -> Matrix a
sliceCols cols m =
  Matrix
    { elems =
        V.generate (nrows m * V.length cols) $ \i ->
          let col = cols V.! (i `rem` V.length cols)
              row = i `div` V.length cols
           in m ! (row, col),
      nrows = nrows m,
      ncols = V.length cols
    }

getColM :: (Unbox a) => Int -> Matrix a -> Matrix a
getColM col = sliceCols $ V.singleton col

getCol :: (Unbox a) => Int -> Matrix a -> Vector a
getCol col = elems . getColM col

setCol :: (Unbox a) => Int -> Vector a -> Matrix a -> Matrix a
setCol c col m =
  m
    { elems =
        V.update_ (elems m) indices col
    }
  where
    indices = V.generate (nrows m) $
      \r -> r * ncols m + c

sliceRows :: (Unbox a) => Vector Int -> Matrix a -> Matrix a
sliceRows rows m =
  Matrix
    { elems =
        V.generate (ncols m * V.length rows) $ \i ->
          let row = rows V.! (i `rem` V.length rows)
              col = i `div` V.length rows
           in m ! (row, col),
      nrows = V.length rows,
      ncols = ncols m
    }

getRowM :: (Unbox a) => Int -> Matrix a -> Matrix a
getRowM row = sliceRows $ V.singleton row

getRow :: (Unbox a) => Int -> Matrix a -> Vector a
getRow row = elems . getRowM row

(<|>) :: (Unbox a) => Matrix a -> Matrix a -> Matrix a
m1 <|> m2 =
  generate f (nrows m1) (ncols m1 + ncols m2)
  where
    f r c
      | c < ncols m1 = m1 ! (r, c)
      | otherwise = m2 ! (r, c - ncols m1)

(<->) :: (Unbox a) => Matrix a -> Matrix a -> Matrix a
m1 <-> m2 =
  generate f (nrows m1 + nrows m2) (ncols m1)
  where
    f r c
      | r < nrows m1 = m1 ! (r, c)
      | otherwise = m2 ! (r - nrows m1, c)

addRow :: (Unbox a) => Matrix a -> Vector a -> Matrix a
addRow m v =
  m
    { elems = elems m V.++ v,
      nrows = nrows m + 1
    }

addRows :: (Unbox a) => Matrix a -> [Vector a] -> Matrix a
addRows = foldl addRow

imap :: (Unbox a) => (Int -> Int -> a -> a) -> Matrix a -> Matrix a
imap f m =
  m
    { elems = V.imap g $ elems m
    }
  where
    g i =
      let r = i `div` ncols m
          c = i `rem` nrows m
       in f r c

generate :: (Unbox a) => (Int -> Int -> a) -> Int -> Int -> Matrix a
generate f rows cols =
  Matrix
    { elems =
        V.generate (rows * cols) $ \i ->
          let r = i `div` cols
              c = i `rem` cols
           in f r c,
      nrows = rows,
      ncols = cols
    }

identity :: (Unbox a, Num a) => Int -> Matrix a
identity n = generate (\r c -> if r == c then 1 else 0) n n

diagonal :: (Unbox a, Num a) => Vector a -> Matrix a
diagonal d = generate (\r c -> if r == c then d V.! r else 0) (V.length d) (V.length d)

(<.>) :: (Unbox a, Num a) => Vector a -> Vector a -> a
v1 <.> v2 = V.sum $ V.zipWith (*) v1 v2

infixl 7 <.>

(*.) :: (Unbox a, Num a) => Matrix a -> Vector a -> Vector a
m *. v =
  V.generate (nrows m) $ \r ->
    getRow r m <.> v

infixl 7 *.

(.*) :: (Unbox a, Num a) => Vector a -> Matrix a -> Vector a
v .* m =
  V.generate (ncols m) $ \c ->
    v <.> getCol c m

infixl 7 .*

(.-.) :: (Unbox a, Num a) => Vector a -> Vector a -> Vector a
(.-.) = V.zipWith (-)

infixl 6 .-.

(.+.) :: (Unbox a, Num a) => Vector a -> Vector a -> Vector a
(.+.) = V.zipWith (+)

infixl 6 .+.
