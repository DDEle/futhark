-- ==
-- input {
--   [ [ [ [1,2,3], [4,5,6] ]
--     , [ [6,7,8], [9,10,11] ]
--     ]
--   , [ [ [3,2,1], [4,5,6] ]
--     , [ [8,7,6], [11,10,9] ]
--     ]
--   ]
--   [ [ [ [4,5,6]  , [1,2,3] ]
--     , [ [9,10,11], [6,7,8] ]
--     ]
--   , [ [ [4,5,6]  , [3,2,1] ]
--     , [ [11,10,9], [8,7,6] ]
--     ]
--   ]
-- }
-- output {
--   [[[[5, 7, 9],
--      [5, 7, 9]],
--     [[15, 17, 19],
--      [15, 17, 19]]],
--    [[[7, 7, 7],
--      [7, 7, 7]],
--     [[19, 17, 15],
--      [19, 17, 15]]]]
-- }
def add1 [n] (xs: [n]i32, ys: [n]i32): [n]i32 =
  map2 (+) xs ys

def add2 [n][m] (xs: [n][m]i32, ys: [n][m]i32): [n][m]i32 =
  map  add1 (zip  xs ys)

def add3 [n][m][l] (xs: [n][m][l]i32, ys: [n][m][l]i32): [n][m][l]i32 =
  map  add2 (zip  xs ys)

def add4 (xs: [][][][]i32, ys: [][][][]i32): [][][][]i32 =
  map  add3 (zip  xs ys)

def main (a: [][][][]i32) (b: [][][][]i32): [][][][]i32 =
  add4(a,b)