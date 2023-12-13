module Futhark.Solve.SimplexTests
  ( tests,
  )
where

import Data.Vector.Unboxed qualified as V
import Futhark.Solve.LP
import Futhark.Solve.Matrix qualified as M
import Futhark.Solve.Simplex
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "SimplexTests"
    [ testCase "1" $
        let lpe =
              LPE
                { pc = V.fromList [1, 1, 0, 0, 0],
                  pA =
                    M.fromLists
                      [ [-1, 1, 1, 0, 0],
                        [1, 0, 0, 1, 0],
                        [0, 1, 0, 0, 1]
                      ],
                  pd = V.fromList [1, 3, 2]
                }
         in simplex lpe @?= Just (5 :: Double, V.fromList [3, 2, 2, 0, 0]),
      testCase "2" $
        let lp =
              LP
                { lpc = V.fromList [40, 30],
                  lpA =
                    M.fromLists
                      [ [1, 1],
                        [2, 1]
                      ],
                  lpd = V.fromList [12, 16]
                }
         in simplexLP lp @?= Just (400 :: Double, V.fromList [4, 8]),
      testCase "3" $
        let lp =
              LP
                { lpc = V.fromList [1, 2, 3],
                  lpA =
                    M.fromLists
                      [ [1, 1, 1],
                        [2, 1, 3]
                      ],
                  lpd = V.fromList [12, 18]
                }
         in simplexLP lp @?= Just (27 :: Double, V.fromList [0, 9, 3]),
      testCase "4" $
        let lp =
              LP
                { lpc = V.fromList [5.5, 2.1],
                  lpA =
                    M.fromLists
                      [ [-1, 1],
                        [8, 2]
                      ],
                  lpd = V.fromList [2, 17]
                }
         in assertBool (show $ simplexLP lp) $
              case simplexLP lp of
                Nothing -> False
                Just (z, sol) ->
                  and
                    [ z `approxEq` (14.08 :: Double),
                      and $ zipWith approxEq (V.toList sol) [1.3, 3.3]
                    ]
    ]

approxEq :: (Fractional a, Ord a) => a -> a -> Bool
approxEq x1 x2 = (abs $ x1 - x2) < 10 ^^ (-10 :: Int)
