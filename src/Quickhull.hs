{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeOperators     #-}

module Quickhull (

  Point, Line, SegmentedPoints,
  quickhull,

  -- Exported for display
  initialPartition,
  partition,

  -- Exported just for testing
  propagateL, shiftHeadFlagsL, segmentedScanl1,
  propagateR, shiftHeadFlagsR, segmentedScanr1,

) where

import Data.Array.Accelerate
import Data.Array.Accelerate.Debug.Trace
import qualified Prelude                      as P


-- Points and lines in two-dimensional space
--
type Point = (Int, Int)
type Line  = (Point, Point)

-- This algorithm will use a head-flags array to distinguish the different
-- sections of the hull (the two arrays are always the same length).
--
-- A flag value of 'True' indicates that the corresponding point is
-- definitely on the convex hull. The points after the 'True' flag until
-- the next 'True' flag correspond to the points in the same segment, and
-- where the algorithm has not yet decided whether or not those points are
-- on the convex hull.
--
type SegmentedPoints = (Vector Bool, Vector Point)


-- Core implementation
-- -------------------

-- Initialise the algorithm by first partitioning the array into two
-- segments. Locate the left-most (p₁) and right-most (p₂) points. The
-- segment descriptor then consists of the point p₁, followed by all the
-- points above the line (p₁,p₂), followed by the point p₂, and finally all
-- of the points below the line (p₁,p₂).
--
-- To make the rest of the algorithm a bit easier, the point p₁ is again
-- placed at the end of the array.
--
-- We indicate some intermediate values that you might find beneficial to
-- compute.
--
initialPartition :: Acc (Vector Point) -> Acc SegmentedPoints
initialPartition points =
  let
      -- Locate the leftmost and rightmost points (p1 and p2)
      p1, p2 :: Exp Point
      p1 = the $ minimum points
      p2 = the $ maximum points

      -- Determine which points are above the line (p1, p2)
      isUpper :: Acc (Vector Bool)
      isUpper = map (pointIsLeftOfLine (T2 p1 p2)) points

      -- Determine which points are below the line (p1, p2)
      isLower :: Acc (Vector Bool)
      isLower = map (pointIsRightOfLine (T2 p1 p2)) points

      -- Number of points above and their relative indices
      offsetUpper :: Acc (Vector Int)
      countUpper  :: Acc (Scalar Int)
      T2 offsetUpper countUpper = scanl' (+) 0 (map boolToInt isUpper)

      -- Number of points below and their relative indices
      offsetLower :: Acc (Vector Int)
      countLower  :: Acc (Scalar Int)
      T2 offsetLower countLower = scanl' (+) 0 (map boolToInt isLower)

      -- Compute the index in the result array for each point
      destination :: Acc (Vector (Maybe DIM1))
      destination = zipWith5 computeIndex points isUpper isLower offsetUpper offsetLower
        where
          computeIndex :: Exp Point -> Exp Bool -> Exp Bool -> Exp Int -> Exp Int -> Exp (Maybe DIM1)
          computeIndex point isUp isLow offsetUp offsetLow =
            let upIndex   = Just_ $ I1 $ 1 + offsetUp
                lowIndex  = Just_ $ I1 $ 2 + the countUpper + offsetLow
                point1Idx = Just_ $ I1 0
                point2Idx = Just_ $ I1 $ 1 + the countUpper
            in cond isUp upIndex $
               cond isLow lowIndex $
               cond (point == p1) point1Idx $
               cond (point == p2) point2Idx $
               Nothing_

      -- Create the new points array
      newPoints :: Acc (Vector Point)
      newPoints = permute const result (destination !) points
        where
          result = generate (I1 arrsize) (const p1)
          arrsize = the countUpper + the countLower + 3

      -- Add p1 at the beginning and end of the array, and p2 after points above
      headFlags :: Acc (Vector Bool)
      headFlags = map (\x -> x == p1 || x == p2) newPoints 
  in T2 headFlags newPoints


-- The core of the algorithm processes all line segments at once in
-- data-parallel. This is similar to the previous partitioning step, except
-- now we are processing many segments at once.
--
-- For each line segment (p₁,p₂) locate the point furthest from that line
-- p₃. This point is on the convex hull. Then determine whether each point
-- p in that segment lies to the left of (p₁,p₃) or the right of (p₂,p₃).
-- These points are undecided.
--
partition :: Acc SegmentedPoints -> Acc SegmentedPoints
partition (T2 headFlags points) =
  let
    -- Propagate points left and right based on head flags
    p1 = propagateL headFlags points
    p2 = propagateR headFlags points

    -- Pair the propagated points to form lines
    line = zip p1 p2

    -- Shift head flags to the left and right
    headFlagsLeft = shiftHeadFlagsL headFlags
    headFlagsRight = shiftHeadFlagsR headFlags

    -- Calculate distances of points from their respective lines
    zippedPoints = zipWith (\line point -> T2 (nonNormalizedDistance line point) point) line points

    -- Get the furthest points within each segment
    getFurthestPoints = map snd $ segmentedScanl1 P.max headFlagsRight zippedPoints

    -- Propagate furthest points to the right
    p3 = propagateR headFlagsLeft getFurthestPoints

    -- Determine points to the left and right of their respective lines
    isLeft = zipWith3 (\(T2 p1 p2) point p3 -> pointIsLeftOfLine (T2 p1 p3) point) line points p3
    isRight = zipWith3 (\(T2 p1 p2) point p3 -> pointIsRightOfLine (T2 p2 p3) point) line points p3

    -- Calculate segment indices for points on the left
    segmentLeftIndex = segmentedScanl1 (+) headFlags (map boolToInt isLeft)

    -- Propagate the number of left points to each segment
    countLeft = propagateR headFlagsLeft segmentLeftIndex

    -- Calculate segment indices for points on the right
    segmentRightIndex = segmentedScanl1 (+) headFlags (map boolToInt isRight)

    -- Calculate the total size of each segment
    segmentTotalSize = zipWith4 
      (\leftIndex rightIndex headFlag headFlagLeft -> headFlag ? (1, headFlagLeft ? (leftIndex + rightIndex + 1, 0))) 
      segmentLeftIndex segmentRightIndex headFlags headFlagsLeft

    -- Compute segment offsets and the total size of all segments
    T2 segmentOffset size = scanl' (+) 0 segmentTotalSize

    -- Determine the destination indices for each point
    destination = zipWith9 
      (\point p3 offsetLeft offsetRight offset flag left right countLeft -> 
        flag ? (Just_ (I1 offset), 
        (point == p3) ? (Just_ (I1 (offset + countLeft)), 
        left ? (Just_ (I1 (offset + offsetLeft - 1)), 
        right ? (Just_ (I1 (offset + offsetRight + countLeft)), 
        Nothing_))))) 
      points p3 segmentLeftIndex segmentRightIndex segmentOffset headFlags isLeft isRight countLeft

    -- Create a default array of points initialized to (0, 0)
    defaultArray = generate (I1 (the size)) (P.const (T2 0 0))

    -- Create a default boolean array initialized to False
    falseList = generate (I1 (length defaultArray)) (P.const False_)

    -- Permute points into their new destinations, filling gaps with default values
    newPoints = permute P.const defaultArray (destination !) points

    -- Update head flags based on the new positions of points
    newHeadFlags = zipWith3 
      (\headFlag p3 newPoint -> headFlag ? (True_, (newPoint == p3) ? (True_, False_)))
      (permute P.const falseList (destination !) headFlags) 
      (permute P.const defaultArray (destination !) p3)
      newPoints
  in
  -- Return the updated head flags and points as the result
  T2 newHeadFlags newPoints

-- The completed algorithm repeatedly partitions the points until there are
-- no undecided points remaining. What remains is the convex hull.
--
quickhull :: Acc (Vector Point) -> Acc (Vector Point)
quickhull =
  error "TODO: quickhull"


-- Helper functions
-- ----------------

propagateL :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateL = segmentedScanl1 const

propagateR :: Elt a => Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
propagateR = segmentedScanr1 (\_ v -> v)

shiftHeadFlagsL :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsL = stencil becomeRightNeighbour padWithTrue_
  where
    -- Assign the value of the right neighbor to the current position.
    becomeRightNeighbour :: Stencil3 Bool -> Exp Bool
    becomeRightNeighbour (_, _, r) = r

    -- Pad boundaries with 'True' to ensure consistent behavior at the edges.
    padWithTrue_ :: Boundary (Array DIM1 Bool)
    padWithTrue_ = function $ const True_

shiftHeadFlagsR :: Acc (Vector Bool) -> Acc (Vector Bool)
shiftHeadFlagsR = stencil becomeLeftNeighbour padWithTrue_
  where
    -- Assign the value of the left neighbor to the current position.
    becomeLeftNeighbour :: Stencil3 Bool -> Exp Bool
    becomeLeftNeighbour (l, _, _) = l

    -- Pad boundaries with 'True' to ensure consistent behavior at the edges.
    padWithTrue_ :: Boundary (Array DIM1 Bool)
    padWithTrue_ = function $ const True_

segmentedScanl1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanl1 f flags values =
  let
    -- Combine flags and values into a single array of tuples
    combined = zip flags values

    -- Use scanl1 with the segmented helper function
    scanned = scanl1
      (\(T2 f1 v1) (T2 f2 v2) ->
        T2 (f1 || f2) (f2 ? (v2, f v1 v2))
      ) combined
  in
    -- Extract only the values from the scanned result
    map snd scanned

segmentedScanr1 :: Elt a => (Exp a -> Exp a -> Exp a) -> Acc (Vector Bool) -> Acc (Vector a) -> Acc (Vector a)
segmentedScanr1 f flags values =
  let
    -- Combine flags and values into a single array of tuples
    combined = zip flags values

    -- Use scanr1 with the segmented helper function
    scanned = scanr1
      (\(T2 f1 v1) (T2 f2 v2) ->
        T2 (f1 || f2) (f1 ? (v1, f v1 v2))
      ) combined
  in
    -- Extract only the values from the scanned result
    map snd scanned


-- Given utility functions
-- -----------------------

pointIsLeftOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsLeftOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y > c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

pointIsRightOfLine :: Exp Line -> Exp Point -> Exp Bool
pointIsRightOfLine (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y < c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1
    
nonNormalizedDistance :: Exp Line -> Exp Point -> Exp Int
nonNormalizedDistance (T2 (T2 x1 y1) (T2 x2 y2)) (T2 x y) = nx * x + ny * y - c
  where
    nx = y1 - y2
    ny = x2 - x1
    c  = nx * x1 + ny * y1

segmented :: Elt a => (Exp a -> Exp a -> Exp a) -> Exp (Bool, a) -> Exp (Bool, a) -> Exp (Bool, a)
segmented f (T2 aF aV) (T2 bF bV) = T2 (aF || bF) (bF ? (bV, f aV bV))

