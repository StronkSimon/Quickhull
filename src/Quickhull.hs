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
    -- Determine the corresponding line for each point
    p1 = propagateL headFlags points -- First boundary point of each segment
    p2 = propagateR headFlags points -- Second boundary point of each segment
    lineSegments = zip p1 p2         -- Line segment for each point

    -- Find the furthest point from each line segment
    distances = zipWith nonNormalizedDistance lineSegments points
    furthestDistances = segmentedScanl1 max headFlags distances

    -- Identify which point is the furthest in each segment
    isFurthest = zipWith (==) distances furthestDistances

    -- Update head flags to include the furthest point
    updatedHeadFlags = zipWith (||) headFlags isFurthest

    -- Get the furthest point for each segment
    furthestPoint = propagateL isFurthest points

    -- Create new lines using the furthest point for partitioning
    leftLines = zip p1 furthestPoint
    rightLines = zip furthestPoint p2

    -- Classify points relative to the new line segments
    leftSegment = zipWith pointIsLeftOfLine leftLines points
    rightSegment = zipWith pointIsRightOfLine rightLines points

    -- Define a destination function for permute
    destination :: Exp DIM1 -> Exp (Maybe DIM1)
    destination ix =
      let
        headFlag = updatedHeadFlags ! ix
        isLeft   = leftSegment ! ix
        isRight  = rightSegment ! ix
      in
        cond headFlag (Just_ ix) $
        cond isLeft (Just_ ix) $
        cond isRight (Just_ ix) $
        Nothing_

    -- Create new points array using permute
    newPoints = permute const points destination points

  in
    T2 updatedHeadFlags newPoints

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

