import Aegis.MinCostConnectPoints.Code.Funs

/-!
# Specifications of `Aegis.MinCostConnectPoints.min_cost_connect_points`

LeetCode problem `min-cost-to-connect-all-points`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCostConnectPoints

open Aegis.MinCostConnectPoints (min_cost_connect_points)

def size (points : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  points.val.length

def coord (points : Slice (alloc.vec.Vec Std.I64)) (i k : Nat) : Int :=
  match points.val[i]? with
  | none => 0
  | some v =>
    match v.val[k]? with
    | none => 0
    | some z => z.val

def xCoord (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  coord points i 0

def yCoord (points : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  coord points i 1

def manh (points : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  |xCoord points i - xCoord points j| + |yCoord points i - yCoord points j|

def listMax : List Int → Int
  | [] => 0
  | a :: l => l.foldl max a

def listMin : List Int → Int
  | [] => 0
  | a :: l => l.foldl min a

def coordList (points : Slice (alloc.vec.Vec Std.I64)) (n k : Nat) : List Int :=
  (List.range n).map (fun i => coord points i k)

def maxCoord (points : Slice (alloc.vec.Vec Std.I64)) (n k : Nat) : Int :=
  listMax (coordList points n k)

def minCoord (points : Slice (alloc.vec.Vec Std.I64)) (n k : Nat) : Int :=
  listMin (coordList points n k)

def maxXValue (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  maxCoord points (size points) 0

def minXValue (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  minCoord points (size points) 0

def maxYValue (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  maxCoord points (size points) 1

def minYValue (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  minCoord points (size points) 1

def spanX (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  maxXValue points - minXValue points

def spanY (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  maxYValue points - minYValue points

def pairDistList (points : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : List Int :=
  (List.range n).flatMap (fun i =>
    ((List.range n).filter (fun j => decide (i < j))).map (fun j => manh points i j))

def maxPairDist (points : Slice (alloc.vec.Vec Std.I64)) : Int :=
  listMax (pairDistList points (size points))

def Adj {n : Nat} (T : Finset (Fin n × Fin n)) (i j : Fin n) : Prop :=
  (i, j) ∈ T ∨ (j, i) ∈ T

def IsSpanningTree (n : Nat) (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ T, e.1 < e.2) ∧ T.card = n - 1 ∧
    (∀ i j : Fin n, Relation.ReflTransGen (Adj T) i j)

def treeCost {n : Nat} (points : Slice (alloc.vec.Vec Std.I64))
    (T : Finset (Fin n × Fin n)) : Int :=
  T.sum (fun e => manh points e.1.val e.2.val)

/-- Let x_i = points[i][0] and y_i = points[i][1]. The function returns a result r, and r is the minimum, over all spanning trees T of the complete graph on vertex set {0,...,n-1}, of sum_{ {i,j} in T } (|x_i - x_j| + |y_i - y_j|). Here a spanning tree is a set of unordered pairs {i,j} with 0 <= i < j < n such that the graph on {0,...,n-1} with edge set T is connected and has exactly n-1 edges; for n=1 the only spanning tree is the empty set with cost 0.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_1 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      (∀ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T → r.val ≤ treeCost points T) ∧
      (∃ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T ∧ treeCost points T = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      (∀ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T → r.val ≤ treeCost points T) ∧
      (∃ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T ∧ treeCost points T = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_2 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r) := by
  sorry

/-- Let span_x = max_{0 <= i < n} points[i][0] - min_{0 <= i < n} points[i][0] and span_y = max_{0 <= i < n} points[i][1] - min_{0 <= i < n} points[i][1]. The returned value r satisfies r >= span_x + span_y.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_3 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      spanX points + spanY points ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      spanX points + spanY points ≤ r.val) := by
  sorry

/-- The returned value r satisfies r <= (len(points) - 1) * 4000000.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_4 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      r.val ≤ ((size points : Int) - 1) * 4000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      r.val ≤ ((size points : Int) - 1) * 4000000) := by
  sorry

/-- Let d(0,i) = |points[0][0] - points[i][0]| + |points[0][1] - points[i][1]|. The returned value r satisfies r <= sum_{i=1}^{len(points)-1} d(0,i), where the sum is 0 when len(points)=1.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_5 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      r.val ≤ (Finset.range (size points - 1)).sum (fun i => manh points 0 (i + 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      r.val ≤ (Finset.range (size points - 1)).sum (fun i => manh points 0 (i + 1))) := by
  sorry

/-- The returned value r satisfies r >= len(points) - 1.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_6 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      (size points : Int) - 1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      (size points : Int) - 1 ≤ r.val) := by
  sorry

/-- The function returns r = 0.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). Also n = 1. -/
theorem spec_7 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hn : size points = 1) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hn : size points = 1), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = |points[0][0] - points[1][0]| + |points[0][1] - points[1][1]|.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). Also n = 2. -/
theorem spec_8 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hn : size points = 2) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = manh points 0 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hn : size points = 2), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = manh points 0 1) := by
  sorry

/-- Let max_y = max_{0 <= i < n} points[i][1] and min_y = min_{0 <= i < n} points[i][1]. The function returns r = max_y - min_y.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). Also there is an integer c such that points[i][0] = c for every 0 <= i < n. -/
theorem spec_9 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hcol : ∃ c : Int, ∀ i, i < size points → xCoord points i = c) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = spanY points := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hcol : ∃ c : Int, ∀ i, i < size points → xCoord points i = c), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = spanY points) := by
  sorry

/-- Let max_x = max_{0 <= i < n} points[i][0] and min_x = min_{0 <= i < n} points[i][0]. The function returns r = max_x - min_x.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). Also there is an integer c such that points[i][1] = c for every 0 <= i < n. -/
theorem spec_10 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hrow : ∃ c : Int, ∀ i, i < size points → yCoord points i = c) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = spanX points := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hrow : ∃ c : Int, ∀ i, i < size points → yCoord points i = c), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = spanX points) := by
  sorry

/-- Let x_i = points[i][0] and y_i = points[i][1]. For every spanning tree T of the complete graph on {0,...,n-1} (a set of n-1 unordered index pairs {i,j} that connects all vertices), the returned value r satisfies r <= sum_{ {i,j} in T } (|x_i - x_j| + |y_i - y_j|).
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_11 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∀ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T → r.val ≤ treeCost points T := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∀ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T → r.val ≤ treeCost points T) := by
  sorry

/-- Let x_i = points[i][0] and y_i = points[i][1]. There exists a spanning tree T of the complete graph on {0,...,n-1} (a set of n-1 unordered index pairs {i,j} that connects all vertices) such that the returned value r equals sum_{ {i,j} in T } (|x_i - x_j| + |y_i - y_j|).
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_12 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∃ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T ∧ r.val = treeCost points T := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∃ T : Finset (Fin (size points) × Fin (size points)),
        IsSpanningTree (size points) T ∧ r.val = treeCost points T) := by
  sorry

/-- For any bijection π of {0,...,n-1}, let q be the slice of length n with q[i] = points[π(i)] for 0 <= i < n. Then the value returned by min_cost_connect_points(q) equals the value returned by min_cost_connect_points(points).
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_13 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (π : Equiv.Perm (Fin (size points)))
    (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (hi : i < size points),
      xCoord q i = xCoord points (π ⟨i, hi⟩).val ∧
      yCoord q i = yCoord points (π ⟨i, hi⟩).val) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (π : Equiv.Perm (Fin (size points)))
    (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (hi : i < size points),
      xCoord q i = xCoord points (π ⟨i, hi⟩).val ∧
      yCoord q i = yCoord points (π ⟨i, hi⟩).val), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r) := by
  sorry

/-- For any integers a and b such that every translated point (points[i][0] + a, points[i][1] + b) still lies in [-1000000, 1000000]^2, let q be the slice with q[i] = [points[i][0] + a, points[i][1] + b]. Then the value returned by min_cost_connect_points(q) equals the value returned by min_cost_connect_points(points).
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_14 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (a b : Int) (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (_hi : i < size points),
      xCoord q i = xCoord points i + a ∧ yCoord q i = yCoord points i + b)
    (hqbound : ∀ i, i < size points →
      -1000000 ≤ xCoord q i ∧ xCoord q i ≤ 1000000 ∧
      -1000000 ≤ yCoord q i ∧ yCoord q i ≤ 1000000) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (a b : Int) (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (_hi : i < size points),
      xCoord q i = xCoord points i + a ∧ yCoord q i = yCoord points i + b)
    (hqbound : ∀ i, i < size points →
      -1000000 ≤ xCoord q i ∧ xCoord q i ≤ 1000000 ∧
      -1000000 ≤ yCoord q i ∧ yCoord q i ≤ 1000000), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r) := by
  sorry

/-- Let q be the slice of length n with q[i] = [points[i][1], points[i][0]] for 0 <= i < n. Then the value returned by min_cost_connect_points(q) equals the value returned by min_cost_connect_points(points).
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_15 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (_hi : i < size points),
      xCoord q i = yCoord points i ∧ yCoord q i = xCoord points i) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (q : Slice (alloc.vec.Vec Std.I64)) (hqsize : size q = size points)
    (hq : ∀ (i : Nat) (_hi : i < size points),
      xCoord q i = yCoord points i ∧ yCoord q i = xCoord points i), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ min_cost_connect_points q = ok r) := by
  sorry

/-- Let D = max_{0 <= i < j < n} (|points[i][0] - points[j][0]| + |points[i][1] - points[j][1]|), with D = 0 when n = 1. The function returns r = D.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). Also all points lie on a common straight line, i.e. there exist real numbers a, b, c with (a,b) != (0,0) and a*points[i][0] + b*points[i][1] = c for every 0 <= i < n. -/
theorem spec_16 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hline : ∃ (a b c : ℚ), (a, b) ≠ (0, 0) ∧
      ∀ i, i < size points → a * (xCoord points i : ℚ) + b * (yCoord points i : ℚ) = c) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = maxPairDist points := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j))
    (hline : ∃ (a b c : ℚ), (a, b) ≠ (0, 0) ∧
      ∀ i, i < size points → a * (xCoord points i : ℚ) + b * (yCoord points i : ℚ) = c), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧ r.val = maxPairDist points) := by
  sorry

/-- Let W be the multiset of all values |points[i][0] - points[j][0]| + |points[i][1] - points[j][1]| for 0 <= i < j < n. Let L be the sum of the n-1 smallest elements of W, with L = 0 when n = 1. The returned value r satisfies r >= L.
  Preconditions: Let n = len(points). Assume 1 <= n <= 1000; for every i with 0 <= i < n, len(points[i]) = 2, -1000000 <= points[i][0] <= 1000000, and -1000000 <= points[i][1] <= 1000000; and for all 0 <= i < j < n, (points[i][0], points[i][1]) != (points[j][0], points[j][1]). -/
theorem spec_17 (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)) :
    ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∀ L : List Int, L.Perm (pairDistList points (size points)) →
        L.Pairwise (· ≤ ·) → (L.take (size points - 1)).sum ≤ r.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (points : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ size points) (hn2 : size points ≤ 1000)
    (hlen : ∀ v ∈ points.val, v.val.length = 2)
    (hx : ∀ i, i < size points → -1000000 ≤ xCoord points i ∧ xCoord points i ≤ 1000000)
    (hy : ∀ i, i < size points → -1000000 ≤ yCoord points i ∧ yCoord points i ≤ 1000000)
    (hne : ∀ i j, i < j → j < size points →
      (xCoord points i, yCoord points i) ≠ (xCoord points j, yCoord points j)), ∃ r : Std.I64, min_cost_connect_points points = ok r ∧
      ∀ L : List Int, L.Perm (pairDistList points (size points)) →
        L.Pairwise (· ≤ ·) → (L.take (size points - 1)).sum ≤ r.val) := by
  sorry

end AegisSpec.MinCostConnectPoints
