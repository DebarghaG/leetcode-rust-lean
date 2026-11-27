import Aegis.MinimumEffortPath.Code.Funs

/-!
# Specifications of `Aegis.MinimumEffortPath.minimum_effort_path`

LeetCode problem `path-with-minimum-effort`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumEffortPath

def gridRows (heights : Slice (alloc.vec.Vec Std.I64)) : Nat := heights.val.length

def gridRow (heights : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
  ((heights.val[i]?).map (fun v => v.val)).getD []

def gridRowLen (heights : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  (gridRow heights i).length

def gridEntry (heights : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Std.I64 :=
  (gridRow heights i)[j]?.getD 0#i64

def gridCell (heights : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (gridEntry heights i j).val

def ValidGrid (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat) : Prop :=
  1 ≤ gridRows heights ∧ gridRows heights ≤ 100 ∧ 1 ≤ C ∧ C ≤ 100 ∧
  (∀ i, i < gridRows heights → gridRowLen heights i = C) ∧
  (∀ i j, i < gridRows heights → j < C →
    1 ≤ gridCell heights i j ∧ gridCell heights i j ≤ 1000000)

def orthoAdj (p q : Nat × Nat) : Prop :=
  ((p.1 : Int) - (q.1 : Int)).natAbs + ((p.2 : Int) - (q.2 : Int)).natAbs = 1

instance (p q : Nat × Nat) : Decidable (orthoAdj p q) := by
  unfold orthoAdj
  infer_instance

def adjChain : List (Nat × Nat) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => orthoAdj p q ∧ adjChain (q :: rest)

def IsRoute (R C : Nat) (P : List (Nat × Nat)) : Prop :=
  P.head? = some (0, 0) ∧
  P.getLast? = some (R - 1, C - 1) ∧
  (∀ p ∈ P, p.1 < R ∧ p.2 < C) ∧
  adjChain P

def stepDiff (heights : Slice (alloc.vec.Vec Std.I64)) (p q : Nat × Nat) : Int :=
  |gridCell heights p.1 p.2 - gridCell heights q.1 q.2|

def routeEffort (heights : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) → Int
  | [] => 0
  | [_] => 0
  | p :: q :: rest => max (stepDiff heights p q) (routeEffort heights (q :: rest))

def allCells (R C : Nat) : List (Nat × Nat) :=
  (List.range R).flatMap (fun i => (List.range C).map (fun j => (i, j)))

def adjDiffs (heights : Slice (alloc.vec.Vec Std.I64)) (R C : Nat) : List Int :=
  (allCells R C).flatMap (fun p =>
    (allCells R C).filterMap (fun q =>
      if orthoAdj p q then some (stepDiff heights p q) else none))

def maxAdjDiff (heights : Slice (alloc.vec.Vec Std.I64)) (R C : Nat) : Int :=
  (adjDiffs heights R C).foldr max 0

def rowMaxDiff (heights : Slice (alloc.vec.Vec Std.I64)) (row C : Nat) : Int :=
  ((List.range (C - 1)).map (fun j => stepDiff heights (row, j) (row, j + 1))).foldr max 0

def IsCutEdge (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (S : Nat × Nat → Prop) (p q : Nat × Nat) : Prop :=
  p.1 < gridRows heights ∧ p.2 < C ∧ q.1 < gridRows heights ∧ q.2 < C ∧
    S p ∧ ¬ S q ∧ orthoAdj p q

theorem gridRows_le_usize_max (heights : Slice (alloc.vec.Vec Std.I64)) :
    gridRows heights ≤ Usize.max := by
  have h : heights.val.length = heights.leng := by
    simpa [Slice.val] using Aeneas.Data.ListN.ListN_length heights.list
  rw [gridRows, h]
  exact heights.bound

def mkSlice {α : Type} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def transposeGrid (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat) :
    Slice (alloc.vec.Vec Std.I64) :=
  if hC : C ≤ Usize.max then
    mkSlice ((List.range C).map (fun i =>
        ⟨mkSlice ((List.range (gridRows heights)).map (fun j => gridEntry heights j i))
          (by simpa using gridRows_le_usize_max heights)⟩))
      (by simpa using hC)
  else heights

def flipGrid (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat) :
    Slice (alloc.vec.Vec Std.I64) :=
  if hC : C ≤ Usize.max then
    mkSlice ((List.range (gridRows heights)).map (fun i =>
        ⟨mkSlice
          ((List.range C).map (fun j =>
            gridEntry heights (gridRows heights - 1 - i) (C - 1 - j)))
          (by simpa using hC)⟩))
      (by simpa using gridRows_le_usize_max heights)
  else heights

/-- The function returns a result r. A route is a finite sequence of cells (a_0,b_0),...,(a_k,b_k) such that 0 <= a_t < R and 0 <= b_t < C for all t, (a_0,b_0) = (0,0), (a_k,b_k) = (R-1,C-1), and for every t with 0 <= t < k, |a_{t+1}-a_t| + |b_{t+1}-b_t| = 1. The effort of such a route is 0 if k = 0, and otherwise is the maximum of |heights[a_t][b_t] - heights[a_{t+1}][b_{t+1}]| over all t with 0 <= t < k. Then r is the minimum effort among all such routes.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_1 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∃ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r ∧
      (∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = r.val) ∧
      (∀ P, IsRoute (gridRows heights) C P → r.val ≤ routeEffort heights P) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∃ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r ∧
      (∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = r.val) ∧
      (∀ P, IsRoute (gridRows heights) C P → r.val ≤ routeEffort heights P)) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, or access an invalid index) for every input satisfying the preconditions.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_2 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∃ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∃ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_3 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, let M = 0 if R*C = 1; otherwise let M be the maximum of |heights[i][j] - heights[i'][j']| over all pairs of cells (i,j),(i',j') with 0 <= i,i' < R, 0 <= j,j' < C, and |i-i'| + |j-j'| = 1. Then r <= M.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_4 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val ≤ maxAdjDiff heights (gridRows heights) C := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val ≤ maxAdjDiff heights (gridRows heights) C) := by
  sorry

/-- Whenever the function returns a result r, for every route P (a finite sequence of orthogonally adjacent cells from (0,0) to (R-1,C-1)), the effort of P is at least r, where the effort is the maximum absolute height difference between consecutive cells of P and is 0 for a one-cell route.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_5 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ P, IsRoute (gridRows heights) C P → r.val ≤ routeEffort heights P := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ P, IsRoute (gridRows heights) C P → r.val ≤ routeEffort heights P) := by
  sorry

/-- Whenever the function returns a result r, there exists a route P (a finite sequence of orthogonally adjacent cells from (0,0) to (R-1,C-1)) whose effort is exactly r, where the effort is the maximum absolute height difference between consecutive cells of P and is 0 for a one-cell route.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_6 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a finite sequence of orthogonally adjacent cells from (0,0) to (R-1,C-1) such that every two consecutive cells of the sequence have equal heights.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_7 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      (r.val = 0 ↔ ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      (r.val = 0 ↔ ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P = 0)) := by
  sorry

/-- Whenever the function returns a result r, for every integer t with 0 <= t <= 1000000, r <= t if and only if there exists a route from (0,0) to (R-1,C-1) whose effort is at most t, where the effort is the maximum absolute height difference between consecutive cells of the route and is 0 for a one-cell route.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_8 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ t : Int, 0 ≤ t → t ≤ 1000000 →
        (r.val ≤ t ↔ ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P ≤ t) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ t : Int, 0 ≤ t → t ≤ 1000000 →
        (r.val ≤ t ↔ ∃ P, IsRoute (gridRows heights) C P ∧ routeEffort heights P ≤ t)) := by
  sorry

/-- Whenever the function returns a result r, either r = 0, or there exist cells (i,j) and (i',j') with 0 <= i,i' < R, 0 <= j,j' < C, and |i-i'| + |j-j'| = 1, such that r = |heights[i][j] - heights[i'][j']|.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_9 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val = 0 ∨ ∃ p q : Nat × Nat,
        p.1 < gridRows heights ∧ p.2 < C ∧ q.1 < gridRows heights ∧ q.2 < C ∧
          orthoAdj p q ∧ r.val = stepDiff heights p q := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val = 0 ∨ ∃ p q : Nat × Nat,
        p.1 < gridRows heights ∧ p.2 < C ∧ q.1 < gridRows heights ∧ q.2 < C ∧
          orthoAdj p q ∧ r.val = stepDiff heights p q) := by
  sorry

/-- Whenever the function returns a result r, with the convention that a maximum over an empty set is 0, r = max over 0 <= j < C-1 of |heights[0][j+1] - heights[0][j]|.
  Preconditions: Let R = len(heights). There is an integer C such that R = 1, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_10 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) (hR : gridRows heights = 1) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val = rowMaxDiff heights 0 C := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) (hR : gridRows heights = 1), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      r.val = rowMaxDiff heights 0 C) := by
  sorry

/-- Let T be the C by R array defined by len(T) = C, len(T[i]) = R for 0 <= i < C, and T[i][j] = heights[j][i] for 0 <= i < C and 0 <= j < R. Whenever minimum_effort_path(heights) returns r and minimum_effort_path(T) returns r', we have r = r'.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_11 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path (transposeGrid heights C) = ok r' →
        r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path (transposeGrid heights C) = ok r' →
        r = r') := by
  sorry

/-- Let F be the R by C array defined by F[i][j] = heights[R-1-i][C-1-j] for 0 <= i < R and 0 <= j < C. Whenever minimum_effort_path(heights) returns r and minimum_effort_path(F) returns r', we have r = r'.
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_12 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path (flipGrid heights C) = ok r' →
        r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path (flipGrid heights C) = ok r' →
        r = r') := by
  sorry

/-- Whenever the function returns a result r, for every set S of cells (i,j) with 0 <= i < R and 0 <= j < C such that (0,0) is in S and (R-1,C-1) is not in S, let B be the set of all |heights[i][j] - heights[i'][j']| for which (i,j) is in S, (i',j') is not in S, and |i-i'| + |j-j'| = 1. Then B is nonempty and r >= min(B).
  Preconditions: Let R = len(heights). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, len(heights[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. -/
theorem spec_13 (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) :
    ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ (S : Nat × Nat → Prop),
        (∀ p, S p → p.1 < gridRows heights ∧ p.2 < C) →
        S (0, 0) →
        ¬ S (gridRows heights - 1, C - 1) →
        (∃ p q, IsCutEdge heights C S p q) ∧
          ∃ b : Int,
            (∃ p q, IsCutEdge heights C S p q ∧ b = stepDiff heights p q) ∧
              (∀ p q, IsCutEdge heights C S p q → b ≤ stepDiff heights p q) ∧
                b ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (heights : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C), ∀ r, Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      ∀ (S : Nat × Nat → Prop),
        (∀ p, S p → p.1 < gridRows heights ∧ p.2 < C) →
        S (0, 0) →
        ¬ S (gridRows heights - 1, C - 1) →
        (∃ p q, IsCutEdge heights C S p q) ∧
          ∃ b : Int,
            (∃ p q, IsCutEdge heights C S p q ∧ b = stepDiff heights p q) ∧
              (∀ p q, IsCutEdge heights C S p q → b ≤ stepDiff heights p q) ∧
                b ≤ r.val) := by
  sorry

/-- Whenever minimum_effort_path(heights) returns r and minimum_effort_path(heights') returns r', we have r <= r'.
  Preconditions: Let heights and heights' be two grids. Let R = len(heights) and R' = len(heights'). There is an integer C such that 1 <= R <= 100, 1 <= C <= 100, R' = R, len(heights[i]) = C and len(heights'[i]) = C for every i with 0 <= i < R, and 1 <= heights[i][j] <= 1000000 and 1 <= heights'[i][j] <= 1000000 for every i,j with 0 <= i < R and 0 <= j < C. Also, for every i,j,i',j' with 0 <= i,i' < R, 0 <= j,j' < C, and |i-i'| + |j-j'| = 1, |heights[i][j]-heights[i'][j']| <= |heights'[i][j]-heights'[i'][j']|. -/
theorem spec_14 (heights heights' : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) (h' : ValidGrid heights' C)
    (hR : gridRows heights' = gridRows heights)
    (hstep : ∀ p q : Nat × Nat,
      p.1 < gridRows heights → p.2 < C → q.1 < gridRows heights → q.2 < C →
        orthoAdj p q → stepDiff heights p q ≤ stepDiff heights' p q) :
    ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path heights' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (heights heights' : Slice (alloc.vec.Vec Std.I64)) (C : Nat)
    (h : ValidGrid heights C) (h' : ValidGrid heights' C)
    (hR : gridRows heights' = gridRows heights)
    (hstep : ∀ p q : Nat × Nat,
      p.1 < gridRows heights → p.2 < C → q.1 < gridRows heights → q.2 < C →
        orthoAdj p q → stepDiff heights p q ≤ stepDiff heights' p q), ∀ r r', Aegis.MinimumEffortPath.minimum_effort_path heights = ok r →
      Aegis.MinimumEffortPath.minimum_effort_path heights' = ok r' → r.val ≤ r'.val) := by
  sorry

end AegisSpec.MinimumEffortPath
