import Aegis.CherryPickup.Code.Funs

/-!
# Specifications of `Aegis.CherryPickup.cherry_pickup`

LeetCode problem `cherry-pickup-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

open Aegis.CherryPickup

namespace AegisSpec.CherryPickup

def cells (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map fun row => row.val.map fun x => x.val

def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (cells grid).length

def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  (cells grid).getD i []

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  (rowAt grid i).getD j 0

def numCols (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (rowAt grid 0).length

def ValidInput (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat) : Prop :=
  R = numRows grid ∧
  C = numCols grid ∧
  2 ≤ R ∧ R ≤ 70 ∧
  2 ≤ C ∧ C ≤ 70 ∧
  (∀ i, i < R → (rowAt grid i).length = C) ∧
  (∀ i j, i < R → j < C → 0 ≤ cell grid i j ∧ cell grid i j ≤ 100)

def Admissible (R C : Nat) (s : Int) (p : Fin R → Int) : Prop :=
  (∀ i : Fin R, i.val = 0 → p i = s) ∧
  (∀ i : Fin R, 0 ≤ p i ∧ p i < (C : Int)) ∧
  (∀ (i : Nat) (h : i + 1 < R), |p ⟨i + 1, h⟩ - p ⟨i, Nat.lt_of_succ_lt h⟩| ≤ 1)

def V (grid : Slice (alloc.vec.Vec Std.I64)) (R : Nat) (p q : Fin R → Int) : Int :=
  ∑ i : Fin R,
    (if p i = q i then cell grid i.val (p i).toNat
     else cell grid i.val (p i).toNat + cell grid i.val (q i).toNat)

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def eraseOne (a : Int) : List Int → List Int
  | [] => []
  | x :: xs => if x = a then xs else x :: eraseOne a xs

def secondMax (l : List Int) : Int :=
  listMax (eraseOne (listMax l) l)

def twoRowValue (grid : Slice (alloc.vec.Vec Std.I64)) (C x y : Nat) : Int :=
  cell grid 0 0 + cell grid 0 (C - 1) +
    (if x = y then cell grid 1 x else cell grid 1 x + cell grid 1 y)

/-- Whenever cherry_pickup(grid) returns a result r, r equals the maximum of V(p,q) over all pairs (p,q) such that p is admissible from column 0 and q is admissible from column C-1. A path p is admissible from column s when p(0)=s, 0 <= p(i) < C for all 0 <= i < R, and |p(i+1)-p(i)| <= 1 for all 0 <= i < R-1. For such paths, V(p,q) = sum_{i=0}^{R-1} (if p(i)=q(i) then grid[i][p(i)] else grid[i][p(i)] + grid[i][q(i)]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    (∀ p q : Fin R → Int, Admissible R C 0 p → Admissible R C ((C : Int) - 1) q →
        V grid R p q ≤ r.val) ∧
      (∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
        V grid R p q = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), (∀ p q : Fin R → Int, Admissible R C 0 p → Admissible R C ((C : Int) - 1) q →
        V grid R p q ≤ r.val) ∧
      (∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
        V grid R p q = r.val)) := by
  sorry

/-- For every grid satisfying the preconditions, cherry_pickup(grid) returns a result; it does not fail, panic, or overflow.
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) :
    ∃ r : Std.I64, cherry_pickup grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C), ∃ r : Std.I64, cherry_pickup grid = ok r) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, 0 <= r <= sum_{i=0}^{R-1} sum_{j=0}^{C-1} grid[i][j].
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    0 ≤ r.val ∧ r.val ≤ ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range C, cell grid i j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), 0 ≤ r.val ∧ r.val ≤ ∑ i ∈ Finset.range R, ∑ j ∈ Finset.range C, cell grid i j) := by
  sorry

/-- For each row i with 1 <= i < R, let a_i be the largest entry in row i and b_i the second largest entry in row i, counting multiplicity, so b_i <= a_i and both are entries of row i. Whenever cherry_pickup(grid) returns r, r <= grid[0][0] + grid[0][C-1] + sum_{i=1}^{R-1} (a_i + b_i).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    r.val ≤ cell grid 0 0 + cell grid 0 (C - 1) +
      ∑ i ∈ Finset.Icc 1 (R - 1), (listMax (rowAt grid i) + secondMax (rowAt grid i)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), r.val ≤ cell grid 0 0 + cell grid 0 (C - 1) +
      ∑ i ∈ Finset.Icc 1 (R - 1), (listMax (rowAt grid i) + secondMax (rowAt grid i))) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, r >= sum_{i=0}^{R-1} (grid[i][0] + grid[i][C-1]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    (∑ i ∈ Finset.range R, (cell grid i 0 + cell grid i (C - 1))) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), (∑ i ∈ Finset.range R, (cell grid i 0 + cell grid i (C - 1))) ≤ r.val) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, r = 2 * R * v.
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. In addition, there exists an integer v with 0 <= v <= 100 such that grid[i][j] = v for every i,j. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (v : Int)
    (hv0 : 0 ≤ v) (hv100 : v ≤ 100)
    (hv : ∀ i j, i < R → j < C → cell grid i j = v)
    (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    r.val = 2 * (R : Int) * v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (v : Int)
    (hv0 : 0 ≤ v) (hv100 : v ≤ 100)
    (hv : ∀ i j, i < R → j < C → cell grid i j = v)
    (r : Std.I64) (hr : cherry_pickup grid = ok r), r.val = 2 * (R : Int) * v) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, r = sum_{i=0}^{R-1} (grid[i][0] + grid[i][1]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. In addition, C = 2. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (hC : C = 2)
    (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    r.val = ∑ i ∈ Finset.range R, (cell grid i 0 + cell grid i 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (hC : C = 2)
    (r : Std.I64) (hr : cherry_pickup grid = ok r), r.val = ∑ i ∈ Finset.range R, (cell grid i 0 + cell grid i 1)) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, r = grid[0][0] + grid[0][C-1].
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. In addition, grid[i][j] = 0 for every i with 1 <= i < R and every j with 0 <= j < C. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C)
    (hzero : ∀ i j, 1 ≤ i → i < R → j < C → cell grid i j = 0)
    (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    r.val = cell grid 0 0 + cell grid 0 (C - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C)
    (hzero : ∀ i j, 1 ≤ i → i < R → j < C → cell grid i j = 0)
    (r : Std.I64) (hr : cherry_pickup grid = ok r), r.val = cell grid 0 0 + cell grid 0 (C - 1)) := by
  sorry

/-- Let h be the grid defined by h[i][j] = grid[i][C-1-j] for 0 <= i < R and 0 <= j < C. Whenever cherry_pickup(grid) returns r and cherry_pickup(h) returns r', r = r'.
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (h' : Slice (alloc.vec.Vec Std.I64))
    (hvalid' : ValidInput h' R C)
    (hmirror : ∀ i j, i < R → j < C → cell h' i j = cell grid i (C - 1 - j))
    (r : Std.I64) (hr : cherry_pickup grid = ok r)
    (r' : Std.I64) (hr' : cherry_pickup h' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (h' : Slice (alloc.vec.Vec Std.I64))
    (hvalid' : ValidInput h' R C)
    (hmirror : ∀ i j, i < R → j < C → cell h' i j = cell grid i (C - 1 - j))
    (r : Std.I64) (hr : cherry_pickup grid = ok r)
    (r' : Std.I64) (hr' : cherry_pickup h' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever cherry_pickup(g) returns r_g and cherry_pickup(h) returns r_h, r_g <= r_h.
  Preconditions: Let R = len(g) = len(h) and C = len(g[0]) = len(h[0]). Both g and h satisfy: 2 <= R <= 70; every row has length C; 2 <= C <= 70; and all entries are between 0 and 100. In addition, g[i][j] <= h[i][j] for every 0 <= i < R and 0 <= j < C. -/
theorem spec_10 (g h' : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (hg : ValidInput g R C) (hh : ValidInput h' R C)
    (hle : ∀ i j, i < R → j < C → cell g i j ≤ cell h' i j)
    (rg : Std.I64) (hrg : cherry_pickup g = ok rg)
    (rh : Std.I64) (hrh : cherry_pickup h' = ok rh) :
    rg.val ≤ rh.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (g h' : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (hg : ValidInput g R C) (hh : ValidInput h' R C)
    (hle : ∀ i j, i < R → j < C → cell g i j ≤ cell h' i j)
    (rg : Std.I64) (hrg : cherry_pickup g = ok rg)
    (rh : Std.I64) (hrh : cherry_pickup h' = ok rh), rg.val ≤ rh.val) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, there exist functions p, q : {0,1,...,R-1} -> Z such that p(0)=0, q(0)=C-1, 0 <= p(i) < C and 0 <= q(i) < C for every 0 <= i < R, |p(i+1)-p(i)| <= 1 and |q(i+1)-q(i)| <= 1 for every 0 <= i < R-1, and r = sum_{i=0}^{R-1} (if p(i)=q(i) then grid[i][p(i)] else grid[i][p(i)] + grid[i][q(i)]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    ∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
      V grid R p q = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), ∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
      V grid R p q = r.val) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, for every pair of functions p, q : {0,1,...,R-1} -> Z satisfying p(0)=0, q(0)=C-1, 0 <= p(i) < C and 0 <= q(i) < C for every 0 <= i < R, and |p(i+1)-p(i)| <= 1 and |q(i+1)-q(i)| <= 1 for every 0 <= i < R-1, we have sum_{i=0}^{R-1} (if p(i)=q(i) then grid[i][p(i)] else grid[i][p(i)] + grid[i][q(i)]) <= r.
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    ∀ p q : Fin R → Int, Admissible R C 0 p → Admissible R C ((C : Int) - 1) q →
      V grid R p q ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), ∀ p q : Fin R → Int, Admissible R C 0 p → Admissible R C ((C : Int) - 1) q →
      V grid R p q ≤ r.val) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, r equals the maximum, over x in {0,1} and y in {C-2,C-1}, of grid[0][0] + grid[0][C-1] + (if x=y then grid[1][x] else grid[1][x] + grid[1][y]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. In addition, R = 2. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (hR : R = 2)
    (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    r.val = max (max (twoRowValue grid C 0 (C - 2)) (twoRowValue grid C 0 (C - 1)))
                (max (twoRowValue grid C 1 (C - 2)) (twoRowValue grid C 1 (C - 1))) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (hR : R = 2)
    (r : Std.I64) (hr : cherry_pickup grid = ok r), r.val = max (max (twoRowValue grid C 0 (C - 2)) (twoRowValue grid C 0 (C - 1)))
                (max (twoRowValue grid C 1 (C - 2)) (twoRowValue grid C 1 (C - 1)))) := by
  sorry

/-- Whenever cherry_pickup(grid) returns r, there exist functions p, q : {0,1,...,R-1} -> Z such that p(0)=0, q(0)=C-1, 0 <= p(i) <= q(i) < C for every 0 <= i < R, |p(i+1)-p(i)| <= 1 and |q(i+1)-q(i)| <= 1 for every 0 <= i < R-1, and r = sum_{i=0}^{R-1} (if p(i)=q(i) then grid[i][p(i)] else grid[i][p(i)] + grid[i][q(i)]).
  Preconditions: Let R = len(grid) and C = len(grid[0]). The input satisfies: 2 <= R <= 70; for every i with 0 <= i < R, len(grid[i]) = C; 2 <= C <= 70; and for every i,j with 0 <= i < R and 0 <= j < C, 0 <= grid[i][j] <= 100. -/
theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r) :
    ∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
      (∀ i : Fin R, p i ≤ q i) ∧ V grid R p q = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (R C : Nat)
    (h : ValidInput grid R C) (r : Std.I64) (hr : cherry_pickup grid = ok r), ∃ p q : Fin R → Int, Admissible R C 0 p ∧ Admissible R C ((C : Int) - 1) q ∧
      (∀ i : Fin R, p i ≤ q i) ∧ V grid R p q = r.val) := by
  sorry

end AegisSpec.CherryPickup
