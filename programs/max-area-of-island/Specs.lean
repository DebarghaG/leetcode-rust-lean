import Aegis.MaxAreaOfIsland.Code.Funs

/-!
# Specifications of `Aegis.MaxAreaOfIsland.max_area_of_island`

LeetCode problem `max-area-of-island`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.alloc.vec
  open Aegis.MaxAreaOfIsland

  namespace AegisSpec.MaxAreaOfIsland

  abbrev Cell := Nat × Nat

  def gridM (g : Slice (Vec I64)) : Nat := g.val.length

  def gridRow (g : Slice (Vec I64)) (i : Nat) : List I64 :=
    match g.val[i]? with
    | some row => row.val
    | none => []

  def gridN (g : Slice (Vec I64)) : Nat := (gridRow g 0).length

  def entry (g : Slice (Vec I64)) (i j : Nat) : Int :=
    ((gridRow g i).getD j (0#i64)).val

  abbrev isOne (g : Slice (Vec I64)) (i j : Nat) : Prop := entry g i j = 1

  def cellsFinset (g : Slice (Vec I64)) : Finset Cell :=
    Finset.range (gridM g) ×ˢ Finset.range (gridN g)

  def Adjacent (c1 c2 : Cell) : Prop :=
    (c1.1 = c2.1 ∧ (c1.2 + 1 = c2.2 ∨ c2.2 + 1 = c1.2)) ∨
    (c1.2 = c2.2 ∧ (c1.1 + 1 = c2.1 ∨ c2.1 + 1 = c1.1))

  def step (g : Slice (Vec I64)) (c1 c2 : Cell) : Prop :=
    isOne g c1.1 c1.2 ∧ isOne g c2.1 c2.2 ∧ Adjacent c1 c2

  def Reach (g : Slice (Vec I64)) (c c' : Cell) : Prop :=
    Relation.ReflTransGen (step g) c c'

  noncomputable def component (g : Slice (Vec I64)) (c : Cell) : Set Cell :=
    { c' : Cell | isOne g c'.1 c'.2 ∧ Reach g c c' }

  noncomputable def countOnes (g : Slice (Vec I64)) : Nat :=
    ((cellsFinset g).filter (fun (c : Cell) => isOne g c.1 c.2)).card

  noncomputable def maxArea (g : Slice (Vec I64)) : Nat :=
    ((cellsFinset g).filter (fun (c : Cell) => isOne g c.1 c.2)).sup
      (fun (c : Cell) => (component g c).ncard)

  noncomputable def rowRunMax (g : Slice (Vec I64)) : Nat :=
    (Finset.range (gridN g + 1) ×ˢ Finset.range (gridN g + 1)).sup
      (fun p =>
        if p.1 < p.2 ∧ (∀ j ∈ Finset.Ico p.1 p.2, isOne g 0 j) then p.2 - p.1 else 0)

  /-- The function returns a result r and r equals the maximum area of an island of grid, where a 1-cell is a pair (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1; two 1-cells are 4-adjacent if they differ by 1 in exactly one coordinate; an island is a maximal nonempty set of 1-cells connected by steps between 4-adjacent 1-cells; and its area is its number of cells. If grid has no 1-cell, the maximum area is defined to be 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∃ r, max_area_of_island g = ok r ∧ r.val = (maxArea g : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∃ r, max_area_of_island g = ok r ∧ r.val = (maxArea g : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail) on every input satisfying the preconditions.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∃ r, max_area_of_island g = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∃ r, max_area_of_island g = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= N, where N is the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r → r.val ≤ (countOnes g : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r → r.val ≤ (countOnes g : Int)) := by
    sorry

  /-- Whenever the function returns a result r and grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n, then r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r →
        (∀ i j, i < gridM g → j < gridN g → entry g i j = 0) → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r →
          (∀ i j, i < gridM g → j < gridN g → entry g i j = 0) → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r and r = 0, then grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r → r.val = 0 →
        ∀ i j, i < gridM g → j < gridN g → entry g i j = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r → r.val = 0 →
          ∀ i j, i < gridM g → j < gridN g → entry g i j = 0) := by
    sorry

  /-- Whenever the function returns a result r and m = 1, r equals the maximum element of the set containing 0 and all integers b - a for which 0 <= a < b <= n and grid[0][j] = 1 for every j with a <= j < b.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r → gridM g = 1 → r.val = (rowRunMax g : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r → gridM g = 1 → r.val = (rowRunMax g : Int)) := by
    sorry

  /-- Whenever the function returns a result r and exactly two cells of grid have value 1, let those two cells be (i,j) and (i',j'). If |i - i'| + |j - j'| = 1 then r = 2; otherwise r = 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r (c1 c2 : Cell), max_area_of_island g = ok r → c1 ≠ c2 →
        (∀ c : Cell, isOne g c.1 c.2 ↔ c = c1 ∨ c = c2) →
        ((Adjacent c1 c2 → r.val = 2) ∧ (¬ Adjacent c1 c2 → r.val = 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r (c1 c2 : Cell), max_area_of_island g = ok r → c1 ≠ c2 →
          (∀ c : Cell, isOne g c.1 c.2 ↔ c = c1 ∨ c = c2) →
          ((Adjacent c1 c2 → r.val = 2) ∧ (¬ Adjacent c1 c2 → r.val = 1))) := by
    sorry

  /-- Whenever the function returns a result r and r > 0, there exists a cell (i,j) with grid[i][j] = 1 such that the set of all cells (i',j') with grid[i'][j'] = 1 that are reachable from (i,j) by a finite sequence of value-1 cells, with consecutive cells differing by 1 in exactly one coordinate, has exactly r elements.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r → 0 < r.val →
        ∃ i j, isOne g i j ∧ ((component g (i, j)).ncard : Int) = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r → 0 < r.val →
          ∃ i j, isOne g i j ∧ ((component g (i, j)).ncard : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every cell (i,j) with grid[i][j] = 1, the set of all cells (i',j') with grid[i'][j'] = 1 that are reachable from (i,j) by a finite sequence of value-1 cells, with consecutive cells differing by 1 in exactly one coordinate, has at most r elements.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r →
        ∀ i j, isOne g i j → ((component g (i, j)).ncard : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r →
          ∀ i j, isOne g i j → ((component g (i, j)).ncard : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r and there exist two cells (i,j) and (i',j') with grid[i][j] = grid[i'][j'] = 1 that are not connected by a finite sequence of value-1 cells with consecutive cells differing by 1 in exactly one coordinate, then r <= N - 1, where N is the number of cells with value 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every i with 0 <= i < m, and grid[i][j] is 0 or 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (g : Slice (Vec I64))
      (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
      (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
      (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
      (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)) :
      ∀ r, max_area_of_island g = ok r →
        (∃ c1 c2 : Cell, isOne g c1.1 c1.2 ∧ isOne g c2.1 c2.2 ∧ ¬ Reach g c1 c2) →
        r.val ≤ (countOnes g : Int) - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (g : Slice (Vec I64))
        (hm1 : 1 ≤ gridM g) (hm50 : gridM g ≤ 50)
        (hn1 : 1 ≤ gridN g) (hn50 : gridN g ≤ 50)
        (hrow : ∀ i, i < gridM g → (gridRow g i).length = gridN g)
        (h01 : ∀ i j, i < gridM g → j < gridN g → (entry g i j = 0 ∨ entry g i j = 1)), ∀ r, max_area_of_island g = ok r →
          (∃ c1 c2 : Cell, isOne g c1.1 c1.2 ∧ isOne g c2.1 c2.2 ∧ ¬ Reach g c1 c2) →
          r.val ≤ (countOnes g : Int) - 1) := by
    sorry

  /-- Whenever the function applied to G returns r_G and the function applied to H returns r_H, r_G <= r_H.
    Preconditions: Let m and n be positive integers with m <= 50 and n <= 50. Let G and H be two inputs such that len(G) = len(H) = m, len(G[i]) = len(H[i]) = n for every 0 <= i < m, every entry of G and H is 0 or 1, and G[i][j] <= H[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (G H : Slice (Vec I64)) (m n : Nat)
      (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
      (hGm : gridM G = m) (hHm : gridM H = m)
      (hGrow : ∀ i, i < m → (gridRow G i).length = n)
      (hHrow : ∀ i, i < m → (gridRow H i).length = n)
      (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
      (hH01 : ∀ i j, i < m → j < n → (entry H i j = 0 ∨ entry H i j = 1))
      (hle : ∀ i j, i < m → j < n → entry G i j ≤ entry H i j) :
      ∀ rG rH, max_area_of_island G = ok rG → max_area_of_island H = ok rH →
        rG.val ≤ rH.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (G H : Slice (Vec I64)) (m n : Nat)
        (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
        (hGm : gridM G = m) (hHm : gridM H = m)
        (hGrow : ∀ i, i < m → (gridRow G i).length = n)
        (hHrow : ∀ i, i < m → (gridRow H i).length = n)
        (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
        (hH01 : ∀ i j, i < m → j < n → (entry H i j = 0 ∨ entry H i j = 1))
        (hle : ∀ i j, i < m → j < n → entry G i j ≤ entry H i j), ∀ rG rH, max_area_of_island G = ok rG → max_area_of_island H = ok rH →
          rG.val ≤ rH.val) := by
    sorry

  /-- Whenever the function applied to G returns r and the function applied to T returns r_T, r = r_T.
    Preconditions: Let m and n be positive integers with m <= 50 and n <= 50. Let G be an input such that len(G) = m, len(G[i]) = n for every 0 <= i < m, and every entry of G is 0 or 1. Define T by len(T) = n, len(T[j]) = m for every 0 <= j < n, and T[j][i] = G[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_13 (G T : Slice (Vec I64)) (m n : Nat)
      (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
      (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
      (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
      (hTn : gridM T = n) (hTrow : ∀ j, j < n → (gridRow T j).length = m)
      (hT : ∀ i j, i < m → j < n → entry T j i = entry G i j) :
      ∀ r rT, max_area_of_island G = ok r → max_area_of_island T = ok rT →
        r.val = rT.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (G T : Slice (Vec I64)) (m n : Nat)
        (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
        (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
        (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
        (hTn : gridM T = n) (hTrow : ∀ j, j < n → (gridRow T j).length = m)
        (hT : ∀ i j, i < m → j < n → entry T j i = entry G i j), ∀ r rT, max_area_of_island G = ok r → max_area_of_island T = ok rT →
          r.val = rT.val) := by
    sorry

  /-- Whenever the function applied to G returns r and the function applied to R returns r_R, r = r_R.
    Preconditions: Let m and n be positive integers with m <= 50 and n <= 50. Let G be an input such that len(G) = m, len(G[i]) = n for every 0 <= i < m, and every entry of G is 0 or 1. Define R by len(R) = m, len(R[i]) = n for every 0 <= i < m, and R[i][j] = G[i][n-1-j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_14 (G R : Slice (Vec I64)) (m n : Nat)
      (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
      (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
      (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
      (hRm : gridM R = m) (hRrow : ∀ i, i < m → (gridRow R i).length = n)
      (hR : ∀ i j, i < m → j < n → entry R i j = entry G i (n - 1 - j)) :
      ∀ r rR, max_area_of_island G = ok r → max_area_of_island R = ok rR →
        r.val = rR.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (G R : Slice (Vec I64)) (m n : Nat)
        (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m ≤ 50) (hn50 : n ≤ 50)
        (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
        (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
        (hRm : gridM R = m) (hRrow : ∀ i, i < m → (gridRow R i).length = n)
        (hR : ∀ i j, i < m → j < n → entry R i j = entry G i (n - 1 - j)), ∀ r rR, max_area_of_island G = ok r → max_area_of_island R = ok rR →
          r.val = rR.val) := by
    sorry

  /-- Whenever the function applied to G returns r and the function applied to G' returns r', r = r'.
    Preconditions: Let m and n be positive integers with m < 50 and n < 50. Let G be an input such that len(G) = m, len(G[i]) = n for every 0 <= i < m, and every entry of G is 0 or 1. Define G' by len(G') = m+1, len(G'[i]) = n+1 for every 0 <= i <= m, G'[i][j] = 0 whenever i = 0 or j = 0, and G'[i+1][j+1] = G[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_15 (G G' : Slice (Vec I64)) (m n : Nat)
      (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m < 50) (hn50 : n < 50)
      (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
      (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
      (hG'm : gridM G' = m + 1) (hG'row : ∀ i, i < m + 1 → (gridRow G' i).length = n + 1)
      (hborder : ∀ i j, i < m + 1 → j < n + 1 → (i = 0 ∨ j = 0) → entry G' i j = 0)
      (hinterior : ∀ i j, i < m → j < n → entry G' (i + 1) (j + 1) = entry G i j) :
      ∀ r r', max_area_of_island G = ok r → max_area_of_island G' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (G G' : Slice (Vec I64)) (m n : Nat)
        (hm1 : 0 < m) (hn1 : 0 < n) (hm50 : m < 50) (hn50 : n < 50)
        (hGm : gridM G = m) (hGrow : ∀ i, i < m → (gridRow G i).length = n)
        (hG01 : ∀ i j, i < m → j < n → (entry G i j = 0 ∨ entry G i j = 1))
        (hG'm : gridM G' = m + 1) (hG'row : ∀ i, i < m + 1 → (gridRow G' i).length = n + 1)
        (hborder : ∀ i j, i < m + 1 → j < n + 1 → (i = 0 ∨ j = 0) → entry G' i j = 0)
        (hinterior : ∀ i j, i < m → j < n → entry G' (i + 1) (j + 1) = entry G i j), ∀ r r', max_area_of_island G = ok r → max_area_of_island G' = ok r' →
          r.val = r'.val) := by
    sorry

  end AegisSpec.MaxAreaOfIsland
