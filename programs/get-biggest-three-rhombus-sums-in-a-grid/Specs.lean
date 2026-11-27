import Aegis.GetBiggestThree.Code.Funs

/-!
# Specifications of `Aegis.GetBiggestThree.get_biggest_three`

LeetCode problem `get-biggest-three-rhombus-sums-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetBiggestThree

def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (a : ℕ) : ℕ :=
  match grid.val[a]? with
  | none => 0
  | some row => row.val.length

def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : ℕ := grid.val.length

def numCols (grid : Slice (alloc.vec.Vec Std.I64)) : ℕ := rowLen grid 0

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (a b : ℕ) : ℤ :=
  match grid.val[a]? with
  | none => 0
  | some row =>
    match row.val[b]? with
    | none => 0
    | some x => x.val

def outList (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

def rhombusCells (grid : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (numRows grid)).product (Finset.range (numCols grid))).filter
    (fun p => |(p.1 : ℤ) - (i : ℤ)| + |(p.2 : ℤ) - (j : ℤ)| = (k : ℤ))

def rhombusSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) : ℤ :=
  ∑ p ∈ rhombusCells grid i j k, cell grid p.1 p.2

def IsValidTriple (grid : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) : Prop :=
  i < numRows grid ∧ j < numCols grid ∧ k ≤ i ∧ i + k < numRows grid ∧ k ≤ j ∧
    j + k < numCols grid

instance decidableIsValidTriple (grid : Slice (alloc.vec.Vec Std.I64)) (i j k : ℕ) :
    Decidable (IsValidTriple grid i j k) := by
  unfold IsValidTriple
  infer_instance

def tripleCandidates (grid : Slice (alloc.vec.Vec Std.I64)) : Finset ((ℕ × ℕ) × ℕ) :=
  ((Finset.range (numRows grid)).product (Finset.range (numCols grid))).product
    (Finset.range (numRows grid))

def validTriples (grid : Slice (alloc.vec.Vec Std.I64)) : Finset ((ℕ × ℕ) × ℕ) :=
  (tripleCandidates grid).filter (fun t : (ℕ × ℕ) × ℕ => IsValidTriple grid t.1.1 t.1.2 t.2)

def rhombusSums (grid : Slice (alloc.vec.Vec Std.I64)) : Finset ℤ :=
  (validTriples grid).image (fun t : (ℕ × ℕ) × ℕ => rhombusSum grid t.1.1 t.1.2 t.2)

def cellValues (grid : Slice (alloc.vec.Vec Std.I64)) : Finset ℤ :=
  ((Finset.range (numRows grid)).product (Finset.range (numCols grid))).image
    (fun p => cell grid p.1 p.2)

def gridTotal (grid : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  ∑ a ∈ Finset.range (numRows grid), ∑ b ∈ Finset.range (rowLen grid a), cell grid a b

def DescEnum (S : Finset ℤ) (s : List ℤ) : Prop :=
  s.Nodup ∧ s.Pairwise (· > ·) ∧ ∀ x : ℤ, x ∈ s ↔ x ∈ S

def IsMaxOf (S : Finset ℤ) (v : ℤ) : Prop :=
  v ∈ S ∧ ∀ s ∈ S, s ≤ v

def IsGreatestBelow (S : Finset ℤ) (bound v : ℤ) : Prop :=
  v ∈ S ∧ v < bound ∧ ∀ s ∈ S, s < bound → s ≤ v

def IsTranspose (T grid : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  numRows T = numCols grid ∧ (∀ c, c < numCols grid → rowLen T c = numRows grid) ∧
    ∀ c r, c < numCols grid → r < numRows grid → cell T c r = cell grid r c

/-- Let a valid triple (i,j,k) mean 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n. For a valid triple, let RhombusSum(i,j,k) be the sum of grid[a][b] over all cells (a,b) with 0 <= a < m, 0 <= b < n and |a-i| + |b-j| = k. Let S = { RhombusSum(i,j,k) : (i,j,k) is valid }. Let D = |S|, and list the distinct elements of S in strictly decreasing order as s_1 > s_2 > ... > s_D. The function returns a vector r such that len(r) = min(3,D), and for every t with 0 <= t < len(r), r[t] = s_{t+1}.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (outList r).length = min 3 (rhombusSums grid).card ∧
      ∃ s : List ℤ, DescEnum (rhombusSums grid) s ∧ outList r = s.take 3 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (outList r).length = min 3 (rhombusSums grid).card ∧
      ∃ s : List ℤ, DescEnum (rhombusSums grid) s ∧ outList r = s.take 3) := by
  sorry

/-- Under these preconditions, the function returns a result r; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r) := by
  sorry

/-- Let S be the set of all valid rhombus sums, where a valid triple (i,j,k) satisfies 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, and the corresponding rhombus sum is the sum of grid[a][b] over all cells with |a-i| + |b-j| = k. The function returns a vector r and len(r) = min(3, |S|).
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (outList r).length = min 3 (rhombusSums grid).card := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (outList r).length = min 3 (rhombusSums grid).card) := by
  sorry

/-- The function returns a vector r and 1 <= len(r) <= 3.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      1 ≤ (outList r).length ∧ (outList r).length ≤ 3 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      1 ≤ (outList r).length ∧ (outList r).length ≤ 3) := by
  sorry

/-- The function returns a vector r and for all indices p and q with 0 <= p < q < len(r), r[p] != r[q].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p q, p < q → q < (outList r).length → (outList r)[p]! ≠ (outList r)[q]! := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p q, p < q → q < (outList r).length → (outList r)[p]! ≠ (outList r)[q]!) := by
  sorry

/-- The function returns a vector r and for every p with 0 <= p < len(r) - 1, r[p] > r[p+1].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p + 1 < (outList r).length → (outList r)[p]! > (outList r)[p+1]! := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p + 1 < (outList r).length → (outList r)[p]! > (outList r)[p+1]!) := by
  sorry

/-- The function returns a vector r and, for every index p with 0 <= p < len(r), there exist integers i, j, k with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, such that r[p] is the sum of grid[a][b] over all cells (a,b) satisfying |a-i| + |b-j| = k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p < (outList r).length →
        ∃ i j k, IsValidTriple grid i j k ∧ (outList r)[p]! = rhombusSum grid i j k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p < (outList r).length →
        ∃ i j k, IsValidTriple grid i j k ∧ (outList r)[p]! = rhombusSum grid i j k) := by
  sorry

/-- Let S be the set of all valid rhombus sums as defined for triples (i,j,k) with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, summing grid[a][b] over |a-i| + |b-j| = k. The function returns a vector r and r[0] = max S.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      IsMaxOf (rhombusSums grid) (outList r)[0]! := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      IsMaxOf (rhombusSums grid) (outList r)[0]!) := by
  sorry

/-- Let S be the set of all valid rhombus sums as defined for triples (i,j,k) with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, summing grid[a][b] over |a-i| + |b-j| = k. The function returns a vector r, and: if |S| >= 2 then len(r) >= 2 and r[1] = max { s in S : s < r[0] }; if |S| < 2 then len(r) = |S|.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (2 ≤ (rhombusSums grid).card →
        2 ≤ (outList r).length ∧
          IsGreatestBelow (rhombusSums grid) (outList r)[0]! (outList r)[1]!) ∧
      ((rhombusSums grid).card < 2 → (outList r).length = (rhombusSums grid).card) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (2 ≤ (rhombusSums grid).card →
        2 ≤ (outList r).length ∧
          IsGreatestBelow (rhombusSums grid) (outList r)[0]! (outList r)[1]!) ∧
      ((rhombusSums grid).card < 2 → (outList r).length = (rhombusSums grid).card)) := by
  sorry

/-- Let S be the set of all valid rhombus sums as defined for triples (i,j,k) with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, summing grid[a][b] over |a-i| + |b-j| = k. The function returns a vector r, and: if |S| >= 3 then len(r) = 3 and r[2] = max { s in S : s < r[1] }; if |S| < 3 then len(r) = |S|.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (3 ≤ (rhombusSums grid).card →
        (outList r).length = 3 ∧
          IsGreatestBelow (rhombusSums grid) (outList r)[1]! (outList r)[2]!) ∧
      ((rhombusSums grid).card < 3 → (outList r).length = (rhombusSums grid).card) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      (3 ≤ (rhombusSums grid).card →
        (outList r).length = 3 ∧
          IsGreatestBelow (rhombusSums grid) (outList r)[1]! (outList r)[2]!) ∧
      ((rhombusSums grid).card < 3 → (outList r).length = (rhombusSums grid).card)) := by
  sorry

/-- Let S be the set of all valid rhombus sums as defined for triples (i,j,k) with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, summing grid[a][b] over |a-i| + |b-j| = k. The function returns a vector r and, for every s in S, if s is not equal to r[p] for any p with 0 <= p < len(r), then s < r[len(r)-1].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ s ∈ rhombusSums grid,
        (∀ p, p < (outList r).length → (outList r)[p]! ≠ s) →
          s < (outList r)[(outList r).length - 1]! := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ s ∈ rhombusSums grid,
        (∀ p, p < (outList r).length → (outList r)[p]! ≠ s) →
          s < (outList r)[(outList r).length - 1]!) := by
  sorry

/-- Let S be the set of all valid rhombus sums as defined for triples (i,j,k) with 0 <= i < m, 0 <= j < n, 0 <= k, k <= i, i + k < m, k <= j, j + k < n, summing grid[a][b] over |a-i| + |b-j| = k. If |S| <= 3, then the function returns a vector r with len(r) = |S| whose entries, read from index 0 to len(r)-1, are exactly the elements of S once each, in strictly decreasing order.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hcard : (rhombusSums grid).card ≤ 3) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      DescEnum (rhombusSums grid) (outList r) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hcard : (rhombusSums grid).card ≤ 3), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      DescEnum (rhombusSums grid) (outList r)) := by
  sorry

/-- If m < 3 or n < 3, then no valid rhombus has positive radius k > 0, so the set S of all valid rhombus sums is exactly the set of cell values { grid[i][j] : 0 <= i < m and 0 <= j < n }. In this case the function returns a vector r that is the strictly decreasing list of the min(3, number of distinct cell values in grid) largest distinct cell values of grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hsmall : numRows grid < 3 ∨ numCols grid < 3) :
    rhombusSums grid = cellValues grid ∧
      ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
        ∃ s : List ℤ, DescEnum (cellValues grid) s ∧ outList r = s.take 3 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hsmall : numRows grid < 3 ∨ numCols grid < 3), rhombusSums grid = cellValues grid ∧
      ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
        ∃ s : List ℤ, DescEnum (cellValues grid) s ∧ outList r = s.take 3) := by
  sorry

/-- Let total = sum over 0 <= i < m and 0 <= j < n of grid[i][j]. The function returns a vector r and, for every p with 0 <= p < len(r), 1 <= r[p] <= total.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000) :
    ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p < (outList r).length → 1 ≤ (outList r)[p]! ∧ (outList r)[p]! ≤ gridTotal grid := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000), ∃ r, Aegis.GetBiggestThree.get_biggest_three grid = ok r ∧
      ∀ p, p < (outList r).length → 1 ≤ (outList r)[p]! ∧ (outList r)[p]! ≤ gridTotal grid) := by
  sorry

/-- Let T be the n by m matrix defined by T[c][r] = grid[r][c] for all 0 <= r < m and 0 <= c < n. Let r be the result of the function on grid and let rT be the result of the function on T. Then rT = r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The grid is nonempty and rectangular: 1 <= m <= 50, 1 <= n <= 50, every row of grid has length n, and 1 <= grid[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_15 (grid T : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hT : IsTranspose T grid) :
    ∀ r rT, Aegis.GetBiggestThree.get_biggest_three grid = ok r →
      Aegis.GetBiggestThree.get_biggest_three T = ok rT → rT = r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid T : Slice (alloc.vec.Vec Std.I64))
    (hm1 : 1 ≤ numRows grid) (hm2 : numRows grid ≤ 50)
    (hn1 : 1 ≤ numCols grid) (hn2 : numCols grid ≤ 50)
    (hrect : ∀ i, i < numRows grid → rowLen grid i = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100000)
    (hT : IsTranspose T grid), ∀ r rT, Aegis.GetBiggestThree.get_biggest_three grid = ok r →
      Aegis.GetBiggestThree.get_biggest_three T = ok rT → rT = r) := by
  sorry

end AegisSpec.GetBiggestThree
