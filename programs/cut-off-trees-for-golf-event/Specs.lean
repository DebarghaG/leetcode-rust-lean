import Aegis.CutOffTree.Code.Funs

/-!
# Specifications of `Aegis.CutOffTree.cut_off_tree`

LeetCode problem `cut-off-trees-for-golf-event`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CutOffTree

open Classical Aegis.CutOffTree

abbrev Cell := ℕ × ℕ

def nRows (forest : Slice (alloc.vec.Vec Std.I64)) : ℕ := (Slice.val forest).length

def nCols (forest : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  match (Slice.val forest)[0]? with
  | some row => (Slice.val row.slice).length
  | none => 0

def entry (forest : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Option ℤ :=
  match (Slice.val forest)[i]? with
  | none => none
  | some row => ((Slice.val row.slice)[j]?).map (fun x => x.val)

def ValidForest (forest : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ nRows forest ∧
  nRows forest ≤ 50 ∧
  1 ≤ nCols forest ∧
  nCols forest ≤ 50 ∧
  (∀ row ∈ Slice.val forest, (Slice.val row.slice).length = nCols forest) ∧
  (∀ (i j : ℕ) (v : ℤ), entry forest i j = some v → 0 ≤ v ∧ v ≤ 1000000000) ∧
  (∃ (i j : ℕ) (v : ℤ), entry forest i j = some v ∧ 1 < v) ∧
  (∀ (i j i' j' : ℕ) (v : ℤ), entry forest i j = some v → entry forest i' j' = some v →
    1 < v → i = i' ∧ j = j')

def SameShape (A B : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (Slice.val B).length = (Slice.val A).length ∧
  ∀ (i : ℕ) (rowA rowB : alloc.vec.Vec Std.I64),
    (Slice.val A)[i]? = some rowA → (Slice.val B)[i]? = some rowB →
      (Slice.val rowA.slice).length = (Slice.val rowB.slice).length

def treeCellsWithHeights (forest : Slice (alloc.vec.Vec Std.I64)) : List (ℤ × Cell) :=
  (List.range (nRows forest)).flatMap (fun i =>
    (List.range (nCols forest)).flatMap (fun j =>
      match entry forest i j with
      | some v => if 1 < v then [(v, (i, j))] else []
      | none => []))

def treeCells (forest : Slice (alloc.vec.Vec Std.I64)) : List Cell :=
  (treeCellsWithHeights forest).map (fun p => p.2)

def heightOrder (forest : Slice (alloc.vec.Vec Std.I64)) : List Cell :=
  (List.insertionSort (fun a b : ℤ × Cell => a.1 ≤ b.1) (treeCellsWithHeights forest)).map
    (fun p => p.2)

def IsMinTreeCell (forest : Slice (alloc.vec.Vec Std.I64)) (P : Cell) : Prop :=
  ∃ v : ℤ, entry forest P.1 P.2 = some v ∧ 1 < v ∧
    ∀ (i j : ℕ) (w : ℤ), entry forest i j = some w → 1 < w → v ≤ w

def AdmStep (forest : Slice (alloc.vec.Vec Std.I64)) (a b : Cell) : Prop :=
  b.1 < nRows forest ∧
  b.2 < nCols forest ∧
  (∃ v : ℤ, entry forest b.1 b.2 = some v ∧ v ≠ 0) ∧
  ((a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
    (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1)))

def IsWalk (forest : Slice (alloc.vec.Vec Std.I64)) (s t : Cell) (C : ℕ → Cell) (L : ℕ) : Prop :=
  C 0 = s ∧ C L = t ∧ ∀ k : ℕ, 1 ≤ k → k ≤ L → AdmStep forest (C (k - 1)) (C k)

noncomputable def pathDist (forest : Slice (alloc.vec.Vec Std.I64)) (s t : Cell) : Option ℕ :=
  if h : ∃ L : ℕ, ∃ C : ℕ → Cell, IsWalk forest s t C L then some (Nat.find h) else none

def legs (P : List Cell) : List (Cell × Cell) := ((0, 0) :: P).zip P

noncomputable def legDists (forest : Slice (alloc.vec.Vec Std.I64)) (P : List Cell) :
    List (Option ℕ) :=
  (legs P).map (fun pq => pathDist forest pq.1 pq.2)

def sumOpts : List (Option ℕ) → Option ℕ
  | [] => some 0
  | none :: _ => none
  | some x :: rest => (sumOpts rest).map (fun s => x + s)

def manhattan (a b : Cell) : ℕ :=
  ((a.1 : ℤ) - (b.1 : ℤ)).natAbs + ((a.2 : ℤ) - (b.2 : ℤ)).natAbs

def legManhattan (P : List Cell) : ℕ := ((legs P).map (fun pq => manhattan pq.1 pq.2)).sum

/-- Let P_1,...,P_t be the tree cells (cells with forest value > 1) ordered so that forest[P_1] < forest[P_2] < ... < forest[P_t]. For k = 1,...,t define d_k as follows. d_1 is the least L >= 0 such that there are cells C_0 = (0,0), C_1,...,C_L = P_1 where, for every s >= 1, C_s is in bounds and forest[C_s] != 0, and consecutive cells differ by one unit in one coordinate. For k >= 2, d_k is the least L >= 0 such that there are cells C_0 = P_{k-1}, C_1,...,C_L = P_k where, for every s >= 1, C_s is in bounds and forest[C_s] != 0, and consecutive cells differ by one unit in one coordinate. If no such L exists, set d_k = infinity. The function returns a result r and: if some d_k is infinite, then r = -1; otherwise r = d_1 + d_2 + ... + d_t.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_1 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∃ r : I64, cut_off_tree forest = ok r ∧
      ((none ∈ legDists forest (heightOrder forest)) → r.val = -1) ∧
      (∀ s : ℕ, sumOpts (legDists forest (heightOrder forest)) = some s → r.val = (s : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∃ r : I64, cut_off_tree forest = ok r ∧
      ((none ∈ legDists forest (heightOrder forest)) → r.val = -1) ∧
      (∀ s : ℕ, sumOpts (legDists forest (heightOrder forest)) = some s → r.val = (s : ℤ))) := by
  sorry

/-- For every forest satisfying the preconditions, the function returns a result r; it does not fail, overflow, index out of bounds, or panic.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_2 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∃ r : I64, cut_off_tree forest = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∃ r : I64, cut_off_tree forest = ok r) := by
  sorry

/-- Let t be the number of cells with forest[i][j] > 1. Whenever the function returns a result r, either r = -1 or 0 <= r <= t * (m*n - 1).
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_3 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ r : I64, cut_off_tree forest = ok r →
      r.val = -1 ∨
        (0 ≤ r.val ∧
          r.val ≤ ((treeCells forest).length : ℤ) *
            (((nRows forest : ℤ) * (nCols forest : ℤ)) - 1)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ r : I64, cut_off_tree forest = ok r →
      r.val = -1 ∨
        (0 ≤ r.val ∧
          r.val ≤ ((treeCells forest).length : ℤ) *
            (((nRows forest : ℤ) * (nCols forest : ℤ)) - 1))) := by
  sorry

/-- Let P_1,...,P_t be the tree cells ordered by increasing height. For k = 1,...,t, let d_k be the shortest admissible path length from (0,0) to P_1 when k = 1 and from P_{k-1} to P_k when k >= 2, or infinity if no such path exists; an admissible path is a cell sequence whose every cell after the first is in bounds and has forest value != 0, with consecutive cells differing by one unit in one coordinate. Whenever the function returns a result r, r = -1 if and only if at least one d_k is infinite.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_4 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ r : I64, cut_off_tree forest = ok r →
      (r.val = -1 ↔ none ∈ legDists forest (heightOrder forest)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ r : I64, cut_off_tree forest = ok r →
      (r.val = -1 ↔ none ∈ legDists forest (heightOrder forest))) := by
  sorry

/-- Let t be the number of cells with forest[i][j] > 1. Whenever the function returns a result r, r = 0 if and only if t = 1 and the unique tree cell is (0,0).
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_5 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ r : I64, cut_off_tree forest = ok r →
      (r.val = 0 ↔ (treeCells forest).length = 1 ∧ treeCells forest = [(0, 0)]) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ r : I64, cut_off_tree forest = ok r →
      (r.val = 0 ↔ (treeCells forest).length = 1 ∧ treeCells forest = [(0, 0)])) := by
  sorry

/-- Whenever the function returns a result r with r != -1, we have r >= 1.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, all values forest[i][j] > 1 are pairwise distinct, and forest[0][0] <= 1. -/
theorem spec_6 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest)
    (h00 : ∀ v : ℤ, entry forest 0 0 = some v → v ≤ 1) :
    ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 → 1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest)
    (h00 : ∀ v : ℤ, entry forest 0 0 = some v → v ≤ 1), ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 → 1 ≤ r.val) := by
  sorry

/-- Let P_1,...,P_t be the tree cells ordered by increasing height, and set P_0 = (0,0). Whenever the function returns a result r, r != -1 and r = sum over k = 1,...,t of ( abs(row(P_{k-1}) - row(P_k)) + abs(col(P_{k-1}) - col(P_k)) ), where row(P) and col(P) are the 0-based coordinates of cell P.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, all values forest[i][j] > 1 are pairwise distinct, and forest[i][j] != 0 for every i,j. -/
theorem spec_7 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest)
    (hnz : ∀ (i j : ℕ) (v : ℤ), entry forest i j = some v → v ≠ 0) :
    ∀ r : I64, cut_off_tree forest = ok r →
      r.val ≠ -1 ∧ r.val = (legManhattan (heightOrder forest) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest)
    (hnz : ∀ (i j : ℕ) (v : ℤ), entry forest i j = some v → v ≠ 0), ∀ r : I64, cut_off_tree forest = ok r →
      r.val ≠ -1 ∧ r.val = (legManhattan (heightOrder forest) : ℤ)) := by
  sorry

/-- Let r_A be the result of the function on A and r_B the result on B. Whenever both calls return results, if r_A = -1 then r_B = -1; if r_A != -1 then either r_B = -1 or r_B >= r_A.
  Preconditions: Let A be an m x n matrix represented as a slice of vectors of 64-bit integers, where 1 <= m,n <= 50, every row has length n, 0 <= A[i][j] <= 10^9 for all i,j, the set of cells with A[i][j] > 1 is nonempty, and all values A[i][j] > 1 are pairwise distinct. Let B be an m x n matrix of the same dimensions such that B[i][j] = A[i][j] whenever A[i][j] != 1, and for every cell with A[i][j] = 1, B[i][j] is either 0 or 1. (Then B has the same nonempty set of tree cells and the same tree heights as A.) -/
theorem spec_8 (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hshape : SameShape A B)
    (hagree : ∀ (i j : ℕ) (v : ℤ), entry A i j = some v → v ≠ 1 → entry B i j = some v)
    (hone : ∀ (i j : ℕ), entry A i j = some 1 → ∃ w : ℤ, entry B i j = some w ∧ (w = 0 ∨ w = 1)) :
    ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB →
      (rA.val = -1 → rB.val = -1) ∧ (rA.val ≠ -1 → rB.val = -1 ∨ rA.val ≤ rB.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hshape : SameShape A B)
    (hagree : ∀ (i j : ℕ) (v : ℤ), entry A i j = some v → v ≠ 1 → entry B i j = some v)
    (hone : ∀ (i j : ℕ), entry A i j = some 1 → ∃ w : ℤ, entry B i j = some w ∧ (w = 0 ∨ w = 1)), ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB →
      (rA.val = -1 → rB.val = -1) ∧ (rA.val ≠ -1 → rB.val = -1 ∨ rA.val ≤ rB.val)) := by
  sorry

/-- Let r_A be the result of the function on A and r_B the result on B. Whenever both calls return results, if r_A != -1 then r_B != -1 and r_B <= r_A.
  Preconditions: Let A be an m x n matrix represented as a slice of vectors of 64-bit integers, where 1 <= m,n <= 50, every row has length n, 0 <= A[i][j] <= 10^9 for all i,j, the set of cells with A[i][j] > 1 is nonempty, and all values A[i][j] > 1 are pairwise distinct. Let B be an m x n matrix of the same dimensions such that B[i][j] = A[i][j] whenever A[i][j] != 0, and for every cell with A[i][j] = 0, B[i][j] is either 0 or 1. (Then B has the same nonempty set of tree cells and the same tree heights as A.) -/
theorem spec_9 (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hshape : SameShape A B)
    (hagree : ∀ (i j : ℕ) (v : ℤ), entry A i j = some v → v ≠ 0 → entry B i j = some v)
    (hzero : ∀ (i j : ℕ), entry A i j = some 0 → ∃ w : ℤ, entry B i j = some w ∧ (w = 0 ∨ w = 1)) :
    ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB →
      (rA.val ≠ -1 → rB.val ≠ -1 ∧ rB.val ≤ rA.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hshape : SameShape A B)
    (hagree : ∀ (i j : ℕ) (v : ℤ), entry A i j = some v → v ≠ 0 → entry B i j = some v)
    (hzero : ∀ (i j : ℕ), entry A i j = some 0 → ∃ w : ℤ, entry B i j = some w ∧ (w = 0 ∨ w = 1)), ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB →
      (rA.val ≠ -1 → rB.val ≠ -1 ∧ rB.val ≤ rA.val)) := by
  sorry

/-- Let r_A be the result of the function on A and r_B the result on B. Whenever both calls return results, r_A = r_B.
  Preconditions: Let A and B be two m x n matrices represented as slices of vectors of 64-bit integers, where 1 <= m,n <= 50, every row has length n, every entry is in [0,10^9], each matrix has at least one cell with value > 1, and all values > 1 in each matrix are pairwise distinct. Assume for every cell (i,j): A[i][j] = 0 if and only if B[i][j] = 0; A[i][j] > 1 if and only if B[i][j] > 1; and for every two tree cells x,y, A[x] < A[y] if and only if B[x] < B[y]. -/
theorem spec_10 (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hB : ValidForest B)
    (hshape : SameShape A B)
    (hzero : ∀ (i j : ℕ) (v : ℤ),
      entry A i j = some v → (v = 0 ↔ ∃ w : ℤ, entry B i j = some w ∧ w = 0))
    (htree : ∀ (i j : ℕ) (v : ℤ),
      entry A i j = some v → (1 < v ↔ ∃ w : ℤ, entry B i j = some w ∧ 1 < w))
    (horder : ∀ (i j i' j' : ℕ) (v v' w w' : ℤ),
      entry A i j = some v → entry B i j = some w → 1 < v → 1 < w →
      entry A i' j' = some v' → entry B i' j' = some w' → 1 < v' → 1 < w' →
      (v < v' ↔ w < w')) :
    ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB → rA.val = rB.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (hA : ValidForest A) (hB : ValidForest B)
    (hshape : SameShape A B)
    (hzero : ∀ (i j : ℕ) (v : ℤ),
      entry A i j = some v → (v = 0 ↔ ∃ w : ℤ, entry B i j = some w ∧ w = 0))
    (htree : ∀ (i j : ℕ) (v : ℤ),
      entry A i j = some v → (1 < v ↔ ∃ w : ℤ, entry B i j = some w ∧ 1 < w))
    (horder : ∀ (i j i' j' : ℕ) (v v' w w' : ℤ),
      entry A i j = some v → entry B i j = some w → 1 < v → 1 < w →
      entry A i' j' = some v' → entry B i' j' = some w' → 1 < v' → 1 < w' →
      (v < v' ↔ w < w')), ∀ rA rB : I64, cut_off_tree A = ok rA → cut_off_tree B = ok rB → rA.val = rB.val) := by
  sorry

/-- Let T_1,...,T_t be the tree cells ordered by increasing height. Whenever the function returns a result r with r != -1, there exists a finite sequence of cells C_0,...,C_r such that C_0 = (0,0), for every s = 1,...,r the cell C_s is in bounds and forest[C_s] != 0, consecutive cells differ by one unit in one coordinate, and T_1,...,T_t occur in the sequence as a subsequence in that order: there are indices 0 <= i_1 < i_2 < ... < i_t <= r with C_{i_k} = T_k for every k.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_11 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 →
      ∃ (L : ℕ) (C : ℕ → Cell),
        r.val = (L : ℤ) ∧ C 0 = (0, 0) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ L → AdmStep forest (C (k - 1)) (C k)) ∧
        ∃ idx : ℕ → ℕ,
          (∀ k : ℕ, k < (treeCells forest).length → idx k ≤ L) ∧
          (∀ k : ℕ, k < (treeCells forest).length →
            (heightOrder forest)[k]? = some (C (idx k))) ∧
          (∀ k : ℕ, k + 1 < (treeCells forest).length → idx k < idx (k + 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 →
      ∃ (L : ℕ) (C : ℕ → Cell),
        r.val = (L : ℤ) ∧ C 0 = (0, 0) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ L → AdmStep forest (C (k - 1)) (C k)) ∧
        ∃ idx : ℕ → ℕ,
          (∀ k : ℕ, k < (treeCells forest).length → idx k ≤ L) ∧
          (∀ k : ℕ, k < (treeCells forest).length →
            (heightOrder forest)[k]? = some (C (idx k))) ∧
          (∀ k : ℕ, k + 1 < (treeCells forest).length → idx k < idx (k + 1))) := by
  sorry

/-- Let P_1 be the shortest tree cell. Whenever the function returns a result r with r != -1, r >= row(P_1) + col(P_1), where row(P_1) and col(P_1) are the 0-based coordinates of P_1.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_12 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ (r : I64) (P : Cell), cut_off_tree forest = ok r → r.val ≠ -1 →
      IsMinTreeCell forest P → ((P.1 : ℤ) + (P.2 : ℤ)) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ (r : I64) (P : Cell), cut_off_tree forest = ok r → r.val ≠ -1 →
      IsMinTreeCell forest P → ((P.1 : ℤ) + (P.2 : ℤ)) ≤ r.val) := by
  sorry

/-- Let P_1,...,P_t be the tree cells ordered by increasing height and set P_0 = (0,0). Whenever the function returns a result r with r != -1, r >= sum_{k=1}^t ( |row(P_{k-1}) - row(P_k)| + |col(P_{k-1}) - col(P_k)| ), where row(P) and col(P) are the 0-based coordinates of cell P.
  Preconditions: Let m = len(forest) and n = len(forest[0]). Assume 1 <= m,n <= 50, every row of forest has length n, every entry forest[i][j] is an integer with 0 <= forest[i][j] <= 10^9, the set of cells with forest[i][j] > 1 is nonempty, and all values forest[i][j] > 1 are pairwise distinct. -/
theorem spec_13 (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest) :
    ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 →
      (legManhattan (heightOrder forest) : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (forest : Slice (alloc.vec.Vec Std.I64)) (h : ValidForest forest), ∀ r : I64, cut_off_tree forest = ok r → r.val ≠ -1 →
      (legManhattan (heightOrder forest) : ℤ) ≤ r.val) := by
  sorry

end AegisSpec.CutOffTree

namespace AegisSpec.CutOffTree

private def mkRow2 (a b : I64) : alloc.vec.Vec I64 :=
  alloc.vec.Vec.mk
    (Slice.mk 2 (Aeneas.Data.ListN.ListN.cons a (Aeneas.Data.ListN.ListN.cons b Aeneas.Data.ListN.ListN.nil))
      (by have h := Usize.cMax_bound_concrete; omega))

private def mkRow1 (a : I64) : alloc.vec.Vec I64 :=
  alloc.vec.Vec.mk
    (Slice.mk 1 (Aeneas.Data.ListN.ListN.cons a Aeneas.Data.ListN.ListN.nil)
      (by have h := Usize.cMax_bound_concrete; omega))

private def mkForest2 (r0 r1 : alloc.vec.Vec I64) : Slice (alloc.vec.Vec I64) :=
  Slice.mk 2 (Aeneas.Data.ListN.ListN.cons r0 (Aeneas.Data.ListN.ListN.cons r1 Aeneas.Data.ListN.ListN.nil))
    (by have h := Usize.cMax_bound_concrete; omega)

private def mkForest1 (r0 : alloc.vec.Vec I64) : Slice (alloc.vec.Vec I64) :=
  Slice.mk 1 (Aeneas.Data.ListN.ListN.cons r0 Aeneas.Data.ListN.ListN.nil)
    (by have h := Usize.cMax_bound_concrete; omega)

private def exA : Slice (alloc.vec.Vec I64) := mkForest2 (mkRow2 0#i64 2#i64) (mkRow2 3#i64 0#i64)

private def exC : Slice (alloc.vec.Vec I64) := mkForest2 (mkRow2 1#i64 2#i64) (mkRow2 4#i64 5#i64)

private def exD : Slice (alloc.vec.Vec I64) := mkForest1 (mkRow1 2#i64)

end AegisSpec.CutOffTree
