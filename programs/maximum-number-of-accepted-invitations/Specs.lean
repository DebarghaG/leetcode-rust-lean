import Aegis.MaximumInvitations.Code.Funs

/-!
# Specifications of `Aegis.MaximumInvitations.maximum_invitations`

LeetCode problem `maximum-number-of-accepted-invitations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumInvitations

open Aegis.MaximumInvitations

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => IScalar.val x

def Binary (M : Nat → Nat → Int) (m n : Nat) : Prop :=
  ∀ i j, i < m → j < n → M i j = 0 ∨ M i j = 1

structure IsValidGrid (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop where

  hm_pos : 1 ≤ m

  hm_le : m ≤ 200

  hn_pos : 1 ≤ n

  hn_le : n ≤ 200

  hlen : grid.val.length = m

  hrows : ∀ row ∈ grid.val, row.val.length = n

  hbinary : Binary (cell grid) m n

def ValidSet (M : Nat → Nat → Int) (m n : Nat) (S : Finset (Nat × Nat)) : Prop :=
  (∀ p ∈ S, p.1 < m ∧ p.2 < n) ∧
    (∀ p ∈ S, M p.1 p.2 = 1) ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) ∧
    (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.2 ≠ q.2)

def MaxInvitations (M : Nat → Nat → Int) (m n : Nat) (r : Int) : Prop :=
  (∃ S : Finset (Nat × Nat), ValidSet M m n S ∧ (S.card : Int) = r) ∧
    ∀ S : Finset (Nat × Nat), ValidSet M m n S → (S.card : Int) ≤ r

def onesCount (M : Nat → Nat → Int) (m n : Nat) : Nat :=
  (((Finset.range m).product (Finset.range n)).filter (fun p => M p.1 p.2 = 1)).card

def deleteRow (M : Nat → Nat → Int) (i0 : Nat) : Nat → Nat → Int :=
  fun i j => if i < i0 then M i j else M (i + 1) j

def deleteCol (M : Nat → Nat → Int) (j0 : Nat) : Nat → Nat → Int :=
  fun i j => if j < j0 then M i j else M i (j + 1)

def transpose (M : Nat → Nat → Int) : Nat → Nat → Int :=
  fun i j => M j i

def permute {m n : Nat} (M : Nat → Nat → Int)
    (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n)) : Nat → Nat → Int :=
  fun i j =>
    if hi : i < m then
      if hj : j < n then M (π ⟨i, hi⟩).val (σ ⟨j, hj⟩).val else 0
    else 0

/-- For every grid satisfying the preconditions, the function returns a result r and r is the maximum possible cardinality of a valid invitation set. A valid invitation set is a set S of ordered pairs (i,j) with 0 <= i < m and 0 <= j < n such that: (a) grid[i][j] = 1 for every (i,j) in S; (b) no two distinct pairs in S have the same first coordinate; (c) no two distinct pairs in S have the same second coordinate. Thus r = max { |S| : S is a valid invitation set }, where the empty set is allowed and contributes 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) :
    ∃ r : Std.I64,
      maximum_invitations grid = ok r ∧ MaxInvitations (cell grid) m n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n), ∃ r : Std.I64,
      maximum_invitations grid = ok r ∧ MaxInvitations (cell grid) m n r.val) := by
  sorry

/-- For every grid satisfying the preconditions, maximum_invitations does not fail: it returns a value r of type i64 (no arithmetic overflow, out-of-bounds access, or panic occurs).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) :
    ∃ r : Std.I64, maximum_invitations grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n), ∃ r : Std.I64, maximum_invitations grid = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 0 <= r <= min(m,n).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((min m n : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r), 0 ≤ r.val ∧ r.val ≤ ((min m n : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, r <= C, where C is the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    r.val ≤ ((onesCount (cell grid) m n : Nat) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r), r.val ≤ ((onesCount (cell grid) m n : Nat) : Int)) := by
  sorry

/-- If there exist i,j with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1, then whenever the function returns a result r, r >= 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hne : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hne : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : maximum_invitations grid = ok r), 1 ≤ r.val) := by
  sorry

/-- If grid[i][j] = 0 for every 0 <= i < m and 0 <= j < n, then the function returns a result r and r = 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hzero : ∀ i j, i < m → j < n → cell grid i j = 0) :
    ∃ r : Std.I64, maximum_invitations grid = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hzero : ∀ i j, i < m → j < n → cell grid i j = 0), ∃ r : Std.I64, maximum_invitations grid = ok r ∧ r.val = 0) := by
  sorry

/-- If grid[i][j] = 1 for every 0 <= i < m and 0 <= j < n, then the function returns a result r and r = min(m,n).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hone : ∀ i j, i < m → j < n → cell grid i j = 1) :
    ∃ r : Std.I64,
      maximum_invitations grid = ok r ∧ r.val = ((min m n : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n)
    (hone : ∀ i j, i < m → j < n → cell grid i j = 1), ∃ r : Std.I64,
      maximum_invitations grid = ok r ∧ r.val = ((min m n : Nat) : Int)) := by
  sorry

/-- If m = 1, then the function returns a result r and r = 1 if there exists j with 0 <= j < n and grid[0][j] = 1, and r = 0 otherwise.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (hm : m = 1) :
    ∃ r : Std.I64, maximum_invitations grid = ok r ∧
      ((∃ j, j < n ∧ cell grid 0 j = 1) → r.val = 1) ∧
      ((¬ ∃ j, j < n ∧ cell grid 0 j = 1) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (hm : m = 1), ∃ r : Std.I64, maximum_invitations grid = ok r ∧
      ((∃ j, j < n ∧ cell grid 0 j = 1) → r.val = 1) ∧
      ((¬ ∃ j, j < n ∧ cell grid 0 j = 1) → r.val = 0)) := by
  sorry

/-- If n = 1, then the function returns a result r and r = 1 if there exists i with 0 <= i < m and grid[i][0] = 1, and r = 0 otherwise.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (hn : n = 1) :
    ∃ r : Std.I64, maximum_invitations grid = ok r ∧
      ((∃ i, i < m ∧ cell grid i 0 = 1) → r.val = 1) ∧
      ((¬ ∃ i, i < m ∧ cell grid i 0 = 1) → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (hn : n = 1), ∃ r : Std.I64, maximum_invitations grid = ok r ∧
      ((∃ i, i < m ∧ cell grid i 0 = 1) → r.val = 1) ∧
      ((¬ ∃ i, i < m ∧ cell grid i 0 = 1) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid invitation set S with |S| = r. Here a valid invitation set is a set of pairs (i,j) with 0 <= i < m and 0 <= j < n such that grid[i][j] = 1 for every (i,j) in S, no two pairs in S share a first coordinate, and no two pairs in S share a second coordinate.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    ∃ S : Finset (Nat × Nat), ValidSet (cell grid) m n S ∧ (S.card : Int) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r), ∃ S : Finset (Nat × Nat), ValidSet (cell grid) m n S ∧ (S.card : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, there is no valid invitation set S with |S| > r, where a valid invitation set is a set of pairs (i,j) with 0 <= i < m and 0 <= j < n such that grid[i][j] = 1 for every (i,j) in S, no two pairs in S share a first coordinate, and no two pairs in S share a second coordinate.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    ∀ S : Finset (Nat × Nat), ValidSet (cell grid) m n S → (S.card : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r), ∀ S : Finset (Nat × Nat), ValidSet (cell grid) m n S → (S.card : Int) ≤ r.val) := by
  sorry

/-- If some row i0 with 0 <= i0 < m satisfies grid[i0][j] = 0 for every 0 <= j < n, then whenever the function returns r, r is also the maximum possible number of accepted invitations for the (m-1) x n matrix obtained by deleting row i0 from grid and keeping the other rows in their original relative order. If m = 1, the matrix after deletion has no rows and its maximum possible number is 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (i0 : Nat) (hi0 : i0 < m)
    (hrow : ∀ j, j < n → cell grid i0 j = 0)
    (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    MaxInvitations (deleteRow (cell grid) i0) (m - 1) n r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (i0 : Nat) (hi0 : i0 < m)
    (hrow : ∀ j, j < n → cell grid i0 j = 0)
    (r : Std.I64) (hr : maximum_invitations grid = ok r), MaxInvitations (deleteRow (cell grid) i0) (m - 1) n r.val) := by
  sorry

/-- If some column j0 with 0 <= j0 < n satisfies grid[i][j0] = 0 for every 0 <= i < m, then whenever the function returns r, r is also the maximum possible number of accepted invitations for the m x (n-1) matrix obtained by deleting column j0 from every row of grid and keeping the other columns in their original relative order. If n = 1, the matrix after deletion has no columns and its maximum possible number is 0.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (j0 : Nat) (hj0 : j0 < n)
    (hcol : ∀ i, i < m → cell grid i j0 = 0)
    (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    MaxInvitations (deleteCol (cell grid) j0) m (n - 1) r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (j0 : Nat) (hj0 : j0 < n)
    (hcol : ∀ i, i < m → cell grid i j0 = 0)
    (r : Std.I64) (hr : maximum_invitations grid = ok r), MaxInvitations (deleteCol (cell grid) j0) m (n - 1) r.val) := by
  sorry

/-- Let H be any m x n matrix with entries in {0,1} such that grid[i][j] <= H[i][j] for every 0 <= i < m and 0 <= j < n. Whenever the function returns r for grid, r <= M(H), where M(H) is the maximum possible number of accepted invitations for H, meaning the maximum size of a set of pairs (i,j) with H[i][j] = 1, at most one per row, and at most one per column.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (H : Nat → Nat → Int) (hH : Binary H m n)
    (hle : ∀ i j, i < m → j < n → cell grid i j ≤ H i j)
    (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    ∃ t : Int, MaxInvitations H m n t ∧ r.val ≤ t := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (H : Nat → Nat → Int) (hH : Binary H m n)
    (hle : ∀ i j, i < m → j < n → cell grid i j ≤ H i j)
    (r : Std.I64) (hr : maximum_invitations grid = ok r), ∃ t : Int, MaxInvitations H m n t ∧ r.val ≤ t) := by
  sorry

/-- Whenever the function returns r for grid, r is also the maximum possible number of accepted invitations for the n x m transpose matrix G^T defined by G^T[j][i] = grid[i][j] for 0 <= j < n and 0 <= i < m, where the maximum is defined as the maximum size of a set of pairs (i,j) with G^T[i][j] = 1, at most one per row, and at most one per column.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_15 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    MaxInvitations (transpose (cell grid)) n m r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (r : Std.I64) (hr : maximum_invitations grid = ok r), MaxInvitations (transpose (cell grid)) n m r.val) := by
  sorry

/-- Whenever the function returns r for grid, for every bijection pi from {0,...,m-1} to itself and every bijection sigma from {0,...,n-1} to itself, r is also the maximum possible number of accepted invitations for the matrix H defined by H[i][j] = grid[pi(i)][sigma(j)] for all 0 <= i < m and 0 <= j < n, where the maximum is defined as the maximum size of a set of pairs (i,j) with H[i][j] = 1, at most one per row, and at most one per column.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 1 <= m <= 200, 1 <= n <= 200, every row of grid has length n, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_16 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n))
    (r : Std.I64) (hr : maximum_invitations grid = ok r) :
    MaxInvitations (permute (cell grid) π σ) m n r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : IsValidGrid grid m n) (π : Equiv.Perm (Fin m)) (σ : Equiv.Perm (Fin n))
    (r : Std.I64) (hr : maximum_invitations grid = ok r), MaxInvitations (permute (cell grid) π σ) m n r.val) := by
  sorry

end AegisSpec.MaximumInvitations
