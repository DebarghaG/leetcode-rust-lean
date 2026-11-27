import Aegis.FindSafeWalk.Code.Funs

/-!
# Specifications of `Aegis.FindSafeWalk.find_safe_walk`

LeetCode problem `find-a-safe-walk-through-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindSafeWalk

open Aegis.FindSafeWalk

@[reducible]
def cellAt (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Option ℤ :=
  (grid.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

structure Shape (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop where

  rows : grid.val.length = m

  cols : ∀ row ∈ grid.val, row.val.length = n

  m_pos : 1 ≤ m

  n_pos : 1 ≤ n

  m_mul_n : 2 ≤ m * n

  zero_or_one : ∀ i j, i < m → j < n → cellAt grid i j = some 0 ∨ cellAt grid i j = some 1

@[reducible]
def Adjacent (p q : ℕ × ℕ) : Prop :=
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
    (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2))

@[reducible]
def AdjacentChain (ps : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ ps.zip (ps.drop 1), Adjacent p.1 p.2

@[reducible]
def Walk (m n : ℕ) (ps : List (ℕ × ℕ)) : Prop :=
  ps.Nodup ∧
    ps.head? = some (0, 0) ∧
    ps.getLast? = some (m - 1, n - 1) ∧
    AdjacentChain ps ∧
    ∀ p ∈ ps, p.1 < m ∧ p.2 < n

def walkCost (grid : Slice (alloc.vec.Vec I64)) (ps : List (ℕ × ℕ)) : ℤ :=
  (ps.map (fun p => (cellAt grid p.1 p.2).getD 0)).sum

@[reducible]
def ZeroWalk (grid : Slice (alloc.vec.Vec I64)) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ ps, cellAt grid p.1 p.2 = some 0

def rowSum (grid : Slice (alloc.vec.Vec I64)) (i n : ℕ) : ℤ :=
  ((List.range n).map (fun j => (cellAt grid i j).getD 0)).sum

def colSum (grid : Slice (alloc.vec.Vec I64)) (m j : ℕ) : ℤ :=
  ((List.range m).map (fun i => (cellAt grid i j).getD 0)).sum

structure IsTranspose (gridT grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop where

  rows : gridT.val.length = n

  cols : ∀ row ∈ gridT.val, row.val.length = m

  entries : ∀ i j, j < n → i < m → cellAt gridT j i = cellAt grid i j

structure IsRot180 (gridR grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop where

  rows : gridR.val.length = m

  cols : ∀ row ∈ gridR.val, row.val.length = n

  entries : ∀ i j, i < m → j < n → cellAt gridR i j = cellAt grid (m - 1 - i) (n - 1 - j)

def EntrywiseLe (grid' grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop :=
  ∀ i j, i < m → j < n →
    ∃ a b : ℤ, cellAt grid' i j = some a ∧ cellAt grid i j = some b ∧ a ≤ b

def cost2x2 (grid : Slice (alloc.vec.Vec I64)) : ℤ :=
  (cellAt grid 0 0).getD 0 + (cellAt grid 1 1).getD 0 +
    min ((cellAt grid 0 1).getD 0) ((cellAt grid 1 0).getD 0)

/-- Let m = len(grid) and n = len(grid[0]). The function returns a result r and r = true if and only if there exists a finite sequence of distinct cells p_0, ..., p_k such that p_0 = (0,0), p_k = (m-1,n-1), for every t with 0 <= t < k the cells p_t and p_{t+1} share an edge (one coordinate differs by 1 and the other is equal) and both lie inside the grid, and health - (sum_{t=0}^k grid[p_t.0][p_t.1]) >= 1. The sum includes the starting cell and the final cell; because all grid entries are non-negative, requiring the cells to be distinct loses no valid walk.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) :
    ∃ r : Bool, find_safe_walk grid health = ok r ∧
      (r = true ↔
        ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ 1 ≤ health.val - walkCost grid ps) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val), ∃ r : Bool, find_safe_walk grid health = ok r ∧
      (r = true ↔
        ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ 1 ≤ health.val - walkCost grid ps)) := by
  sorry

/-- The function returns a result (either true or false) and does not fail: it does not overflow, index out of bounds, or panic.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hfit : m * n ≤ Usize.max) :
    ∃ r : Bool, find_safe_walk grid health = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hfit : m * n ≤ Usize.max), ∃ r : Bool, find_safe_walk grid health = ok r) := by
  sorry

/-- If health >= m+n, then whenever the function returns a result r, r = true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val)
    (hbig : (m : ℤ) + (n : ℤ) ≤ health.val) :
    ∀ r : Bool, find_safe_walk grid health = ok r → r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val)
    (hbig : (m : ℤ) + (n : ℤ) ≤ health.val), ∀ r : Bool, find_safe_walk grid health = ok r → r = true) := by
  sorry

/-- If health = 1, then whenever the function returns a result r, r = true if and only if there exists a finite sequence of distinct cells p_0, ..., p_k such that p_0 = (0,0), p_k = (m-1,n-1), consecutive cells share an edge, and grid[p_t.0][p_t.1] = 0 for every t with 0 <= t <= k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : health.val = 1) :
    ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔ ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ ZeroWalk grid ps) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : health.val = 1), ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔ ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ ZeroWalk grid ps)) := by
  sorry

/-- For any two integers h and h' such that 1 <= h <= h' and both are representable as signed 64-bit integers, if find_safe_walk(grid, h) returns true, then find_safe_walk(grid, h') returns true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h h' : I64)
    (hshape : Shape grid m n) (hh : 1 ≤ h.val) (hle : h.val ≤ h'.val) :
    find_safe_walk grid h = ok true → find_safe_walk grid h' = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h h' : I64)
    (hshape : Shape grid m n) (hh : 1 ≤ h.val) (hle : h.val ≤ h'.val), find_safe_walk grid h = ok true → find_safe_walk grid h' = ok true) := by
  sorry

/-- Let grid' be any m by n matrix with entries in {0,1} satisfying grid'[i][j] <= grid[i][j] for every 0 <= i < m and 0 <= j < n. If find_safe_walk(grid, health) returns true, then find_safe_walk(grid', health) returns true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_6 (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hshape' : Shape grid' m n)
    (hhealth : 1 ≤ health.val) (hle : EntrywiseLe grid' grid m n) :
    find_safe_walk grid health = ok true → find_safe_walk grid' health = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hshape' : Shape grid' m n)
    (hhealth : 1 ≤ health.val) (hle : EntrywiseLe grid' grid m n), find_safe_walk grid health = ok true → find_safe_walk grid' health = ok true) := by
  sorry

/-- If m = 1, let S = sum_{j=0}^{n-1} grid[0][j]; if n = 1, let S = sum_{i=0}^{m-1} grid[i][0]. Whenever the function returns a result r, r = true if and only if health - S >= 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. Assume m = 1 or n = 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hline : m = 1 ∨ n = 1) :
    ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔
        (m = 1 ∧ 1 ≤ health.val - rowSum grid 0 n) ∨
          (n = 1 ∧ 1 ≤ health.val - colSum grid m 0)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hline : m = 1 ∨ n = 1), ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔
        (m = 1 ∧ 1 ≤ health.val - rowSum grid 0 n) ∨
          (n = 1 ∧ 1 ≤ health.val - colSum grid m 0))) := by
  sorry

/-- If there exists a finite sequence of distinct cells p_0, ..., p_k such that p_0 = (0,0), p_k = (m-1,n-1), consecutive cells share an edge, and grid[p_t.0][p_t.1] = 0 for every t with 0 <= t <= k, then whenever the function returns a result r, r = true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val)
    (hwitness : ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ ZeroWalk grid ps) :
    ∀ r : Bool, find_safe_walk grid health = ok r → r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val)
    (hwitness : ∃ ps : List (ℕ × ℕ), Walk m n ps ∧ ZeroWalk grid ps), ∀ r : Bool, find_safe_walk grid health = ok r → r = true) := by
  sorry

/-- Let gridT be the n by m matrix defined by gridT[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. For every health >= 1, find_safe_walk(grid, health) and find_safe_walk(gridT, health) return the same Boolean result.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_9 (grid gridT : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hshape : Shape grid m n) (hT : IsTranspose gridT grid m n) (health : I64)
    (hhealth : 1 ≤ health.val) :
    find_safe_walk grid health = find_safe_walk gridT health := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hshape : Shape grid m n) (hT : IsTranspose gridT grid m n) (health : I64)
    (hhealth : 1 ≤ health.val), find_safe_walk grid health = find_safe_walk gridT health) := by
  sorry

/-- Let gridR be the m by n matrix defined by gridR[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. For every health >= 1, find_safe_walk(grid, health) and find_safe_walk(gridR, health) return the same Boolean result.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. -/
theorem spec_10 (grid gridR : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hshape : Shape grid m n) (hR : IsRot180 gridR grid m n) (health : I64)
    (hhealth : 1 ≤ health.val) :
    find_safe_walk grid health = find_safe_walk gridR health := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Slice (alloc.vec.Vec I64)) (m n : ℕ)
    (hshape : Shape grid m n) (hR : IsRot180 gridR grid m n) (health : I64)
    (hhealth : 1 ≤ health.val), find_safe_walk grid health = find_safe_walk gridR health) := by
  sorry

/-- Let C = grid[0][0] + grid[1][1] + min(grid[0][1], grid[1][0]). Whenever the function returns a result r, r = true if and only if health - C >= 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, every row of grid has length n, m*n >= 2, health >= 1, and for every 0 <= i < m and 0 <= j < n, grid[i][j] is either 0 or 1. Assume m = 2 and n = 2. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hm : m = 2) (hn : n = 2) :
    ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔ 1 ≤ health.val - cost2x2 grid) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (m n : ℕ) (health : I64)
    (hshape : Shape grid m n) (hhealth : 1 ≤ health.val) (hm : m = 2) (hn : n = 2), ∀ r : Bool, find_safe_walk grid health = ok r →
      (r = true ↔ 1 ≤ health.val - cost2x2 grid)) := by
  sorry

end AegisSpec.FindSafeWalk
