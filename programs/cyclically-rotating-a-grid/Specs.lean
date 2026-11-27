import Aegis.RotateGrid.Code.Funs

/-!
# Specifications of `Aegis.RotateGrid.rotate_grid`

LeetCode problem `cyclically-rotating-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.RotateGrid

namespace AegisSpec.RotateGrid

def nrows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat := grid.val.length

def rowLen? (g : List (alloc.vec.Vec Std.I64)) (i : Nat) : Option Nat :=
  (g[i]?).map (fun row => row.val.length)

def cell? (g : List (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
  match g[i]? with
  | none => none
  | some row => (row.val[j]?).map (fun x => x.val)

def SameCell (g₁ : List (alloc.vec.Vec Std.I64)) (i₁ j₁ : Nat)
    (g₂ : List (alloc.vec.Vec Std.I64)) (i₂ j₂ : Nat) : Prop :=
  ∃ v : Int, cell? g₁ i₁ j₁ = some v ∧ cell? g₂ i₂ j₂ = some v

def depth (m n i j : Nat) : Nat :=
  Nat.min (Nat.min i (m - 1 - i)) (Nat.min j (n - 1 - j))

def ringLen (m n d : Nat) : Nat := 2 * (m + n - 4 * d) - 4

def ringIdx (m n d t : Nat) : Nat × Nat :=
  let right := n - 1 - d
  let bottom := m - 1 - d
  let seg0 := n - 2 * d
  let seg1 := seg0 + (m - 1 - 2 * d)
  let seg2 := seg1 + (n - 1 - 2 * d)
  if t < seg0 then (d, d + t)
  else if t < seg1 then (d + 1 + (t - seg0), right)
  else if t < seg2 then (bottom, right - 1 - (t - seg1))
  else (bottom - 1 - (t - seg2), d)

def ringPos (m n i j : Nat) : Nat :=
  let d := depth m n i j
  let right := n - 1 - d
  let bottom := m - 1 - d
  let seg0 := n - 2 * d
  let seg1 := seg0 + (m - 1 - 2 * d)
  let seg2 := seg1 + (n - 1 - 2 * d)
  if i = d then j - d
  else if j = right then seg0 + (i - d - 1)
  else if i = bottom then seg1 + (right - 1 - j)
  else seg2 + (bottom - 1 - i)

def ringShift (L t k : Nat) : Nat := (t + k) % L

def ringCells (m n d : Nat) : List (Nat × Nat) :=
  (List.range (ringLen m n d)).map (fun t => ringIdx m n d t)

def ringVals (g : List (alloc.vec.Vec Std.I64)) (m n d : Nat) : List (Option Int) :=
  (ringCells m n d).map (fun p => cell? g p.1 p.2)

/-- Let m = len(grid) and n = len(grid[0]). For each integer d with 0 <= d < min(m,n)/2, let L_d = 2*(m+n-4*d)-4 and let C_d(0),...,C_d(L_d-1) be the cells of the ring R_d = {(i,j) : 0<=i<m, 0<=j<n, min(i,m-1-i,j,n-1-j)=d} enumerated clockwise starting at (d,d): first (d,j) for j=d,d+1,...,n-1-d; then (i,n-1-d) for i=d+1,...,m-1-d; then (m-1-d,j) for j=n-2-d,n-3-d,...,d; then (i,d) for i=m-2-d,m-3-d,...,d+1. The function returns a matrix r with len(r)=m and len(r[i])=n for every i, and for every 0 <= i < m and 0 <= j < n: if d(i,j)=min(i,m-1-i,j,n-1-j) < min(m,n)/2, let t be the unique index with C_{d(i,j)}(t)=(i,j); then r[i][j] = grid[row][col] where (row,col)=C_{d(i,j)}((t+k) mod L_{d(i,j)}). If d(i,j) >= min(m,n)/2, then r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. (The original problem also requires m and n even; this specification uses the natural closed-ring generalization that also covers the supplied 3x3 example: cells with min(i,m-1-i,j,n-1-j) >= min(m,n)/2 are left fixed.) -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      r.val.length = m ∧
      (∀ (i : Nat), i < m → rowLen? r.val i = some n) ∧

      (∀ (i j : Nat), i < m → j < n → depth m n i j < Nat.min m n / 2 →
        ∀ (t : Nat), ringIdx m n (depth m n i j) t = (i, j) →
          SameCell r.val i j grid.val
            (ringIdx m n (depth m n i j)
              (ringShift (ringLen m n (depth m n i j)) t k.val.toNat)).1
            (ringIdx m n (depth m n i j)
              (ringShift (ringLen m n (depth m n i j)) t k.val.toNat)).2) ∧

      (∀ (i j : Nat), i < m → j < n → Nat.min m n / 2 ≤ depth m n i j →
        SameCell r.val i j grid.val i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      r.val.length = m ∧
      (∀ (i : Nat), i < m → rowLen? r.val i = some n) ∧

      (∀ (i j : Nat), i < m → j < n → depth m n i j < Nat.min m n / 2 →
        ∀ (t : Nat), ringIdx m n (depth m n i j) t = (i, j) →
          SameCell r.val i j grid.val
            (ringIdx m n (depth m n i j)
              (ringShift (ringLen m n (depth m n i j)) t k.val.toNat)).1
            (ringIdx m n (depth m n i j)
              (ringShift (ringLen m n (depth m n i j)) t k.val.toNat)).2) ∧

      (∀ (i j : Nat), i < m → j < n → Nat.min m n / 2 ≤ depth m n i j →
        SameCell r.val i j grid.val i j)) := by
  sorry

/-- The function returns a matrix r such that len(r) = m and len(r[i]) = n for every 0 <= i < m. In other words, the result has exactly the same m-by-n shape as the input grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      r.val.length = m ∧
      ∀ (i : Nat), i < m → rowLen? r.val i = some n := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      r.val.length = m ∧
      ∀ (i : Nat), i < m → rowLen? r.val i = some n) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result matrix r; it does not fail, panic, or overflow.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), rotate_grid grid k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), rotate_grid grid k = ok r) := by
  sorry

/-- For every integer d with 0 <= d < min(m,n)/2, let R_d = {(i,j) : 0<=i<m, 0<=j<n, min(i,m-1-i,j,n-1-j)=d}. The multiset of values { r[i][j] : (i,j) in R_d } is equal to the multiset of values { grid[i][j] : (i,j) in R_d }.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (d : Nat), d < Nat.min m n / 2 →
        List.Perm (ringVals r.val m n d) (ringVals grid.val m n d) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (d : Nat), d < Nat.min m n / 2 →
        List.Perm (ringVals r.val m n d) (ringVals grid.val m n d)) := by
  sorry

/-- For each d with 0 <= d < min(m,n)/2, use the clockwise enumeration C_d and length L_d from the main specification. Define A_d(t)=grid at C_d(t) and B_d(t)=r at C_d(t) for 0<=t<L_d. There exists an integer s_d with 0 <= s_d < L_d such that B_d(t) = A_d((t+s_d) mod L_d) for every 0 <= t < L_d. In fact s_d = k mod L_d.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (d : Nat), d < Nat.min m n / 2 →
        ∃ s : Nat,
          s < ringLen m n d ∧
          s = k.val.toNat % ringLen m n d ∧
          ∀ (t : Nat), t < ringLen m n d →
            SameCell r.val (ringIdx m n d t).1 (ringIdx m n d t).2 grid.val
              (ringIdx m n d (ringShift (ringLen m n d) t s)).1
              (ringIdx m n d (ringShift (ringLen m n d) t s)).2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (d : Nat), d < Nat.min m n / 2 →
        ∃ s : Nat,
          s < ringLen m n d ∧
          s = k.val.toNat % ringLen m n d ∧
          ∀ (t : Nat), t < ringLen m n d →
            SameCell r.val (ringIdx m n d t).1 (ringIdx m n d t).2 grid.val
              (ringIdx m n d (ringShift (ringLen m n d) t s)).1
              (ringIdx m n d (ringShift (ringLen m n d) t s)).2) := by
  sorry

/-- For every d with 0 <= d < min(m,n)/2, if k ≡ k' (mod L_d), where L_d = 2*(m+n-4*d)-4, then for every cell (i,j) in R_d = {(i,j) : min(i,m-1-i,j,n-1-j)=d}, the two calls agree on that cell: rotate_grid(grid,k)[i][j] = rotate_grid(grid,k')[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. Also let k' be an integer with 1 <= k' <= 10^9. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9)
    (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 10 ^ 9) :
    ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid k = ok r →
      rotate_grid grid k' = ok r' →
      ∀ (d : Nat), d < Nat.min m n / 2 →
        k.val % (ringLen m n d : Int) = k'.val % (ringLen m n d : Int) →
        ∀ (i j : Nat), i < m → j < n → depth m n i j = d →
          SameCell r.val i j r'.val i j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9)
    (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 10 ^ 9), ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid k = ok r →
      rotate_grid grid k' = ok r' →
      ∀ (d : Nat), d < Nat.min m n / 2 →
        k.val % (ringLen m n d : Int) = k'.val % (ringLen m n d : Int) →
        ∀ (i j : Nat), i < m → j < n → depth m n i j = d →
          SameCell r.val i j r'.val i j) := by
  sorry

/-- Let r1 = rotate_grid(grid,a), let r2 = rotate_grid(r1,b), and let r3 = rotate_grid(grid,a+b). Then r2 = r3 as matrices (same dimensions and r2[i][j] = r3[i][j] for every 0 <= i < m and 0 <= j < n).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n. Let a and b be integers with 1 <= a,b and a+b <= 10^9. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec Std.I64)) (ka kb kc : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (ha1 : 1 ≤ ka.val) (hb1 : 1 ≤ kb.val)
    (hsum : ka.val + kb.val ≤ 10 ^ 9)
    (hkc : kc.val = ka.val + kb.val) :
    ∀ (r1 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid ka = ok r1 →
      ∀ (r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
        rotate_grid r1.slice kb = ok r2 →
        ∀ (r3 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
          rotate_grid grid kc = ok r3 → r2.val = r3.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (ka kb kc : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (ha1 : 1 ≤ ka.val) (hb1 : 1 ≤ kb.val)
    (hsum : ka.val + kb.val ≤ 10 ^ 9)
    (hkc : kc.val = ka.val + kb.val), ∀ (r1 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid ka = ok r1 →
      ∀ (r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
        rotate_grid r1.slice kb = ok r2 →
        ∀ (r3 : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
          rotate_grid grid kc = ok r3 → r2.val = r3.val) := by
  sorry

/-- For every 0 <= i < m and 0 <= j < n, the returned value satisfies 1 <= r[i][j] <= 5000.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (i j : Nat), i < m → j < n →
        ∃ v : Int, cell? r.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (i j : Nat), i < m → j < n →
        ∃ v : Int, cell? r.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000) := by
  sorry

/-- For every 0 <= i < m and 0 <= j < n, there exist indices 0 <= i' < m and 0 <= j' < n such that r[i][j] = grid[i'][j']. Moreover, if d(i,j)=min(i,m-1-i,j,n-1-j) < min(m,n)/2, then (i',j') can be chosen in the same ring R_{d(i,j)}; if d(i,j) >= min(m,n)/2, then (i',j')=(i,j).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (i j : Nat), i < m → j < n →
        ∃ (i' j' : Nat),
          i' < m ∧ j' < n ∧
          SameCell r.val i j grid.val i' j' ∧
          (depth m n i j < Nat.min m n / 2 → depth m n i' j' = depth m n i j) ∧
          (Nat.min m n / 2 ≤ depth m n i j → i' = i ∧ j' = j) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      ∀ (i j : Nat), i < m → j < n →
        ∃ (i' j' : Nat),
          i' < m ∧ j' < n ∧
          SameCell r.val i j grid.val i' j' ∧
          (depth m n i j < Nat.min m n / 2 → depth m n i' j' = depth m n i j) ∧
          (Nat.min m n / 2 ≤ depth m n i j → i' = i ∧ j' = j)) := by
  sorry

/-- For every d with 0 <= d < min(m,n)/2, if k ≡ 0 (mod L_d) where L_d = 2*(m+n-4*d)-4, then for every cell (i,j) in R_d = {(i,j) : min(i,m-1-i,j,n-1-j)=d}, r[i][j] = grid[i][j]. In particular, if k is a positive multiple of L_d for every d, then the whole returned matrix equals grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. -/
theorem spec_10
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      (∀ (d : Nat), d < Nat.min m n / 2 → k.val % (ringLen m n d : Int) = 0 →
        ∀ (i j : Nat), i < m → j < n → depth m n i j = d →
          SameCell r.val i j grid.val i j) ∧
      ((∀ (d : Nat), d < Nat.min m n / 2 → k.val % (ringLen m n d : Int) = 0) →
        r.val = grid.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      rotate_grid grid k = ok r ∧
      (∀ (d : Nat), d < Nat.min m n / 2 → k.val % (ringLen m n d : Int) = 0 →
        ∀ (i j : Nat), i < m → j < n → depth m n i j = d →
          SameCell r.val i j grid.val i j) ∧
      ((∀ (d : Nat), d < Nat.min m n / 2 → k.val % (ringLen m n d : Int) = 0) →
        r.val = grid.val)) := by
  sorry

/-- If k ≡ k' (mod L_d) for every d with 0 <= d < min(m,n)/2, where L_d = 2*(m+n-4*d)-4, then rotate_grid(grid,k) = rotate_grid(grid,k') as matrices (same dimensions and equal entry by entry).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m,n <= 50, every row of grid has length n, 1 <= grid[i][j] <= 5000 for all 0 <= i < m and 0 <= j < n, and 1 <= k <= 10^9. Also let k' be an integer with 1 <= k' <= 10^9. -/
theorem spec_11
    (grid : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9)
    (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 10 ^ 9) :
    ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid k = ok r →
      rotate_grid grid k' = ok r' →
      (∀ (d : Nat), d < Nat.min m n / 2 →
        k.val % (ringLen m n d : Int) = k'.val % (ringLen m n d : Int)) →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k k' : Std.I64) (m n : Nat)
    (hm : m = nrows grid) (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hcell : ∀ (i j : Nat) (hi : i < m) (hj : j < n),
      ∃ v : Int, cell? grid.val i j = some v ∧ 1 ≤ v ∧ v ≤ 5000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 9)
    (hk'1 : 1 ≤ k'.val) (hk'2 : k'.val ≤ 10 ^ 9), ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      rotate_grid grid k = ok r →
      rotate_grid grid k' = ok r' →
      (∀ (d : Nat), d < Nat.min m n / 2 →
        k.val % (ringLen m n d : Int) = k'.val % (ringLen m n d : Int)) →
      r.val = r'.val) := by
  sorry

end AegisSpec.RotateGrid
