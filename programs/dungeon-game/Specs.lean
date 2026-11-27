import Aegis.CalculateMinimumHp.Code.Funs

/-!
# Specifications of `Aegis.CalculateMinimumHp.calculate_minimum_hp`

LeetCode problem `dungeon-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CalculateMinimumHp (calculate_minimum_hp)

namespace AegisSpec.CalculateMinimumHp

def grid (dungeon : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  dungeon.val.map (fun row => row.val.map (fun x => x.val))

def cell (g : List (List ℤ)) (i j : ℕ) : ℤ := ((g[i]?).bind (fun row => row[j]?)).getD 0

abbrev Pos := ℕ × ℕ

def IsPath (m n : ℕ) (P : List Pos) : Prop :=
  P.length = m + n - 1 ∧
    P[0]? = some (0, 0) ∧
    P[m + n - 2]? = some (m - 1, n - 1) ∧
    (∀ p ∈ P, p.1 < m ∧ p.2 < n) ∧
    (∀ p q : Pos, (p, q) ∈ P.zip P.tail →
      (q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 ∧ q.2 = p.2 + 1))

def Psum (g : List (List ℤ)) (P : List Pos) (k : ℕ) : ℤ :=
  ((P.take (k + 1)).map (fun p => cell g p.1 p.2)).sum

def Admissible (g : List (List ℤ)) (m n : ℕ) (H : ℤ) : Prop :=
  ∃ P, IsPath m n P ∧ ∀ k, k < m + n - 1 → 0 < H + Psum g P k

/-- Whenever the function returns a result r, let H* be the least integer H with H >= 1 for which there exists a legal path P from (0,0) to (m-1,n-1) moving only right or down such that, for every k with 0 <= k < m+n-1, H + S_P(k) > 0, where S_P(k) is the sum of dungeon over the first k+1 rooms of P (including the starting room and the ending room). Then r = H*.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_1 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      IsLeast {H : ℤ | 1 ≤ H ∧ Admissible (grid dungeon) m n H} r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      IsLeast {H : ℤ | 1 ≤ H ∧ Admissible (grid dungeon) m n H} r.val) := by
  sorry

/-- The function does not fail on the stated inputs: there exists an integer r such that calculate_minimum_hp(dungeon) returns r.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_2 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∃ r : Std.I64, calculate_minimum_hp dungeon = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∃ r : Std.I64, calculate_minimum_hp dungeon = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= 1 + 1000 * (m + n - 1).
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_3 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      r.val ≤ 1 + 1000 * ((m : ℤ) + (n : ℤ) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      r.val ≤ 1 + 1000 * ((m : ℤ) + (n : ℤ) - 1)) := by
  sorry

/-- Whenever the function returns a result r, r >= max(1, 1 - dungeon[0][0]).
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_4 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      max 1 (1 - cell (grid dungeon) 0 0) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      max 1 (1 - cell (grid dungeon) 0 0) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a legal path P from (0,0) to (m-1,n-1) moving only right or down such that for every k with 0 <= k < m+n-1, r + S_P(k) > 0, where S_P(k) is the sum of dungeon over the first k+1 rooms of P.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_5 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      ∃ P, IsPath m n P ∧ ∀ k, k < m + n - 1 → 0 < r.val + Psum (grid dungeon) P k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      ∃ P, IsPath m n P ∧ ∀ k, k < m + n - 1 → 0 < r.val + Psum (grid dungeon) P k) := by
  sorry

/-- Whenever the function returns a result r, for every integer H with 1 <= H < r and every legal path P from (0,0) to (m-1,n-1) moving only right or down, there exists k with 0 <= k < m+n-1 such that H + S_P(k) <= 0, where S_P(k) is the sum of dungeon over the first k+1 rooms of P.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_6 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      ∀ H : ℤ, 1 ≤ H → H < r.val →
        ∀ P, IsPath m n P → ∃ k, k < m + n - 1 ∧ H + Psum (grid dungeon) P k ≤ 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      ∀ H : ℤ, 1 ≤ H → H < r.val →
        ∀ P, IsPath m n P → ∃ k, k < m + n - 1 ∧ H + Psum (grid dungeon) P k ≤ 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if there exists a legal path P from (0,0) to (m-1,n-1) moving only right or down such that S_P(k) >= 0 for every k with 0 <= k < m+n-1, where S_P(k) is the sum of dungeon over the first k+1 rooms of P.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_7 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      (r.val = 1 ↔
        ∃ P, IsPath m n P ∧ ∀ k, k < m + n - 1 → 0 ≤ Psum (grid dungeon) P k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r →
      (r.val = 1 ↔
        ∃ P, IsPath m n P ∧ ∀ k, k < m + n - 1 → 0 ≤ Psum (grid dungeon) P k)) := by
  sorry

/-- Whenever the function returns a result r with r > 1, for every legal path P from (0,0) to (m-1,n-1) moving only right or down, if r + S_P(k) > 0 for every k with 0 <= k < m+n-1, then there exists some k with 0 <= k < m+n-1 such that S_P(k) = 1 - r, where S_P(k) is the sum of dungeon over the first k+1 rooms of P.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers. Let m = len(dungeon) and n = len(dungeon[0]). Then 1 <= m <= 200, 1 <= n <= 200, for every i with 0 <= i < m, len(dungeon[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= dungeon[i][j] <= 1000. -/
theorem spec_8 (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000) :
    ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r → 1 < r.val →
      ∀ P, IsPath m n P →
        (∀ k, k < m + n - 1 → 0 < r.val + Psum (grid dungeon) P k) →
          ∃ k, k < m + n - 1 ∧ Psum (grid dungeon) P k = 1 - r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (dungeon : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000), ∀ r : Std.I64, calculate_minimum_hp dungeon = ok r → 1 < r.val →
      ∀ P, IsPath m n P →
        (∀ k, k < m + n - 1 → 0 < r.val + Psum (grid dungeon) P k) →
          ∃ k, k < m + n - 1 ∧ Psum (grid dungeon) P k = 1 - r.val) := by
  sorry

/-- If calculate_minimum_hp(dungeon) returns r and calculate_minimum_hp(dungeon') returns r', then r' <= r.
  Preconditions: Both dungeon and dungeon' are nonempty slices of nonempty vectors of 64-bit integers with the same number of rows m and columns n. For both grids, 1 <= m <= 200, 1 <= n <= 200, every row has length n, and every entry lies in [-1000,1000]. Also, for every i,j with 0 <= i < m and 0 <= j < n, dungeon'[i][j] >= dungeon[i][j]. -/
theorem spec_9 (dungeon dungeon' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m) (hm' : dungeon'.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hrows' : ∀ row ∈ grid dungeon', row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000)
    (hbound' : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon') i j ∧ cell (grid dungeon') i j ≤ 1000)
    (hle : ∀ i j, i < m → j < n → cell (grid dungeon) i j ≤ cell (grid dungeon') i j) :
    ∀ (r r' : Std.I64), calculate_minimum_hp dungeon = ok r →
      calculate_minimum_hp dungeon' = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (dungeon dungeon' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m) (hm' : dungeon'.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hrows' : ∀ row ∈ grid dungeon', row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000)
    (hbound' : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon') i j ∧ cell (grid dungeon') i j ≤ 1000)
    (hle : ∀ i j, i < m → j < n → cell (grid dungeon) i j ≤ cell (grid dungeon') i j), ∀ (r r' : Std.I64), calculate_minimum_hp dungeon = ok r →
      calculate_minimum_hp dungeon' = ok r' → r'.val ≤ r.val) := by
  sorry

/-- If calculate_minimum_hp(dungeon) returns r and calculate_minimum_hp(dungeon') returns r', then r = r'.
  Preconditions: dungeon is a nonempty slice of nonempty vectors of 64-bit integers with m = len(dungeon), n = len(dungeon[0]), 1 <= m,n <= 200, every row length n, and every entry in [-1000,1000]. dungeon' is the transpose of dungeon: it has n rows and m columns, every row length m, and for every i,j with 0 <= i < m and 0 <= j < n, dungeon'[j][i] = dungeon[i][j]. -/
theorem spec_10 (dungeon dungeon' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000)
    (hm' : dungeon'.val.length = n)
    (hrows' : ∀ row ∈ grid dungeon', row.length = m)
    (htrans : ∀ i j, i < m → j < n → cell (grid dungeon') j i = cell (grid dungeon) i j) :
    ∀ (r r' : Std.I64), calculate_minimum_hp dungeon = ok r →
      calculate_minimum_hp dungeon' = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (dungeon dungeon' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hm : dungeon.val.length = m)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 200) (hn1 : 1 ≤ n) (hn2 : n ≤ 200)
    (hrows : ∀ row ∈ grid dungeon, row.length = n)
    (hbound : ∀ i j, i < m → j < n →
      -1000 ≤ cell (grid dungeon) i j ∧ cell (grid dungeon) i j ≤ 1000)
    (hm' : dungeon'.val.length = n)
    (hrows' : ∀ row ∈ grid dungeon', row.length = m)
    (htrans : ∀ i j, i < m → j < n → cell (grid dungeon') j i = cell (grid dungeon) i j), ∀ (r r' : Std.I64), calculate_minimum_hp dungeon = ok r →
      calculate_minimum_hp dungeon' = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.CalculateMinimumHp
