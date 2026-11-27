import Aegis.DiagonalPrime.Code.Funs

/-!
# Specifications of `Aegis.DiagonalPrime.diagonal_prime`

LeetCode problem `prime-in-diagonal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.DiagonalPrime

def vecContents (v : alloc.vec.Vec Std.I64) : List ℤ :=
  v.val.map (fun x => x.val)

def rowOf (nums : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List ℤ :=
  match nums.val[i]? with
  | none => []
  | some row => vecContents row

def entry (nums : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
  (rowOf nums i)[j]?.getD 0

def IsPrime (v : ℤ) : Prop := 1 < v ∧ ¬ ∃ d : ℤ, 2 ≤ d ∧ d < v ∧ d ∣ v

def OnDiagonal (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (v : ℤ) : Prop :=
  ∃ i : Nat, i < n ∧ (entry nums i i = v ∨ entry nums i (n - 1 - i) = v)

/-- Whenever the function returns a result r, the following holds. If there is no integer v such that v lies on at least one diagonal of nums and v is prime, then r = 0. Otherwise, r is prime, r lies on at least one diagonal of nums, and for every v that lies on at least one diagonal of nums, if v is prime then v <= r. Here v lies on at least one diagonal of nums iff there exists i with 0 <= i < n and (nums[i][i] = v or nums[i][n - 1 - i] = v); and v is prime iff v > 1 and there is no integer d with 2 <= d < v such that d divides v.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_1 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    if ∃ v : ℤ, OnDiagonal nums n v ∧ IsPrime v then
      IsPrime r.val ∧ OnDiagonal nums n r.val ∧
        ∀ v : ℤ, OnDiagonal nums n v → IsPrime v → v ≤ r.val
    else r.val = 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), if ∃ v : ℤ, OnDiagonal nums n v ∧ IsPrime v then
      IsPrime r.val ∧ OnDiagonal nums n r.val ∧
        ∀ v : ℤ, OnDiagonal nums n v → IsPrime v → v ≤ r.val
    else r.val = 0) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, or access an index out of bounds.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_2 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000) :
    ∃ r : Std.I64, Aegis.DiagonalPrime.diagonal_prime nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000), ∃ r : Std.I64, Aegis.DiagonalPrime.diagonal_prime nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have r = 0 if and only if for every i with 0 <= i < n, nums[i][i] is not prime and nums[i][n - 1 - i] is not prime. Here v is prime iff v > 1 and there is no integer d with 2 <= d < v such that d divides v.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_3 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    (r.val = 0 ↔
      ∀ i : Nat, i < n → ¬ IsPrime (entry nums i i) ∧ ¬ IsPrime (entry nums i (n - 1 - i))) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), (r.val = 0 ↔
      ∀ i : Nat, i < n → ¬ IsPrime (entry nums i i) ∧ ¬ IsPrime (entry nums i (n - 1 - i)))) := by
  sorry

/-- Whenever the function returns a result r with r != 0, r is prime, where v is prime iff v > 1 and there is no integer d with 2 <= d < v such that d divides v.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_4 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    r.val ≠ 0 → IsPrime r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), r.val ≠ 0 → IsPrime r.val) := by
  sorry

/-- Whenever the function returns a result r with r != 0, there exists i with 0 <= i < n such that nums[i][i] = r or nums[i][n - 1 - i] = r.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_5 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    r.val ≠ 0 →
      ∃ i : Nat, i < n ∧ (entry nums i i = r.val ∨ entry nums i (n - 1 - i) = r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), r.val ≠ 0 →
      ∃ i : Nat, i < n ∧ (entry nums i i = r.val ∨ entry nums i (n - 1 - i) = r.val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n and every v such that v = nums[i][i] or v = nums[i][n - 1 - i], if v is prime then v <= r. Here v is prime iff v > 1 and there is no integer d with 2 <= d < v such that d divides v.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_6 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    ∀ i : Nat, i < n → ∀ v : ℤ,
      (v = entry nums i i ∨ v = entry nums i (n - 1 - i)) → IsPrime v → v ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), ∀ i : Nat, i < n → ∀ v : ℤ,
      (v = entry nums i i ∨ v = entry nums i (n - 1 - i)) → IsPrime v → v ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 4000000.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_7 (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ 4000000 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r), 0 ≤ r.val ∧ r.val ≤ 4000000) := by
  sorry

/-- Let B be the n by n matrix defined by B[i][j] = nums[i][n - 1 - j] for all 0 <= i < n and 0 <= j < n. Whenever the function returns r on input nums and returns s on input B, r = s.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_8 (nums B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r s : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hBn : n = B.val.length)
    (hB_rows : ∀ i : Nat, i < n → (rowOf B i).length = n)
    (hB : ∀ i j : Nat, i < n → j < n → entry B i j = entry nums i (n - 1 - j))
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hs : Aegis.DiagonalPrime.diagonal_prime B = ok s) :
    r.val = s.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r s : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hBn : n = B.val.length)
    (hB_rows : ∀ i : Nat, i < n → (rowOf B i).length = n)
    (hB : ∀ i j : Nat, i < n → j < n → entry B i j = entry nums i (n - 1 - j))
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hs : Aegis.DiagonalPrime.diagonal_prime B = ok s), r.val = s.val) := by
  sorry

/-- Let B be the n by n matrix defined by B[i][j] = nums[j][i] for all 0 <= i < n and 0 <= j < n. Whenever the function returns r on input nums and returns s on input B, r = s.
  Preconditions: Let n = len(nums). The input satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. -/
theorem spec_9 (nums B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r s : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hBn : n = B.val.length)
    (hB_rows : ∀ i : Nat, i < n → (rowOf B i).length = n)
    (hB : ∀ i j : Nat, i < n → j < n → entry B i j = entry nums j i)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hs : Aegis.DiagonalPrime.diagonal_prime B = ok s) :
    r.val = s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums B : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r s : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hBn : n = B.val.length)
    (hB_rows : ∀ i : Nat, i < n → (rowOf B i).length = n)
    (hB : ∀ i j : Nat, i < n → j < n → entry B i j = entry nums j i)
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hs : Aegis.DiagonalPrime.diagonal_prime B = ok s), r.val = s.val) := by
  sorry

/-- Whenever the function returns r on input nums and returns r' on input nums', r = r'.
  Preconditions: Let n = len(nums). nums satisfies: 1 <= n <= 300; for every i with 0 <= i < n, len(nums[i]) = n; and for every i, j with 0 <= i < n and 0 <= j < n, 1 <= nums[i][j] <= 4000000. Let nums' be another slice of n vectors, each of length n, with 1 <= nums'[i][j] <= 4000000 for all 0 <= i, j < n, and such that for every i with 0 <= i < n, nums'[i][i] = nums[i][i] and nums'[i][n - 1 - i] = nums[i][n - 1 - i]. -/
theorem spec_10 (nums nums' : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r r' : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hn' : n = nums'.val.length)
    (h_rows' : ∀ i : Nat, i < n → (rowOf nums' i).length = n)
    (h_bounds' : ∀ i j : Nat, i < n → j < n →
      1 ≤ entry nums' i j ∧ entry nums' i j ≤ 4000000)
    (h_diag : ∀ i : Nat, i < n →
      entry nums' i i = entry nums i i ∧
        entry nums' i (n - 1 - i) = entry nums i (n - 1 - i))
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hr' : Aegis.DiagonalPrime.diagonal_prime nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (r r' : Std.I64)
    (hn : n = nums.val.length)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 300)
    (h_rows : ∀ i : Nat, i < n → (rowOf nums i).length = n)
    (h_bounds : ∀ i j : Nat, i < n → j < n → 1 ≤ entry nums i j ∧ entry nums i j ≤ 4000000)
    (hn' : n = nums'.val.length)
    (h_rows' : ∀ i : Nat, i < n → (rowOf nums' i).length = n)
    (h_bounds' : ∀ i j : Nat, i < n → j < n →
      1 ≤ entry nums' i j ∧ entry nums' i j ≤ 4000000)
    (h_diag : ∀ i : Nat, i < n →
      entry nums' i i = entry nums i i ∧
        entry nums' i (n - 1 - i) = entry nums i (n - 1 - i))
    (hr : Aegis.DiagonalPrime.diagonal_prime nums = ok r)
    (hr' : Aegis.DiagonalPrime.diagonal_prime nums' = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.DiagonalPrime
