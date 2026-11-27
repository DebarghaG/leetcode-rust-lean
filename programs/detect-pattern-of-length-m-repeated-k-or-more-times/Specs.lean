import Aegis.ContainsPattern.Code.Funs

/-!
# Specifications of `Aegis.ContainsPattern.contains_pattern`

LeetCode problem `detect-pattern-of-length-m-repeated-k-or-more-times`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ContainsPattern

namespace AegisSpec.ContainsPattern

def elems (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

def elem (arr : Slice Std.I64) (i : ℕ) : ℤ := (elems arr).getD i 0

def toNat (x : Std.I64) : ℕ := x.val.toNat

def BlockRepeated (arr : Slice Std.I64) (m k i : ℕ) : Prop :=
  i + m * k ≤ arr.val.length ∧
    ∀ b : ℕ, b < k → ∀ j : ℕ, j < m → elem arr (i + b * m + j) = elem arr (i + j)

/-- The function returns ok r for some Boolean r and does not fail. Say that the block of length m starting at i is k-repeated when 0 <= i, i + m*k <= L, and for every b with 0 <= b < k and every j with 0 <= j < m, arr[i + b*m + j] = arr[i + j]. Then r = true if and only if there exists an integer i such that the block of length m starting at i is k-repeated; otherwise r = false.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_1 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100) :
    ∃ r : Bool, contains_pattern arr m k = ok r ∧
      (r = true ↔ ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100), ∃ r : Bool, contains_pattern arr m k = ok r ∧
      (r = true ↔ ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i)) := by
  sorry

/-- The function returns ok r for some Boolean r; in particular, it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_2 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100) :
    ∃ r : Bool, contains_pattern arr m k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100), ∃ r : Bool, contains_pattern arr m k = ok r) := by
  sorry

/-- Whenever the function returns ok true, there exists an integer i such that 0 <= i, i + m*k <= L, and for every b with 0 <= b < k and every j with 0 <= j < m, arr[i + b*m + j] = arr[i + j].
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_3 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true) :
    ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true), ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i) := by
  sorry

/-- Whenever the function returns ok false, for every integer i with 0 <= i and i + m*k <= L, there exist b with 0 <= b < k and j with 0 <= j < m such that arr[i + b*m + j] != arr[i + j].
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_4 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok false) :
    ∀ i : ℕ, i + toNat m * toNat k ≤ arr.val.length →
      ∃ b : ℕ, b < toNat k ∧ ∃ j : ℕ, j < toNat m ∧
        elem arr (i + b * toNat m + j) ≠ elem arr (i + j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok false), ∀ i : ℕ, i + toNat m * toNat k ≤ arr.val.length →
      ∃ b : ℕ, b < toNat k ∧ ∃ j : ℕ, j < toNat m ∧
        elem arr (i + b * toNat m + j) ≠ elem arr (i + j)) := by
  sorry

/-- If there exists an integer i such that 0 <= i, i + m*k <= L, and for every b with 0 <= b < k and every j with 0 <= j < m, arr[i + b*m + j] = arr[i + j], then the function returns ok true.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_5 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i) :
    contains_pattern arr m k = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : ∃ i : ℕ, BlockRepeated arr (toNat m) (toNat k) i), contains_pattern arr m k = ok true) := by
  sorry

/-- Whenever the function returns ok true, m*k <= L.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_6 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true) :
    m.val * k.val ≤ (arr.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true), m.val * k.val ≤ (arr.val.length : ℤ)) := by
  sorry

/-- If m*k > L, then the function returns ok false.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_7 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : (arr.val.length : ℤ) < m.val * k.val) :
    contains_pattern arr m k = ok false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : (arr.val.length : ℤ) < m.val * k.val), contains_pattern arr m k = ok false) := by
  sorry

/-- If m*k = L, then the function returns ok true if and only if for every b with 0 <= b < k and every j with 0 <= j < m, arr[b*m + j] = arr[j].
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_8 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : m.val * k.val = (arr.val.length : ℤ)) :
    (contains_pattern arr m k = ok true ↔
      ∀ b : ℕ, b < toNat k → ∀ j : ℕ, j < toNat m →
        elem arr (b * toNat m + j) = elem arr j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : m.val * k.val = (arr.val.length : ℤ)), (contains_pattern arr m k = ok true ↔
      ∀ b : ℕ, b < toNat k → ∀ j : ℕ, j < toNat m →
        elem arr (b * toNat m + j) = elem arr j)) := by
  sorry

/-- If m = 1, then the function returns ok true if and only if there exists an integer i with 0 <= i, i + k <= L, and for every j with 0 <= j < k, arr[i + j] = arr[i].
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_9 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : m.val = 1) :
    (contains_pattern arr m k = ok true ↔
      ∃ i : ℕ, i + toNat k ≤ arr.val.length ∧
        ∀ j : ℕ, j < toNat k → elem arr (i + j) = elem arr i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : m.val = 1), (contains_pattern arr m k = ok true ↔
      ∃ i : ℕ, i + toNat k ≤ arr.val.length ∧
        ∀ j : ℕ, j < toNat k → elem arr (i + j) = elem arr i)) := by
  sorry

/-- If k = 2, then the function returns ok true if and only if there exists an integer i with 0 <= i, i + 2*m <= L, and for every j with 0 <= j < m, arr[i + j] = arr[i + m + j].
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_10 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : k.val = 2) :
    (contains_pattern arr m k = ok true ↔
      ∃ i : ℕ, i + 2 * toNat m ≤ arr.val.length ∧
        ∀ j : ℕ, j < toNat m →
          elem arr (i + j) = elem arr (i + toNat m + j)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : k.val = 2), (contains_pattern arr m k = ok true ↔
      ∃ i : ℕ, i + 2 * toNat m ≤ arr.val.length ∧
        ∀ j : ℕ, j < toNat m →
          elem arr (i + j) = elem arr (i + toNat m + j))) := by
  sorry

/-- If all entries of arr are equal (that is, arr[i] = arr[0] for every i with 0 <= i < L), then the function returns ok true if and only if m*k <= L.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_11 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hconst : ∀ i : ℕ, i < arr.val.length → elem arr i = elem arr 0) :
    (contains_pattern arr m k = ok true ↔
      m.val * k.val ≤ (arr.val.length : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hconst : ∀ i : ℕ, i < arr.val.length → elem arr i = elem arr 0), (contains_pattern arr m k = ok true ↔
      m.val * k.val ≤ (arr.val.length : ℤ))) := by
  sorry

/-- For every integer k' with 2 <= k' <= k, if contains_pattern arr m k returns ok true, then contains_pattern arr m k' returns ok true.
  Preconditions: Let L = len(arr). All indices are 0-based. Assume: L is an integer with 2 <= L <= 100; for every i with 0 <= i < L, arr[i] is an integer with 1 <= arr[i] <= 100; m is an integer with 1 <= m <= 100; k is an integer with 2 <= k <= 100. -/
theorem spec_12 (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true) :
    ∀ k' : Std.I64, 2 ≤ k'.val → k'.val ≤ k.val →
      contains_pattern arr m k' = ok true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64) (m k : Std.I64)
    (hL_lo : 2 ≤ arr.val.length) (hL_hi : arr.val.length ≤ 100)
    (harr : ∀ i : ℕ, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 100)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 100)
    (hk_lo : 2 ≤ k.val) (hk_hi : k.val ≤ 100)
    (h : contains_pattern arr m k = ok true), ∀ k' : Std.I64, 2 ≤ k'.val → k'.val ≤ k.val →
      contains_pattern arr m k' = ok true) := by
  sorry

end AegisSpec.ContainsPattern
