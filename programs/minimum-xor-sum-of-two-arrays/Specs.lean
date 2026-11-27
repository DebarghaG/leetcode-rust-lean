import Aegis.MinimumXorSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumXorSum.minimum_xor_sum`

LeetCode problem `minimum-xor-sum-of-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumXorSum

namespace AegisSpec.MinimumXorSum

def elem (xs : List Int) (i : Nat) : Int := xs.getD i 0

def bxor (a b : Int) : Int := ((Nat.xor a.toNat b.toNat : Nat) : Int)

def sumList (xs : List Int) : Int := xs.foldl (fun acc x => acc + x) 0

def xorSum (xs ys : List Int) : Int :=
  sumList (xs.zipWith (fun a b => bxor a b) ys)

/-- The function returns a result r (it does not fail) and r = min { sum_{i=0}^{n-1} (nums1[i] XOR nums2[sigma(i)]) | sigma is a permutation of {0,1,...,n-1} }. Here XOR is bitwise exclusive-or of two nonnegative integers. Equivalently, r is the smallest possible XOR sum over all rearrangements of nums2.
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_1 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∃ r, minimum_xor_sum nums1 nums2 = ok r ∧
      (∀ ys, ys.Perm nums2.val → r.val ≤ xorSum nums1.val ys) ∧
      (∃ ys, ys.Perm nums2.val ∧ r.val = xorSum nums1.val ys) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∃ r, minimum_xor_sum nums1 nums2 = ok r ∧
      (∀ ys, ys.Perm nums2.val → r.val ≤ xorSum nums1.val ys) ∧
      (∃ ys, ys.Perm nums2.val ∧ r.val = xorSum nums1.val ys)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, use an out-of-range index, or panic on any input satisfying the preconditions.
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_2 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∃ r, minimum_xor_sum nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∃ r, minimum_xor_sum nums1 nums2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every permutation tau of {0,1,...,n-1}, r <= sum_{i=0}^{n-1} (nums1[i] XOR nums2[tau(i)]).
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_3 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      ∀ ys, ys.Perm nums2.val → r.val ≤ xorSum nums1.val ys := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      ∀ ys, ys.Perm nums2.val → r.val ≤ xorSum nums1.val ys) := by
  sorry

/-- Whenever the function returns a result r, there exists a permutation sigma of {0,1,...,n-1} such that r = sum_{i=0}^{n-1} (nums1[i] XOR nums2[sigma(i)]).
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_4 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      ∃ ys, ys.Perm nums2.val ∧ r.val = xorSum nums1.val ys := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      ∃ ys, ys.Perm nums2.val ∧ r.val = xorSum nums1.val ys) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_5 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r → 0 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r, minimum_xor_sum nums1 nums2 = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = nums1[0] XOR nums2[0].
  Preconditions: Let n = len(nums1). n = len(nums2), n = 1, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_6 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn : n = 1)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      r.val = bxor (elem nums1.val 0) (elem nums2.val 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn : n = 1)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      r.val = bxor (elem nums1.val 0) (elem nums2.val 0)) := by
  sorry

/-- Whenever the function returns a result r, r = min( (nums1[0] XOR nums2[0]) + (nums1[1] XOR nums2[1]), (nums1[0] XOR nums2[1]) + (nums1[1] XOR nums2[0]) ), where min denotes the smaller of the two integers.
  Preconditions: Let n = len(nums1). n = len(nums2), n = 2, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_7 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn : n = 2)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      r.val = min (bxor (elem nums1.val 0) (elem nums2.val 0) +
                     bxor (elem nums1.val 1) (elem nums2.val 1))
                  (bxor (elem nums1.val 0) (elem nums2.val 1) +
                     bxor (elem nums1.val 1) (elem nums2.val 0)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn : n = 2)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r, minimum_xor_sum nums1 nums2 = ok r →
      r.val = min (bxor (elem nums1.val 0) (elem nums2.val 0) +
                     bxor (elem nums1.val 1) (elem nums2.val 1))
                  (bxor (elem nums1.val 0) (elem nums2.val 1) +
                     bxor (elem nums1.val 1) (elem nums2.val 0))) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} nums2[i].
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7, and for every i with 0 <= i < n, nums1[i] = 0. -/
theorem spec_8 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hz1 : ∀ i, i < n → elem nums1.val i = 0) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = sumList nums2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hz1 : ∀ i, i < n → elem nums1.val i = 0), ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = sumList nums2.val) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} nums1[i].
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7, and for every i with 0 <= i < n, nums2[i] = 0. -/
theorem spec_9 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hz2 : ∀ i, i < n → elem nums2.val i = 0) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = sumList nums1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hz2 : ∀ i, i < n → elem nums2.val i = 0), ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = sumList nums1.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7, and there exists a permutation sigma of {0,1,...,n-1} such that nums2[sigma(i)] = nums1[i] for every i with 0 <= i < n. -/
theorem spec_10 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hperm : nums1.val.Perm nums2.val) :
    ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hperm : nums1.val.Perm nums2.val), ∀ r, minimum_xor_sum nums1 nums2 = ok r → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r on (nums1, nums2) and a result r' on (nums1, nums2'), r = r'.
  Preconditions: Let n = len(nums1). Assume n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. Let nums2' be a slice of length n such that for some permutation pi of {0,1,...,n-1}, nums2'[i] = nums2[pi(i)] for every i with 0 <= i < n; thus nums2' is a reordering of nums2. -/
theorem spec_11 (nums1 nums2 nums2' : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hn2' : nums2'.val.length = n) (hperm : nums2'.val.Perm nums2.val) :
    ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums1 nums2' = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 nums2' : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hn2' : nums2'.val.length = n) (hperm : nums2'.val.Perm nums2.val), ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums1 nums2' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r on (nums1, nums2) and a result r' on (nums1', nums2), r = r'.
  Preconditions: Let n = len(nums1). Assume n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. Let nums1' be a slice of length n such that for some permutation pi of {0,1,...,n-1}, nums1'[i] = nums1[pi(i)] for every i with 0 <= i < n; thus nums1' is a reordering of nums1. -/
theorem spec_12 (nums1 nums1' nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hn1' : nums1'.val.length = n) (hperm : nums1'.val.Perm nums1.val) :
    ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums1' nums2 = ok r' → r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums1' nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7)
    (hn1' : nums1'.val.length = n) (hperm : nums1'.val.Perm nums1.val), ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums1' nums2 = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r on (nums1, nums2) and a result r' on (nums2, nums1), r = r'.
  Preconditions: Let n = len(nums1). n = len(nums2), 1 <= n <= 14, and for every i with 0 <= i < n, 0 <= nums1[i] <= 10^7 and 0 <= nums2[i] <= 10^7. -/
theorem spec_13 (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7) :
    ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums2 nums1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (n : Nat)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 14)
    (hb1 : ∀ i, i < n → 0 ≤ elem nums1.val i ∧ elem nums1.val i ≤ 10 ^ 7)
    (hb2 : ∀ i, i < n → 0 ≤ elem nums2.val i ∧ elem nums2.val i ≤ 10 ^ 7), ∀ r r', minimum_xor_sum nums1 nums2 = ok r →
      minimum_xor_sum nums2 nums1 = ok r' → r.val = r'.val) := by
  sorry

end AegisSpec.MinimumXorSum
