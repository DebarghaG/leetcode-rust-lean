import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `sum-of-k-subarrays-with-length-at-least-m`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSum

structure Selection where

  l : ℕ → ℕ

  r : ℕ → ℕ

def intSum (nums : List Std.I64) (l r : ℕ) : ℤ :=
  ((nums.drop l).take (r - l)).map (fun x => x.val) |>.sum

def selectionSum (nums : List Std.I64) (k : ℕ) (S : Selection) : ℤ :=
  ∑ j ∈ Finset.range k, intSum nums (S.l j) (S.r j)

def IsValidSelection (nums : List Std.I64) (k m : ℕ) (S : Selection) : Prop :=
  (∀ j, j < k → S.l j < S.r j ∧ S.r j ≤ nums.length) ∧
  (∀ j, j < k → S.l j + m ≤ S.r j) ∧
  (∀ j, j + 1 < k → S.r j ≤ S.l (j + 1))

def IsExactSelection (nums : List Std.I64) (k m : ℕ) (S : Selection) : Prop :=
  IsValidSelection nums k m S ∧ ∀ j, j < k → S.r j = S.l j + m

def IsMaxSelectionSum (nums : List Std.I64) (k m : ℕ) (v : ℤ) : Prop :=
  (∀ S, IsValidSelection nums k m S → selectionSum nums k S ≤ v) ∧
  ∃ S, IsValidSelection nums k m S ∧ selectionSum nums k S = v

def IsMaxExactSelectionSum (nums : List Std.I64) (k m : ℕ) (v : ℤ) : Prop :=
  (∀ S, IsExactSelection nums k m S → selectionSum nums k S ≤ v) ∧
  ∃ S, IsExactSelection nums k m S ∧ selectionSum nums k S = v

def positiveSum (nums : List Std.I64) : ℤ :=
  (nums.map (fun x => max x.val 0)).sum

def totalSum (nums : List Std.I64) : ℤ :=
  (nums.map (fun x => x.val)).sum

def EntrywiseLE (a b : List Std.I64) : Prop :=
  ∀ p ∈ a.zip b, p.1.val ≤ p.2.val

/-- Let a valid k-selection be a sequence of k half-open intervals [l_j, r_j) for j = 0,...,k-1 such that 0 <= l_0, l_j < r_j, r_j <= l_{j+1} for every j < k-1, r_{k-1} <= n, and r_j - l_j >= m for every j. Its sum is sum_{j=0}^{k-1} sum_{i=l_j}^{r_j-1} nums[i]. The function returns a result r and r is the maximum of the sums of all valid k-selections.
  Preconditions: Let n = len(nums). The following hold: 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n (equivalently k <= floor(n/m)). -/
theorem spec_1 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∃ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r ∧
      IsMaxSelectionSum nums.val k.val.toNat m.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∃ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r ∧
      IsMaxSelectionSum nums.val k.val.toNat m.val.toNat r.val) := by
  sorry

/-- Under these preconditions, the function returns a result (that is, it does not fail, panic, or overflow).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n. -/
theorem spec_2 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∃ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∃ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r) := by
  sorry

/-- Whenever the function returns a result r, then for every valid k-selection S, the sum of S is at most r. Here a valid k-selection is a sequence of k half-open intervals [l_j, r_j) with 0 <= l_j < r_j <= n, r_j <= l_{j+1} for j < k-1, and r_j - l_j >= m for every j, and its sum is sum_{j=0}^{k-1} sum_{i=l_j}^{r_j-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n. -/
theorem spec_3 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      ∀ S : Selection, IsValidSelection nums.val k.val.toNat m.val.toNat S →
        selectionSum nums.val k.val.toNat S ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      ∀ S : Selection, IsValidSelection nums.val k.val.toNat m.val.toNat S →
        selectionSum nums.val k.val.toNat S ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a valid k-selection S, that is, a sequence of k half-open intervals [l_j, r_j) for j = 0,...,k-1 such that 0 <= l_j < r_j <= n for every j, r_j <= l_{j+1} for every j < k-1, and r_j - l_j >= m for every j, whose sum sum_{j=0}^{k-1} sum_{i=l_j}^{r_j-1} nums[i] is exactly r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n. -/
theorem spec_4 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      ∃ S : Selection, IsValidSelection nums.val k.val.toNat m.val.toNat S ∧
        selectionSum nums.val k.val.toNat S = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      ∃ S : Selection, IsValidSelection nums.val k.val.toNat m.val.toNat S ∧
        selectionSum nums.val k.val.toNat S = r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} max(nums[i], 0).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n. -/
theorem spec_5 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      r.val ≤ positiveSum nums.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      r.val ≤ positiveSum nums.val) := by
  sorry

/-- Whenever the function returns a result r, -10000*n <= r <= 10000*n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; and k*m <= n. -/
theorem spec_6 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      -(10000 * (nums.val.length : ℤ)) ≤ r.val ∧
        r.val ≤ 10000 * (nums.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ)), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      -(10000 * (nums.val.length : ℤ)) ≤ r.val ∧
        r.val ≤ 10000 * (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; k*m <= n; and k*m = n. -/
theorem spec_7 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hkm_eq : k.val * m.val = (nums.val.length : ℤ)) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      r.val = totalSum nums.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hkm_eq : k.val * m.val = (nums.val.length : ℤ)), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      r.val = totalSum nums.val) := by
  sorry

/-- Whenever the function returns a result r, r is the maximum of the sums of all valid k-selections whose every chosen interval has length exactly m.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 2000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < n; 1 <= k; 1 <= m <= 3; k*m <= n; and nums[i] <= 0 for every i with 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hnonpos : ∀ x ∈ nums.val, x.val ≤ 0) :
    ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      IsMaxExactSelectionSum nums.val k.val.toNat m.val.toNat r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hnonpos : ∀ x ∈ nums.val, x.val ≤ 0), ∀ r : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      IsMaxExactSelectionSum nums.val k.val.toNat m.val.toNat r.val) := by
  sorry

/-- Whenever max_sum(nums,k,m) returns a result r and max_sum(nums2,k,m) returns a result r2, we have r <= r2.
  Preconditions: Let n = len(nums) = len(nums2). Assume 1 <= n <= 2000; all entries of nums and nums2 lie in [-10000,10000]; 1 <= k; 1 <= m <= 3; k*m <= n; and nums[i] <= nums2[i] for every i with 0 <= i < n. -/
theorem spec_9 (nums nums2 : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hn12 : nums.val.length = nums2.val.length)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hbound2 : ∀ x ∈ nums2.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hle : EntrywiseLE nums.val nums2.val) :
    ∀ r r2 : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      Aegis.MaxSum.max_sum nums2 k m = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k m : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 2000)
    (hn12 : nums.val.length = nums2.val.length)
    (hbound : ∀ x ∈ nums.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hbound2 : ∀ x ∈ nums2.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hk : 1 ≤ k.val) (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 3)
    (hkm : k.val * m.val ≤ (nums.val.length : ℤ))
    (hle : EntrywiseLE nums.val nums2.val), ∀ r r2 : Std.I64, Aegis.MaxSum.max_sum nums k m = ok r →
      Aegis.MaxSum.max_sum nums2 k m = ok r2 → r.val ≤ r2.val) := by
  sorry

end AegisSpec.MaxSum
