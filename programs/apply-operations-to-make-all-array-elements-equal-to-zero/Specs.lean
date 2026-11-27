import Aegis.CheckArray.Code.Funs

/-!
# Specifications of `Aegis.CheckArray.check_array`

LeetCode problem `apply-operations-to-make-all-array-elements-equal-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckArray

def isum (c : ℕ → ℤ) (lo hi : ℤ) : ℤ :=
  if hi < 0 ∨ hi < lo then 0 else ∑ i ∈ Finset.Icc lo.toNat hi.toNat, c i

def windowSum (c : ℕ → ℤ) (n k j : ℕ) : ℤ :=
  isum c ((j : ℤ) - (k : ℤ) + 1) ((min j (n - k) : ℕ) : ℤ)

def IsDecomp (nums : Slice Std.I64) (k : ℕ) (c : ℕ → ℤ) : Prop :=
  (∀ i, i ≤ nums.val.length - k → 0 ≤ c i) ∧
    ∀ j, j < nums.val.length → (nums.val[j]!).val = windowSum c nums.val.length k j

def residueSum (nums : Slice Std.I64) (k a : ℕ) : ℤ :=
  ∑ i ∈ (Finset.range nums.val.length).filter (fun i => i % k = a), (nums.val[i]!).val

def altSum (nums : Slice Std.I64) (i : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (i + 1), (-1 : ℤ) ^ (i - t) * (nums.val[t]!).val

def greedyStep (nums : Slice Std.I64) (k : ℕ) (cs : List ℤ) : ℤ :=
  (nums.val[cs.length]!).val -
    ∑ h ∈ (Finset.range cs.length).filter
        (fun (h : ℕ) => (cs.length : ℤ) - (k : ℤ) + 1 ≤ (h : ℤ)), cs[h]!

def greedyList (nums : Slice Std.I64) (k : ℕ) : ℕ → List ℤ
  | 0 => [greedyStep nums k []]
  | i + 1 => greedyList nums k i ++ [greedyStep nums k (greedyList nums k i)]

def greedy (nums : Slice Std.I64) (k : ℕ) (i : ℕ) : ℤ := (greedyList nums k i)[i]!

/-- The function returns a result r, and r = true if and only if there exist integers c_0, ..., c_{n-k} such that: (1) c_i >= 0 for every i with 0 <= i <= n-k; and (2) for every j with 0 <= j < n, nums[j] = sum_{i = max(0, j-k+1)}^{min(j, n-k)} c_i.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, Aegis.CheckArray.check_array nums k = ok r ∧
      (r = true ↔ ∃ c : ℕ → ℤ, IsDecomp nums k.val.toNat c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, Aegis.CheckArray.check_array nums k = ok r ∧
      (r = true ↔ ∃ c : ℕ → ℤ, IsDecomp nums k.val.toNat c)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∃ r, Aegis.CheckArray.check_array nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∃ r, Aegis.CheckArray.check_array nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if all elements of nums are equal, that is, for every i and j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j].
  Preconditions: Let n = len(nums). Assume n >= 1, k = n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hnk : k.val = (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔ ∀ i j : ℕ, i < nums.val.length → j < nums.val.length →
        (nums.val[i]!).val = (nums.val[j]!).val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hnk : k.val = (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔ ∀ i j : ℕ, i < nums.val.length → j < nums.val.length →
        (nums.val[i]!).val = (nums.val[j]!).val)) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if for every j with 1 <= j <= n-2, nums[j] = nums[0] + nums[n-1].
  Preconditions: Let n = len(nums). Assume n = k + 1, k >= 2, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : (nums.val.length : ℤ) = k.val + 1) (hk : 2 ≤ k.val)
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔ ∀ j : ℕ, 1 ≤ j → j ≤ nums.val.length - 2 →
        (nums.val[j]!).val = (nums.val[0]!).val + (nums.val[nums.val.length - 1]!).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : (nums.val.length : ℤ) = k.val + 1) (hk : 2 ≤ k.val)
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔ ∀ j : ℕ, 1 ≤ j → j ≤ nums.val.length - 2 →
        (nums.val[j]!).val = (nums.val[0]!).val + (nums.val[nums.val.length - 1]!).val)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an integer m >= 0 such that sum_{i=0}^{n-1} nums[i] = m * k.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∃ m : ℤ, 0 ≤ m ∧ (∑ i ∈ Finset.range nums.val.length, (nums.val[i]!).val) = m * k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∃ m : ℤ, 0 ≤ m ∧ (∑ i ∈ Finset.range nums.val.length, (nums.val[i]!).val) = m * k.val) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every a and b with 0 <= a < k and 0 <= b < k, sum_{0 <= i < n, i mod k = a} nums[i] = sum_{0 <= i < n, i mod k = b} nums[i].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ a b : ℕ, a < k.val.toNat → b < k.val.toNat →
        residueSum nums k.val.toNat a = residueSum nums k.val.toNat b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ a b : ℕ, a < k.val.toNat → b < k.val.toNat →
        residueSum nums k.val.toNat a = residueSum nums k.val.toNat b) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every j with 1 <= j <= min(k-1, n-k), nums[j] >= nums[j-1].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, 1 ≤ j → j ≤ min (k.val.toNat - 1) (nums.val.length - k.val.toNat) →
        (nums.val[j - 1]!).val ≤ (nums.val[j]!).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, 1 ≤ j → j ≤ min (k.val.toNat - 1) (nums.val.length - k.val.toNat) →
        (nums.val[j - 1]!).val ≤ (nums.val[j]!).val) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every j with n-k < j < n, nums[j] <= nums[j-1].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, nums.val.length - k.val.toNat < j → j < nums.val.length →
        (nums.val[j]!).val ≤ (nums.val[j - 1]!).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, nums.val.length - k.val.toNat < j → j < nums.val.length →
        (nums.val[j]!).val ≤ (nums.val[j - 1]!).val) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every j with n-k < j < min(n, k), nums[j] = nums[j-1].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, nums.val.length - k.val.toNat < j → j < min nums.val.length k.val.toNat →
        (nums.val[j]!).val = (nums.val[j - 1]!).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ j : ℕ, nums.val.length - k.val.toNat < j → j < min nums.val.length k.val.toNat →
        (nums.val[j]!).val = (nums.val[j - 1]!).val) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every tuple (c_0, ..., c_{n-k}) of nonnegative integers such that for every j with 0 <= j < n, nums[j] = sum_{i = max(0, j-k+1)}^{min(j, n-k)} c_i, we have c_0 = nums[0] and c_{n-k} = nums[n-1].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        c 0 = (nums.val[0]!).val ∧
          c (nums.val.length - k.val.toNat) = (nums.val[nums.val.length - 1]!).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        c 0 = (nums.val[0]!).val ∧
          c (nums.val.length - k.val.toNat) = (nums.val[nums.val.length - 1]!).val) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there is exactly one tuple (c_0, ..., c_{n-k}) of nonnegative integers such that for every j with 0 <= j < n, nums[j] = sum_{i = max(0, j-k+1)}^{min(j, n-k)} c_i.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∃ c : ℕ → ℤ, IsDecomp nums k.val.toNat c ∧
        ∀ c' : ℕ → ℤ, IsDecomp nums k.val.toNat c' →
          ∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → c' i = c i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∃ c : ℕ → ℤ, IsDecomp nums k.val.toNat c ∧
        ∀ c' : ℕ → ℤ, IsDecomp nums k.val.toNat c' →
          ∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → c' i = c i) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every tuple (c_0, ..., c_{n-k}) of nonnegative integers such that for every j with 0 <= j < n, nums[j] = sum_{i = max(0, j-k+1)}^{min(j, n-k)} c_i, and for every i with 0 <= i <= n-k, we have c_i <= nums[i].
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        ∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → c i ≤ (nums.val[i]!).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        ∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → c i ≤ (nums.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, r = true if and only if: (a) for every i with 0 <= i <= n-2, A_i >= 0, where A_i = sum_{t=0}^{i} (-1)^{i-t} nums[t]; and (b) nums[n-1] = A_{n-2}.
  Preconditions: Let n = len(nums). Assume n >= 2, k = 2, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 2 ≤ nums.val.length) (hnk : k.val = 2)
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔
        (∀ i : ℕ, i ≤ nums.val.length - 2 → 0 ≤ altSum nums i) ∧
          (nums.val[nums.val.length - 1]!).val = altSum nums (nums.val.length - 2)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 2 ≤ nums.val.length) (hnk : k.val = 2)
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔
        (∀ i : ℕ, i ≤ nums.val.length - 2 → 0 ≤ altSum nums i) ∧
          (nums.val[nums.val.length - 1]!).val = altSum nums (nums.val.length - 2))) := by
  sorry

/-- Define c_i recursively for i = 0, ..., n-k by c_i = nums[i] - sum_{h=max(0,i-k+1)}^{i-1} c_h. Whenever the function returns a result r, r = true if and only if (1) c_i >= 0 for every i with 0 <= i <= n-k, and (2) for every j with n-k < j < n, nums[j] = sum_{h=max(0,j-k+1)}^{n-k} c_h.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔
        (∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → 0 ≤ greedy nums k.val.toNat i) ∧
          (∀ j : ℕ, nums.val.length - k.val.toNat < j → j < nums.val.length →
            (nums.val[j]!).val =
              isum (greedy nums k.val.toNat)
                ((j : ℤ) - (k.val.toNat : ℤ) + 1)
                ((nums.val.length - k.val.toNat : ℕ) : ℤ))) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r →
      (r = true ↔
        (∀ i : ℕ, i ≤ nums.val.length - k.val.toNat → 0 ≤ greedy nums k.val.toNat i) ∧
          (∀ j : ℕ, nums.val.length - k.val.toNat < j → j < nums.val.length →
            (nums.val[j]!).val =
              isum (greedy nums k.val.toNat)
                ((j : ℤ) - (k.val.toNat : ℤ) + 1)
                ((nums.val.length - k.val.toNat : ℕ) : ℤ)))) := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every tuple (c_0, ..., c_{n-k}) of nonnegative integers such that for every j with 0 <= j < n, nums[j] = sum_{i=max(0,j-k+1)}^{min(j,n-k)} c_i, we have sum_{i=0}^{n-k} c_i = (sum_{j=0}^{n-1} nums[j]) / k.
  Preconditions: Let n = len(nums). Assume n >= 1, 1 <= k <= n, and 0 <= nums[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000) :
    ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        (∑ i ∈ Finset.range (nums.val.length - k.val.toNat + 1), c i) =
          (∑ j ∈ Finset.range nums.val.length, (nums.val[j]!).val) / k.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hk1 : 1 ≤ k.val)
    (hk2 : k.val ≤ (nums.val.length : ℤ))
    (hbd : ∀ i, i < nums.val.length →
      0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000), ∀ r, Aegis.CheckArray.check_array nums k = ok r → r = true →
      ∀ c : ℕ → ℤ, IsDecomp nums k.val.toNat c →
        (∑ i ∈ Finset.range (nums.val.length - k.val.toNat + 1), c i) =
          (∑ j ∈ Finset.range nums.val.length, (nums.val[j]!).val) / k.val) := by
  sorry

end AegisSpec.CheckArray
