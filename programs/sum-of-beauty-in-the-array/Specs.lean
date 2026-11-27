import Aegis.SumOfBeauties.Code.Funs

/-!
# Specifications of `Aegis.SumOfBeauties.sum_of_beauties`

LeetCode problem `sum-of-beauty-in-the-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SumOfBeauties
open Classical

namespace AegisSpec.SumOfBeauties

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val.getD i 0#i64).val

@[simp] theorem elem_of_lt (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) :
    elem nums i = (nums.val[i]).val := by
  simp [elem, List.getD, h]

@[simp] theorem elem_of_le (nums : Slice Std.I64) (i : ℕ) (h : nums.val.length ≤ i) :
    elem nums i = 0 := by
  simp [elem, List.getD, h]

def isPrefixMax (nums : Slice Std.I64) (i : ℕ) : Prop :=
  ∀ j : ℕ, j < i → elem nums j < elem nums i

def isSuffixMin (nums : Slice Std.I64) (i : ℕ) : Prop :=
  ∀ k : ℕ, i < k → k < nums.val.length → elem nums i < elem nums k

def isLocalPeak (nums : Slice Std.I64) (i : ℕ) : Prop :=
  elem nums (i - 1) < elem nums i ∧ elem nums i < elem nums (i + 1)

def isBothSided (nums : Slice Std.I64) (i : ℕ) : Prop :=
  isPrefixMax nums i ∧ isSuffixMin nums i

noncomputable def beauty (nums : Slice Std.I64) (i : ℕ) : ℤ :=
  if isBothSided nums i then 2 else if isLocalPeak nums i then 1 else 0

noncomputable def peakCount (nums : Slice Std.I64) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 2)).filter (fun i => isLocalPeak nums i)).card

noncomputable def bothCount (nums : Slice Std.I64) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 2)).filter (fun i => isBothSided nums i)).card

/-- For each integer i with 1 <= i <= n-2, define B(i) = 2 if (for every j with 0 <= j < i, nums[j] < nums[i]) and (for every k with i < k < n, nums[i] < nums[k]); otherwise B(i) = 1 if nums[i-1] < nums[i] and nums[i] < nums[i+1]; otherwise B(i) = 0. The function returns a result r and r = sum_{i=1}^{n-2} B(i).
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      r.val = ∑ i ∈ Finset.Icc 1 (n - 2), beauty nums i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      r.val = ∑ i ∈ Finset.Icc 1 (n - 2), beauty nums i) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r.
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 2 * (n - 2), where n = len(nums).
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ r.val ≤ 2 * ((n - 2 : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ r.val ≤ 2 * ((n - 2 : ℕ) : ℤ)) := by
  sorry

/-- Let L be the number of integers i with 1 <= i <= n-2 such that nums[i-1] < nums[i] and nums[i] < nums[i+1]. Let A be the number of integers i with 1 <= i <= n-2 such that (for every j with 0 <= j < i, nums[j] < nums[i]) and (for every k with i < k < n, nums[i] < nums[k]). The function returns a result r and r = L + A.
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      r.val = (peakCount nums n : ℤ) + (bothCount nums n : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      r.val = (peakCount nums n : ℤ) + (bothCount nums n : ℤ)) := by
  sorry

/-- The function returns a result r, and r = 2 * (n - 2) if and only if for every t with 0 <= t < n-1, nums[t] < nums[t+1].
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      (r.val = 2 * ((n - 2 : ℕ) : ℤ) ↔ ∀ t : ℕ, t < n - 1 → elem nums t < elem nums (t + 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      (r.val = 2 * ((n - 2 : ℕ) : ℤ) ↔ ∀ t : ℕ, t < n - 1 → elem nums t < elem nums (t + 1))) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if for every integer i with 1 <= i <= n-2, it is not the case that nums[i-1] < nums[i] and nums[i] < nums[i+1].
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      (r.val = 0 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ n - 2 → ¬ isLocalPeak nums i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧
      (r.val = 0 ↔ ∀ i : ℕ, 1 ≤ i → i ≤ n - 2 → ¬ isLocalPeak nums i)) := by
  sorry

/-- If there exists an integer i with 1 <= i <= n-2 such that (for every j with 0 <= j < i, nums[j] < nums[i]) and (for every k with i < k < n, nums[i] < nums[k]), then the function returns a result r with r >= 2.
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧ isBothSided nums i) →
      ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ 2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), (∃ i : ℕ, 1 ≤ i ∧ i ≤ n - 2 ∧ isBothSided nums i) →
      ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ 2 ≤ r.val) := by
  sorry

/-- Let L be the number of integers i with 1 <= i <= n-2 such that nums[i-1] < nums[i] and nums[i] < nums[i+1]. The function returns a result r and L <= r.
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ (peakCount nums n : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ (peakCount nums n : ℤ) ≤ r.val) := by
  sorry

/-- Let L be the number of integers i with 1 <= i <= n-2 such that nums[i-1] < nums[i] and nums[i] < nums[i+1]. The function returns a result r and r <= 2 * L.
  Preconditions: Let n = len(nums). The slice nums has length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= nums[t] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000) :
    ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ r.val ≤ 2 * (peakCount nums n : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (h_len : nums.val.length = n) (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem : ∀ t : ℕ, t < n → 1 ≤ elem nums t ∧ elem nums t ≤ 100000), ∃ r : Std.I64, sum_of_beauties nums = ok r ∧ r.val ≤ 2 * (peakCount nums n : ℤ)) := by
  sorry

/-- Suppose that for all i and j with 0 <= i < n and 0 <= j < n, a[i] < a[j] if and only if b[i] < b[j]. Then the function returns a result r_a on a and a result r_b on b, and r_a = r_b.
  Preconditions: Let n = len(a) = len(b). Both slices have length n with 3 <= n <= 100000, and for every t with 0 <= t < n, 1 <= a[t] <= 100000 and 1 <= b[t] <= 100000. -/
theorem spec_11 (a b : Slice Std.I64) (n : ℕ)
    (h_len_a : a.val.length = n) (h_len_b : b.val.length = n)
    (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem_a : ∀ t : ℕ, t < n → 1 ≤ elem a t ∧ elem a t ≤ 100000)
    (h_elem_b : ∀ t : ℕ, t < n → 1 ≤ elem b t ∧ elem b t ≤ 100000)
    (h_order : ∀ i j : ℕ, i < n → j < n → (elem a i < elem a j ↔ elem b i < elem b j)) :
    ∃ r_a r_b : Std.I64, sum_of_beauties a = ok r_a ∧ sum_of_beauties b = ok r_b ∧
      r_a.val = r_b.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : Slice Std.I64) (n : ℕ)
    (h_len_a : a.val.length = n) (h_len_b : b.val.length = n)
    (h_lo : 3 ≤ n) (h_hi : n ≤ 100000)
    (h_elem_a : ∀ t : ℕ, t < n → 1 ≤ elem a t ∧ elem a t ≤ 100000)
    (h_elem_b : ∀ t : ℕ, t < n → 1 ≤ elem b t ∧ elem b t ≤ 100000)
    (h_order : ∀ i j : ℕ, i < n → j < n → (elem a i < elem a j ↔ elem b i < elem b j)), ∃ r_a r_b : Std.I64, sum_of_beauties a = ok r_a ∧ sum_of_beauties b = ok r_b ∧
      r_a.val = r_b.val) := by
  sorry

end AegisSpec.SumOfBeauties
