import Aegis.MaxNonDecreasingLength.Code.Funs

/-!
# Specifications of `Aegis.MaxNonDecreasingLength.max_non_decreasing_length`

LeetCode problem `longest-non-decreasing-subarray-from-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxNonDecreasingLength

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map Std.IScalar.val

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (vals nums).getD i 0

theorem vals_length (nums : Slice Std.I64) : (vals nums).length = nums.val.length := by
  simp [vals]

theorem elem_eq (nums : Slice Std.I64) {i : ℕ} (h : i < nums.val.length) :
    elem nums i = (nums.val[i]).val := by
  simp [elem, vals, h]

def pick (a b : List ℤ) (c : ℕ → Bool) (i : ℕ) : ℤ :=
  if c i then b.getD i 0 else a.getD i 0

def IsNonDecreasingOn (v : ℕ → ℤ) (l u : ℕ) : Prop :=
  ∀ j, l ≤ j → j < u → v j ≤ v (j + 1)

def Achievable (a b : List ℤ) (L : ℕ) : Prop :=
  ∃ (c : ℕ → Bool) (l u : ℕ),
    l ≤ u ∧ u < a.length ∧ L = u - l + 1 ∧ IsNonDecreasingOn (pick a b c) l u

noncomputable def maxWindowLength (a b : List ℤ) : ℕ := by
  classical
  exact (Finset.range (a.length + 1)).sup
    (fun L => if Achievable a b L then L else 0)

theorem Achievable_le_length {a b : List ℤ} {L : ℕ} (h : Achievable a b L) :
    L ≤ a.length := by
  obtain ⟨c, l, u, hlu, hu, hL, -⟩ := h
  omega

theorem le_maxWindowLength {a b : List ℤ} {L : ℕ} (hL : L ≤ a.length)
    (h : Achievable a b L) : L ≤ maxWindowLength a b := by
  classical
  have hmem : L ∈ Finset.range (a.length + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hL)
  have hs := Finset.le_sup (s := Finset.range (a.length + 1))
    (f := fun L => if Achievable a b L then L else 0) hmem
  simpa [maxWindowLength, h] using hs

theorem maxWindowLength_le (a b : List ℤ) : maxWindowLength a b ≤ a.length := by
  classical
  unfold maxWindowLength
  refine Finset.sup_le (fun L _ => ?_)
  by_cases h : Achievable a b L
  · simp only [h, ite_true]
    exact Achievable_le_length h
  · simp only [h, ite_false]
    exact Nat.zero_le _

theorem maxWindowLength_nil (b : List ℤ) : maxWindowLength [] b = 0 :=
  Nat.le_zero.mp (maxWindowLength_le [] b)

/-- The function returns a result ans and ans is the maximum, over all choice functions c : {0,...,n-1} -> {0,1} and all index pairs l,u with 0 <= l <= u < n, of the length u-l+1 subject to the condition that, writing v_i = nums1[i] if c(i)=0 and v_i = nums2[i] if c(i)=1, one has v_j <= v_{j+1} for every j with l <= j < u. In other words, ans is the largest achievable length of a contiguous non-empty subarray of some nums3 obtained by choosing at each index one of the two given values.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ans.val = (maxWindowLength (vals nums1) (vals nums2) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ans.val = (maxWindowLength (vals nums1) (vals nums2) : ℤ)) := by
  sorry

/-- The function returns a result ans and does not fail (no overflow, panic, or out-of-bounds failure).
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, 1 <= ans <= n.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      1 ≤ ans.val ∧ ans.val ≤ (n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      1 ≤ ans.val ∧ ans.val ≤ (n : ℤ)) := by
  sorry

/-- The function returns a result ans and ans = n.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. Assume also that either nums1 is non-decreasing, meaning nums1[i] <= nums1[i+1] for every i with 0 <= i < n-1, or nums2 is non-decreasing, meaning nums2[i] <= nums2[i+1] for every i with 0 <= i < n-1. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hmo : (∀ i, i < n - 1 → elem nums1 i ≤ elem nums1 (i + 1)) ∨
           (∀ i, i < n - 1 → elem nums2 i ≤ elem nums2 (i + 1))) :
    ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ans.val = (n : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (hmo : (∀ i, i < n - 1 → elem nums1 i ≤ elem nums1 (i + 1)) ∨
           (∀ i, i < n - 1 → elem nums2 i ≤ elem nums2 (i + 1))), ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ans.val = (n : ℤ)) := by
  sorry

/-- Whenever the function returns a result ans, for every choice function c : {0,...,n-1} -> {0,1} and every l,u with 0 <= l <= u < n, writing v_i = nums1[i] if c(i)=0 and v_i = nums2[i] if c(i)=1, if v_j <= v_{j+1} for every j with l <= j < u, then u-l+1 <= ans.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      ∀ (c : ℕ → Bool) (l u : ℕ), l ≤ u → u < n →
        IsNonDecreasingOn (pick (vals nums1) (vals nums2) c) l u →
        (u - l + 1 : ℤ) ≤ ans.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      ∀ (c : ℕ → Bool) (l u : ℕ), l ≤ u → u < n →
        IsNonDecreasingOn (pick (vals nums1) (vals nums2) c) l u →
        (u - l + 1 : ℤ) ≤ ans.val) := by
  sorry

/-- The function returns a result ans and there exist a choice function c : {0,...,n-1} -> {0,1} and indices l,u with 0 <= l <= u < n such that u-l+1 = ans and, writing v_i = nums1[i] if c(i)=0 and v_i = nums2[i] if c(i)=1, one has v_j <= v_{j+1} for every j with l <= j < u.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ∃ (c : ℕ → Bool) (l u : ℕ),
        l ≤ u ∧ u < n ∧ ans.val = (u - l + 1 : ℤ) ∧
          IsNonDecreasingOn (pick (vals nums1) (vals nums2) c) l u := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      ∃ (c : ℕ → Bool) (l u : ℕ),
        l ≤ u ∧ u < n ∧ ans.val = (u - l + 1 : ℤ) ∧
          IsNonDecreasingOn (pick (vals nums1) (vals nums2) c) l u) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result ans on the argument pair (nums1,nums2) and a result ans_swapped on the argument pair (nums2,nums1), and ans = ans_swapped.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∃ ans ans' : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums2 nums1 = ok ans' ∧
      ans = ans' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∃ ans ans' : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums2 nums1 = ok ans' ∧
      ans = ans') := by
  sorry

/-- Let a1 and a2 be the length-n arrays defined by a1[k] = nums2[k], a2[k] = nums1[k], and a1[i] = nums1[i] and a2[i] = nums2[i] for every i with 0 <= i < n and i != k. The function returns a result ans on (nums1,nums2) and a result ans_swapped_index on (a1,a2), and ans = ans_swapped_index.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. Fix an index k with 0 <= k < n. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (k : ℕ) (hk : k < n) :
    ∃ (a1 a2 : Slice Std.I64) (ans ans' : Std.I64),
      vals a1 = (vals nums1).set k (elem nums2 k) ∧
      vals a2 = (vals nums2).set k (elem nums1 k) ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length a1 a2 = ok ans' ∧
      ans = ans' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9)
    (k : ℕ) (hk : k < n), ∃ (a1 a2 : Slice Std.I64) (ans ans' : Std.I64),
      vals a1 = (vals nums1).set k (elem nums2 k) ∧
      vals a2 = (vals nums2).set k (elem nums1 k) ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans ∧
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length a1 a2 = ok ans' ∧
      ans = ans') := by
  sorry

/-- Whenever the function returns a result ans, ans = 1 if and only if for every i with 0 <= i < n-1, min(nums1[i], nums2[i]) > max(nums1[i+1], nums2[i+1]), where min and max are the ordinary integer minimum and maximum.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 2, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 2 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      (ans.val = 1 ↔
        ∀ i, i < n - 1 →
          min (elem nums1 i) (elem nums2 i) >
            max (elem nums1 (i + 1)) (elem nums2 (i + 1))) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 2 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      (ans.val = 1 ↔
        ∀ i, i < n - 1 →
          min (elem nums1 i) (elem nums2 i) >
            max (elem nums1 (i + 1)) (elem nums2 (i + 1)))) := by
  sorry

/-- Whenever the function returns a result ans, ans = n if and only if there exists a choice function c : {0,...,n-1} -> {0,1} such that, writing v_i = nums1[i] if c(i)=0 and v_i = nums2[i] if c(i)=1, the inequalities v_i <= v_{i+1} hold for every i with 0 <= i < n-1.
  Preconditions: Let n = len(nums1). Assume len(nums1) = len(nums2) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9 and 1 <= nums2[i] <= 10^9. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9) :
    ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      (ans.val = (n : ℤ) ↔
        ∃ c : ℕ → Bool,
          ∀ i, i < n - 1 →
            pick (vals nums1) (vals nums2) c i ≤
              pick (vals nums1) (vals nums2) c (i + 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n) (hn : 1 ≤ n)
    (hb1 : ∀ i, i < n → 1 ≤ elem nums1 i ∧ elem nums1 i ≤ 10 ^ 9)
    (hb2 : ∀ i, i < n → 1 ≤ elem nums2 i ∧ elem nums2 i ≤ 10 ^ 9), ∀ ans : Std.I64,
      Aegis.MaxNonDecreasingLength.max_non_decreasing_length nums1 nums2 = ok ans →
      (ans.val = (n : ℤ) ↔
        ∃ c : ℕ → Bool,
          ∀ i, i < n - 1 →
            pick (vals nums1) (vals nums2) c i ≤
              pick (vals nums1) (vals nums2) c (i + 1))) := by
  sorry

end AegisSpec.MaxNonDecreasingLength
