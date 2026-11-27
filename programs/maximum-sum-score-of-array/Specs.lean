import Aegis.MaximumSumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumSumScore.maximum_sum_score`

LeetCode problem `maximum-sum-score-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximumSumScore (maximum_sum_score)

namespace AegisSpec.MaximumSumScore

def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def prefixSum (nums : Slice Std.I64) (i : Nat) : ℤ := ((contents nums).take (i + 1)).sum

def suffixSum (nums : Slice Std.I64) (i : Nat) : ℤ := ((contents nums).drop i).sum

def bestScore (nums : Slice Std.I64) (n : Nat) (hn : 0 < n) : ℤ :=
  (Finset.range n).sup' (by simp [Finset.nonempty_range_iff]; omega)
    (fun i => max (prefixSum nums i) (suffixSum nums i))

def maxPrefixScore (nums : Slice Std.I64) (n : Nat) (hn : 0 < n) : ℤ :=
  (Finset.range n).sup' (by simp [Finset.nonempty_range_iff]; omega)
    (fun i => prefixSum nums i)

def maxSuffixScore (nums : Slice Std.I64) (n : Nat) (hn : 0 < n) : ℤ :=
  (Finset.range n).sup' (by simp [Finset.nonempty_range_iff]; omega)
    (fun i => suffixSum nums i)

def totalSum (nums : Slice Std.I64) : ℤ := (contents nums).sum

def positivePartSum (nums : Slice Std.I64) : ℤ :=
  ((contents nums).map (fun x => max x 0)).sum

def AllInRange (nums : Slice Std.I64) (lo hi : ℤ) : Prop :=
  ∀ (j : Nat) (hj : j < nums.val.length),
    lo ≤ (nums.val.get ⟨j, hj⟩).val ∧ (nums.val.get ⟨j, hj⟩).val ≤ hi

def PointwiseLE (nums nums2 : Slice Std.I64) : Prop :=
  ∀ (j : Nat) (h₁ : j < nums.val.length) (h₂ : j < nums2.val.length),
    (nums.val.get ⟨j, h₁⟩).val ≤ (nums2.val.get ⟨j, h₂⟩).val

def IsReverseOf (rev nums : Slice Std.I64) : Prop :=
  contents rev = (contents nums).reverse

def InI64Range (x : ℤ) : Prop := -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807

/-- Let P(i) = sum_{j=0}^{i} nums[j] and S(i) = sum_{j=i}^{n-1} nums[j] for 0 <= i < n. The function returns a result r and r = max_{0 <= i < n} max(P(i), S(i)).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val = bestScore nums n (by omega) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val = bestScore nums n (by omega)) := by
  sorry

/-- The function returns a result r and does not fail (no panic, out-of-bounds access, or i64 overflow). In particular, every prefix sum sum_{j=0}^{i} nums[j], every suffix sum sum_{j=i}^{n-1} nums[j], and the returned value r lie in the i64 range.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      (∀ (i : Nat), i < n → InI64Range (prefixSum nums i)) ∧
      (∀ (i : Nat), i < n → InI64Range (suffixSum nums i)) ∧
      InI64Range r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      (∀ (i : Nat), i < n → InI64Range (prefixSum nums i)) ∧
      (∀ (i : Nat), i < n → InI64Range (suffixSum nums i)) ∧
      InI64Range r.val) := by
  sorry

/-- Let P(i) = sum_{j=0}^{i} nums[j] for 0 <= i < n. The function returns a result r and for every i with 0 <= i < n, r >= P(i).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (i : Nat), i < n → prefixSum nums i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (i : Nat), i < n → prefixSum nums i ≤ r.val) := by
  sorry

/-- Let S(i) = sum_{j=i}^{n-1} nums[j] for 0 <= i < n. The function returns a result r and for every i with 0 <= i < n, r >= S(i).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (i : Nat), i < n → suffixSum nums i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (i : Nat), i < n → suffixSum nums i ≤ r.val) := by
  sorry

/-- Let P(i) = sum_{j=0}^{i} nums[j] and S(i) = sum_{j=i}^{n-1} nums[j] for 0 <= i < n. The function returns a result r and there exists an index i with 0 <= i < n such that r = max(P(i), S(i)).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∃ (i : Nat), i < n ∧ r.val = max (prefixSum nums i) (suffixSum nums i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∃ (i : Nat), i < n ∧ r.val = max (prefixSum nums i) (suffixSum nums i)) := by
  sorry

/-- Let P(i) = sum_{j=0}^{i} nums[j] and S(i) = sum_{j=i}^{n-1} nums[j] for 0 <= i < n. The function returns a result r and r is equal to P(i) for some i with 0 <= i < n, or r is equal to S(i) for some i with 0 <= i < n.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ((∃ (i : Nat), i < n ∧ r.val = prefixSum nums i) ∨
        (∃ (i : Nat), i < n ∧ r.val = suffixSum nums i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ((∃ (i : Nat), i < n ∧ r.val = prefixSum nums i) ∨
        (∃ (i : Nat), i < n ∧ r.val = suffixSum nums i))) := by
  sorry

/-- Let pos = sum_{j=0}^{n-1} max(nums[j], 0). The function returns a result r and r <= pos.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val ≤ positivePartSum nums := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val ≤ positivePartSum nums) := by
  sorry

/-- Let total = sum_{j=0}^{n-1} nums[j]. The function returns a result r and r = total.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, 0 <= nums[j] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums 0 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val = totalSum nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums 0 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧ r.val = totalSum nums) := by
  sorry

/-- The function returns a result r and r = max(nums[0], nums[n-1]).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 0. -/
theorem spec_9 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 0) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      r.val = max ((nums.val.get ⟨0, by omega⟩).val)
        ((nums.val.get ⟨n - 1, by omega⟩).val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 0), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      r.val = max ((nums.val.get ⟨0, by omega⟩).val)
        ((nums.val.get ⟨n - 1, by omega⟩).val)) := by
  sorry

/-- Let P(i) = sum_{j=0}^{i} nums[j] and S(i) = sum_{j=i}^{n-1} nums[j] for 0 <= i < n. The function returns a result r and r = max( max_{0 <= i < n} P(i), max_{0 <= i < n} S(i) ).
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      r.val = max (maxPrefixScore nums n (by omega)) (maxSuffixScore nums n (by omega)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      r.val = max (maxPrefixScore nums n (by omega)) (maxSuffixScore nums n (by omega))) := by
  sorry

/-- The function returns a result r on nums. For every slice nums2 such that len(nums2) = n and for every j with 0 <= j < n, nums[j] <= nums2[j] and -100000 <= nums2[j] <= 100000, whenever the function on nums2 returns r2, we have r <= r2.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (nums2 : Slice Std.I64) (r2 : Std.I64),
        n = nums2.val.length →
        AllInRange nums2 (-100000) 100000 →
        PointwiseLE nums nums2 →
        maximum_sum_score nums2 = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (nums2 : Slice Std.I64) (r2 : Std.I64),
        n = nums2.val.length →
        AllInRange nums2 (-100000) 100000 →
        PointwiseLE nums nums2 →
        maximum_sum_score nums2 = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- The function returns a result r on nums. Let rev be the slice with len(rev) = n and rev[i] = nums[n-1-i] for 0 <= i < n. Whenever the function on rev returns r_rev, we have r = r_rev.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every j with 0 <= j < n, -100000 <= nums[j] <= 100000. -/
theorem spec_12 (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000) :
    ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (rev : Slice Std.I64) (r_rev : Std.I64),
        IsReverseOf rev nums → maximum_sum_score rev = ok r_rev → r.val = r_rev.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn_len : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb : AllInRange nums (-100000) 100000), ∃ (r : Std.I64), maximum_sum_score nums = ok r ∧
      ∀ (rev : Slice Std.I64) (r_rev : Std.I64),
        IsReverseOf rev nums → maximum_sum_score rev = ok r_rev → r.val = r_rev.val) := by
  sorry

end AegisSpec.MaximumSumScore
