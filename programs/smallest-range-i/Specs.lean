import Aegis.SmallestRangeI.Code.Funs

/-!
# Specifications of `Aegis.SmallestRangeI.smallest_range_i`

LeetCode problem `smallest-range-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestRangeI

  def values (s : Aeneas.Std.Slice Aeneas.Std.I64) : List ℤ :=
    s.val.map (fun x => x.val)

  def valueAt (s : Aeneas.Std.Slice Aeneas.Std.I64) (i : ℕ) : ℤ :=
    (values s).getD i 0

  def maxOf (l : List ℤ) : ℤ :=
    match l with
    | [] => 0
    | a :: t => t.foldr max a

  def minOf (l : List ℤ) : ℤ :=
    match l with
    | [] => 0
    | a :: t => t.foldr min a

  def spread (s : Aeneas.Std.Slice Aeneas.Std.I64) : ℤ :=
    maxOf (values s) - minOf (values s)

  def Pre (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) : Prop :=
    1 ≤ (values nums).length ∧
    (values nums).length ≤ 10000 ∧
    (∀ i, i < (values nums).length → 0 ≤ valueAt nums i ∧ valueAt nums i ≤ 10000) ∧
    0 ≤ k.val ∧ k.val ≤ 10000

  /-- Let R = (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]). The function returns a result r and r = max(0, R - 2*k).
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_1
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∃ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
        r.val = max (0 : ℤ) (spread nums - 2 * k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∃ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
          r.val = max (0 : ℤ) (spread nums - 2 * k.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_2
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∃ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∃ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_3
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          0 ≤ r.val) := by
    sorry

  /-- Let R = (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]). Whenever the function returns a result r, r <= R.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_4
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        r.val ≤ spread nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          r.val ≤ spread nums) := by
    sorry

  /-- Let R = (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]). Whenever the function returns a result r, r >= R - 2*k.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_5
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        spread nums - 2 * k.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          spread nums - 2 * k.val ≤ r.val) := by
    sorry

  /-- Let R = (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]). Whenever the function returns a result r, r = 0 if and only if R <= 2*k.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_6
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        (r.val = 0 ↔ spread nums ≤ 2 * k.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          (r.val = 0 ↔ spread nums ≤ 2 * k.val)) := by
    sorry

  /-- Let r be the value returned by a call on nums with k. For every permutation p of {0, ..., len(nums)-1}, let nums' be the array of length len(nums) with nums'[i] = nums[p(i)] for every i. Then a call smallest_range_i(nums', k) returns the same value r.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_7
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        ∀ nums' : Aeneas.Std.Slice Aeneas.Std.I64,
          nums'.val.Perm nums.val →
          Aegis.SmallestRangeI.smallest_range_i nums' k = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          ∀ nums' : Aeneas.Std.Slice Aeneas.Std.I64,
            nums'.val.Perm nums.val →
            Aegis.SmallestRangeI.smallest_range_i nums' k = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Let r be the value returned by a call on nums with k. For every integer c such that 0 <= nums[i] + c <= 10000 for every i with 0 <= i < len(nums), let nums'[i] = nums[i] + c for every i. Then a call smallest_range_i(nums', k) returns the same value r.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_8
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        ∀ c : ℤ,
          (∀ i, i < (values nums).length →
            0 ≤ valueAt nums i + c ∧ valueAt nums i + c ≤ 10000) →
          ∀ nums' : Aeneas.Std.Slice Aeneas.Std.I64,
            (values nums').length = (values nums).length →
            (∀ i, i < (values nums).length → valueAt nums' i = valueAt nums i + c) →
            Aegis.SmallestRangeI.smallest_range_i nums' k = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          ∀ c : ℤ,
            (∀ i, i < (values nums).length →
              0 ≤ valueAt nums i + c ∧ valueAt nums i + c ≤ 10000) →
            ∀ nums' : Aeneas.Std.Slice Aeneas.Std.I64,
              (values nums').length = (values nums).length →
              (∀ i, i < (values nums).length → valueAt nums' i = valueAt nums i + c) →
              Aegis.SmallestRangeI.smallest_range_i nums' k = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Let r be the value returned by a call on nums with k. For every integer k' with 0 <= k' <= k, a call smallest_range_i(nums, k') returns a value r' with r' >= r.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_9
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∀ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
        ∀ k' : Aeneas.Std.I64,
          0 ≤ k'.val → k'.val ≤ k.val →
          ∃ r' : Aeneas.Std.I64,
            Aegis.SmallestRangeI.smallest_range_i nums k' = Aeneas.Std.Result.ok r' ∧
            r.val ≤ r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∀ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r →
          ∀ k' : Aeneas.Std.I64,
            0 ≤ k'.val → k'.val ≤ k.val →
            ∃ r' : Aeneas.Std.I64,
              Aegis.SmallestRangeI.smallest_range_i nums k' = Aeneas.Std.Result.ok r' ∧
              r.val ≤ r'.val) := by
    sorry

  /-- The function returns a result r and there exists a sequence b of length len(nums) of integers such that for every i with 0 <= i < len(nums), nums[i] - k <= b[i] <= nums[i] + k, and (max_{0 <= i < len(nums)} b[i]) - (min_{0 <= i < len(nums)} b[i]) = r.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_10
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∃ (r : Aeneas.Std.I64) (b : List ℤ),
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
        b.length = (values nums).length ∧
        (∀ i, i < b.length →
          valueAt nums i - k.val ≤ b.getD i 0 ∧ b.getD i 0 ≤ valueAt nums i + k.val) ∧
        maxOf b - minOf b = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∃ (r : Aeneas.Std.I64) (b : List ℤ),
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
          b.length = (values nums).length ∧
          (∀ i, i < b.length →
            valueAt nums i - k.val ≤ b.getD i 0 ∧ b.getD i 0 ≤ valueAt nums i + k.val) ∧
          maxOf b - minOf b = r.val) := by
    sorry

  /-- The function returns a result r and for every sequence b of length len(nums) of integers satisfying nums[i] - k <= b[i] <= nums[i] + k for every i with 0 <= i < len(nums), we have (max_{0 <= i < len(nums)} b[i]) - (min_{0 <= i < len(nums)} b[i]) >= r.
    Preconditions: 1 <= len(nums) <= 10000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10000; 0 <= k <= 10000. -/
  theorem spec_11
      (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k) :
      ∃ r : Aeneas.Std.I64,
        Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
        ∀ b : List ℤ,
          b.length = (values nums).length →
          (∀ i, i < b.length →
            valueAt nums i - k.val ≤ b.getD i 0 ∧ b.getD i 0 ≤ valueAt nums i + k.val) →
          r.val ≤ maxOf b - minOf b := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64) (hpre : Pre nums k), ∃ r : Aeneas.Std.I64,
          Aegis.SmallestRangeI.smallest_range_i nums k = Aeneas.Std.Result.ok r ∧
          ∀ b : List ℤ,
            b.length = (values nums).length →
            (∀ i, i < b.length →
              valueAt nums i - k.val ≤ b.getD i 0 ∧ b.getD i 0 ≤ valueAt nums i + k.val) →
            r.val ≤ maxOf b - minOf b) := by
    sorry

  end AegisSpec.SmallestRangeI
