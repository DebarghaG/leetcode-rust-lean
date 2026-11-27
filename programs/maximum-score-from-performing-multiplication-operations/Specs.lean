import Aegis.MaximumScore.Code.Funs

/-!
# Specifications of `Aegis.MaximumScore.maximum_score`

LeetCode problem `maximum-score-from-performing-multiplication-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumScore

def entry (s : Slice Std.I64) (i : ℕ) : ℤ :=
  match s.val[i]? with
  | some v => v.val
  | none => 0

def I64Repr (x : ℤ) : Prop := -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807

inductive Choice where
  | F
  | B
  deriving DecidableEq

def countF (c : ℕ → Choice) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    match c i with
    | Choice.F => countF c i + 1
    | Choice.B => countF c i

def countB (c : ℕ → Choice) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    match c i with
    | Choice.F => countB c i
    | Choice.B => countB c i + 1

def chosen (nums : Slice Std.I64) (n : ℕ) (c : ℕ → Choice) (i : ℕ) : ℤ :=
  match c i with
  | Choice.F => entry nums (countF c i)
  | Choice.B => entry nums (n - 1 - countB c i)

def score (nums multipliers : Slice Std.I64) (n m : ℕ) (c : ℕ → Choice) : ℤ :=
  ∑ i ∈ Finset.range m, entry multipliers i * chosen nums n c i

structure Precond (nums multipliers : Slice Std.I64) (n m : ℕ) : Prop where

  len_nums : n = (Slice.len nums).val

  len_multipliers : m = (Slice.len multipliers).val

  m_pos : 1 ≤ m

  m_le_300 : m ≤ 300

  m_le_n : m ≤ n

  n_le_100000 : n ≤ 100000

  nums_bounds : ∀ i, i < n → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000

  multipliers_bounds : ∀ j, j < m → -1000 ≤ entry multipliers j ∧ entry multipliers j ≤ 1000

def prefixSum (s : Slice Std.I64) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, entry s i

def suffixSum (s : Slice Std.I64) (n k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, entry s (n - k + j)

def splitSum (nums : Slice Std.I64) (n m k : ℕ) : ℤ :=
  prefixSum nums k + suffixSum nums n (m - k)

def maxSplitSum (nums : Slice Std.I64) (n m : ℕ) : ℤ :=
  match (List.range (m + 1)).map (fun k => splitSum nums n m k) with
  | [] => 0
  | x :: xs => xs.foldl max x

/-- The function returns a result r and r = max over all choice sequences c of Score(c), where a choice sequence is a function c : {0,...,m-1} -> {F,B}; for each i in 0..m-1, define f(i) = |{j : 0 <= j < i and c(j) = F}| and b(i) = |{j : 0 <= j < i and c(j) = B}|, let x_i = nums[f(i)] if c(i)=F and nums[n-1-b(i)] if c(i)=B, and Score(c) = sum_{i=0}^{m-1} multipliers[i] * x_i.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_1 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      (∀ c : ℕ → Choice, score nums multipliers n m c ≤ r.val) ∧
      (∃ c : ℕ → Choice, score nums multipliers n m c = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      (∀ c : ℕ → Choice, score nums multipliers n m c ≤ r.val) ∧
      (∃ c : ℕ → Choice, score nums multipliers n m c = r.val)) := by
  sorry

/-- The function returns a result r and for every choice sequence c (with Score(c) defined as in spec_1), Score(c) <= r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_2 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      ∀ c : ℕ → Choice, score nums multipliers n m c ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      ∀ c : ℕ → Choice, score nums multipliers n m c ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists a choice sequence c such that Score(c) = r, where Score is defined as in spec_1.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_3 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      ∃ c : ℕ → Choice, score nums multipliers n m c = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      ∃ c : ℕ → Choice, score nums multipliers n m c = r.val) := by
  sorry

/-- The function returns a result r and -m * 10^6 <= r <= m * 10^6.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_4 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      -((m : ℤ) * 1000000) ≤ r.val ∧ r.val ≤ (m : ℤ) * 1000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      -((m : ℤ) * 1000000) ≤ r.val ∧ r.val ≤ (m : ℤ) * 1000000) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, the function returns a result r (i.e., it does not fail, panic, overflow, or go out of bounds).
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_5 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, let nums_rev be the slice of length n with nums_rev[i] = nums[n-1-i] for 0 <= i < n. The function returns results r for (nums, multipliers) and r' for (nums_rev, multipliers), and r = r'.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_6 (nums nums_rev multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len : n = (Slice.len nums_rev).val)
    (h_rev : ∀ i, i < n → entry nums_rev i = entry nums (n - 1 - i)) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums_rev multipliers = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums_rev multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len : n = (Slice.len nums_rev).val)
    (h_rev : ∀ i, i < n → entry nums_rev i = entry nums (n - 1 - i)), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums_rev multipliers = ok r' ∧
      r.val = r'.val) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, and every integer c >= 0 such that c * multipliers[j] is representable in i64 for all 0 <= j < m, let multipliers' be the slice of length m with multipliers'[j] = c * multipliers[j]. Whenever the function returns a result r for (nums, multipliers) and a result r' for (nums, multipliers'), we have r' = c * r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_7 (nums multipliers multipliers' : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_repr : ∀ j, j < m → I64Repr (c * entry multipliers j))
    (h_len : m = (Slice.len multipliers').val)
    (h_entry : ∀ j, j < m → entry multipliers' j = c * entry multipliers j) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums multipliers' = ok r' ∧
      r'.val = c * r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums multipliers multipliers' : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_repr : ∀ j, j < m → I64Repr (c * entry multipliers j))
    (h_len : m = (Slice.len multipliers').val)
    (h_entry : ∀ j, j < m → entry multipliers' j = c * entry multipliers j), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums multipliers' = ok r' ∧
      r'.val = c * r.val) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, and every integer c such that nums[i] + c is representable in i64 for all 0 <= i < n, let nums' be the slice of length n with nums'[i] = nums[i] + c. Whenever the function returns a result r for (nums, multipliers) and a result r' for (nums', multipliers), we have r' = r + c * (sum_{j=0}^{m-1} multipliers[j]).
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_8 (nums nums' multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (h_repr : ∀ i, i < n → I64Repr (entry nums i + c))
    (h_len : n = (Slice.len nums').val)
    (h_entry : ∀ i, i < n → entry nums' i = entry nums i + c) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r'.val = r.val + c * (∑ j ∈ Finset.range m, entry multipliers j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (h_repr : ∀ i, i < n → I64Repr (entry nums i + c))
    (h_len : n = (Slice.len nums').val)
    (h_entry : ∀ i, i < n → entry nums' i = entry nums i + c), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r'.val = r.val + c * (∑ j ∈ Finset.range m, entry multipliers j)) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, let nums'[i] = -nums[i] for 0 <= i < n and multipliers'[j] = -multipliers[j] for 0 <= j < m. Whenever the function returns a result r for (nums, multipliers) and a result r' for (nums', multipliers'), we have r' = r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_9 (nums nums' multipliers multipliers' : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len_nums : n = (Slice.len nums').val)
    (h_nums : ∀ i, i < n → entry nums' i = -entry nums i)
    (h_len_multipliers : m = (Slice.len multipliers').val)
    (h_multipliers : ∀ j, j < m → entry multipliers' j = -entry multipliers j) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers' = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' multipliers multipliers' : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len_nums : n = (Slice.len nums').val)
    (h_nums : ∀ i, i < n → entry nums' i = -entry nums i)
    (h_len_multipliers : m = (Slice.len multipliers').val)
    (h_multipliers : ∀ j, j < m → entry multipliers' j = -entry multipliers j), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers' = ok r' ∧
      r.val = r'.val) := by
  sorry

/-- For every nums, nums' (both of length n) and multipliers (of length m) satisfying the preconditions, if nums'[i] >= nums[i] for all 0 <= i < n and multipliers[j] >= 0 for all 0 <= j < m, then whenever the function returns a result r for (nums, multipliers) and a result r' for (nums', multipliers), we have r' >= r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000, and additionally nums' is a slice of length n with -1000 <= nums'[i] <= 1000 for all i. -/
theorem spec_10 (nums nums' multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len : n = (Slice.len nums').val)
    (h_bounds : ∀ i, i < n → -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000)
    (h_ge : ∀ i, i < n → entry nums i ≤ entry nums' i)
    (h_mult_nn : ∀ j, j < m → 0 ≤ entry multipliers j) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_len : n = (Slice.len nums').val)
    (h_bounds : ∀ i, i < n → -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000)
    (h_ge : ∀ i, i < n → entry nums i ≤ entry nums' i)
    (h_mult_nn : ∀ j, j < m → 0 ≤ entry multipliers j), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and r = c * max_{0 <= k <= m} ( sum_{i=0}^{k-1} nums[i] + sum_{i=n-(m-k)}^{n-1} nums[i] ), where each sum over an empty range is 0.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and there exists an integer c >= 0 such that multipliers[j] = c for all 0 <= j < m. -/
theorem spec_11 (nums multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_const : ∀ j, j < m → entry multipliers j = c) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val = c * maxSplitSum nums n m := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_const : ∀ j, j < m → entry multipliers j = c), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val = c * maxSplitSum nums n m) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000, and additionally nums[i] >= 0 for all 0 <= i < n and multipliers[j] >= 0 for all 0 <= j < m. -/
theorem spec_12 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_mult_nn : ∀ j, j < m → 0 ≤ entry multipliers j) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      0 ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_mult_nn : ∀ j, j < m → 0 ≤ entry multipliers j), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= 0.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000, and additionally nums[i] >= 0 for all 0 <= i < n and multipliers[j] <= 0 for all 0 <= j < m. -/
theorem spec_13 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_mult_np : ∀ j, j < m → entry multipliers j ≤ 0) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val ≤ 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_mult_np : ∀ j, j < m → entry multipliers j ≤ 0), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val ≤ 0) := by
  sorry

/-- The function returns a result r and r = max(nums[0] * multipliers[0], nums[n-1] * multipliers[0]).
  Preconditions: n = len(nums), m = len(multipliers), m = 1, 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, and for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000. -/
theorem spec_14 (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (hm : m = 1) :
    ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val = max (entry nums 0 * entry multipliers 0) (entry nums (n - 1) * entry multipliers 0) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums multipliers : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (hm : m = 1), ∃ r : Std.I64, Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      r.val = max (entry nums 0 * entry multipliers 0) (entry nums (n - 1) * entry multipliers 0)) := by
  sorry

/-- For every nums and multipliers satisfying the preconditions, let nums' be the slice of length n with nums'[i] = c * nums[i]. Whenever the function returns a result r for (nums, multipliers) and a result r' for (nums', multipliers), we have r' = c * r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000, for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000, and c is an integer with c >= 0 such that c * nums[i] is representable in i64 for all 0 <= i < n. -/
theorem spec_15 (nums nums' multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_repr : ∀ i, i < n → I64Repr (c * entry nums i))
    (h_len : n = (Slice.len nums').val)
    (h_entry : ∀ i, i < n → entry nums' i = c * entry nums i) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r'.val = c * r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums nums' multipliers : Slice Std.I64) (n m : ℕ) (c : ℤ)
    (h : Precond nums multipliers n m)
    (hc : 0 ≤ c)
    (h_repr : ∀ i, i < n → I64Repr (c * entry nums i))
    (h_len : n = (Slice.len nums').val)
    (h_entry : ∀ i, i < n → entry nums' i = c * entry nums i), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums' multipliers = ok r' ∧
      r'.val = c * r.val) := by
  sorry

/-- For every nums, multipliers, and multipliers' satisfying the preconditions, whenever the function returns a result r for (nums, multipliers) and a result r' for (nums, multipliers'), we have r' >= r.
  Preconditions: n = len(nums), m = len(multipliers), 1 <= m <= 300, m <= n <= 100000, for every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] >= 0, for every j with 0 <= j < m, -1000 <= multipliers[j] <= 1000, and multipliers' is a slice of length m with -1000 <= multipliers'[j] <= 1000 and multipliers'[j] >= multipliers[j] for all 0 <= j < m. -/
theorem spec_16 (nums multipliers multipliers' : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_len : m = (Slice.len multipliers').val)
    (h_bounds : ∀ j, j < m → -1000 ≤ entry multipliers' j ∧ entry multipliers' j ≤ 1000)
    (h_ge : ∀ j, j < m → entry multipliers j ≤ entry multipliers' j) :
    ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums multipliers' = ok r' ∧
      r.val ≤ r'.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums multipliers multipliers' : Slice Std.I64) (n m : ℕ)
    (h : Precond nums multipliers n m)
    (h_nums_nn : ∀ i, i < n → 0 ≤ entry nums i)
    (h_len : m = (Slice.len multipliers').val)
    (h_bounds : ∀ j, j < m → -1000 ≤ entry multipliers' j ∧ entry multipliers' j ≤ 1000)
    (h_ge : ∀ j, j < m → entry multipliers j ≤ entry multipliers' j), ∃ r r' : Std.I64,
      Aegis.MaximumScore.maximum_score nums multipliers = ok r ∧
      Aegis.MaximumScore.maximum_score nums multipliers' = ok r' ∧
      r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaximumScore
