import Aegis.MinNumberOfSeconds.Code.Funs

/-!
# Specifications of `Aegis.MinNumberOfSeconds.min_number_of_seconds`

LeetCode problem `minimum-number-of-seconds-to-make-mountain-height-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AegisSpec.MinNumberOfSeconds

def slen (workerTimes : Slice Std.I64) : ℕ := workerTimes.val.length

def wt (workerTimes : Slice Std.I64) (i : ℕ) : ℤ :=
  match workerTimes.val[i]? with
  | some w => w.val
  | none => 0

def costZ (w x : ℤ) : ℤ := w * x * (x + 1) / 2

def cost (w : ℤ) (x : ℕ) : ℤ := costZ w (x : ℤ)

def sumRange (n : ℕ) (f : ℕ → ℤ) : ℤ := ∑ i ∈ Finset.range n, f i

def Feasible (n : ℕ) (w : ℕ → ℤ) (H T : ℤ) : Prop :=
  ∃ x : ℕ → ℕ, sumRange n (fun i => (x i : ℤ)) = H ∧ ∀ i, i < n → cost (w i) (x i) ≤ T

def capBounded (w T : ℤ) (b : ℕ) : ℕ := Nat.findGreatest (fun x => cost w x ≤ T) b

def cap (w T : ℤ) : ℕ := capBounded w T (T.toNat + 1)

def capSum (n : ℕ) (w : ℕ → ℤ) (T : ℤ) : ℤ := ∑ i ∈ Finset.range n, (cap (w i) T : ℤ)

def rangeMin (n : ℕ) (f : ℕ → ℤ) : ℤ := (((List.range n).map f).min?).getD 0

def PermOf (n : ℕ) (w w' : ℕ → ℤ) : Prop :=
  ∃ p : ℕ → ℕ,
    (∀ i, i < n → p i < n) ∧
      (∀ i, i < n → ∀ j, j < n → p i = p j → i = j) ∧
        (∀ j, j < n → ∃ i, i < n ∧ p i = j) ∧ ∀ i, i < n → w' i = w (p i)

def Inserted (n : ℕ) (w w' : ℕ → ℤ) : Prop :=
  ∃ k, k ≤ n ∧ (∀ i, i < k → w' i = w i) ∧ ∀ i, i < n → k ≤ i → w' (i + 1) = w i

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns a result r, r is the least nonnegative integer T for which there exist nonnegative integers x_0, ..., x_{n-1} satisfying sum_{i=0}^{n-1} x_i = mountainHeight and, for every i with 0 <= i < n, workerTimes[i] * x_i * (x_i + 1) / 2 <= T.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_1 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    0 ≤ r.val ∧ Feasible n (wt workerTimes) mountainHeight.val r.val ∧
      ∀ T : ℤ, 0 ≤ T → Feasible n (wt workerTimes) mountainHeight.val T → r.val ≤ T := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), 0 ≤ r.val ∧ Feasible n (wt workerTimes) mountainHeight.val r.val ∧
      ∀ T : ℤ, 0 ≤ T → Feasible n (wt workerTimes) mountainHeight.val T → r.val ≤ T) := by
  sorry

/-- For every mountainHeight and workerTimes satisfying the preconditions, min_number_of_seconds(mountainHeight, workerTimes) returns a result r; in particular it does not fail, panic, index out of bounds, or report arithmetic overflow.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_2 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000), ∃ r : Std.I64, Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, there exist nonnegative integers x_0, ..., x_{n-1} such that sum_{i=0}^{n-1} x_i = mountainHeight and, for every i with 0 <= i < n, workerTimes[i] * x_i * (x_i + 1) / 2 <= r.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_3 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    Feasible n (wt workerTimes) mountainHeight.val r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), Feasible n (wt workerTimes) mountainHeight.val r.val) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, for every integer T with 0 <= T < r there do not exist nonnegative integers x_0, ..., x_{n-1} such that sum_{i=0}^{n-1} x_i = mountainHeight and workerTimes[i] * x_i * (x_i + 1) / 2 <= T for every i with 0 <= i < n.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_4 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ Feasible n (wt workerTimes) mountainHeight.val T := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), ∀ T : ℤ, 0 ≤ T → T < r.val → ¬ Feasible n (wt workerTimes) mountainHeight.val T) := by
  sorry

/-- For an integer T >= 0 and an index i with 0 <= i < n, let cap_i(T) be the largest integer x >= 0 such that workerTimes[i] * x * (x + 1) / 2 <= T. Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, for every integer T >= 0, T >= r if and only if sum_{i=0}^{n-1} cap_i(T) >= mountainHeight.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_5 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    ∀ T : ℤ, 0 ≤ T → (r.val ≤ T ↔ mountainHeight.val ≤ capSum n (wt workerTimes) T) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), ∀ T : ℤ, 0 ≤ T → (r.val ≤ T ↔ mountainHeight.val ≤ capSum n (wt workerTimes) T)) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, r >= min { workerTimes[i] | 0 <= i < n }.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_6 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    rangeMin n (wt workerTimes) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), rangeMin n (wt workerTimes) ≤ r.val) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, r <= min { workerTimes[i] * mountainHeight * (mountainHeight + 1) / 2 | 0 <= i < n }.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_7 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    r.val ≤ rangeMin n (fun i => costZ (wt workerTimes i) mountainHeight.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), r.val ≤ rangeMin n (fun i => costZ (wt workerTimes i) mountainHeight.val)) := by
  sorry

/-- Whenever min_number_of_seconds(1, workerTimes) returns r, r = min { workerTimes[i] | 0 <= i < n }.
  Preconditions: mountainHeight = 1; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_8 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_eq : mountainHeight.val = 1)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    r.val = rangeMin n (wt workerTimes) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_eq : mountainHeight.val = 1)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), r.val = rangeMin n (wt workerTimes)) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, r = workerTimes[0] * mountainHeight * (mountainHeight + 1) / 2.
  Preconditions: n = len(workerTimes) = 1; mountainHeight is an integer with 1 <= mountainHeight <= 100000; 1 <= workerTimes[0] <= 1000000. -/
theorem spec_9 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_eq : n = 1)
    (hw_low : 1 ≤ wt workerTimes 0) (hw_high : wt workerTimes 0 ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    r.val = costZ (wt workerTimes 0) mountainHeight.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_eq : n = 1)
    (hw_low : 1 ≤ wt workerTimes 0) (hw_high : wt workerTimes 0 ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), r.val = costZ (wt workerTimes 0) mountainHeight.val) := by
  sorry

/-- If r1 is the result of min_number_of_seconds(mountainHeight1, workerTimes) and r2 is the result of min_number_of_seconds(mountainHeight2, workerTimes), then r1 <= r2.
  Preconditions: mountainHeight1 and mountainHeight2 are integers with 1 <= mountainHeight1 <= mountainHeight2 <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_10 (mountainHeight1 mountainHeight2 : Std.I64) (workerTimes : Slice Std.I64)
    (n : ℕ)
    (h1_low : 1 ≤ mountainHeight1.val)
    (h12 : mountainHeight1.val ≤ mountainHeight2.val)
    (h2_high : mountainHeight2.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight1 workerTimes = ok r1)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight2 workerTimes = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mountainHeight1 mountainHeight2 : Std.I64) (workerTimes : Slice Std.I64)
    (n : ℕ)
    (h1_low : 1 ≤ mountainHeight1.val)
    (h12 : mountainHeight1.val ≤ mountainHeight2.val)
    (h2_high : mountainHeight2.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight1 workerTimes = ok r1)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight2 workerTimes = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If r is the result of min_number_of_seconds(mountainHeight, workerTimes) and r2 is the result of min_number_of_seconds(mountainHeight, workerTimes2), then r = r2.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes and workerTimes2 are slices of integers of the same length n with 1 <= n <= 10000, all entries in [1, 1000000], and workerTimes2 is a permutation of workerTimes (there is a bijection p on {0,...,n-1} with workerTimes2[i] = workerTimes[p(i)] for every i). -/
theorem spec_11 (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : n = slen workerTimes2)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (hw2_low : ∀ i, i < n → 1 ≤ wt workerTimes2 i)
    (hw2_high : ∀ i, i < n → wt workerTimes2 i ≤ 1000000)
    (hperm : PermOf n (wt workerTimes) (wt workerTimes2))
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2) :
    r.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : n = slen workerTimes2)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (hw2_low : ∀ i, i < n → 1 ≤ wt workerTimes2 i)
    (hw2_high : ∀ i, i < n → wt workerTimes2 i ≤ 1000000)
    (hperm : PermOf n (wt workerTimes) (wt workerTimes2))
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2), r.val = r2.val) := by
  sorry

/-- If r is the result of min_number_of_seconds(mountainHeight, workerTimes) and r2 is the result of min_number_of_seconds(mountainHeight, workerTimes2), then r2 <= r.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 9999, and 1 <= workerTimes[i] <= 1000000 for every i; workerTimes2 is obtained from workerTimes by inserting one additional integer w with 1 <= w <= 1000000, so len(workerTimes2) = n + 1 <= 10000. -/
theorem spec_12 (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (w : Std.I64)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : slen workerTimes2 = n + 1)
    (hn_low : 1 ≤ n) (hn_high : n + 1 ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (hw_inserted_low : 1 ≤ w.val) (hw_inserted_high : w.val ≤ 1000000)
    (hins : Inserted n (wt workerTimes) (wt workerTimes2))
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2) :
    r2.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (w : Std.I64)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : slen workerTimes2 = n + 1)
    (hn_low : 1 ≤ n) (hn_high : n + 1 ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (hw_inserted_low : 1 ≤ w.val) (hw_inserted_high : w.val ≤ 1000000)
    (hins : Inserted n (wt workerTimes) (wt workerTimes2))
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2), r2.val ≤ r.val) := by
  sorry

/-- If r is the result of min_number_of_seconds(mountainHeight, workerTimes) and r2 is the result of min_number_of_seconds(mountainHeight, workerTimes2), then r2 = c * r.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes and workerTimes2 are slices of integers of the same length n, 1 <= n <= 10000, all entries of workerTimes2 are in [1, 1000000], and there is a positive integer c such that workerTimes2[i] = c * workerTimes[i] for every i with 0 <= i < n. -/
theorem spec_13 (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (c : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : n = slen workerTimes2)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hc : 0 < c)
    (hw2_low : ∀ i, i < n → 1 ≤ wt workerTimes2 i)
    (hw2_high : ∀ i, i < n → wt workerTimes2 i ≤ 1000000)
    (hscale : ∀ i, i < n → wt workerTimes2 i = (c : ℤ) * wt workerTimes i)
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2) :
    r2.val = (c : ℤ) * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes workerTimes2 : Slice Std.I64) (n : ℕ)
    (c : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn2 : n = slen workerTimes2)
    (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hc : 0 < c)
    (hw2_low : ∀ i, i < n → 1 ≤ wt workerTimes2 i)
    (hw2_high : ∀ i, i < n → wt workerTimes2 i ≤ 1000000)
    (hscale : ∀ i, i < n → wt workerTimes2 i = (c : ℤ) * wt workerTimes i)
    (r r2 : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r)
    (hr2 : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes2 = ok r2), r2.val = (c : ℤ) * r.val) := by
  sorry

/-- Whenever min_number_of_seconds(mountainHeight, workerTimes) returns r, there exist nonnegative integers x_0, ..., x_{n-1} such that sum_{i=0}^{n-1} x_i = mountainHeight, for every i with 0 <= i < n workerTimes[i] * x_i * (x_i + 1) / 2 <= r, and there exists an index j with 0 <= j < n such that workerTimes[j] * x_j * (x_j + 1) / 2 = r.
  Preconditions: mountainHeight is an integer with 1 <= mountainHeight <= 100000; workerTimes is a slice of integers with n = len(workerTimes), 1 <= n <= 10000, and 1 <= workerTimes[i] <= 1000000 for every i with 0 <= i < n. -/
theorem spec_14 (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r) :
    ∃ x : ℕ → ℕ, sumRange n (fun i => (x i : ℤ)) = mountainHeight.val ∧
      (∀ i, i < n → cost (wt workerTimes i) (x i) ≤ r.val) ∧
      ∃ j, j < n ∧ cost (wt workerTimes j) (x j) = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (mountainHeight : Std.I64) (workerTimes : Slice Std.I64) (n : ℕ)
    (hm_low : 1 ≤ mountainHeight.val) (hm_high : mountainHeight.val ≤ 100000)
    (hn : n = slen workerTimes) (hn_low : 1 ≤ n) (hn_high : n ≤ 10000)
    (hw_low : ∀ i, i < n → 1 ≤ wt workerTimes i)
    (hw_high : ∀ i, i < n → wt workerTimes i ≤ 1000000)
    (r : Std.I64)
    (hr : Aegis.MinNumberOfSeconds.min_number_of_seconds mountainHeight workerTimes = ok r), ∃ x : ℕ → ℕ, sumRange n (fun i => (x i : ℤ)) = mountainHeight.val ∧
      (∀ i, i < n → cost (wt workerTimes i) (x i) ≤ r.val) ∧
      ∃ j, j < n ∧ cost (wt workerTimes j) (x j) = r.val) := by
  sorry

end AegisSpec.MinNumberOfSeconds
