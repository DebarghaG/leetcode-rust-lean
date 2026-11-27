import Aegis.SumOfSquares.Code.Funs

/-!
# Specifications of `Aegis.SumOfSquares.sum_of_squares`

LeetCode problem `sum-of-squares-of-special-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOfSquares

  def tau (n : Nat) : Nat := (Nat.divisors n).card

  /-- The function returns a result r and does not fail, and r = sum over j with 0 <= j < n and n mod (j+1) = 0 of nums[j] * nums[j]. Equivalently, using the problem's 1-indexed positions i = j+1, r = sum over i with 1 <= i <= n and n mod i = 0 of nums[i-1] * nums[i-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_1
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50) :
    ∃ r, Aegis.SumOfSquares.sum_of_squares nums = ok r ∧
      r.val = ∑ j : Fin n,
        if n % (j.val + 1) = 0
        then (nums.val[j.val]'(by omega)).val * (nums.val[j.val]'(by omega)).val
        else 0 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50), ∃ r, Aegis.SumOfSquares.sum_of_squares nums = ok r ∧
        r.val = ∑ j : Fin n,
          if n % (j.val + 1) = 0
          then (nums.val[j.val]'(by omega)).val * (nums.val[j.val]'(by omega)).val
          else 0) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_2
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50) :
    ∃ r, Aegis.SumOfSquares.sum_of_squares nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50), ∃ r, Aegis.SumOfSquares.sum_of_squares nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum over j with 0 <= j < n of nums[j] * nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_3
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    r.val ≤ ∑ j : Fin n,
      (nums.val[j.val]'(by omega)).val * (nums.val[j.val]'(by omega)).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), r.val ≤ ∑ j : Fin n,
        (nums.val[j.val]'(by omega)).val * (nums.val[j.val]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 125000.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_4
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    r.val ≤ 125000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), r.val ≤ 125000) := by
    sorry

  /-- If n > 1, whenever the function returns a result r, r >= nums[0] * nums[0] + nums[n-1] * nums[n-1].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50, for every j with 0 <= j < n, 1 <= nums[j] <= 50, and n > 1. -/
  theorem spec_5
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (hgt : 1 < n)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    (nums.val[0]'(by omega)).val * (nums.val[0]'(by omega)).val
        + (nums.val[n - 1]'(by omega)).val * (nums.val[n - 1]'(by omega)).val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (hgt : 1 < n)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), (nums.val[0]'(by omega)).val * (nums.val[0]'(by omega)).val
          + (nums.val[n - 1]'(by omega)).val * (nums.val[n - 1]'(by omega)).val ≤ r.val) := by
    sorry

  /-- Whenever the function on nums returns r and the function on nums' returns r', we have r = r'.
    Preconditions: Let n = len(nums) = len(nums'). Both nums and nums' satisfy: 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50 and 1 <= nums'[j] <= 50. Assume nums[j] = nums'[j] for every j with 0 <= j < n and n mod (j+1) = 0. -/
  theorem spec_6
    (nums nums' : Slice Std.I64) (n : Nat)
    (hn : nums.val.length = n) (hn' : nums'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (hb' : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
    (heq : ∀ (j : Nat) (hj : j < n), n % (j + 1) = 0 →
      (nums.val[j]'(by omega)).val = (nums'.val[j]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
    (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r') :
    r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn' : nums'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (hb' : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
      (heq : ∀ (j : Nat) (hj : j < n), n % (j + 1) = 0 →
        (nums.val[j]'(by omega)).val = (nums'.val[j]'(by omega)).val)
      (r r' : Std.I64)
      (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
      (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function on nums returns r and the function on nums' returns r', we have r <= r'.
    Preconditions: Let n = len(nums) = len(nums'). Both nums and nums' satisfy: 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50 and 1 <= nums'[j] <= 50. Assume nums[j] <= nums'[j] for every j with 0 <= j < n. -/
  theorem spec_7
    (nums nums' : Slice Std.I64) (n : Nat)
    (hn : nums.val.length = n) (hn' : nums'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (hb' : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
    (hle : ∀ (j : Nat) (hj : j < n),
      (nums.val[j]'(by omega)).val ≤ (nums'.val[j]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
    (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r') :
    r.val ≤ r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn' : nums'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (hb' : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
      (hle : ∀ (j : Nat) (hj : j < n),
        (nums.val[j]'(by omega)).val ≤ (nums'.val[j]'(by omega)).val)
      (r r' : Std.I64)
      (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
      (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function on nums returns r and the function on nums' returns r', we have r' = c * c * r.
    Preconditions: Let n = len(nums) = len(nums'). Both nums and nums' satisfy: 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50 and 1 <= nums'[j] <= 50. Let c be a positive integer such that nums'[j] = c * nums[j] for every j with 0 <= j < n. -/
  theorem spec_8
    (nums nums' : Slice Std.I64) (n : Nat)
    (hn : nums.val.length = n) (hn' : nums'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (hb' : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
    (c : Nat) (hc : 0 < c)
    (hmul : ∀ (j : Nat) (hj : j < n),
      (nums'.val[j]'(by omega)).val = (c : Int) * (nums.val[j]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
    (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r') :
    r'.val = (c : Int) * (c : Int) * r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn' : nums'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (hb' : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
      (c : Nat) (hc : 0 < c)
      (hmul : ∀ (j : Nat) (hj : j < n),
        (nums'.val[j]'(by omega)).val = (c : Int) * (nums.val[j]'(by omega)).val)
      (r r' : Std.I64)
      (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
      (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r'), r'.val = (c : Int) * (c : Int) * r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < n and n mod (j+1) = 0, r >= nums[j] * nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_9
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    ∀ (j : Nat) (hj : j < n), n % (j + 1) = 0 →
      (nums.val[j]'(by omega)).val * (nums.val[j]'(by omega)).val ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), ∀ (j : Nat) (hj : j < n), n % (j + 1) = 0 →
        (nums.val[j]'(by omega)).val * (nums.val[j]'(by omega)).val ≤ r.val) := by
    sorry

  /-- Whenever the function on nums returns r and the function on nums' returns r', r' - r = nums'[j0] * nums'[j0] - nums[j0] * nums[j0].
    Preconditions: Let n = len(nums) = len(nums'). Both nums and nums' satisfy: 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50 and 1 <= nums'[j] <= 50. There is an index j0 with 0 <= j0 < n and n mod (j0+1) = 0, and for every k with 0 <= k < n and k != j0, nums'[k] = nums[k]. -/
  theorem spec_10
    (nums nums' : Slice Std.I64) (n : Nat)
    (hn : nums.val.length = n) (hn' : nums'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (hb' : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
    (j0 : Nat) (hj0 : j0 < n) (hdiv : n % (j0 + 1) = 0)
    (hother : ∀ (k : Nat) (hk : k < n), k ≠ j0 →
      (nums'.val[k]'(by omega)).val = (nums.val[k]'(by omega)).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
    (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r') :
    r'.val - r.val
      = (nums'.val[j0]'(by omega)).val * (nums'.val[j0]'(by omega)).val
        - (nums.val[j0]'(by omega)).val * (nums.val[j0]'(by omega)).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn' : nums'.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (hb' : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums'.val[j]'(by omega)).val ∧ (nums'.val[j]'(by omega)).val ≤ 50)
      (j0 : Nat) (hj0 : j0 < n) (hdiv : n % (j0 + 1) = 0)
      (hother : ∀ (k : Nat) (hk : k < n), k ≠ j0 →
        (nums'.val[k]'(by omega)).val = (nums.val[k]'(by omega)).val)
      (r r' : Std.I64)
      (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r)
      (hr' : Aegis.SumOfSquares.sum_of_squares nums' = ok r'), r'.val - r.val
        = (nums'.val[j0]'(by omega)).val * (nums'.val[j0]'(by omega)).val
          - (nums.val[j0]'(by omega)).val * (nums.val[j0]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r, r >= tau(n), where tau(n) is the number of positive divisors of n, i.e. the number of special positions. (Each special element is at least 1, and there are tau(n) of them.)
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_11
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    (tau n : Int) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), (tau n : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = tau(n) * v * v, where tau(n) is the number of positive divisors of n. (Generalises the all-ones case to any constant array.)
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and there is an integer v with 1 <= v <= 50 such that nums[j] = v for every j with 0 <= j < n. -/
  theorem spec_12
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (v : Int) (hv1 : 1 ≤ v) (hv2 : v ≤ 50)
    (hconst : ∀ (j : Nat) (hj : j < n),
      (nums.val[j]'(by omega)).val = v)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    r.val = (tau n : Int) * v * v := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (v : Int) (hv1 : 1 ≤ v) (hv2 : v ≤ 50)
      (hconst : ∀ (j : Nat) (hj : j < n),
        (nums.val[j]'(by omega)).val = v)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), r.val = (tau n : Int) * v * v) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2500 * tau(n), where tau(n) is the number of positive divisors of n. (Each of the tau(n) special squares is at most 2500; sharper than the 125000 bound.)
    Preconditions: Let n = len(nums). Assume 1 <= n <= 50 and for every j with 0 <= j < n, 1 <= nums[j] <= 50. -/
  theorem spec_13
    (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
    (hb : ∀ (j : Nat) (hj : j < n),
      1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
    (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r) :
    r.val ≤ 2500 * (tau n : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 50)
      (hb : ∀ (j : Nat) (hj : j < n),
        1 ≤ (nums.val[j]'(by omega)).val ∧ (nums.val[j]'(by omega)).val ≤ 50)
      (r : Std.I64) (hr : Aegis.SumOfSquares.sum_of_squares nums = ok r), r.val ≤ 2500 * (tau n : Int)) := by
    sorry

  end AegisSpec.SumOfSquares
