import Aegis.MaxResult.Code.Funs

/-!
# Specifications of `Aegis.MaxResult.max_result`

LeetCode problem `jump-game-vi`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxResult

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def nthVal (nums : Slice Std.I64) (i : Nat) : Int := (vals nums).getD i 0

  def stepOK (k : Int) (a b : Nat) : Prop :=
    1 ≤ (b : Int) - (a : Int) ∧ (b : Int) - (a : Int) ≤ k

  def IsRoute (n : Nat) (k : Int) (p : List Nat) : Prop :=
    p.head? = some 0 ∧
      p.getLast? = some (n - 1) ∧
        p.Pairwise (· < ·) ∧
          ∀ ⦃a b : Nat⦄, (a, b) ∈ p.zip p.tail → stepOK k a b

  def routeScore (nums : Slice Std.I64) (p : List Nat) : Int :=
    (p.map (fun i => nthVal nums i)).sum

  def skipScore (nums : Slice Std.I64) : Int :=
    let v := vals nums
    let n := v.length
    v.getD 0 0 + v.getD (n - 1) 0 +
      ((List.range (n - 2)).map (fun i => max (v.getD (i + 1) 0) 0)).sum

  /-- A route is a finite sequence of indices p_0, ..., p_m such that p_0 = 0, p_m = n - 1, p_0 < p_1 < ... < p_m, and 1 <= p_{t+1} - p_t <= k for every t with 0 <= t < m. The score of a route is sum_{t=0}^{m} nums[p_t]. The function returns a result r (it does not fail) and r is the maximum score among all routes; equivalently, some route has score r and every route has score at most r.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.MaxResult.max_result nums k = ok r ∧
          (∃ p : List Nat, IsRoute nums.val.length k.val p ∧ routeScore nums p = r.val) ∧
            (∀ (p : List Nat), IsRoute nums.val.length k.val p → routeScore nums p ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64,
          Aegis.MaxResult.max_result nums k = ok r ∧
            (∃ p : List Nat, IsRoute nums.val.length k.val p ∧ routeScore nums p = r.val) ∧
              (∀ (p : List Nat), IsRoute nums.val.length k.val p → routeScore nums p ≤ r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∃ r : Std.I64, Aegis.MaxResult.max_result nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MaxResult.max_result nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exist an integer m >= 0 and indices p_0, ..., p_m such that p_0 = 0, p_m = n - 1, p_0 < p_1 < ... < p_m, 1 <= p_{t+1} - p_t <= k for every t with 0 <= t < m, and r = sum_{t=0}^{m} nums[p_t].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
        ∃ p : List Nat, IsRoute nums.val.length k.val p ∧ routeScore nums p = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
          ∃ p : List Nat, IsRoute nums.val.length k.val p ∧ routeScore nums p = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer m >= 0 and every sequence of indices p_0, ..., p_m such that p_0 = 0, p_m = n - 1, p_0 < p_1 < ... < p_m, and 1 <= p_{t+1} - p_t <= k for every t with 0 <= t < m, it holds that sum_{t=0}^{m} nums[p_t] <= r.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
        ∀ (p : List Nat), IsRoute nums.val.length k.val p → routeScore nums p ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
          ∀ (p : List Nat), IsRoute nums.val.length k.val p → routeScore nums p ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= sum_{i=0}^{n-1} nums[i].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → (vals nums).sum ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → (vals nums).sum ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= nums[0] + nums[n-1] + sum_{i=1}^{n-2} max(nums[i], 0).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val ≤ skipScore nums := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val ≤ skipScore nums) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} nums[i].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, k = 1, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000) (hk_eq : k.val = 1)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val = (vals nums).sum := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000) (hk_eq : k.val = 1)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val = (vals nums).sum) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[0] + nums[n-1] + sum_{i=1}^{n-2} max(nums[i], 0).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, n - 1 <= k <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : (nums.val.length : Int) - 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val = skipScore nums := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_lo : 2 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : (nums.val.length : Int) - 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r : Std.I64), Aegis.MaxResult.max_result nums k = ok r → r.val = skipScore nums) := by
    sorry

  /-- Whenever max_result(nums, k1) returns a result r1 and max_result(nums, k2) returns a result r2, r1 <= r2.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, 1 <= k1 <= k2 <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. -/
  theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∀ (r1 : Std.I64), Aegis.MaxResult.max_result nums k1 = ok r1 →
        ∀ (r2 : Std.I64), Aegis.MaxResult.max_result nums k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk1_lo : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_hi : k2.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ (r1 : Std.I64), Aegis.MaxResult.max_result nums k1 = ok r1 →
          ∀ (r2 : Std.I64), Aegis.MaxResult.max_result nums k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever max_result(nums, k) returns a result r and max_result(nums', k) returns a result r', r <= r'.
    Preconditions: Let n = len(nums) = len(nums'). Assume 1 <= n <= 100000, 1 <= k <= 100000, -10000 <= nums[i] <= 10000 and -10000 <= nums'[i] <= 10000 for every i with 0 <= i < n, and nums[i] <= nums'[i] for every i with 0 <= i < n. -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen : nums'.val.length = nums.val.length)
      (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
      (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
        -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hbnd' : ∀ (i : Nat) (hi : i < nums'.val.length),
        -10000 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
      (hle : ∀ (i : Nat) (hi : i < nums.val.length),
        (nums.val[i]).val ≤ (nums'.val[i]'(by omega)).val) :
      ∀ (r r' : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
        Aegis.MaxResult.max_result nums' k = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen : nums'.val.length = nums.val.length)
        (hn_lo : 1 ≤ nums.val.length) (hn_hi : nums.val.length ≤ 100000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100000)
        (hbnd : ∀ (i : Nat) (hi : i < nums.val.length),
          -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hbnd' : ∀ (i : Nat) (hi : i < nums'.val.length),
          -10000 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
        (hle : ∀ (i : Nat) (hi : i < nums.val.length),
          (nums.val[i]).val ≤ (nums'.val[i]'(by omega)).val), ∀ (r r' : Std.I64), Aegis.MaxResult.max_result nums k = ok r →
          Aegis.MaxResult.max_result nums' k = ok r' → r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MaxResult
