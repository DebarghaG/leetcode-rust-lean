import Aegis.WaysToSplit.Code.Funs

/-!
# Specifications of `Aegis.WaysToSplit.ways_to_split`

LeetCode problem `ways-to-split-array-into-three-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WaysToSplit

  namespace AegisSpec.WaysToSplit

  def modulus : Nat := 1000000007

  def segSum (nums : Slice Std.I64) (lo hi : Nat) : Int :=
    (((nums.val.drop lo).take (hi - lo)).map (fun x => x.val)).sum

  def leftSum (nums : Slice Std.I64) (a : Nat) : Int := segSum nums 0 a

  def midSum (nums : Slice Std.I64) (a b : Nat) : Int := segSum nums a b

  def rightSum (nums : Slice Std.I64) (b : Nat) : Int := segSum nums b nums.val.length

  def GoodSplit (nums : Slice Std.I64) (a b : Nat) : Prop :=
    leftSum nums a ≤ midSum nums a b ∧ midSum nums a b ≤ rightSum nums b

  instance decidableGoodSplit (nums : Slice Std.I64) (a b : Nat) :
      Decidable (GoodSplit nums a b) := by
    unfold GoodSplit
    infer_instance

  def goodCount (nums : Slice Std.I64) : Nat :=
    ((List.range nums.val.length).product (List.range nums.val.length)).filter
      (fun p => decide (1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ nums.val.length - 1 ∧
        GoodSplit nums p.1 p.2)) |>.length

  def ScaledSlice (c : Int) (nums nums_c : Slice Std.I64)
      (hlen : nums_c.val.length = nums.val.length) : Prop :=
    ∀ (i : Nat) (h : i < nums.val.length),
      (nums_c.val[i]'(by omega)).val = c * (nums.val[i]).val

  /-- Let n = len(nums). For integers a and b with 1 <= a < b <= n-1, define L(a) = sum_{t=0}^{a-1} nums[t], M(a,b) = sum_{t=a}^{b-1} nums[t], and R(b) = sum_{t=b}^{n-1} nums[t]. Let C be the number of pairs (a,b) with 1 <= a < b <= n-1 such that L(a) <= M(a,b) and M(a,b) <= R(b). Whenever `ways_to_split` returns a result r, r = C mod (10^9 + 7).
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) :
      r.val = ((goodCount nums % modulus : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hr : ways_to_split nums = ok r), r.val = ((goodCount nums % modulus : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, `ways_to_split` returns a result (it does not fail).
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
      ∃ r : Std.I64, ways_to_split nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, ways_to_split nums = ok r) := by
    sorry

  /-- Whenever `ways_to_split` returns a result r, 0 <= r <= 10^9 + 6.
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) :
      0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hr : ways_to_split nums = ok r), 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- Whenever `ways_to_split` returns a result r with r != 0, there exist integers a and b with 1 <= a < b <= n-1 such that, with L(a) = sum_{t=0}^{a-1} nums[t], M(a,b) = sum_{t=a}^{b-1} nums[t], and R(b) = sum_{t=b}^{n-1} nums[t], we have L(a) <= M(a,b) and M(a,b) <= R(b).
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) (hne : r.val ≠ 0) :
      ∃ a b : Nat, 1 ≤ a ∧ a < b ∧ b ≤ n - 1 ∧ GoodSplit nums a b := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hr : ways_to_split nums = ok r) (hne : r.val ≠ 0), ∃ a b : Nat, 1 ≤ a ∧ a < b ∧ b ≤ n - 1 ∧ GoodSplit nums a b) := by
    sorry

  /-- Whenever `ways_to_split` returns a result r, r = 1 if nums[0] <= nums[1] and nums[1] <= nums[2], and r = 0 otherwise.
    Preconditions: len(nums) = 3; 0 <= nums[0] <= 10000; 0 <= nums[1] <= 10000; 0 <= nums[2] <= 10000. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : nums.val.length = 3)
      (h0 : 0 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 10000)
      (h1 : 0 ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ 10000)
      (h2 : 0 ≤ (nums.val[2]).val ∧ (nums.val[2]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) :
      r.val = if (nums.val[0]).val ≤ (nums.val[1]).val ∧
          (nums.val[1]).val ≤ (nums.val[2]).val then 1 else 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : nums.val.length = 3)
        (h0 : 0 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 10000)
        (h1 : 0 ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ 10000)
        (h2 : 0 ≤ (nums.val[2]).val ∧ (nums.val[2]).val ≤ 10000)
        (hr : ways_to_split nums = ok r), r.val = if (nums.val[0]).val ≤ (nums.val[1]).val ∧
            (nums.val[1]).val ≤ (nums.val[2]).val then 1 else 0) := by
    sorry

  /-- Whenever `ways_to_split` returns a result r, r = ((n-1)*(n-2)/2) mod (10^9 + 7).
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, nums[i] = 0. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hz : ∀ (i : Nat) (_ : i < n), (nums.val[i]).val = 0)
      (hr : ways_to_split nums = ok r) :
      r.val = ((((n - 1) * (n - 2) / 2) % modulus : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hz : ∀ (i : Nat) (_ : i < n), (nums.val[i]).val = 0)
        (hr : ways_to_split nums = ok r), r.val = ((((n - 1) * (n - 2) / 2) % modulus : Nat) : Int)) := by
    sorry

  /-- Let n = len(nums) and S = sum_{t=0}^{n-1} nums[t]. If 3*nums[0] > S, then whenever `ways_to_split` returns a result r, r = 0.
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hS : 3 * (nums.val[0]).val > segSum nums 0 n)
      (hr : ways_to_split nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hS : 3 * (nums.val[0]).val > segSum nums 0 n)
        (hr : ways_to_split nums = ok r), r.val = 0) := by
    sorry

  /-- Whenever `ways_to_split` returns a result r, r <= (n-1)*(n-2)/2.
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) :
      r.val ≤ (((n - 1) * (n - 2) / 2 : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (r : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hr : ways_to_split nums = ok r), r.val ≤ (((n - 1) * (n - 2) / 2 : Nat) : Int)) := by
    sorry

  /-- Let c be any integer with 2 <= c such that c*nums[i] <= 10000 for every i with 0 <= i < n. Let nums_c be the slice of length n with nums_c[i] = c*nums[i]. Whenever `ways_to_split` returns a result r on nums and a result r_c on nums_c, we have r = r_c.
    Preconditions: n = len(nums); 3 <= n <= 100000; for every i with 0 <= i < n, 0 <= nums[i] <= 10000. -/
  theorem spec_9 (nums nums_c : Slice Std.I64) (n : Nat) (c : Int) (r r_c : Std.I64)
      (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
      (hb : ∀ (i : Nat) (_ : i < n),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
      (hc : 2 ≤ c)
      (hlen : nums_c.val.length = nums.val.length)
      (hscale : ScaledSlice c nums nums_c hlen)
      (hbound : ∀ (i : Nat) (_ : i < n), c * (nums.val[i]).val ≤ 10000)
      (hr : ways_to_split nums = ok r) (hrc : ways_to_split nums_c = ok r_c) :
      r.val = r_c.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums_c : Slice Std.I64) (n : Nat) (c : Int) (r r_c : Std.I64)
        (hn : n = nums.val.length) (h3 : 3 ≤ n) (h100000 : n ≤ 100000)
        (hb : ∀ (i : Nat) (_ : i < n),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
        (hc : 2 ≤ c)
        (hlen : nums_c.val.length = nums.val.length)
        (hscale : ScaledSlice c nums nums_c hlen)
        (hbound : ∀ (i : Nat) (_ : i < n), c * (nums.val[i]).val ≤ 10000)
        (hr : ways_to_split nums = ok r) (hrc : ways_to_split nums_c = ok r_c), r.val = r_c.val) := by
    sorry

  end AegisSpec.WaysToSplit
