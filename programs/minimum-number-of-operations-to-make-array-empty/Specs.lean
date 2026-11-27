import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-operations-to-make-array-empty`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  open Classical

  def ival (x : I64) : Int := IScalar.val x

  def vals (nums : Slice I64) : List Int := nums.val.map (fun x => ival x)

  def cnt (nums : Slice I64) (x : Int) : Nat := (vals nums).count x

  def values (nums : Slice I64) : Finset Int := (vals nums).toFinset

  def occurs (nums : Slice I64) (x : Int) : Prop := x ∈ values nums

  def ceilDiv3 (c : Nat) : Nat := (c + 2) / 3

  def sumCeil (nums : Slice I64) : Nat := ∑ x ∈ values nums, ceilDiv3 (cnt nums x)

  def eraseK : List Int → Int → Nat → List Int
    | [], _, _ => []
    | l, _, 0 => l
    | y :: ys, x, k + 1 => if y = x then eraseK ys x k else y :: eraseK ys x (k + 1)

  def Step (l l' : List Int) : Prop :=
    ∃ x k, (k = 2 ∨ k = 3) ∧ k ≤ l.count x ∧ l' = eraseK l x k

  inductive ReachIn : Nat → List Int → List Int → Prop
    | zero (l : List Int) : ReachIn 0 l l
    | succ {n : Nat} {l l' l'' : List Int} :
        Step l l' → ReachIn n l' l'' → ReachIn (n + 1) l l''

  def CanEmpty (nums : Slice I64) : Prop := ∃ n : Nat, ReachIn n (vals nums) []

  /-- Let c(x) = #{ i | 0 <= i < len(nums) and nums[i] = x } and let D = { nums[i] | 0 <= i < len(nums) }. Whenever min_operations(nums) returns a result r, r = -1 if there exists x in D with c(x) = 1; otherwise r = sum_{x in D} ceil(c(x)/3), where ceil(c/3) is the least integer >= c/3 (equivalently (c+2) div 3).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) :
      ival r = if (∃ x ∈ values nums, cnt nums x = 1) then -1 else (sumCeil nums : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r), ival r = if (∃ x ∈ values nums, cnt nums x = 1) then -1 else (sumCeil nums : Int)) := by
    sorry

  /-- The call min_operations(nums) returns a result r (it does not fail, panic, overflow, or return an error).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000) :
      ∃ r : I64, Aegis.MinOperations.min_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000), ∃ r : I64, Aegis.MinOperations.min_operations nums = ok r) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r, if r != -1 then r >= ceil(len(nums)/3), where ceil(len(nums)/3) is the least integer >= len(nums)/3.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ival r ≥ (ceilDiv3 nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ival r ≥ (ceilDiv3 nums.val.length : Int)) := by
    sorry

  /-- Let D = { nums[i] | 0 <= i < len(nums) }. Whenever min_operations(nums) returns a result r, if r != -1 then r >= |D|, the number of distinct values occurring in nums.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ival r ≥ ((values nums).card : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ival r ≥ ((values nums).card : Int)) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r, if r != -1 then r <= floor(len(nums)/2).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ival r ≤ ((nums.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ival r ≤ ((nums.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Let D = { nums[i] | 0 <= i < len(nums) }. Whenever min_operations(nums) returns a result r, if r != -1 then r <= len(nums) - |D|.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ival r ≤ ((nums.val.length - (values nums).card : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ival r ≤ ((nums.val.length - (values nums).card : Nat) : Int)) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r, if r != -1 then there exists a finite sequence of exactly r operations, each deleting either two or three equal-valued elements from the current array, that removes all elements of nums.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ∃ n : Nat, (n : Int) = ival r ∧ ReachIn n (vals nums) [] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ∃ n : Nat, (n : Int) = ival r ∧ ReachIn n (vals nums) []) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r, if r != -1 then every finite sequence of operations, each deleting either two or three equal-valued elements from the current array, that removes all elements of nums has length at least r.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1) :
      ∀ n : Nat, ReachIn n (vals nums) [] → ival r ≤ (n : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hne : ival r ≠ -1), ∀ n : Nat, ReachIn n (vals nums) [] → ival r ≤ (n : Int)) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r and min_operations(nums') returns a result r', we have r = r'.
    Preconditions: nums and nums' are arrays satisfying the same constraints as in spec_1, and for every integer x the number of occurrences of x in nums' equals the number of occurrences of x in nums. -/
  theorem spec_9 (nums nums' : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100000)
      (hrange' : ∀ (i : Nat) (h : i < nums'.val.length),
        1 ≤ ival (nums'.val[i]) ∧ ival (nums'.val[i]) ≤ 1000000)
      (hcnt : ∀ x : Int, cnt nums' x = cnt nums x)
      (r r' : I64)
      (hr : Aegis.MinOperations.min_operations nums = ok r)
      (hr' : Aegis.MinOperations.min_operations nums' = ok r') :
      ival r = ival r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100000)
        (hrange' : ∀ (i : Nat) (h : i < nums'.val.length),
          1 ≤ ival (nums'.val[i]) ∧ ival (nums'.val[i]) ≤ 1000000)
        (hcnt : ∀ x : Int, cnt nums' x = cnt nums x)
        (r r' : I64)
        (hr : Aegis.MinOperations.min_operations nums = ok r)
        (hr' : Aegis.MinOperations.min_operations nums' = ok r'), ival r = ival r') := by
    sorry

  /-- Whenever min_operations(nums) returns a result r and min_operations(nums') returns a result r', we have r = r' + ceil(c/3), where ceil(c/3) is the least integer >= c/3.
    Preconditions: nums satisfies the constraints of spec_1, every value occurring in nums occurs at least twice, x is a value occurring in nums with c(x) = c, and nums' is obtained from nums by deleting every position i with nums[i] = x. Assume len(nums') >= 2. -/
  theorem spec_10 (nums nums' : Slice I64) (x : Int) (c : Nat)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (htwice : ∀ y ∈ values nums, 2 ≤ cnt nums y)
      (hx : occurs nums x) (hc : cnt nums x = c)
      (hdelete : vals nums' = (vals nums).filter (fun y => y ≠ x))
      (hlen' : 2 ≤ nums'.val.length)
      (r r' : I64)
      (hr : Aegis.MinOperations.min_operations nums = ok r)
      (hr' : Aegis.MinOperations.min_operations nums' = ok r') :
      ival r = ival r' + (ceilDiv3 c : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64) (x : Int) (c : Nat)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (htwice : ∀ y ∈ values nums, 2 ≤ cnt nums y)
        (hx : occurs nums x) (hc : cnt nums x = c)
        (hdelete : vals nums' = (vals nums).filter (fun y => y ≠ x))
        (hlen' : 2 ≤ nums'.val.length)
        (r r' : I64)
        (hr : Aegis.MinOperations.min_operations nums = ok r)
        (hr' : Aegis.MinOperations.min_operations nums' = ok r'), ival r = ival r' + (ceilDiv3 c : Int)) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r and min_operations(nums') returns a result r', we have r' = r + 1.
    Preconditions: nums satisfies the constraints of spec_1 and every value occurring in nums occurs at least twice. Let x be any integer with 1 <= x <= 1000000, and let nums' be the array obtained by appending three copies of x to nums. Assume len(nums) + 3 <= 100000. -/
  theorem spec_11 (nums nums' : Slice I64) (x : Int)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (htwice : ∀ y ∈ values nums, 2 ≤ cnt nums y)
      (hx_low : 1 ≤ x) (hx_high : x ≤ 1000000)
      (happend : vals nums' = vals nums ++ [x, x, x])
      (hlen : nums.val.length + 3 ≤ 100000)
      (r r' : I64)
      (hr : Aegis.MinOperations.min_operations nums = ok r)
      (hr' : Aegis.MinOperations.min_operations nums' = ok r') :
      ival r' = ival r + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice I64) (x : Int)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (htwice : ∀ y ∈ values nums, 2 ≤ cnt nums y)
        (hx_low : 1 ≤ x) (hx_high : x ≤ 1000000)
        (happend : vals nums' = vals nums ++ [x, x, x])
        (hlen : nums.val.length + 3 ≤ 100000)
        (r r' : I64)
        (hr : Aegis.MinOperations.min_operations nums = ok r)
        (hr' : Aegis.MinOperations.min_operations nums' = ok r'), ival r' = ival r + 1) := by
    sorry

  /-- Whenever min_operations(nums) returns a result r, if r = -1 then there does not exist a finite sequence of operations, each deleting either two or three equal-valued elements from the current array, that removes all elements of nums.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_12 (nums : Slice I64)
      (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
      (hrange : ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
      (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hneg : ival r = -1) :
      ¬ CanEmpty nums := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100000)
        (hrange : ∀ (i : Nat) (h : i < nums.val.length),
          1 ≤ ival (nums.val[i]) ∧ ival (nums.val[i]) ≤ 1000000)
        (r : I64) (hr : Aegis.MinOperations.min_operations nums = ok r) (hneg : ival r = -1), ¬ CanEmpty nums) := by
    sorry

  end AegisSpec.MinOperations
