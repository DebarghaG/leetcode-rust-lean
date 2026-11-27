import Aegis.GetSum.Code.Funs

/-!
# Specifications of `Aegis.GetSum.get_sum`

LeetCode problem `sum-of-consecutive-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetSum

  def elems (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

  def IsStepChain (v : List I64) {k : Nat} (f : Fin k → Fin v.length) : Prop :=
    (∀ j : Fin k, 1 ≤ (j : Nat) →
        (v.get (f j)).val = (v.get (f ⟨(j : Nat) - 1, by have := j.isLt; omega⟩)).val + 1) ∨
    (∀ j : Fin k, 1 ≤ (j : Nat) →
        (v.get (f j)).val = (v.get (f ⟨(j : Nat) - 1, by have := j.isLt; omega⟩)).val - 1)

  noncomputable def chainSum (nums : Slice I64) : Int :=
    by
      classical
      exact
        Finset.sum (Finset.Icc 1 nums.val.length) fun k =>
          Finset.sum (Finset.univ : Finset (Fin k → Fin nums.val.length)) fun f =>
            if StrictMono f ∧ IsStepChain nums.val f then
              Finset.sum (Finset.univ : Finset (Fin k)) fun j => (nums.val.get (f j)).val
            else 0

  def sumAll (nums : Slice I64) : Int := (elems nums).sum

  def Precondition (nums : Slice I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
      ∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val.get ⟨i, h⟩).val ∧ (nums.val.get ⟨i, h⟩).val ≤ 100000

  /-- The function returns a result r such that 0 <= r < 1000000007 and r is congruent modulo 1000000007 to S(nums), where S(nums) is the sum, over all choices of an integer k >= 1 and indices 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) such that either nums[i_j] = nums[i_{j-1}] + 1 for every j with 1 <= j < k, or nums[i_j] = nums[i_{j-1}] - 1 for every j with 1 <= j < k, of the value nums[i_0] + nums[i_1] + ... + nums[i_{k-1}]. For k = 1 the difference conditions are vacuous, so every singleton index choice is included.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice I64) (hpre : Precondition nums) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007 ∧
        r.val % 1000000007 = chainSum nums % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val % 1000000007 = chainSum nums % 1000000007) := by
    sorry

  /-- The function returns a result r for every nums satisfying the preconditions; in particular it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice I64) (hpre : Precondition nums) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice I64) (hpre : Precondition nums) :
      ∀ r : I64, Aegis.GetSum.get_sum nums = ok r → 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums), ∀ r : I64, Aegis.GetSum.get_sum nums = ok r → 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Whenever the function returns a result r, r is congruent modulo 1000000007 to S(nums), where S(nums) is the total sum of values of all non-empty consecutive subsequences of nums counted by index choices as in spec_1.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_4 (nums : Slice I64) (hpre : Precondition nums) :
      ∀ r : I64, Aegis.GetSum.get_sum nums = ok r →
        r.val % 1000000007 = chainSum nums % 1000000007 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums), ∀ r : I64, Aegis.GetSum.get_sum nums = ok r →
          r.val % 1000000007 = chainSum nums % 1000000007) := by
    sorry

  /-- If for every i and j with 0 <= i < j < len(nums) we have nums[j] - nums[i] not equal to 1 and not equal to -1, then the function returns a result r and r is congruent modulo 1000000007 to nums[0] + nums[1] + ... + nums[len(nums)-1].
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice I64) (hpre : Precondition nums)
      (hno : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
        (nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val ≠ 1 ∧
        (nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val ≠ -1) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
        r.val % 1000000007 = sumAll nums % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums)
        (hno : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
          (nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val ≠ 1 ∧
          (nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val ≠ -1), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
          r.val % 1000000007 = sumAll nums % 1000000007) := by
    sorry

  /-- If there exists an integer a such that nums[i] = a + i for every i with 0 <= i < len(nums), then the function returns a result r and r is congruent modulo 1000000007 to sum_{i=0}^{len(nums)-1} (a + i) * (i + 1) * (len(nums) - i).
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice I64) (hpre : Precondition nums) (a : Int)
      (ha : ∀ (i : Nat) (h : i < nums.val.length),
        (nums.val.get ⟨i, h⟩).val = a + (i : Int)) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
        r.val % 1000000007 =
          (Finset.sum (Finset.range nums.val.length) fun i =>
            (a + (i : Int)) * ((i : Int) + 1) * ((nums.val.length : Int) - (i : Int))) %
            1000000007 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums) (a : Int)
        (ha : ∀ (i : Nat) (h : i < nums.val.length),
          (nums.val.get ⟨i, h⟩).val = a + (i : Int)), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
          r.val % 1000000007 =
            (Finset.sum (Finset.range nums.val.length) fun i =>
              (a + (i : Int)) * ((i : Int) + 1) * ((nums.val.length : Int) - (i : Int))) %
              1000000007) := by
    sorry

  /-- If there exists an integer a such that nums[i] = a - i for every i with 0 <= i < len(nums), then the function returns a result r and r is congruent modulo 1000000007 to sum_{i=0}^{len(nums)-1} (a - i) * (i + 1) * (len(nums) - i).
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_7 (nums : Slice I64) (hpre : Precondition nums) (a : Int)
      (ha : ∀ (i : Nat) (h : i < nums.val.length),
        (nums.val.get ⟨i, h⟩).val = a - (i : Int)) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
        r.val % 1000000007 =
          (Finset.sum (Finset.range nums.val.length) fun i =>
            (a - (i : Int)) * ((i : Int) + 1) * ((nums.val.length : Int) - (i : Int))) %
            1000000007 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums) (a : Int)
        (ha : ∀ (i : Nat) (h : i < nums.val.length),
          (nums.val.get ⟨i, h⟩).val = a - (i : Int)), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
          r.val % 1000000007 =
            (Finset.sum (Finset.range nums.val.length) fun i =>
              (a - (i : Int)) * ((i : Int) + 1) * ((nums.val.length : Int) - (i : Int))) %
              1000000007) := by
    sorry

  /-- Let rev be the array of length len(nums) with rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). If r is the result returned by get_sum(nums) and r' is the result returned by get_sum(rev), then r = r'.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums rev : Slice I64) (hpre : Precondition nums)
      (hlen : rev.val.length = nums.val.length)
      (hrev : ∀ (i : Nat) (h : i < rev.val.length),
        (rev.val.get ⟨i, h⟩).val =
          (nums.val.get ⟨nums.val.length - 1 - i, by omega⟩).val) :
      ∀ r r' : I64, Aegis.GetSum.get_sum nums = ok r → Aegis.GetSum.get_sum rev = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums rev : Slice I64) (hpre : Precondition nums)
        (hlen : rev.val.length = nums.val.length)
        (hrev : ∀ (i : Nat) (h : i < rev.val.length),
          (rev.val.get ⟨i, h⟩).val =
            (nums.val.get ⟨nums.val.length - 1 - i, by omega⟩).val), ∀ r r' : I64, Aegis.GetSum.get_sum nums = ok r → Aegis.GetSum.get_sum rev = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Let S(nums) be the total sum of values of all non-empty consecutive subsequences counted by index choices as in spec_1. If S(nums) < 1000000007, then the function returns a result r and r = S(nums).
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice I64) (hpre : Precondition nums)
      (hS : chainSum nums < 1000000007) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧ r.val = chainSum nums := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums)
        (hS : chainSum nums < 1000000007), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧ r.val = chainSum nums) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if S(nums) is divisible by 1000000007, where S(nums) is the total sum of values of all non-empty consecutive subsequences counted by index choices as in spec_1.
    Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice I64) (hpre : Precondition nums) :
      ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
        (r.val = 0 ↔ (1000000007 : Int) ∣ chainSum nums) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Precondition nums), ∃ r : I64, Aegis.GetSum.get_sum nums = ok r ∧
          (r.val = 0 ↔ (1000000007 : Int) ∣ chainSum nums)) := by
    sorry

  end AegisSpec.GetSum
