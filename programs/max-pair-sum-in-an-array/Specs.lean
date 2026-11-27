import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `max-pair-sum-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result
open Classical

namespace AegisSpec.MaxSum

def largestDecimalDigitNat (n : Nat) : Nat :=
  if h : n = 0 then 0 else max (n % 10) (largestDecimalDigitNat (n / 10))
termination_by n
decreasing_by omega

def D (x : Int) : Int :=
  if 0 < x then (largestDecimalDigitNat x.toNat : Int) else 0

def AdmissiblePair (nums : Slice I64) (i j : Nat) : Prop :=
  ∃ (hij : i < j) (hj : j < nums.val.length),
    D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val)

noncomputable def admissiblePairValues (nums : Slice I64) : Finset Int :=
  ((Finset.univ : Finset (Fin nums.val.length × Fin nums.val.length)).filter
      (fun p => AdmissiblePair nums p.1.val p.2.val)).image
    (fun p => (nums.val.get p.1).val + (nums.val.get p.2).val)

noncomputable def maxAdmissibleSum (nums : Slice I64) : Int :=
  if h : (admissiblePairValues nums).Nonempty then (admissiblePairValues nums).max' h else -1

noncomputable def allPairValues (nums : Slice I64) : Finset Int :=
  ((Finset.univ : Finset (Fin nums.val.length × Fin nums.val.length)).filter
      (fun p => p.1.val < p.2.val)).image
    (fun p => (nums.val.get p.1).val + (nums.val.get p.2).val)

noncomputable def maxAllPairSum (nums : Slice I64) : Int :=
  if h : (allPairValues nums).Nonempty then (allPairValues nums).max' h else -1

def maxValue (nums : Slice I64) : Int :=
  ((nums.val.map (fun x => x.val)).max?).getD 0

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, the following holds. Let D(x) be the largest decimal digit of the positive integer x. Call a pair of indices (i, j) admissible when 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]). If no admissible pair exists, then r = -1. If at least one admissible pair exists, then r = max{ nums[i] + nums[j] | (i, j) is admissible }, where the maximum is over all admissible pairs and addition is ordinary integer addition.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = maxAdmissibleSum nums := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = maxAdmissibleSum nums) := by
  sorry

/-- For every nums satisfying the preconditions, the call max_sum(nums) returns a result r (it does not fail, panic, or overflow).
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∃ r, Aegis.MaxSum.max_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∃ r, Aegis.MaxSum.max_sum nums = ok r) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r with r != -1, there exist indices i and j such that 0 <= i < j < len(nums), D(nums[i]) = D(nums[j]), and r = nums[i] + nums[j], where D(x) is the largest decimal digit of x.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 →
      ∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
        D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) ∧
          r.val = (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 →
      ∃ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
        D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) ∧
          r.val = (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r with r != -1, for every pair of indices i, j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]), we have nums[i] + nums[j] <= r. Here D(x) is the largest decimal digit of x.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 →
      ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
        D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) →
          (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 →
      ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
        D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) →
          (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val ≤ r.val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, we have r = -1 if and only if there do not exist indices i, j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]), where D(x) is the largest decimal digit of x.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      (r.val = -1 ↔ ¬ ∃ (i j : Nat), AdmissiblePair nums i j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      (r.val = -1 ↔ ¬ ∃ (i j : Nat), AdmissiblePair nums i j)) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, either r = -1 or 2 <= r. In other words, no non-sentinel answer is 0, 1, or negative.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = -1 ∨ 2 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = -1 ∨ 2 ≤ r.val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, either r = -1 or r <= 20000.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = -1 ∨ r.val ≤ 20000 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = -1 ∨ r.val ≤ 20000) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r with r != -1, r <= 2 * M, where M is the maximum value among nums[0], ..., nums[len(nums)-1].
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_8 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 → r.val ≤ 2 * maxValue nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val ≠ -1 → r.val ≤ 2 * maxValue nums) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, if D(nums[0]) = D(nums[1]) then r = nums[0] + nums[1], and otherwise r = -1, where D(x) is the largest decimal digit of x.
  Preconditions: nums is a slice of 64-bit signed integers with len(nums) = 2, and for every i with 0 <= i < 2, 1 <= nums[i] <= 10000. -/
theorem spec_9 (nums : Slice I64)
    (hlen : nums.val.length = 2)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      ((D ((nums.val[0]'(by omega)).val) = D ((nums.val[1]'(by omega)).val) →
          r.val = (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val) ∧
        (D ((nums.val[0]'(by omega)).val) ≠ D ((nums.val[1]'(by omega)).val) →
          r.val = -1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : nums.val.length = 2)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      ((D ((nums.val[0]'(by omega)).val) = D ((nums.val[1]'(by omega)).val) →
          r.val = (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val) ∧
        (D ((nums.val[0]'(by omega)).val) ≠ D ((nums.val[1]'(by omega)).val) →
          r.val = -1))) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, r = max{ nums[i] + nums[j] | 0 <= i < j < len(nums) }, where the maximum is over all index pairs.
  Preconditions: Let D(x) be the largest decimal digit of the positive integer x. nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, and D(nums[i]) = D(nums[0]) for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hconst : ∀ (i : Nat) (h : i < nums.val.length),
      D ((nums.val[i]'h).val) = D ((nums.val[0]'(by omega)).val)) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = maxAllPairSum nums := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hconst : ∀ (i : Nat) (h : i < nums.val.length),
      D ((nums.val[i]'h).val) = D ((nums.val[0]'(by omega)).val)), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = maxAllPairSum nums) := by
  sorry

/-- Whenever max_sum(nums) returns a result r and max_sum(nums') returns a result r', we have r = r'.
  Preconditions: nums and nums' are slices of 64-bit signed integers satisfying the base constraints: each has length between 2 and 100 inclusive, and every element of each is between 1 and 10000 inclusive. Also len(nums') = len(nums), and there exists a bijection pi on {0, ..., len(nums)-1} such that nums'[i] = nums[pi(i)] for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums nums' : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100)
    (hval' : ∀ (i : Nat) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 10000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ (π : Fin nums'.val.length ≃ Fin nums.val.length),
      ∀ (i : Fin nums'.val.length), (nums'.val.get i).val = (nums.val.get (π i)).val) :
    ∀ r r', Aegis.MaxSum.max_sum nums = ok r →
      Aegis.MaxSum.max_sum nums' = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100)
    (hval' : ∀ (i : Nat) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 10000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ (π : Fin nums'.val.length ≃ Fin nums.val.length),
      ∀ (i : Fin nums'.val.length), (nums'.val.get i).val = (nums.val.get (π i)).val), ∀ r r', Aegis.MaxSum.max_sum nums = ok r →
      Aegis.MaxSum.max_sum nums' = ok r' → r = r') := by
  sorry

/-- Whenever max_sum(nums) returns a result r and max_sum(nums') returns a result r', we have r' >= r.
  Preconditions: nums and nums' are slices of 64-bit signed integers satisfying the base constraints: each has length between 2 and 100 inclusive, and every element of each is between 1 and 10000 inclusive. Also nums' contains nums as a sub-multiset: there is an injective map f from {0, ..., len(nums)-1} to {0, ..., len(nums')-1} such that nums'[f(i)] = nums[i] for every i with 0 <= i < len(nums). -/
theorem spec_12 (nums nums' : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100)
    (hval' : ∀ (i : Nat) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 10000)
    (hsub : ∃ (f : Fin nums.val.length → Fin nums'.val.length),
      Function.Injective f ∧
        ∀ (i : Fin nums.val.length), (nums'.val.get (f i)).val = (nums.val.get i).val) :
    ∀ r r', Aegis.MaxSum.max_sum nums = ok r →
      Aegis.MaxSum.max_sum nums' = ok r' → r'.val ≥ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hlen_low' : 2 ≤ nums'.val.length) (hlen_high' : nums'.val.length ≤ 100)
    (hval' : ∀ (i : Nat) (h : i < nums'.val.length),
      1 ≤ (nums'.val[i]'h).val ∧ (nums'.val[i]'h).val ≤ 10000)
    (hsub : ∃ (f : Fin nums.val.length → Fin nums'.val.length),
      Function.Injective f ∧
        ∀ (i : Fin nums.val.length), (nums'.val.get (f i)).val = (nums.val.get i).val), ∀ r r', Aegis.MaxSum.max_sum nums = ok r →
      Aegis.MaxSum.max_sum nums' = ok r' → r'.val ≥ r.val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, if there exists at least one admissible pair, then r != -1 and for every admissible pair (i, j), nums[i] + nums[j] <= r. Here an admissible pair means indices i, j with 0 <= i < j < len(nums) and D(nums[i]) = D(nums[j]), where D(x) is the largest decimal digit of x.
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_13 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      (∃ (i j : Nat), AdmissiblePair nums i j) →
        r.val ≠ -1 ∧
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) →
              (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000), ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      (∃ (i j : Nat), AdmissiblePair nums i j) →
        r.val ≠ -1 ∧
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            D ((nums.val[i]'(hij.trans hj)).val) = D ((nums.val[j]'hj).val) →
              (nums.val[i]'(hij.trans hj)).val + (nums.val[j]'hj).val ≤ r.val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, if p and q are the unique indices with 0 <= p < q < len(nums) and D(nums[p]) = D(nums[q]), then r = nums[p] + nums[q].
  Preconditions: Let D(x) be the largest decimal digit of the positive integer x. nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, and there is exactly one pair of indices (p, q) with 0 <= p < q < len(nums) and D(nums[p]) = D(nums[q]). -/
theorem spec_14 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hunique : ∃ (p q : Nat) (hij : p < q) (hj : q < nums.val.length),
      D ((nums.val[p]'(hij.trans hj)).val) = D ((nums.val[q]'hj).val) ∧
        ∀ (p' q' : Nat) (hij' : p' < q') (hj' : q' < nums.val.length),
          D ((nums.val[p']'(hij'.trans hj')).val) = D ((nums.val[q']'hj').val) →
            p' = p ∧ q' = q) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      ∀ (p q : Nat) (hij : p < q) (hj : q < nums.val.length),
        D ((nums.val[p]'(hij.trans hj)).val) = D ((nums.val[q]'hj).val) →
          (∀ (p' q' : Nat) (hij' : p' < q') (hj' : q' < nums.val.length),
            D ((nums.val[p']'(hij'.trans hj')).val) = D ((nums.val[q']'hj').val) →
              p' = p ∧ q' = q) →
            r.val = (nums.val[p]'(hij.trans hj)).val + (nums.val[q]'hj).val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hunique : ∃ (p q : Nat) (hij : p < q) (hj : q < nums.val.length),
      D ((nums.val[p]'(hij.trans hj)).val) = D ((nums.val[q]'hj).val) ∧
        ∀ (p' q' : Nat) (hij' : p' < q') (hj' : q' < nums.val.length),
          D ((nums.val[p']'(hij'.trans hj')).val) = D ((nums.val[q']'hj').val) →
            p' = p ∧ q' = q), ∀ r, Aegis.MaxSum.max_sum nums = ok r →
      ∀ (p q : Nat) (hij : p < q) (hj : q < nums.val.length),
        D ((nums.val[p]'(hij.trans hj)).val) = D ((nums.val[q]'hj).val) →
          (∀ (p' q' : Nat) (hij' : p' < q') (hj' : q' < nums.val.length),
            D ((nums.val[p']'(hij'.trans hj')).val) = D ((nums.val[q']'hj').val) →
              p' = p ∧ q' = q) →
            r.val = (nums.val[p]'(hij.trans hj)).val + (nums.val[q]'hj).val) := by
  sorry

/-- For every nums satisfying the preconditions, whenever max_sum(nums) returns a result r, r = 2 * M, where M is the maximum value among nums[0], ..., nums[len(nums)-1].
  Preconditions: nums is a slice of 64-bit signed integers with 2 <= len(nums) <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000, and the maximum value M among nums[0], ..., nums[len(nums)-1] occurs at least twice among the indices. -/
theorem spec_15 (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hmax_twice : ∃ (i j : Fin nums.val.length), i ≠ j ∧
      (nums.val.get i).val = maxValue nums ∧ (nums.val.get j).val = maxValue nums) :
    ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = 2 * maxValue nums := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_low : 2 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hval : ∀ (i : Nat) (h : i < nums.val.length),
      1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 10000)
    (hmax_twice : ∃ (i j : Fin nums.val.length), i ≠ j ∧
      (nums.val.get i).val = maxValue nums ∧ (nums.val.get j).val = maxValue nums), ∀ r, Aegis.MaxSum.max_sum nums = ok r → r.val = 2 * maxValue nums) := by
  sorry

end AegisSpec.MaxSum
