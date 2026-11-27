import Aegis.CanDistribute.Code.Funs

/-!
# Specifications of `Aegis.CanDistribute.can_distribute`

LeetCode problem `distribute-repeating-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanDistribute (can_distribute)

namespace AegisSpec.CanDistribute

def occ (nums : Slice Std.I64) (v : Int) : Nat :=
  (nums.val.filter (fun x => decide (x.val = v))).length

def values (nums : Slice Std.I64) : List Int :=
  nums.val.map (fun x => x.val)

def distinctValues (nums : Slice Std.I64) : List Int :=
  (values nums).dedup

def distinctCount (nums : Slice Std.I64) : Nat :=
  (distinctValues nums).length

def freqProfile (nums : Slice Std.I64) : List Nat :=
  (distinctValues nums).map (fun v => occ nums v)

def totalQuantity (quantity : Slice Std.I64) : Int :=
  (quantity.val.map (fun x => x.val)).sum

def floorSum (nums : Slice Std.I64) (q : Int) : Int :=
  ((distinctValues nums).map (fun v => (occ nums v : Int) / q)).sum

/-- Let occ(v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Whenever can_distribute nums quantity returns a result r, we have r = true if and only if there exists a function assign from {0,1,...,len(quantity)-1} to the set of integers such that: (1) for every customer i, occ(assign(i)) >= quantity[i]; and (2) for every integer v, the sum of quantity[i] over all i with assign(i) = v is at most occ(v). Consequently r = false exactly when no such assign exists.
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_1 (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : Bool, can_distribute nums quantity = ok r →
      (r = true ↔
        ∃ assign : Fin quantity.val.length → Int,
          (∀ i : Fin quantity.val.length,
            (quantity.val.get i).val ≤ (occ nums (assign i) : Int)) ∧
          (∀ v : Int,
            (∑ i : Fin quantity.val.length,
              if assign i = v then (quantity.val.get i).val else 0) ≤ (occ nums v : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r : Bool, can_distribute nums quantity = ok r →
      (r = true ↔
        ∃ assign : Fin quantity.val.length → Int,
          (∀ i : Fin quantity.val.length,
            (quantity.val.get i).val ≤ (occ nums (assign i) : Int)) ∧
          (∀ v : Int,
            (∑ i : Fin quantity.val.length,
              if assign i = v then (quantity.val.get i).val else 0) ≤ (occ nums v : Int)))) := by
  sorry

/-- For every nums and quantity satisfying the preconditions, the call can_distribute nums quantity returns a result r, i.e. in Lean it evaluates to Result.ok r for some Bool r. In particular, it does not fail because of arithmetic overflow, out-of-bounds indexing, or a panic.
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_2 (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r : Bool, can_distribute nums quantity = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r : Bool, can_distribute nums quantity = ok r) := by
  sorry

/-- Whenever can_distribute nums quantity returns a result r and r = true, the total requested amount satisfies sum over i from 0 to len(quantity)-1 of quantity[i] <= len(nums).
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_3 (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      totalQuantity quantity ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      totalQuantity quantity ≤ (nums.val.length : Int)) := by
  sorry

/-- Let occ(v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Whenever can_distribute nums quantity returns a result r and r = true, for every customer index i with 0 <= i < len(quantity), there exists an integer v such that occ(v) >= quantity[i].
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_4 (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      ∀ i : Fin quantity.val.length, ∃ v : Int, (quantity.val.get i).val ≤ (occ nums v : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      ∀ i : Fin quantity.val.length, ∃ v : Int, (quantity.val.get i).val ≤ (occ nums v : Int)) := by
  sorry

/-- Let occ(v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Whenever can_distribute nums quantity returns a result r, r = true if and only if the sum over all values v occurring in nums of floor(occ(v) / q) is at least len(quantity).
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]; len(quantity) >= 2; and there exists an integer q such that quantity[i] = q for every i with 0 <= i < len(quantity). -/
theorem spec_5 (nums quantity : Slice Std.I64) (q : Int)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu_len_two : 2 ≤ quantity.val.length)
    (hqu_const : ∀ i : Fin quantity.val.length, (quantity.val.get i).val = q) :
    ∀ r : Bool, can_distribute nums quantity = ok r →
      (r = true ↔ (quantity.val.length : Int) ≤ floorSum nums q) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums quantity : Slice Std.I64) (q : Int)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu_len_two : 2 ≤ quantity.val.length)
    (hqu_const : ∀ i : Fin quantity.val.length, (quantity.val.get i).val = q), ∀ r : Bool, can_distribute nums quantity = ok r →
      (r = true ↔ (quantity.val.length : Int) ≤ floorSum nums q)) := by
  sorry

/-- Let occ(v) be the number of indices j with 0 <= j < len(nums) and nums[j] = v. Whenever can_distribute nums quantity returns a result r, r = true, and sum over i from 0 to len(quantity)-1 of quantity[i] = len(nums), there exists a function assign from {0,1,...,len(quantity)-1} to integers such that: (1) for every customer i, occ(assign(i)) >= quantity[i]; and (2) for every integer v, the sum of quantity[i] over all i with assign(i) = v is exactly occ(v).
  Preconditions: nums and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_6 (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      totalQuantity quantity = (nums.val.length : Int) →
        ∃ assign : Fin quantity.val.length → Int,
          (∀ i : Fin quantity.val.length,
            (quantity.val.get i).val ≤ (occ nums (assign i) : Int)) ∧
          (∀ v : Int,
            (∑ i : Fin quantity.val.length,
              if assign i = v then (quantity.val.get i).val else 0) = (occ nums v : Int)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∀ r : Bool, can_distribute nums quantity = ok r → r = true →
      totalQuantity quantity = (nums.val.length : Int) →
        ∃ assign : Fin quantity.val.length → Int,
          (∀ i : Fin quantity.val.length,
            (quantity.val.get i).val ≤ (occ nums (assign i) : Int)) ∧
          (∀ v : Int,
            (∑ i : Fin quantity.val.length,
              if assign i = v then (quantity.val.get i).val else 0) = (occ nums v : Int))) := by
  sorry

/-- Let occ(v) be the number of indices j with nums[j] = v, and let occ'(v) be the number of indices j with nums'[j] = v. If for every positive integer k, the number of integers v with occ(v) = k equals the number of integers v with occ'(v) = k, then whenever both can_distribute nums quantity and can_distribute nums' quantity return results r and r', we have r = r'.
  Preconditions: nums, nums', and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; the same constraints hold for nums'; and 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]. -/
theorem spec_7 (nums nums' quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hnum'_len_lo : 1 ≤ nums'.val.length) (hnum'_len_hi : nums'.val.length ≤ 100000)
    (hnum'_range : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum'_distinct : distinctCount nums' ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprofile : ∀ k : Nat, 1 ≤ k →
      ((distinctValues nums).filter (fun v => decide (occ nums v = k))).length =
        ((distinctValues nums').filter (fun v => decide (occ nums' v = k))).length) :
    ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums' quantity = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hnum'_len_lo : 1 ≤ nums'.val.length) (hnum'_len_hi : nums'.val.length ≤ 100000)
    (hnum'_range : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum'_distinct : distinctCount nums' ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprofile : ∀ k : Nat, 1 ≤ k →
      ((distinctValues nums).filter (fun v => decide (occ nums v = k))).length =
        ((distinctValues nums').filter (fun v => decide (occ nums' v = k))).length), ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums' quantity = ok r' → r = r') := by
  sorry

/-- Whenever both can_distribute nums quantity and can_distribute nums quantity' return results r and r', we have r = r'.
  Preconditions: nums, quantity, and quantity' satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]; len(quantity') = len(quantity); and the entries of quantity' are a permutation of the entries of quantity. -/
theorem spec_8 (nums quantity quantity' : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu'_len : quantity'.val.length = quantity.val.length)
    (hqu'_perm : (quantity'.val.map (fun x => x.val)).Perm
      (quantity.val.map (fun x => x.val))) :
    ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums quantity' = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums quantity quantity' : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu'_len : quantity'.val.length = quantity.val.length)
    (hqu'_perm : (quantity'.val.map (fun x => x.val)).Perm
      (quantity.val.map (fun x => x.val))), ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums quantity' = ok r' → r = r') := by
  sorry

/-- Whenever both can_distribute nums quantity and can_distribute nums quantity' return results r and r', if r = true then r' = true.
  Preconditions: nums, quantity, and quantity' satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]; len(quantity') = len(quantity); and 1 <= quantity'[i] <= quantity[i] for every i with 0 <= i < len(quantity). -/
theorem spec_9 (nums quantity quantity' : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu'_len : quantity'.val.length = quantity.val.length)
    (hqu'_bounds : ∀ i : Fin quantity.val.length,
      1 ≤ (quantity'.val.get (Fin.cast hqu'_len.symm i)).val ∧
        (quantity'.val.get (Fin.cast hqu'_len.symm i)).val ≤ (quantity.val.get i).val) :
    ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums quantity' = ok r' → r = true → r' = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums quantity quantity' : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hqu'_len : quantity'.val.length = quantity.val.length)
    (hqu'_bounds : ∀ i : Fin quantity.val.length,
      1 ≤ (quantity'.val.get (Fin.cast hqu'_len.symm i)).val ∧
        (quantity'.val.get (Fin.cast hqu'_len.symm i)).val ≤ (quantity.val.get i).val), ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums quantity' = ok r' → r = true → r' = true) := by
  sorry

/-- Whenever both can_distribute nums quantity and can_distribute nums' quantity return results r and r', if r = true then r' = true.
  Preconditions: nums, nums', and quantity satisfy: 1 <= len(nums) <= 100000; every nums[j] for 0 <= j < len(nums) is in [1, 1000]; nums has at most 50 distinct values; the same constraints hold for nums'; 1 <= len(quantity) <= 10; every quantity[i] for 0 <= i < len(quantity) is in [1, 100000]; and for every integer v, the number of occurrences of v in nums' is at least the number of occurrences of v in nums. -/
theorem spec_10 (nums nums' quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hnum'_len_lo : 1 ≤ nums'.val.length) (hnum'_len_hi : nums'.val.length ≤ 100000)
    (hnum'_range : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum'_distinct : distinctCount nums' ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hocc_mono : ∀ v : Int, occ nums v ≤ occ nums' v) :
    ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums' quantity = ok r' → r = true → r' = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' quantity : Slice Std.I64)
    (hnum_len_lo : 1 ≤ nums.val.length) (hnum_len_hi : nums.val.length ≤ 100000)
    (hnum_range : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum_distinct : distinctCount nums ≤ 50)
    (hnum'_len_lo : 1 ≤ nums'.val.length) (hnum'_len_hi : nums'.val.length ≤ 100000)
    (hnum'_range : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000)
    (hnum'_distinct : distinctCount nums' ≤ 50)
    (hqu_len_lo : 1 ≤ quantity.val.length) (hqu_len_hi : quantity.val.length ≤ 10)
    (hqu_range : ∀ x ∈ quantity.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hocc_mono : ∀ v : Int, occ nums v ≤ occ nums' v), ∀ r r' : Bool, can_distribute nums quantity = ok r →
      can_distribute nums' quantity = ok r' → r = true → r' = true) := by
  sorry

end AegisSpec.CanDistribute
