import Aegis.NumberOfGoodSubarraySplits.Code.Funs

/-!
# Specifications of `Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits`

LeetCode problem `ways-to-split-array-into-good-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfGoodSubarraySplits

def onesIn (nums : Slice Std.I64) (a b : Nat) : Nat :=
  ((nums.val.drop a).take (b - a)).countP (fun x => decide (x.val = 1))

def IsGoodSplitCuts (nums : Slice Std.I64) (c : List Nat) : Prop :=
  2 ≤ c.length ∧
    c.head? = some 0 ∧
    c.getLast? = some nums.val.length ∧
    (∀ q, q ∈ c.zip c.tail → q.1 < q.2 ∧ onesIn nums q.1 q.2 = 1)

def isGoodSplitCuts (nums : Slice Std.I64) (c : List Nat) : Bool :=
  decide (2 ≤ c.length)
    && (c.head? == some 0)
    && (c.getLast? == some nums.val.length)
    && (c.zip c.tail).all (fun q => decide (q.1 < q.2) && decide (onesIn nums q.1 q.2 = 1))

def numGoodSplits (nums : Slice Std.I64) : Nat :=
  ((List.range (nums.val.length + 1)).sublists.filter (fun c => isGoodSplitCuts nums c)).length

def gaps (p : List Nat) : List Nat :=
  (p.zip p.tail).map (fun q => q.2 - q.1)

/-- Let M = 1000000007. Let C be the number of sequences of indices 0 = c_0 < c_1 < ... < c_k = len(nums) with k >= 1 such that for every j with 1 <= j <= k, the subarray nums[c_{j-1} .. c_j - 1] contains exactly one index i with nums[i] = 1. The function returns a result r and r = C mod M.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        r.val = ((numGoodSplits nums : Int) % 1000000007) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        r.val = ((numGoodSplits nums : Int) % 1000000007)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (i.e., evaluation does not fail, panic, or overflow).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∃ r : Std.I64, Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∃ r : Std.I64, Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r) := by
  sorry

/-- For every input satisfying the preconditions, the returned result r satisfies 0 <= r < 1000000007.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- If there is at least one index i with 0 <= i < len(nums) such that nums[i] = 1, then the returned result r satisfies 1 <= r < 1000000007; in particular, r >= 1 witnesses that at least one good split exists.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1)
    (hwitness : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = 1) :
    ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        1 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1)
    (hwitness : ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = 1), ∃ r : Std.I64,
      Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
        1 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- For every integer k >= 0 such that k + len(nums) <= 100000, let nums' be the array of length k + len(nums) defined by nums'[i] = 0 for 0 <= i < k and nums'[k + i] = nums[i] for 0 <= i < len(nums). Then the result of the function on nums' equals the result on nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∀ (k : Nat) (nums' : Slice Std.I64),
      k + nums.val.length ≤ 100000 →
        nums'.val = List.replicate k (0#i64) ++ nums.val →
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
            Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∀ (k : Nat) (nums' : Slice Std.I64),
      k + nums.val.length ≤ 100000 →
        nums'.val = List.replicate k (0#i64) ++ nums.val →
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
            Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums) := by
  sorry

/-- For every integer k >= 0 such that len(nums) + k <= 100000, let nums' be the array of length len(nums) + k defined by nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[i] = 0 for len(nums) <= i < len(nums) + k. Then the result of the function on nums' equals the result on nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∀ (k : Nat) (nums' : Slice Std.I64),
      nums.val.length + k ≤ 100000 →
        nums'.val = nums.val ++ List.replicate k (0#i64) →
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
            Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∀ (k : Nat) (nums' : Slice Std.I64),
      nums.val.length + k ≤ 100000 →
        nums'.val = nums.val ++ List.replicate k (0#i64) →
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
            Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums) := by
  sorry

/-- Let nums_rev be the array of length len(nums) defined by nums_rev[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). Then the result of the function on nums_rev equals the result on nums.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1) :
    ∀ nums' : Slice Std.I64,
      nums'.val = nums.val.reverse →
        Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1), ∀ nums' : Slice Std.I64,
      nums'.val = nums.val.reverse →
        Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums' =
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums) := by
  sorry

/-- Let p_1 < p_2 < ... < p_m be all indices i with 0 <= i < len(nums) and nums[i] = 1. If m = 0 then the function returns r = 0. If m >= 1 then the function returns r = (product from i=1 to m-1 of (p_{i+1} - p_i)) mod 1000000007, where the empty product for m=1 is 1.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), nums[i] = 0 or nums[i] = 1. -/
theorem spec_8 (nums : Slice Std.I64) (p : List Nat)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1)
    (hp_increasing : p.Pairwise (· < ·))
    (hp_occurs : ∀ (i : Nat), i ∈ p ↔ ∃ (hi : i < nums.val.length), (nums.val[i]).val = 1) :
    ((p = []) →
        ∃ r : Std.I64,
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
            r.val = 0) ∧
      (p ≠ [] →
        ∃ r : Std.I64,
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
            r.val = (((gaps p).prod : Int) % 1000000007)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (p : List Nat)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 100000)
    (hentries : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val[i]).val = 0 ∨ (nums.val[i]).val = 1)
    (hp_increasing : p.Pairwise (· < ·))
    (hp_occurs : ∀ (i : Nat), i ∈ p ↔ ∃ (hi : i < nums.val.length), (nums.val[i]).val = 1), ((p = []) →
        ∃ r : Std.I64,
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
            r.val = 0) ∧
      (p ≠ [] →
        ∃ r : Std.I64,
          Aegis.NumberOfGoodSubarraySplits.number_of_good_subarray_splits nums = ok r ∧
            r.val = (((gaps p).prod : Int) % 1000000007))) := by
  sorry

end AegisSpec.NumberOfGoodSubarraySplits
