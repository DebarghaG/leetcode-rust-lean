import Aegis.CountDistinctIntegers.Code.Funs

/-!
# Specifications of `Aegis.CountDistinctIntegers.count_distinct_integers`

LeetCode problem `count-number-of-distinct-integers-after-reverse-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountDistinctIntegers

  def reverseDigitsAux (n acc : Nat) : Nat :=
    if n = 0 then acc else reverseDigitsAux (n / 10) (acc * 10 + n % 10)
  termination_by n
  decreasing_by omega

  def reverseDigits (n : Nat) : Nat := reverseDigitsAux n 0

  def reverseInt (z : Int) : Int := (reverseDigits z.toNat : Int)

  def numAt (nums : Slice Std.I64) (i : Nat) : Int :=
    ((nums.val[i]?).map (fun v => v.val)).getD 0

  def origVals (nums : Slice Std.I64) : Finset Int := (nums.val.map (fun v => v.val)).toFinset

  def revVals (nums : Slice Std.I64) : Finset Int :=
    (nums.val.map (fun v => reverseInt v.val)).toFinset

  def doubledVals (nums : Slice Std.I64) : List Int :=
    nums.val.map (fun v => v.val) ++ nums.val.map (fun v => reverseInt v.val)

  /-- Define reverse(n) for a positive integer n as follows: if n has decimal digits d_0,...,d_{k-1} with n = sum_{j=0}^{k-1} d_j * 10^j, d_{k-1} != 0, and 0 <= d_j <= 9, then reverse(n) = sum_{j=0}^{k-1} d_j * 10^{k-1-j} (the integer obtained by reversing the decimal digits and ignoring leading zeros). The function returns a result r, and r is the cardinality of the set S = { x | (there exists i with 0 <= i < len(nums) and x = nums[i]) or (there exists i with 0 <= i < len(nums) and x = reverse(nums[i])) }. Equivalently, r is the number of distinct integers in the array formed by appending reverse(nums[0]), reverse(nums[1]), ..., reverse(nums[len(nums)-1]) to nums.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000) :
      ∃ r : Std.I64, Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r ∧
        r.val = ((origVals nums ∪ revVals nums).card : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000), ∃ r : Std.I64, Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r ∧
          r.val = ((origVals nums ∪ revVals nums).card : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, count_distinct_integers returns a result r; in particular, it does not fail, overflow, or panic.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000) :
      ∃ r : Std.I64, Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000), ∃ r : Std.I64, Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }|, the number of distinct values occurring in nums.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      ((origVals nums).card : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), ((origVals nums).card : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= |{ x | there exists i with 0 <= i < len(nums) and x = reverse(nums[i]) }|, where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      ((revVals nums).card : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), ((revVals nums).card : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }| + |{ x | there exists i with 0 <= i < len(nums) and x = reverse(nums[i]) }|, where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      r.val ≤ ((origVals nums).card : Int) + ((revVals nums).card : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), r.val ≤ ((origVals nums).card : Int) + ((revVals nums).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if for every i with 0 <= i < len(nums) there exists j with 0 <= j < len(nums) such that reverse(nums[i]) = nums[j], then r = |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }|, where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hclosed : ∀ (i : Nat), i < nums.val.length →
        ∃ (j : Nat), j < nums.val.length ∧ reverseInt (numAt nums i) = numAt nums j)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      r.val = ((origVals nums).card : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hclosed : ∀ (i : Nat), i < nums.val.length →
          ∃ (j : Nat), j < nums.val.length ∧ reverseInt (numAt nums i) = numAt nums j)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), r.val = ((origVals nums).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if for every i,j with 0 <= i < len(nums) and 0 <= j < len(nums) we have reverse(nums[i]) != nums[j], then r = |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }| + |{ x | there exists i with 0 <= i < len(nums) and x = reverse(nums[i]) }|, where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hdisj : ∀ (i : Nat), i < nums.val.length → ∀ (j : Nat), j < nums.val.length →
        reverseInt (numAt nums i) ≠ numAt nums j)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      r.val = ((origVals nums).card : Int) + ((revVals nums).card : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hdisj : ∀ (i : Nat), i < nums.val.length → ∀ (j : Nat), j < nums.val.length →
          reverseInt (numAt nums i) ≠ numAt nums j)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), r.val = ((origVals nums).card : Int) + ((revVals nums).card : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an integer v such that for every i with 0 <= i < len(nums), nums[i] = v, then r = 1 if reverse(v) = v, and r = 2 if reverse(v) != v, where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      ∃ v : Int, (∀ (i : Nat), i < nums.val.length → numAt nums i = v) ∧
        r.val = (if reverseInt v = v then 1 else 2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), ∃ v : Int, (∀ (i : Nat), i < nums.val.length → numAt nums i = v) ∧
          r.val = (if reverseInt v = v then 1 else 2)) := by
    sorry

  /-- Whenever the function returns a result r, if the 2*len(nums) integers nums[0], ..., nums[len(nums)-1], reverse(nums[0]), ..., reverse(nums[len(nums)-1]) are pairwise distinct, then r = 2 * len(nums), where reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hpairwise : (doubledVals nums).Nodup)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      r.val = ((2 * nums.val.length : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hpairwise : (doubledVals nums).Nodup)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), r.val = ((2 * nums.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r for nums, and nums' is any slice that is a permutation of nums (that is, len(nums') = len(nums) and there is a bijection p from {0,...,len(nums)-1} to itself with nums'[i] = nums[p(i)] for every i with 0 <= i < len(nums)), then if the function returns r' on nums', r' = r.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_10 (nums nums' : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hperm : List.Perm (nums'.val.map (fun v => v.val)) (nums.val.map (fun v => v.val)))
      (r r' : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r)
      (hret' : Aegis.CountDistinctIntegers.count_distinct_integers nums' = ok r') :
      r' = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hperm : List.Perm (nums'.val.map (fun v => v.val)) (nums.val.map (fun v => v.val)))
        (r r' : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r)
        (hret' : Aegis.CountDistinctIntegers.count_distinct_integers nums' = ok r'), r' = r) := by
    sorry

  /-- Whenever the function returns a result r for nums, and nums' is any slice satisfying the same constraints and containing every value that occurs in nums (i.e., for every i with 0 <= i < len(nums) there exists j with 0 <= j < len(nums') and nums'[j] = nums[i]), then if the function returns r' on nums', r' >= r.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_11 (nums nums' : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hlen'_ge : 1 ≤ nums'.val.length) (hlen'_le : nums'.val.length ≤ 100000)
      (hbound' : ∀ (i : Nat), i < nums'.val.length → 1 ≤ numAt nums' i ∧ numAt nums' i ≤ 1000000)
      (hcover : ∀ (i : Nat), i < nums.val.length →
        ∃ (j : Nat), j < nums'.val.length ∧ numAt nums' j = numAt nums i)
      (r r' : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r)
      (hret' : Aegis.CountDistinctIntegers.count_distinct_integers nums' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hlen'_ge : 1 ≤ nums'.val.length) (hlen'_le : nums'.val.length ≤ 100000)
        (hbound' : ∀ (i : Nat), i < nums'.val.length → 1 ≤ numAt nums' i ∧ numAt nums' i ≤ 1000000)
        (hcover : ∀ (i : Nat), i < nums.val.length →
          ∃ (j : Nat), j < nums'.val.length ∧ numAt nums' j = numAt nums i)
        (r r' : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r)
        (hret' : Aegis.CountDistinctIntegers.count_distinct_integers nums' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r, if every nums[i] is a power of ten (i.e., for every i with 0 <= i < len(nums) there exists k >= 0 with nums[i] = 10^k), then r = D if 1 occurs among the values nums[i], and r = D + 1 otherwise, where D = |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }|.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hpow : ∀ (i : Nat), i < nums.val.length → ∃ k : Nat, numAt nums i = (10 : Int) ^ k)
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      ((1 : Int) ∈ origVals nums → r.val = ((origVals nums).card : Int)) ∧
        ((1 : Int) ∉ origVals nums → r.val = ((origVals nums).card : Int) + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hpow : ∀ (i : Nat), i < nums.val.length → ∃ k : Nat, numAt nums i = (10 : Int) ^ k)
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), ((1 : Int) ∈ origVals nums → r.val = ((origVals nums).card : Int)) ∧
          ((1 : Int) ∉ origVals nums → r.val = ((origVals nums).card : Int) + 1)) := by
    sorry

  /-- Whenever the function returns a result r, if there exist i,j with 0 <= i < len(nums) and 0 <= j < len(nums) such that nums[i] = reverse(nums[j]), then r <= D_orig + D_rev - 1, where D_orig = |{ x | there exists i with 0 <= i < len(nums) and x = nums[i] }| and D_rev = |{ x | there exists i with 0 <= i < len(nums) and x = reverse(nums[i]) }|, and reverse(n) is the integer obtained by reversing the decimal digits of n and dropping leading zeros.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
      (hoverlap : ∃ (i : Nat), i < nums.val.length ∧
        ∃ (j : Nat), j < nums.val.length ∧ numAt nums i = reverseInt (numAt nums j))
      (r : Std.I64)
      (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r) :
      r.val ≤ ((origVals nums).card : Int) + ((revVals nums).card : Int) - 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ (i : Nat), i < nums.val.length → 1 ≤ numAt nums i ∧ numAt nums i ≤ 1000000)
        (hoverlap : ∃ (i : Nat), i < nums.val.length ∧
          ∃ (j : Nat), j < nums.val.length ∧ numAt nums i = reverseInt (numAt nums j))
        (r : Std.I64)
        (hret : Aegis.CountDistinctIntegers.count_distinct_integers nums = ok r), r.val ≤ ((origVals nums).card : Int) + ((revVals nums).card : Int) - 1) := by
    sorry

  end AegisSpec.CountDistinctIntegers
