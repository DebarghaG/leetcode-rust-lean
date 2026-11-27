import Aegis.XorAllNums.Code.Funs

/-!
# Specifications of `Aegis.XorAllNums.xor_all_nums`

LeetCode problem `bitwise-xor-of-all-pairings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.XorAllNums

  def vals (s : Slice Std.I64) : List Nat := s.val.map (fun x => x.val.toNat)

  def xorAll (l : List Nat) : Nat := l.foldr (fun x acc => x ^^^ acc) 0

  def sliceXor (s : Slice Std.I64) : Nat := xorAll (vals s)

  def pairXor (nums1 nums2 : Slice Std.I64) : Nat :=
    xorAll ((vals nums1).flatMap fun a => (vals nums2).map fun b => a ^^^ b)

  def nthBit (x : Nat) (k : Nat) : Nat := (x >>> k) % 2

  def pairBitOnes (nums1 nums2 : Slice Std.I64) (k : Nat) : Nat :=
    (((vals nums1).flatMap fun a => (vals nums2).map fun b => a ^^^ b).filter
        (fun x => nthBit x k = 1)).length

  def PermOf {α : Type} [DecidableEq α] (p nums : List α) : Prop :=
    ∀ v : α,
      (p.filter (fun x => decide (x = v))).length =
        (nums.filter (fun x => decide (x = v))).length

  /-- The function returns a result r and r is the bitwise XOR of all len(nums1)*len(nums2) integers of the form nums1[i] XOR nums2[j], where 0 <= i < len(nums1) and 0 <= j < len(nums2). The XOR over these integers is taken in any order; it is well-defined because bitwise XOR is associative and commutative.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∃ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r ∧ r.val = pairXor nums1 nums2 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∃ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r ∧ r.val = pairXor nums1 nums2) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, the function returns a result r; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∃ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∃ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 2^30, i.e. 0 <= r < 1073741824.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        0 ≤ r.val ∧ r.val < 1073741824 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          0 ≤ r.val ∧ r.val < 1073741824) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000; len(nums1) is even; len(nums2) is even. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hlen1_even : Even nums1.val.length) (hlen2_even : Even nums2.val.length) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hlen1_even : Even nums1.val.length) (hlen2_even : Even nums2.val.length), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = 0) := by
    sorry

  /-- Let X2 be nums2[0] XOR nums2[1] XOR ... XOR nums2[len(nums2)-1]. Whenever the function returns a result r, r = X2.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000; len(nums2) is even; len(nums1) is odd. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hlen2_even : Even nums2.val.length) (hlen1_odd : Odd nums1.val.length) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = sliceXor nums2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hlen2_even : Even nums2.val.length) (hlen1_odd : Odd nums1.val.length), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = sliceXor nums2) := by
    sorry

  /-- Let X1 be nums1[0] XOR nums1[1] XOR ... XOR nums1[len(nums1)-1]. Whenever the function returns a result r, r = X1.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000; len(nums1) is even; len(nums2) is odd. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hlen1_even : Even nums1.val.length) (hlen2_odd : Odd nums2.val.length) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = sliceXor nums1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hlen1_even : Even nums1.val.length) (hlen2_odd : Odd nums2.val.length), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r → r.val = sliceXor nums1) := by
    sorry

  /-- For any two slices b and b' of 64-bit integers such that len(b) = len(b') = len(nums2) and every element of b and b' is between 0 and 1000000000, if xor_all_nums(nums1,b) returns r and xor_all_nums(nums1,b') returns r', then r = r'.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; len(nums1) is even. -/
  theorem spec_7 (nums1 nums2 b b' : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (hlen1_even : Even nums1.val.length)
      (hb_len : b.val.length = nums2.val.length)
      (hb'_len : b'.val.length = nums2.val.length)
      (hb_elem : ∀ (j : Nat) (hj : j < b.val.length),
        0 ≤ (b.val[j]).val ∧ (b.val[j]).val ≤ 1000000000)
      (hb'_elem : ∀ (j : Nat) (hj : j < b'.val.length),
        0 ≤ (b'.val[j]).val ∧ (b'.val[j]).val ≤ 1000000000) :
      ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 b = ok r →
        Aegis.XorAllNums.xor_all_nums nums1 b' = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 b b' : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (hlen1_even : Even nums1.val.length)
        (hb_len : b.val.length = nums2.val.length)
        (hb'_len : b'.val.length = nums2.val.length)
        (hb_elem : ∀ (j : Nat) (hj : j < b.val.length),
          0 ≤ (b.val[j]).val ∧ (b.val[j]).val ≤ 1000000000)
        (hb'_elem : ∀ (j : Nat) (hj : j < b'.val.length),
          0 ≤ (b'.val[j]).val ∧ (b'.val[j]).val ≤ 1000000000), ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 b = ok r →
          Aegis.XorAllNums.xor_all_nums nums1 b' = ok r' → r = r') := by
    sorry

  /-- For any two slices a and a' of 64-bit integers such that len(a) = len(a') = len(nums1) and every element of a and a' is between 0 and 1000000000, if xor_all_nums(a,nums2) returns r and xor_all_nums(a',nums2) returns r', then r = r'.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000; len(nums2) is even. -/
  theorem spec_8 (nums1 nums2 a a' : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hlen2_even : Even nums2.val.length)
      (ha_len : a.val.length = nums1.val.length)
      (ha'_len : a'.val.length = nums1.val.length)
      (ha_elem : ∀ (i : Nat) (hi : i < a.val.length),
        0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 1000000000)
      (ha'_elem : ∀ (i : Nat) (hi : i < a'.val.length),
        0 ≤ (a'.val[i]).val ∧ (a'.val[i]).val ≤ 1000000000) :
      ∀ r r', Aegis.XorAllNums.xor_all_nums a nums2 = ok r →
        Aegis.XorAllNums.xor_all_nums a' nums2 = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 a a' : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hlen2_even : Even nums2.val.length)
        (ha_len : a.val.length = nums1.val.length)
        (ha'_len : a'.val.length = nums1.val.length)
        (ha_elem : ∀ (i : Nat) (hi : i < a.val.length),
          0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 1000000000)
        (ha'_elem : ∀ (i : Nat) (hi : i < a'.val.length),
          0 ≤ (a'.val[i]).val ∧ (a'.val[i]).val ≤ 1000000000), ∀ r r', Aegis.XorAllNums.xor_all_nums a nums2 = ok r →
          Aegis.XorAllNums.xor_all_nums a' nums2 = ok r' → r = r') := by
    sorry

  /-- If xor_all_nums(nums1,nums2) returns r and xor_all_nums(nums2,nums1) returns r', then r = r'.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        Aegis.XorAllNums.xor_all_nums nums2 nums1 = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          Aegis.XorAllNums.xor_all_nums nums2 nums1 = ok r' → r = r') := by
    sorry

  /-- Let p be any slice of the same length as nums1 such that p is a permutation of nums1, meaning that for every integer v the number of indices i with p[i] = v equals the number of indices i with nums1[i] = v, and every element of p is between 0 and 1000000000. If xor_all_nums(nums1,nums2) returns r and xor_all_nums(p,nums2) returns r', then r = r'.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_10 (nums1 nums2 p : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hp_len : p.val.length = nums1.val.length)
      (hp_perm : PermOf (vals p) (vals nums1))
      (hp_elem : ∀ (i : Nat) (hi : i < p.val.length),
        0 ≤ (p.val[i]).val ∧ (p.val[i]).val ≤ 1000000000) :
      ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        Aegis.XorAllNums.xor_all_nums p nums2 = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 p : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hp_len : p.val.length = nums1.val.length)
        (hp_perm : PermOf (vals p) (vals nums1))
        (hp_elem : ∀ (i : Nat) (hi : i < p.val.length),
          0 ≤ (p.val[i]).val ∧ (p.val[i]).val ≤ 1000000000), ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          Aegis.XorAllNums.xor_all_nums p nums2 = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k < 64, the k-th least-significant bit of r is 1 if and only if the number of pairs (i,j) with 0 <= i < len(nums1), 0 <= j < len(nums2), and the k-th bit of nums1[i] XOR nums2[j] equal to 1, is odd. The k-th bit of a non-negative integer x is (x >> k) mod 2.
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_11 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        ∀ k : Nat, k < 64 →
          (nthBit r.val.toNat k = 1 ↔ Odd (pairBitOnes nums1 nums2 k)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          ∀ k : Nat, k < 64 →
            (nthBit r.val.toNat k = 1 ↔ Odd (pairBitOnes nums1 nums2 k))) := by
    sorry

  /-- Let X1 be nums1[0] XOR nums1[1] XOR ... XOR nums1[len(nums1)-1], and let X2 be nums2[0] XOR nums2[1] XOR ... XOR nums2[len(nums2)-1]. Whenever the function returns a result r, r = ((if len(nums2) is odd then X1 else 0) XOR (if len(nums1) is odd then X2 else 0)).
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_12 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        r.val = ((if Odd nums2.val.length then sliceXor nums1 else 0) ^^^
          (if Odd nums1.val.length then sliceXor nums2 else 0)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          r.val = ((if Odd nums2.val.length then sliceXor nums1 else 0) ^^^
            (if Odd nums1.val.length then sliceXor nums2 else 0))) := by
    sorry

  /-- Let X1 be nums1[0] XOR nums1[1] XOR ... XOR nums1[len(nums1)-1], and let X2 be nums2[0] XOR nums2[1] XOR ... XOR nums2[len(nums2)-1]. Whenever the function returns a result r, r = X1 XOR X2. (This completes the case table of spec_4, spec_5, spec_6: both odd is the only remaining parity combination.)
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000; len(nums1) is odd; len(nums2) is odd. -/
  theorem spec_13 (nums1 nums2 : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hlen1_odd : Odd nums1.val.length) (hlen2_odd : Odd nums2.val.length) :
      ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        r.val = (sliceXor nums1 ^^^ sliceXor nums2) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hlen1_odd : Odd nums1.val.length) (hlen2_odd : Odd nums2.val.length), ∀ r, Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          r.val = (sliceXor nums1 ^^^ sliceXor nums2)) := by
    sorry

  /-- Let p be any slice with len(p) = len(nums2) that is a permutation of nums2 (for every integer v, the number of indices j with p[j] = v equals the number of indices j with nums2[j] = v) and whose elements are all between 0 and 1000000000. If xor_all_nums(nums1,nums2) returns r and xor_all_nums(nums1,p) returns r', then r = r'. (Symmetric counterpart of spec_10, which only covers reordering nums1.)
    Preconditions: len(nums1) and len(nums2) are between 1 and 100000 inclusive; for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 1000000000; for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 1000000000. -/
  theorem spec_14 (nums1 nums2 p : Slice Std.I64)
      (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
      (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
      (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
        0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
      (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
        0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
      (hp_len : p.val.length = nums2.val.length)
      (hp_perm : PermOf (vals p) (vals nums2))
      (hp_elem : ∀ (j : Nat) (hj : j < p.val.length),
        0 ≤ (p.val[j]).val ∧ (p.val[j]).val ≤ 1000000000) :
      ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
        Aegis.XorAllNums.xor_all_nums nums1 p = ok r' → r = r' := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 p : Slice Std.I64)
        (hlen1_lo : 1 ≤ nums1.val.length) (hlen1_hi : nums1.val.length ≤ 100000)
        (hlen2_lo : 1 ≤ nums2.val.length) (hlen2_hi : nums2.val.length ≤ 100000)
        (helem1 : ∀ (i : Nat) (hi : i < nums1.val.length),
          0 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 1000000000)
        (helem2 : ∀ (j : Nat) (hj : j < nums2.val.length),
          0 ≤ (nums2.val[j]).val ∧ (nums2.val[j]).val ≤ 1000000000)
        (hp_len : p.val.length = nums2.val.length)
        (hp_perm : PermOf (vals p) (vals nums2))
        (hp_elem : ∀ (j : Nat) (hj : j < p.val.length),
          0 ≤ (p.val[j]).val ∧ (p.val[j]).val ≤ 1000000000), ∀ r r', Aegis.XorAllNums.xor_all_nums nums1 nums2 = ok r →
          Aegis.XorAllNums.xor_all_nums nums1 p = ok r' → r = r') := by
    sorry

  end AegisSpec.XorAllNums
