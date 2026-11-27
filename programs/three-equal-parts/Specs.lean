import Aegis.ThreeEqualParts.Code.Funs

/-!
# Specifications of `Aegis.ThreeEqualParts.three_equal_parts`

LeetCode problem `three-equal-parts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.ThreeEqualParts

  def outVals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

  def cut (l : List Std.I64) (a b : Nat) : List Std.I64 := (l.drop a).take (b + 1 - a)

  def binVal (l : List Std.I64) : Nat :=
    l.foldl (fun acc x => 2 * acc + (if x.val = 1 then 1 else 0)) 0

  def onesIn (l : List Std.I64) : Nat := (l.filter (fun x => x.val = 1)).length

  def AllZero (l : List Std.I64) : Prop := ∀ x ∈ l, x.val = 0

  def IsBitSlice (arr : Slice Std.I64) : Prop :=
    ∀ (k : Nat) (hk : k < arr.val.length),
      (arr.val.get ⟨k, hk⟩).val = 0 ∨ (arr.val.get ⟨k, hk⟩).val = 1

  def IsZeroSlice (arr : Slice Std.I64) : Prop :=
    ∀ (k : Nat) (hk : k < arr.val.length), (arr.val.get ⟨k, hk⟩).val = 0

  def IsOneSlice (arr : Slice Std.I64) : Prop :=
    ∀ (k : Nat) (hk : k < arr.val.length), (arr.val.get ⟨k, hk⟩).val = 1

  def bitAt (l : List Std.I64) (k : Nat) : Int := (l.getD k 0#i64).val

  def threeWayEq (l : List Std.I64) (i j : Nat) : Prop :=
    binVal (cut l 0 i) = binVal (cut l (i + 1) (j - 1)) ∧
      binVal (cut l (i + 1) (j - 1)) = binVal (cut l j (l.length - 1))

  def hasEqualSplit (l : List Std.I64) : Prop :=
    ∃ i j : Nat, 0 ≤ i ∧ i + 1 < j ∧ j < l.length ∧ threeWayEq l i j

  /-- Whenever the function returns a result r, the vector r has length 2, and exactly one of the following holds: (1) r = [-1, -1] and there do not exist indices i, j with 0 <= i, i + 1 < j, j <= n - 1 such that arr[0..i], arr[i+1..j-1], and arr[j..n-1] have equal binary value; (2) r = [i, j] for some indices i, j with 0 <= i, i + 1 < j, j <= n - 1 such that arr[0..i], arr[i+1..j-1], and arr[j..n-1] have equal binary value.
    Preconditions: Let n = len(arr). 3 <= n <= 30000. For every k with 0 <= k < n, arr[k] is either 0 or 1. For a non-empty part arr[a..b] (inclusive), its binary value is the value of the bits arr[a], ..., arr[b] read in order with arr[a] most significant, allowing and ignoring leading zeros; two parts have equal binary value exactly when their bit strings after deleting all leading zeros are identical (the empty string is allowed and represents 0). -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        r.val.length = 2 ∧
          ((outVals r = [-1, -1] ∧ ¬ hasEqualSplit arr.val) ∨
            (∃ i j : Nat,
              0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
                outVals r = [(i : Int), (j : Int)] ∧ threeWayEq arr.val i j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          r.val.length = 2 ∧
            ((outVals r = [-1, -1] ∧ ¬ hasEqualSplit arr.val) ∨
              (∃ i j : Nat,
                0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
                  outVals r = [(i : Int), (j : Int)] ∧ threeWayEq arr.val i j))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → r.val.length = 2 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r and r != [-1, -1], writing r = [i, j], we have 0 <= i, i + 1 < j, and j <= n - 1. Consequently the three parts arr[0..i], arr[i+1..j-1], and arr[j..n-1] are all non-empty.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
        ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
          0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
            0 < (cut arr.val 0 i).length ∧
            0 < (cut arr.val (i + 1) (j - 1)).length ∧
            0 < (cut arr.val j (arr.val.length - 1)).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
          ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
            0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
              0 < (cut arr.val 0 i).length ∧
              0 < (cut arr.val (i + 1) (j - 1)).length ∧
              0 < (cut arr.val j (arr.val.length - 1)).length) := by
    sorry

  /-- Whenever the function returns a result r and r != [-1, -1], writing r = [i, j], the three parts arr[0..i], arr[i+1..j-1], and arr[j..n-1] all have the same binary value.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. Binary value of a part means reading its bits in order with the first bit most significant and ignoring leading zeros. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
        ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] → threeWayEq arr.val i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
          ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] → threeWayEq arr.val i j) := by
    sorry

  /-- Whenever the function returns a result r, if there exist indices i, j with 0 <= i, i + 1 < j, j <= n - 1 such that arr[0..i], arr[i+1..j-1], and arr[j..n-1] have equal binary value, then r != [-1, -1].
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. Binary value ignores leading zeros as usual. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        hasEqualSplit arr.val → outVals r ≠ [-1, -1] := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          hasEqualSplit arr.val → outVals r ≠ [-1, -1]) := by
    sorry

  /-- Whenever the function returns a result r and r = [-1, -1], there do not exist indices i, j with 0 <= i, i + 1 < j, j <= n - 1 such that arr[0..i], arr[i+1..j-1], and arr[j..n-1] have equal binary value.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. Binary value ignores leading zeros as usual. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        outVals r = [-1, -1] → ¬ hasEqualSplit arr.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          outVals r = [-1, -1] → ¬ hasEqualSplit arr.val) := by
    sorry

  /-- Whenever the function returns a result r and r != [-1, -1], the number of indices k with 0 <= k < n and arr[k] = 1 is divisible by 3.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
        ∃ m : Nat, onesIn arr.val = 3 * m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
          ∃ m : Nat, onesIn arr.val = 3 * m) := by
    sorry

  /-- If the number of indices k with 0 <= k < n and arr[k] = 1 is not divisible by 3, then whenever the function returns a result r, r = [-1, -1].
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      (¬ ∃ m : Nat, onesIn arr.val = 3 * m) →
        ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r = [-1, -1] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), (¬ ∃ m : Nat, onesIn arr.val = 3 * m) →
          ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r = [-1, -1]) := by
    sorry

  /-- Whenever the function returns a result r and r != [-1, -1], writing r = [i, j], the number of ones in arr[0..i], the number of ones in arr[i+1..j-1], and the number of ones in arr[j..n-1] are all equal.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
        ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
          onesIn (cut arr.val 0 i) = onesIn (cut arr.val (i + 1) (j - 1)) ∧
            onesIn (cut arr.val (i + 1) (j - 1)) =
              onesIn (cut arr.val j (arr.val.length - 1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r → outVals r ≠ [-1, -1] →
          ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
            onesIn (cut arr.val 0 i) = onesIn (cut arr.val (i + 1) (j - 1)) ∧
              onesIn (cut arr.val (i + 1) (j - 1)) =
                onesIn (cut arr.val j (arr.val.length - 1))) := by
    sorry

  /-- Whenever the function returns a result r, r != [-1, -1]; moreover, writing r = [i, j], we have 0 <= i, i + 1 < j, j <= n - 1 and all three parts arr[0..i], arr[i+1..j-1], and arr[j..n-1] are all-zero, hence all have binary value 0.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] = 0. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hzero : IsZeroSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        outVals r ≠ [-1, -1] ∧
          ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
            0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
              AllZero (cut arr.val 0 i) ∧
              AllZero (cut arr.val (i + 1) (j - 1)) ∧
              AllZero (cut arr.val j (arr.val.length - 1)) ∧
              binVal (cut arr.val 0 i) = 0 ∧
              binVal (cut arr.val (i + 1) (j - 1)) = 0 ∧
              binVal (cut arr.val j (arr.val.length - 1)) = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hzero : IsZeroSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          outVals r ≠ [-1, -1] ∧
            ∀ i j : Nat, outVals r = [(i : Int), (j : Int)] →
              0 ≤ i ∧ i + 1 < j ∧ j < arr.val.length ∧
                AllZero (cut arr.val 0 i) ∧
                AllZero (cut arr.val (i + 1) (j - 1)) ∧
                AllZero (cut arr.val j (arr.val.length - 1)) ∧
                binVal (cut arr.val 0 i) = 0 ∧
                binVal (cut arr.val (i + 1) (j - 1)) = 0 ∧
                binVal (cut arr.val j (arr.val.length - 1)) = 0) := by
    sorry

  /-- Whenever the function returns a result r, if n is divisible by 3 then r = [n/3 - 1, 2*n/3], and if n is not divisible by 3 then r = [-1, -1].
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] = 1. -/
  theorem spec_11 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hone : IsOneSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        ((∃ m : Nat, arr.val.length = 3 * m) →
            outVals r = [((arr.val.length / 3 : Nat) : Int) - 1,
                          ((2 * arr.val.length / 3 : Nat) : Int)]) ∧
          ((¬ ∃ m : Nat, arr.val.length = 3 * m) → outVals r = [-1, -1]) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hone : IsOneSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          ((∃ m : Nat, arr.val.length = 3 * m) →
              outVals r = [((arr.val.length / 3 : Nat) : Int) - 1,
                            ((2 * arr.val.length / 3 : Nat) : Int)]) ∧
            ((¬ ∃ m : Nat, arr.val.length = 3 * m) → outVals r = [-1, -1])) := by
    sorry

  /-- Whenever the function returns a result r, r = [0, 2] if arr[0] = arr[1] = arr[2], and r = [-1, -1] otherwise.
    Preconditions: len(arr) = 3, and for every k with 0 <= k < 3, arr[k] is either 0 or 1. -/
  theorem spec_12 (arr : Slice Std.I64)
      (hlen : arr.val.length = 3) (hbits : IsBitSlice arr) :
      ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
        ((bitAt arr.val 0 = bitAt arr.val 1 ∧ bitAt arr.val 1 = bitAt arr.val 2) →
            outVals r = [0, 2]) ∧
          ((¬ (bitAt arr.val 0 = bitAt arr.val 1 ∧ bitAt arr.val 1 = bitAt arr.val 2)) →
            outVals r = [-1, -1]) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : arr.val.length = 3) (hbits : IsBitSlice arr), ∀ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r →
          ((bitAt arr.val 0 = bitAt arr.val 1 ∧ bitAt arr.val 1 = bitAt arr.val 2) →
              outVals r = [0, 2]) ∧
            ((¬ (bitAt arr.val 0 = bitAt arr.val 1 ∧ bitAt arr.val 1 = bitAt arr.val 2)) →
              outVals r = [-1, -1])) := by
    sorry

  /-- The function returns a result r for every arr satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: Let n = len(arr). 3 <= n <= 30000, and for every k with 0 <= k < n, arr[k] is either 0 or 1. -/
  theorem spec_13 (arr : Slice Std.I64)
      (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
      (hbits : IsBitSlice arr) :
      ∃ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 30000)
        (hbits : IsBitSlice arr), ∃ r, Aegis.ThreeEqualParts.three_equal_parts arr = ok r) := by
    sorry

  end AegisSpec.ThreeEqualParts
