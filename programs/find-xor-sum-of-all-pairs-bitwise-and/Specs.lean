import Aegis.GetXorSum.Code.Funs

/-!
# Specifications of `Aegis.GetXorSum.get_xor_sum`

LeetCode problem `find-xor-sum-of-all-pairs-bitwise-and`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GetXorSum

namespace AegisSpec.GetXorSum

def words (l : List Std.I64) : List (BitVec 64) := l.map fun x => x.bv

def xorWords (l : List (BitVec 64)) : BitVec 64 := l.foldr (fun w acc => w ^^^ acc) 0

def xorAll (l : List Std.I64) : BitVec 64 := xorWords (words l)

def xorAllPairs (l1 l2 : List Std.I64) : BitVec 64 :=
  xorWords ((words l1).flatMap fun a => (words l2).map fun b => a &&& b)

def xorAndXorLeft (l1 l2 : List Std.I64) : BitVec 64 :=
  xorWords ((words l1).map fun a => a &&& xorAll l2)

def xorAndXorRight (l1 l2 : List Std.I64) : BitVec 64 :=
  xorWords ((words l2).map fun b => b &&& xorAll l1)

def bitCount (l : List Std.I64) (k : Fin 64) : ℕ := (l.filter fun x => x.bv.getLsb k).length

def bitSet (w : BitVec 64) (k : Fin 64) : Prop := w.getLsb k = true

def bitSetI64 (x : Std.I64) (k : Fin 64) : Prop := x.bv.getLsb k = true

def permute {α : Type} (l : List α) (π : Equiv.Perm (Fin l.length)) : List α :=
  (List.finRange l.length).map fun i => l.get (π i)

def InRange (l : List Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), 0 ≤ (l.get ⟨i, hi⟩).val ∧ (l.get ⟨i, hi⟩).val ≤ 10 ^ 9

def Pre (arr1 arr2 : Slice Std.I64) : Prop :=
  1 ≤ arr1.val.length ∧ 1 ≤ arr2.val.length ∧ InRange arr1.val ∧ InRange arr2.val

/-- The function returns a result r and r = XOR_{i=0}^{len(arr1)-1} XOR_{j=0}^{len(arr2)-1} (arr1[i] AND arr2[j]), where AND and XOR are bitwise operations on 64-bit non-negative integers. Equivalently, r is the XOR sum of the list containing arr1[i] AND arr2[j] for every pair (i, j) with 0 <= i < len(arr1) and 0 <= j < len(arr2).
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_1 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAllPairs arr1.val arr2.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAllPairs arr1.val arr2.val) := by
  sorry

/-- The function returns a result r and r = XOR1 AND XOR2, where XOR1 is the bitwise XOR of all elements of arr1 and XOR2 is the bitwise XOR of all elements of arr2.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_2 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = (xorAll arr1.val &&& xorAll arr2.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = (xorAll arr1.val &&& xorAll arr2.val)) := by
  sorry

/-- The function returns a result r such that for every bit position k with 0 <= k < 64, the k-th bit of r is 1 if and only if both of the following are true: (a) the number of indices i with 0 <= i < len(arr1) and the k-th bit of arr1[i] equal to 1 is odd; (b) the number of indices j with 0 <= j < len(arr2) and the k-th bit of arr2[j] equal to 1 is odd.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_3 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64,
        (bitSet r.bv k ↔ Odd (bitCount arr1.val k) ∧ Odd (bitCount arr2.val k)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64,
        (bitSet r.bv k ↔ Odd (bitCount arr1.val k) ∧ Odd (bitCount arr2.val k))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_4 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r) := by
  sorry

/-- For any arr1 and arr2 satisfying the preconditions, the value returned by get_xor_sum arr1 arr2 equals the value returned by get_xor_sum arr2 arr1 (i.e., the result is symmetric in its two arguments).
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_5 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r1 r2, get_xor_sum arr1 arr2 = ok r1 ∧ get_xor_sum arr2 arr1 = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r1 r2, get_xor_sum arr1 arr2 = ok r1 ∧ get_xor_sum arr2 arr1 = ok r2 ∧
      r1.val = r2.val) := by
  sorry

/-- The function returns a result r and r = XOR_{i=0}^{len(arr1)-1} (arr1[i] AND XOR2), where XOR2 is the bitwise XOR of all elements of arr2.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_6 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAndXorLeft arr1.val arr2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAndXorLeft arr1.val arr2.val) := by
  sorry

/-- The function returns a result r and r = XOR_{j=0}^{len(arr2)-1} (arr2[j] AND XOR1), where XOR1 is the bitwise XOR of all elements of arr1.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_7 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAndXorRight arr1.val arr2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧ r.bv = xorAndXorRight arr1.val arr2.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if for every bit position k with 0 <= k < 64, the number of indices i with 0 <= i < len(arr1) and the k-th bit of arr1[i] equal to 1 is even, or the number of indices j with 0 <= j < len(arr2) and the k-th bit of arr2[j] equal to 1 is even.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_8 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      (r.val = 0 ↔ ∀ k : Fin 64,
        Even (bitCount arr1.val k) ∨ Even (bitCount arr2.val k)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      (r.val = 0 ↔ ∀ k : Fin 64,
        Even (bitCount arr1.val k) ∨ Even (bitCount arr2.val k))) := by
  sorry

/-- The function returns a result r and 0 <= r < 2^30 (i.e., 0 <= r <= 1073741823).
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_9 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧ 0 ≤ r.val ∧ r.val < 2 ^ 30 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧ 0 ≤ r.val ∧ r.val < 2 ^ 30) := by
  sorry

/-- The function returns a result r and r is a bitwise submask of both XOR1 and XOR2: for every bit position k with 0 <= k < 64, if the k-th bit of r is 1 then the k-th bit of XOR1 is 1 and the k-th bit of XOR2 is 1, where XOR1 is the bitwise XOR of all elements of arr1 and XOR2 is the bitwise XOR of all elements of arr2.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_10 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64, bitSet r.bv k →
        bitSet (xorAll arr1.val) k ∧ bitSet (xorAll arr2.val) k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64, bitSet r.bv k →
        bitSet (xorAll arr1.val) k ∧ bitSet (xorAll arr2.val) k) := by
  sorry

/-- The function returns a result r such that for every bit position k with 0 <= k < 64, if the k-th bit of r is 1, then there exists an index i with 0 <= i < len(arr1) and an index j with 0 <= j < len(arr2) such that the k-th bit of arr1[i] is 1 and the k-th bit of arr2[j] is 1.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_11 (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val) :
    ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64, bitSet r.bv k →
        ∃ (i : ℕ) (hi : i < arr1.val.length) (j : ℕ) (hj : j < arr2.val.length),
          bitSetI64 (arr1.val.get ⟨i, hi⟩) k ∧ bitSetI64 (arr2.val.get ⟨j, hj⟩) k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val), ∃ r, get_xor_sum arr1 arr2 = ok r ∧
      ∀ k : Fin 64, bitSet r.bv k →
        ∃ (i : ℕ) (hi : i < arr1.val.length) (j : ℕ) (hj : j < arr2.val.length),
          bitSetI64 (arr1.val.get ⟨i, hi⟩) k ∧ bitSetI64 (arr2.val.get ⟨j, hj⟩) k) := by
  sorry

/-- For any permutation π of the index set {0, 1, ..., len(arr1)-1}, let arr1' be the slice defined by arr1'[i] = arr1[π(i)] for all 0 <= i < len(arr1). Then the value returned by get_xor_sum arr1' arr2 equals the value returned by get_xor_sum arr1 arr2.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_12 (arr1 arr2 arr1' : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val)
    (π : Equiv.Perm (Fin arr1.val.length))
    (hperm : arr1'.val = permute arr1.val π) :
    ∃ r r', get_xor_sum arr1' arr2 = ok r ∧ get_xor_sum arr1 arr2 = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr1 arr2 arr1' : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val)
    (π : Equiv.Perm (Fin arr1.val.length))
    (hperm : arr1'.val = permute arr1.val π), ∃ r r', get_xor_sum arr1' arr2 = ok r ∧ get_xor_sum arr1 arr2 = ok r' ∧
      r.val = r'.val) := by
  sorry

/-- For any permutation σ of the index set {0, 1, ..., len(arr2)-1}, let arr2' be the slice defined by arr2'[j] = arr2[σ(j)] for all 0 <= j < len(arr2). Then the value returned by get_xor_sum arr1 arr2' equals the value returned by get_xor_sum arr1 arr2.
  Preconditions: len(arr1) >= 1, len(arr2) >= 1, for every i with 0 <= i < len(arr1), 0 <= arr1[i] <= 10^9, and for every j with 0 <= j < len(arr2), 0 <= arr2[j] <= 10^9. -/
theorem spec_13 (arr1 arr2 arr2' : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val)
    (σ : Equiv.Perm (Fin arr2.val.length))
    (hperm : arr2'.val = permute arr2.val σ) :
    ∃ r r', get_xor_sum arr1 arr2' = ok r ∧ get_xor_sum arr1 arr2 = ok r' ∧
      r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr1 arr2 arr2' : Slice Std.I64)
    (h1 : 1 ≤ arr1.val.length) (h2 : 1 ≤ arr2.val.length)
    (ha : InRange arr1.val) (hb : InRange arr2.val)
    (σ : Equiv.Perm (Fin arr2.val.length))
    (hperm : arr2'.val = permute arr2.val σ), ∃ r r', get_xor_sum arr1 arr2' = ok r ∧ get_xor_sum arr1 arr2 = ok r' ∧
      r.val = r'.val) := by
  sorry

end AegisSpec.GetXorSum
