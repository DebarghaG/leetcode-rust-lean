import Aegis.NumberOfStableArrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfStableArrays.number_of_stable_arrays`

LeetCode problem `find-all-possible-stable-binary-arrays-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical

  namespace AegisSpec.NumberOfStableArrays

  def IsBinary (arr : List ℕ) : Prop := ∀ x ∈ arr, x = 0 ∨ x = 1

  def numOcc (v : ℕ) (arr : List ℕ) : ℕ := (arr.filter (fun x => x = v)).length

  noncomputable def binarySeqs (n : ℕ) : Finset (List ℕ) :=
    (Finset.univ : Finset (Fin n → Bool)).image fun f =>
      List.ofFn (fun i => if f i then 1 else 0)

  def BlockMixed (arr : List ℕ) (i j : ℕ) : Prop :=
    (∃ k, i ≤ k ∧ k ≤ j ∧ arr[k]? = some 0) ∧
    (∃ k, i ≤ k ∧ k ≤ j ∧ arr[k]? = some 1)

  def IsStable (limit : ℕ) (arr : List ℕ) : Prop :=
    ∀ i j : ℕ, i ≤ j → j < arr.length → limit < j - i + 1 → BlockMixed arr i j

  def RunsBounded (limit : ℕ) (arr : List ℕ) : Prop :=
    ∀ i j : ℕ, i ≤ j → j < arr.length →
      (∀ k, i ≤ k → k ≤ j → arr[k]? = arr[i]?) → j - i + 1 ≤ limit

  noncomputable def stableSeqs (zero one limit : ℕ) : Finset (List ℕ) :=
    (binarySeqs (zero + one)).filter fun arr =>
      IsBinary arr ∧ numOcc 0 arr = zero ∧ numOcc 1 arr = one ∧ IsStable limit arr

  noncomputable def runsBoundedSeqs (zero one limit : ℕ) : Finset (List ℕ) :=
    (binarySeqs (zero + one)).filter fun arr =>
      IsBinary arr ∧ numOcc 0 arr = zero ∧ numOcc 1 arr = one ∧ RunsBounded limit arr

  def N1 (O L : ℤ) : ℤ := max 0 (min O L - max 0 (O - L) + 1)

  /-- Let M = 1000000007. Let S be the set of all finite binary sequences arr, indexed 0,1,...,len(arr)-1, such that: (1) len(arr) = zero + one; (2) every entry arr[i] is either 0 or 1; (3) the number of indices i with arr[i] = 0 is exactly zero, and the number with arr[i] = 1 is exactly one; (4) for every pair of indices i,j with 0 <= i <= j < len(arr) and j-i+1 > limit, the contiguous subarray arr[i..j] contains at least one 0 and at least one 1. Then the function returns a result r, and r is the unique integer such that 0 <= r < M and r is congruent to |S| modulo M.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_1 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∃ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        r.val ≡ ((stableSeqs zero.val.toNat one.val.toNat limit.val.toNat).card : ℤ)
          [ZMOD 1000000007] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∃ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val ≡ ((stableSeqs zero.val.toNat one.val.toNat limit.val.toNat).card : ℤ)
            [ZMOD 1000000007]) := by
    sorry

  /-- For every zero, one, and limit satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_2 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∃ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∃ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r) := by
    sorry

  /-- Whenever the function returns a result r on a valid input, the integer value of r satisfies 0 <= r < 1000000007.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_3 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Whenever the function returns r for (zero, one, limit), r is the least nonnegative residue modulo 1000000007 of the number of binary sequences arr with exactly one occurrences of 0, exactly zero occurrences of 1, and such that every contiguous subarray of arr of length greater than limit contains both 0 and 1.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_4 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val ≡ ((stableSeqs one.val.toNat zero.val.toNat limit.val.toNat).card : ℤ)
          [ZMOD 1000000007] := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val ≡ ((stableSeqs one.val.toNat zero.val.toNat limit.val.toNat).card : ℤ)
            [ZMOD 1000000007]) := by
    sorry

  /-- If limit = 1, then whenever the function returns r, r = 2 if zero = one; r = 1 if zero = one + 1 or one = zero + 1; and r = 0 otherwise.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_5 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
      (hlim : limit.val = 1) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        (zero.val = one.val → r.val = 2) ∧
        ((zero.val = one.val + 1 ∨ one.val = zero.val + 1) → r.val = 1) ∧
        ((¬ zero.val = one.val) ∧ (¬ zero.val = one.val + 1) ∧
          (¬ one.val = zero.val + 1) → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
        (hlim : limit.val = 1), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          (zero.val = one.val → r.val = 2) ∧
          ((zero.val = one.val + 1 ∨ one.val = zero.val + 1) → r.val = 1) ∧
          ((¬ zero.val = one.val) ∧ (¬ zero.val = one.val + 1) ∧
            (¬ one.val = zero.val + 1) → r.val = 0)) := by
    sorry

  /-- If limit >= zero and limit >= one, then whenever the function returns r, r is the least nonnegative residue modulo 1000000007 of the binomial coefficient choose(zero + one, zero).
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_6 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
      (hbig : limit.val ≥ zero.val ∧ limit.val ≥ one.val) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val = (((Nat.choose (zero.val.toNat + one.val.toNat) zero.val.toNat) % 1000000007 :
          ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
        (hbig : limit.val ≥ zero.val ∧ limit.val ≥ one.val), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val = (((Nat.choose (zero.val.toNat + one.val.toNat) zero.val.toNat) % 1000000007 :
            ℕ) : ℤ)) := by
    sorry

  /-- If zero = 1, then whenever the function returns r, r is congruent modulo 1000000007 to N1(one, limit), where N1(O,L) = max(0, min(O,L) - max(0,O-L) + 1).
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_7 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
      (hz : zero.val = 1) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val ≡ N1 one.val limit.val [ZMOD 1000000007] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
        (hz : zero.val = 1), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val ≡ N1 one.val limit.val [ZMOD 1000000007]) := by
    sorry

  /-- If one = 1, then whenever the function returns r, r is congruent modulo 1000000007 to N1(zero, limit), where N1(O,L) = max(0, min(O,L) - max(0,O-L) + 1).
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_8 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
      (ho : one.val = 1) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val ≡ N1 zero.val limit.val [ZMOD 1000000007] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
        (ho : one.val = 1), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val ≡ N1 zero.val limit.val [ZMOD 1000000007]) := by
    sorry

  /-- If zero > limit * (one + 1) or one > limit * (zero + 1), then whenever the function returns r, r = 0.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_9 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
      (hsep : zero.val > limit.val * (one.val + 1) ∨
        one.val > limit.val * (zero.val + 1)) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200)
        (hsep : zero.val > limit.val * (one.val + 1) ∨
          one.val > limit.val * (zero.val + 1)), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists at least one binary sequence arr with exactly zero occurrences of 0, exactly one occurrences of 1, and such that every contiguous subarray of arr of length greater than limit contains both 0 and 1.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_10 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val > 0 →
        ∃ arr : List ℕ, numOcc 0 arr = zero.val.toNat ∧
          numOcc 1 arr = one.val.toNat ∧ IsStable limit.val.toNat arr := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val > 0 →
          ∃ arr : List ℕ, numOcc 0 arr = zero.val.toNat ∧
            numOcc 1 arr = one.val.toNat ∧ IsStable limit.val.toNat arr) := by
    sorry

  /-- Whenever the function returns r, r is the least nonnegative residue modulo 1000000007 of the number of binary sequences arr with exactly zero occurrences of 0 and exactly one occurrences of 1 such that no maximal contiguous run of equal bits in arr has length greater than limit.
    Preconditions: The integer values of zero, one, and limit satisfy 1 <= zero <= 200, 1 <= one <= 200, and 1 <= limit <= 200. -/
  theorem spec_11 (zero one limit : Std.I64)
      (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
      (hone : 1 ≤ one.val ∧ one.val ≤ 200)
      (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200) :
      ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
        r.val = (((runsBoundedSeqs zero.val.toNat one.val.toNat limit.val.toNat).card %
          1000000007 : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (zero one limit : Std.I64)
        (hzero : 1 ≤ zero.val ∧ zero.val ≤ 200)
        (hone : 1 ≤ one.val ∧ one.val ≤ 200)
        (hlimit : 1 ≤ limit.val ∧ limit.val ≤ 200), ∀ r, Aegis.NumberOfStableArrays.number_of_stable_arrays zero one limit = ok r →
          r.val = (((runsBoundedSeqs zero.val.toNat one.val.toNat limit.val.toNat).card %
            1000000007 : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.NumberOfStableArrays
