import Aegis.PlusOne.Code.Funs

/-!
# Specifications of `Aegis.PlusOne.plus_one`

LeetCode problem `plus-one`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PlusOne

  def val (l : List Std.I64) : Int :=
    ((List.range l.length).map (fun i => l[i]!.val * 10 ^ (l.length - 1 - i))).sum

  def allNines (l : List Std.I64) : Prop := ∀ d ∈ l, d.val = 9

  def countLeading (p : Std.I64 → Bool) : List Std.I64 → Nat
    | [] => 0
    | d :: ds => if p d then countLeading p ds + 1 else 0

  def trailingNines (l : List Std.I64) : Nat := countLeading (fun d => d.val == 9) l.reverse

  def trailingZeros (l : List Std.I64) : Nat := countLeading (fun d => d.val == 0) l.reverse

  /-- The function returns a result r and r is exactly the decimal digit sequence of val(digits)+1, most significant digit first, with no leading zero. Formally, with val(x) = sum_{i=0}^{len(x)-1} x[i] * 10^(len(x)-1-i), we have len(r) >= 1, 0 <= r[i] <= 9 for every i with 0 <= i < len(r), r[0] != 0, and val(r) = val(digits) + 1. These conditions determine r uniquely.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. The single-digit input [0] is allowed, matching the provided test cases. -/
  theorem spec_1 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.PlusOne.plus_one digits = ok r ∧
        1 ≤ r.val.length ∧
        (∀ i, i < r.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 9) ∧
        (r.val[0]!).val ≠ 0 ∧
        val r.val = val digits.val + 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.PlusOne.plus_one digits = ok r ∧
          1 ≤ r.val.length ∧
          (∀ i, i < r.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 9) ∧
          (r.val[0]!).val ≠ 0 ∧
          val r.val = val digits.val + 1) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, panic, or access out of bounds) for every digits satisfying the preconditions.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_2 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∃ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every entry of r is a decimal digit: for every i with 0 <= i < len(r), 0 <= r[i] <= 9.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_3 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        ∀ i, i < r.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 9 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          ∀ i, i < r.val.length → 0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 9) := by
    sorry

  /-- Whenever the function returns a result r, if every digit of digits equals 9 then len(r) = len(digits) + 1; otherwise len(r) = len(digits).
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_4 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        (allNines digits.val → r.val.length = digits.val.length + 1) ∧
        (¬ allNines digits.val → r.val.length = digits.val.length) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          (allNines digits.val → r.val.length = digits.val.length + 1) ∧
          (¬ allNines digits.val → r.val.length = digits.val.length)) := by
    sorry

  /-- Whenever the function returns a result r, r is non-empty and has no leading zero: len(r) >= 1 and r[0] != 0.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_5 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        1 ≤ r.val.length ∧ (r.val[0]!).val ≠ 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          1 ≤ r.val.length ∧ (r.val[0]!).val ≠ 0) := by
    sorry

  /-- Whenever the function returns a result r, val(r) = val(digits) + 1, where val(x) = sum_{i=0}^{len(x)-1} x[i] * 10^(len(x)-1-i).
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_6 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        val r.val = val digits.val + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          val r.val = val digits.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, the last digit of r is the last digit of digits incremented modulo 10: r[len(r)-1] = (digits[len(digits)-1] + 1) mod 10, with mod giving the nonnegative remainder in {0,...,9}.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_7 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        (r.val[r.val.length - 1]!).val = ((digits.val[digits.val.length - 1]!).val + 1) % 10 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          (r.val[r.val.length - 1]!).val = ((digits.val[digits.val.length - 1]!).val + 1) % 10) := by
    sorry

  /-- Whenever the function returns a result r, if digits[len(digits)-1] < 9, then len(r) = len(digits), r[len(digits)-1] = digits[len(digits)-1] + 1, and r[i] = digits[i] for every i with 0 <= i < len(digits)-1.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_8 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        (digits.val[digits.val.length - 1]!).val < 9 →
          r.val.length = digits.val.length ∧
          (r.val[digits.val.length - 1]!).val = (digits.val[digits.val.length - 1]!).val + 1 ∧
          (∀ i, i < digits.val.length - 1 → (r.val[i]!).val = (digits.val[i]!).val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          (digits.val[digits.val.length - 1]!).val < 9 →
            r.val.length = digits.val.length ∧
            (r.val[digits.val.length - 1]!).val = (digits.val[digits.val.length - 1]!).val + 1 ∧
            (∀ i, i < digits.val.length - 1 → (r.val[i]!).val = (digits.val[i]!).val)) := by
    sorry

  /-- Let n = len(digits), and let k be the largest integer with 0 <= k <= n such that digits[n-1-j] = 9 for every j with 0 <= j < k. If k < n, then whenever the function returns a result r: len(r) = n; r[i] = digits[i] for every i with 0 <= i < n-k-1; r[n-k-1] = digits[n-k-1] + 1; and r[i] = 0 for every i with n-k <= i < n.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_9 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0)
      (hk : trailingNines digits.val < digits.val.length) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        r.val.length = digits.val.length ∧
        (∀ i, i < digits.val.length - trailingNines digits.val - 1 →
          (r.val[i]!).val = (digits.val[i]!).val) ∧
        (r.val[digits.val.length - trailingNines digits.val - 1]!).val =
          (digits.val[digits.val.length - trailingNines digits.val - 1]!).val + 1 ∧
        (∀ i, digits.val.length - trailingNines digits.val ≤ i → i < digits.val.length →
          (r.val[i]!).val = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0)
        (hk : trailingNines digits.val < digits.val.length), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          r.val.length = digits.val.length ∧
          (∀ i, i < digits.val.length - trailingNines digits.val - 1 →
            (r.val[i]!).val = (digits.val[i]!).val) ∧
          (r.val[digits.val.length - trailingNines digits.val - 1]!).val =
            (digits.val[digits.val.length - trailingNines digits.val - 1]!).val + 1 ∧
          (∀ i, digits.val.length - trailingNines digits.val ≤ i → i < digits.val.length →
            (r.val[i]!).val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if every digit of digits equals 9, then len(r) = len(digits) + 1, r[0] = 1, and r[i] = 0 for every i with 1 <= i < len(r).
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_10 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        allNines digits.val →
          r.val.length = digits.val.length + 1 ∧
          (r.val[0]!).val = 1 ∧
          (∀ i, 1 ≤ i → i < r.val.length → (r.val[i]!).val = 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          allNines digits.val →
            r.val.length = digits.val.length + 1 ∧
            (r.val[0]!).val = 1 ∧
            (∀ i, 1 ≤ i → i < r.val.length → (r.val[i]!).val = 0)) := by
    sorry

  /-- Let k be the number of trailing nines in digits, i.e. the largest k with 0 <= k <= len(digits) such that digits[len(digits)-1-j] = 9 for every j with 0 <= j < k. Whenever the function returns a result r, the number of trailing zeros in r is exactly k: if z is the largest integer with 0 <= z <= len(r) such that r[len(r)-1-j] = 0 for every j with 0 <= j < z, then z = k.
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_11 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        trailingZeros r.val = trailingNines digits.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          trailingZeros r.val = trailingNines digits.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer p with -1 <= p < len(digits) for which exactly one of the following holds: (a) p = -1, every digit of digits is 9, len(r) = len(digits)+1, r[0] = 1, and r[i+1] = 0 for every i with 0 <= i < len(digits); or (b) p >= 0, digits[p] <= 8, digits[i] = 9 for every i with p < i < len(digits), len(r) = len(digits), r[i] = digits[i] for every i with 0 <= i < p, r[p] = digits[p]+1, and r[i] = 0 for every i with p < i < len(digits).
    Preconditions: 1 <= len(digits) <= 100; for every i with 0 <= i < len(digits), 0 <= digits[i] <= 9; and if len(digits) > 1 then digits[0] != 0. -/
  theorem spec_12 (digits : Slice Std.I64)
      (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
      (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
      (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0) :
      ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
        ∃ p : Int, -1 ≤ p ∧ p < (digits.val.length : Int) ∧
          ((p = -1 ∧ allNines digits.val ∧
              r.val.length = digits.val.length + 1 ∧
              (r.val[0]!).val = 1 ∧
              (∀ i, i < digits.val.length → (r.val[i + 1]!).val = 0)) ∨
           (0 ≤ p ∧ (digits.val[p.toNat]!).val ≤ 8 ∧
              (∀ i, p.toNat < i → i < digits.val.length → (digits.val[i]!).val = 9) ∧
              r.val.length = digits.val.length ∧
              (∀ i, i < p.toNat → (r.val[i]!).val = (digits.val[i]!).val) ∧
              (r.val[p.toNat]!).val = (digits.val[p.toNat]!).val + 1 ∧
              (∀ i, p.toNat < i → i < digits.val.length → (r.val[i]!).val = 0))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (digits : Slice Std.I64)
        (hlen1 : 1 ≤ digits.val.length) (hlen2 : digits.val.length ≤ 100)
        (hdigits : ∀ i, i < digits.val.length → 0 ≤ (digits.val[i]!).val ∧ (digits.val[i]!).val ≤ 9)
        (hnz : 1 < digits.val.length → (digits.val[0]!).val ≠ 0), ∀ r : alloc.vec.Vec Std.I64, Aegis.PlusOne.plus_one digits = ok r →
          ∃ p : Int, -1 ≤ p ∧ p < (digits.val.length : Int) ∧
            ((p = -1 ∧ allNines digits.val ∧
                r.val.length = digits.val.length + 1 ∧
                (r.val[0]!).val = 1 ∧
                (∀ i, i < digits.val.length → (r.val[i + 1]!).val = 0)) ∨
             (0 ≤ p ∧ (digits.val[p.toNat]!).val ≤ 8 ∧
                (∀ i, p.toNat < i → i < digits.val.length → (digits.val[i]!).val = 9) ∧
                r.val.length = digits.val.length ∧
                (∀ i, i < p.toNat → (r.val[i]!).val = (digits.val[i]!).val) ∧
                (r.val[p.toNat]!).val = (digits.val[p.toNat]!).val + 1 ∧
                (∀ i, p.toNat < i → i < digits.val.length → (r.val[i]!).val = 0)))) := by
    sorry

  end AegisSpec.PlusOne
