import Aegis.SelfDividingNumbers.Code.Funs

/-!
# Specifications of `Aegis.SelfDividingNumbers.self_dividing_numbers`

LeetCode problem `self-dividing-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SelfDividingNumbers

  def decimalDigitsAux (n : Nat) : List Nat :=
    if n = 0 then [] else decimalDigitsAux (n / 10) ++ [n % 10]
  termination_by n
  decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero (by omega)) (by decide)

  def decimalDigits (n : Nat) : List Nat :=
    if n = 0 then [0] else decimalDigitsAux n

  def digitOccurs (d : Nat) (x : Int) : Prop := d ∈ decimalDigits x.natAbs

  def HasNoZeroDigit (x : Int) : Prop := ∀ d : Nat, digitOccurs d x → d ≠ 0

  def IsSelfDividing (x : Int) : Prop :=
    0 < x ∧ HasNoZeroDigit x ∧ ∀ d : Nat, digitOccurs d x → x % (d : Int) = 0

  instance instDecidableHasNoZeroDigit (x : Int) : Decidable (HasNoZeroDigit x) := by
    unfold HasNoZeroDigit digitOccurs
    infer_instance

  instance instDecidableIsSelfDividing (x : Int) : Decidable (IsSelfDividing x) := by
    unfold IsSelfDividing HasNoZeroDigit digitOccurs
    infer_instance

  def vals (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

  def rangeInts (left right : Int) : List Int :=
    (List.range (right - left + 1).toNat).map (fun k => left + (k : Int))

  def selfDividingIn (left right : Int) : List Int :=
    (rangeInts left right).filter (fun x => decide (IsSelfDividing x))

  def IsLeastSelfDividingIn (left right y : Int) : Prop :=
    left ≤ y ∧ y ≤ right ∧ IsSelfDividing y ∧
      ∀ z : Int, left ≤ z → z ≤ right → IsSelfDividing z → y ≤ z

  def IsGreatestSelfDividingIn (left right y : Int) : Prop :=
    left ≤ y ∧ y ≤ right ∧ IsSelfDividing y ∧
      ∀ z : Int, left ≤ z → z ≤ right → IsSelfDividing z → z ≤ y

  /-- Whenever the function returns a result r, the returned vector r is exactly the strictly increasing list of all integers x such that left <= x <= right and x is self-dividing. A positive integer x is self-dividing when its standard decimal representation (with no leading zeros) contains no digit 0 and, for every decimal digit d occurring in that representation, x mod d = 0. Equivalently, r = [x_0, x_1, ..., x_{m-1}] where x_0 < x_1 < ... < x_{m-1} and {x_0, ..., x_{m-1}} = {x | left <= x <= right and x is self-dividing}.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_1 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      vals r = selfDividingIn left.val right.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), vals r = selfDividingIn left.val right.val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), the integer r[i] satisfies left <= r[i] <= right.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_2 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      ∀ (i : Nat) (hi : i < (vals r).length),
        left.val ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ right.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), ∀ (i : Nat) (hi : i < (vals r).length),
          left.val ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ right.val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), r[i] is positive and its standard decimal representation contains no digit 0.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_3 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      ∀ (i : Nat) (hi : i < (vals r).length),
        0 < (vals r)[i]'hi ∧ HasNoZeroDigit ((vals r)[i]'hi) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), ∀ (i : Nat) (hi : i < (vals r).length),
          0 < (vals r)[i]'hi ∧ HasNoZeroDigit ((vals r)[i]'hi)) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r) and every decimal digit d such that d ≠ 0 and d occurs in the standard decimal representation of r[i], r[i] mod d = 0.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_4 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      ∀ (i : Nat) (hi : i < (vals r).length) (d : Nat),
        d ≠ 0 → digitOccurs d ((vals r)[i]'hi) → (vals r)[i]'hi % (d : Int) = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), ∀ (i : Nat) (hi : i < (vals r).length) (d : Nat),
          d ≠ 0 → digitOccurs d ((vals r)[i]'hi) → (vals r)[i]'hi % (d : Int) = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i and i + 1 < len(r), we have r[i] < r[i + 1].
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_5 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      ∀ (i : Nat) (hi : i + 1 < (vals r).length),
        (vals r)[i]'(Nat.lt_of_succ_lt hi) < (vals r)[i + 1]'hi := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), ∀ (i : Nat) (hi : i + 1 < (vals r).length),
          (vals r)[i]'(Nat.lt_of_succ_lt hi) < (vals r)[i + 1]'hi) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x such that left <= x <= right and x is self-dividing (positive, with no zero decimal digit, and divisible by each of its decimal digits), there exists an index i with 0 <= i < len(r) and r[i] = x.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_6 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      ∀ x : Int, left.val ≤ x → x ≤ right.val → IsSelfDividing x →
        ∃ (i : Nat) (hi : i < (vals r).length), (vals r)[i]'hi = x := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), ∀ x : Int, left.val ≤ x → x ≤ right.val → IsSelfDividing x →
          ∃ (i : Nat) (hi : i < (vals r).length), (vals r)[i]'hi = x) := by
    sorry

  /-- Whenever the function returns a result r, len(r) is equal to the number of integers x such that left <= x <= right and x is self-dividing.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_7 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      (vals r).length = (selfDividingIn left.val right.val).length := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), (vals r).length = (selfDividingIn left.val right.val).length) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0 if and only if there is no integer x with left <= x <= right that is self-dividing.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_8 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      (vals r).length = 0 ↔
        ∀ x : Int, left.val ≤ x → x ≤ right.val → ¬ IsSelfDividing x := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), (vals r).length = 0 ↔
          ∀ x : Int, left.val ≤ x → x ≤ right.val → ¬ IsSelfDividing x) := by
    sorry

  /-- Whenever the function returns a result r, if left = right, then: (a) if left is self-dividing, len(r) = 1 and r[0] = left; (b) if left is not self-dividing, len(r) = 0.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_9 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
      (heq : left.val = right.val) :
      (IsSelfDividing left.val → (vals r).length = 1 ∧ (vals r).head? = some left.val) ∧
        (¬ IsSelfDividing left.val → (vals r).length = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
        (heq : left.val = right.val), (IsSelfDividing left.val → (vals r).length = 1 ∧ (vals r).head? = some left.val) ∧
          (¬ IsSelfDividing left.val → (vals r).length = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if 1 <= left <= right <= 9, then len(r) = right - left + 1 and for every index i with 0 <= i < len(r), r[i] = left + i.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_10 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
      (hsmall : right.val ≤ 9) :
      (vals r).length = (right.val - left.val + 1).toNat ∧
        ∀ (i : Nat) (hi : i < (vals r).length), (vals r)[i]'hi = left.val + (i : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
        (hsmall : right.val ≤ 9), (vals r).length = (right.val - left.val + 1).toNat ∧
          ∀ (i : Nat) (hi : i < (vals r).length), (vals r)[i]'hi = left.val + (i : Int)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= len(r) <= right - left + 1.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_11 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      0 ≤ (vals r).length ∧ (vals r).length ≤ (right.val - left.val + 1).toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), 0 ≤ (vals r).length ∧ (vals r).length ≤ (right.val - left.val + 1).toNat) := by
    sorry

  /-- Whenever the function returns a result r and len(r) > 0, r[0] is the least self-dividing integer in [left, right], and r[len(r) - 1] is the greatest self-dividing integer in [left, right].
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_12 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
      (hne : 0 < (vals r).length) :
      ∃ y z : Int,
        (vals r).head? = some y ∧ IsLeastSelfDividingIn left.val right.val y ∧
          (vals r).getLast? = some z ∧ IsGreatestSelfDividingIn left.val right.val z := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
        (hne : 0 < (vals r).length), ∃ y z : Int,
          (vals r).head? = some y ∧ IsLeastSelfDividingIn left.val right.val y ∧
            (vals r).getLast? = some z ∧ IsGreatestSelfDividingIn left.val right.val z) := by
    sorry

  /-- For every left and right satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, panic, or other error).
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_13 (left right : Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (left right : Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an integer x with left <= x <= right that is self-dividing, then len(r) > 0 and there exists an index i with 0 <= i < len(r) such that left <= r[i] <= right and r[i] is self-dividing.
    Preconditions: left and right are I64 values whose mathematical integer values satisfy 1 <= left <= right <= 10000. -/
  theorem spec_14 (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r) :
      (∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧ IsSelfDividing x) →
        0 < (vals r).length ∧
          ∃ (i : Nat) (hi : i < (vals r).length),
            left.val ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ right.val ∧
              IsSelfDividing ((vals r)[i]'hi) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (left right : Std.I64) (r : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hleft : left.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r), (∃ x : Int, left.val ≤ x ∧ x ≤ right.val ∧ IsSelfDividing x) →
          0 < (vals r).length ∧
            ∃ (i : Nat) (hi : i < (vals r).length),
              left.val ≤ (vals r)[i]'hi ∧ (vals r)[i]'hi ≤ right.val ∧
                IsSelfDividing ((vals r)[i]'hi)) := by
    sorry

  /-- Whenever the call on (left, right) returns r and the call on (a, b) returns s, the vector s is exactly the subsequence of r consisting of all entries x with a <= x <= b, in the same order.
    Preconditions: left, right, a, and b are I64 values whose mathematical integer values satisfy 1 <= left <= a <= b <= right <= 10000. -/
  theorem spec_15 (left right a b : Std.I64) (r s : alloc.vec.Vec Std.I64)
      (hl : 1 ≤ left.val) (hla : left.val ≤ a.val) (hab : a.val ≤ b.val)
      (hb : b.val ≤ right.val) (hright : right.val ≤ 10000)
      (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
      (hres' : Aegis.SelfDividingNumbers.self_dividing_numbers a b = ok s) :
      vals s = (vals r).filter (fun x => decide (a.val ≤ x ∧ x ≤ b.val)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (left right a b : Std.I64) (r s : alloc.vec.Vec Std.I64)
        (hl : 1 ≤ left.val) (hla : left.val ≤ a.val) (hab : a.val ≤ b.val)
        (hb : b.val ≤ right.val) (hright : right.val ≤ 10000)
        (hres : Aegis.SelfDividingNumbers.self_dividing_numbers left right = ok r)
        (hres' : Aegis.SelfDividingNumbers.self_dividing_numbers a b = ok s), vals s = (vals r).filter (fun x => decide (a.val ≤ x ∧ x ≤ b.val))) := by
    sorry

  end AegisSpec.SelfDividingNumbers
