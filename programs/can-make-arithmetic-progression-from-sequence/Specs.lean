import Aegis.CanMakeArithmeticProgression.Code.Funs

/-!
# Specifications of `Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression`

LeetCode problem `can-make-arithmetic-progression-from-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanMakeArithmeticProgression

  def vals (arr : Slice Std.I64) : List Int := arr.val.map fun x => x.val

  def valAt (arr : Slice Std.I64) (i : Nat) : Int := (vals arr).getD i 0

  def listAt (s : List Int) (i : Nat) : Int := s.getD i 0

  def InBounds (arr : Slice Std.I64) (lo hi : Int) : Prop :=
    ∀ i, i < arr.val.length → lo ≤ valAt arr i ∧ valAt arr i ≤ hi

  def WithinLimits (arr : Slice Std.I64) : Prop := InBounds arr (-1000000) 1000000

  def IsPermOn (p : Nat → Nat) (n : Nat) : Prop :=
    (∀ i, i < n → p i < n) ∧
      (∀ i j, i < n → j < n → p i = p j → i = j) ∧
        (∀ j, j < n → ∃ i, i < n ∧ p i = j)

  def IsNondecreasingRearrangement (l s : List Int) : Prop :=
    s.length = l.length ∧ s.Pairwise (· ≤ ·) ∧ l.Perm s

  def IsMinOf (arr : Slice Std.I64) (m : Int) : Prop :=
    (∃ i, i < arr.val.length ∧ valAt arr i = m) ∧
      ∀ i, i < arr.val.length → m ≤ valAt arr i

  def IsMaxOf (arr : Slice Std.I64) (M : Int) : Prop :=
    (∃ i, i < arr.val.length ∧ valAt arr i = M) ∧
      ∀ i, i < arr.val.length → valAt arr i ≤ M

  /-- Whenever can_make_arithmetic_progression(arr) returns a result r, r is true if and only if there exist an integer d and a bijection p from the set {0,...,len(arr)-1} to itself such that for every i with 0 <= i < len(arr)-1, arr[p(i+1)] - arr[p(i)] = d. Equivalently, the entries p(0),...,p(len(arr)-1) are a rearrangement of arr whose consecutive differences are all equal to d.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000 (arr[i] is interpreted as the mathematical integer value of the 64-bit element). -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        (r = true ↔
          ∃ d : Int, ∃ p : Nat → Nat,
            IsPermOn p arr.val.length ∧
              ∀ i, i + 1 < arr.val.length →
                valAt arr (p (i + 1)) - valAt arr (p i) = d) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          (r = true ↔
            ∃ d : Int, ∃ p : Nat → Nat,
              IsPermOn p arr.val.length ∧
                ∀ i, i + 1 < arr.val.length →
                  valAt arr (p (i + 1)) - valAt arr (p i) = d)) := by
    sorry

  /-- For every arr satisfying the preconditions, the call can_make_arithmetic_progression(arr) returns a result r; it does not fail, overflow, panic, or go out of bounds.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∃ r : Bool, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∃ r : Bool, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r) := by
    sorry

  /-- For every arr satisfying the preconditions and every slice arr2 such that len(arr2) = len(arr), every element of arr2 lies in [-1000000,1000000], and arr2 is a rearrangement of arr (there is a bijection q with arr2[i] = arr[q(i)] for all i), if can_make_arithmetic_progression(arr) returns r and can_make_arithmetic_progression(arr2) returns r2, then r = r2.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_3 (arr arr2 : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr)
      (hlen2 : arr2.val.length = arr.val.length)
      (hb2 : WithinLimits arr2)
      (hperm : ∃ q : Nat → Nat,
        IsPermOn q arr.val.length ∧
          ∀ i, i < arr.val.length → valAt arr2 i = valAt arr (q i)) :
      ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
          r = r2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr)
        (hlen2 : arr2.val.length = arr.val.length)
        (hb2 : WithinLimits arr2)
        (hperm : ∃ q : Nat → Nat,
          IsPermOn q arr.val.length ∧
            ∀ i, i < arr.val.length → valAt arr2 i = valAt arr (q i)), ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
            r = r2) := by
    sorry

  /-- For every integer c such that -1000000 <= arr[i] + c <= 1000000 for every i with 0 <= i < len(arr), let arr2 be the slice of the same length with arr2[i] = arr[i] + c for all i. If can_make_arithmetic_progression(arr) returns r and can_make_arithmetic_progression(arr2) returns r2, then r = r2.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr)
      (c : Int)
      (hc : ∀ i, i < arr.val.length →
        -1000000 ≤ valAt arr i + c ∧ valAt arr i + c ≤ 1000000)
      (arr2 : Slice Std.I64)
      (hlen2 : arr2.val.length = arr.val.length)
      (h2 : ∀ i, i < arr.val.length → valAt arr2 i = valAt arr i + c) :
      ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
          r = r2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr)
        (c : Int)
        (hc : ∀ i, i < arr.val.length →
          -1000000 ≤ valAt arr i + c ∧ valAt arr i + c ≤ 1000000)
        (arr2 : Slice Std.I64)
        (hlen2 : arr2.val.length = arr.val.length)
        (h2 : ∀ i, i < arr.val.length → valAt arr2 i = valAt arr i + c), ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
            r = r2) := by
    sorry

  /-- For every nonzero integer k such that -1000000 <= k * arr[i] <= 1000000 for every i with 0 <= i < len(arr), let arr2 be the slice of the same length with arr2[i] = k * arr[i] for all i. If can_make_arithmetic_progression(arr) returns r and can_make_arithmetic_progression(arr2) returns r2, then r = r2.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr)
      (k : Int) (hk : k ≠ 0)
      (hk_bounds : ∀ i, i < arr.val.length →
        -1000000 ≤ k * valAt arr i ∧ k * valAt arr i ≤ 1000000)
      (arr2 : Slice Std.I64)
      (hlen2 : arr2.val.length = arr.val.length)
      (h2 : ∀ i, i < arr.val.length → valAt arr2 i = k * valAt arr i) :
      ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
          r = r2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr)
        (k : Int) (hk : k ≠ 0)
        (hk_bounds : ∀ i, i < arr.val.length →
          -1000000 ≤ k * valAt arr i ∧ k * valAt arr i ≤ 1000000)
        (arr2 : Slice Std.I64)
        (hlen2 : arr2.val.length = arr.val.length)
        (h2 : ∀ i, i < arr.val.length → valAt arr2 i = k * valAt arr i), ∀ r r2, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr2 = ok r2 →
            r = r2) := by
    sorry

  /-- For every arr satisfying the preconditions, if there exist values x and y with x != y such that every element arr[i] is equal to either x or y, and both x and y occur among the elements, then whenever can_make_arithmetic_progression(arr) returns a result r, r is false.
    Preconditions: len(arr) >= 3; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen : 3 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr)
      (hxy : ∃ x y : Int, x ≠ y ∧
        (∀ i, i < arr.val.length → valAt arr i = x ∨ valAt arr i = y) ∧
          (∃ i, i < arr.val.length ∧ valAt arr i = x) ∧
            (∃ i, i < arr.val.length ∧ valAt arr i = y)) :
      ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 3 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr)
        (hxy : ∃ x y : Int, x ≠ y ∧
          (∀ i, i < arr.val.length → valAt arr i = x ∨ valAt arr i = y) ∧
            (∃ i, i < arr.val.length ∧ valAt arr i = x) ∧
              (∃ i, i < arr.val.length ∧ valAt arr i = y)), ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          r = false) := by
    sorry

  /-- For every arr satisfying the preconditions, whenever can_make_arithmetic_progression(arr) returns a result r and r is true, either arr[i] = arr[j] for all i and j with 0 <= i,j < len(arr), or arr[i] != arr[j] for all i and j with 0 <= i < j < len(arr).
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_7 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        r = true →
          (∀ i j, i < arr.val.length → j < arr.val.length → valAt arr i = valAt arr j) ∨
            (∀ i j, i < arr.val.length → j < arr.val.length → i < j → valAt arr i ≠ valAt arr j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          r = true →
            (∀ i j, i < arr.val.length → j < arr.val.length → valAt arr i = valAt arr j) ∨
              (∀ i j, i < arr.val.length → j < arr.val.length → i < j → valAt arr i ≠ valAt arr j)) := by
    sorry

  /-- For every arr satisfying the preconditions, whenever can_make_arithmetic_progression(arr) returns a result r and r is true, let m be the minimum of arr[i] over 0 <= i < len(arr) and M be the maximum of arr[i] over 0 <= i < len(arr); then M - m is divisible by len(arr) - 1.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_8 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        r = true →
          ∀ m M : Int, IsMinOf arr m → IsMaxOf arr M →
            ((arr.val.length - 1 : Nat) : Int) ∣ (M - m) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          r = true →
            ∀ m M : Int, IsMinOf arr m → IsMaxOf arr M →
              ((arr.val.length - 1 : Nat) : Int) ∣ (M - m)) := by
    sorry

  /-- For every arr satisfying the preconditions, let s be any sequence of length len(arr) that is a nondecreasing rearrangement of arr. Whenever can_make_arithmetic_progression(arr) returns a result r and r is true, for every i with 0 <= i < len(arr)-1 we have s[i+1] - s[i] = s[1] - s[0].
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_9 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
        r = true →
          ∀ s : List Int, IsNondecreasingRearrangement (vals arr) s →
            ∀ i, i + 1 < arr.val.length →
              listAt s (i + 1) - listAt s i = listAt s 1 - listAt s 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
          r = true →
            ∀ s : List Int, IsNondecreasingRearrangement (vals arr) s →
              ∀ i, i + 1 < arr.val.length →
                listAt s (i + 1) - listAt s i = listAt s 1 - listAt s 0) := by
    sorry

  /-- For every arr satisfying the preconditions, let s be any sequence of length len(arr) that is a nondecreasing rearrangement of arr. If for every i with 0 <= i < len(arr)-1 we have s[i+1] - s[i] = s[1] - s[0], then whenever can_make_arithmetic_progression(arr) returns a result r, r is true.
    Preconditions: len(arr) >= 2; len(arr) <= 1000; and for every i with 0 <= i < len(arr), -1000000 <= arr[i] <= 1000000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
      (hb : WithinLimits arr) :
      ∀ s : List Int, IsNondecreasingRearrangement (vals arr) s →
        (∀ i, i + 1 < arr.val.length →
          listAt s (i + 1) - listAt s i = listAt s 1 - listAt s 0) →
          ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
            r = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen : 2 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 1000)
        (hb : WithinLimits arr), ∀ s : List Int, IsNondecreasingRearrangement (vals arr) s →
          (∀ i, i + 1 < arr.val.length →
            listAt s (i + 1) - listAt s i = listAt s 1 - listAt s 0) →
            ∀ r, Aegis.CanMakeArithmeticProgression.can_make_arithmetic_progression arr = ok r →
              r = true) := by
    sorry

  end AegisSpec.CanMakeArithmeticProgression
