import Aegis.ThreeConsecutiveOdds.Code.Funs

/-!
# Specifications of `Aegis.ThreeConsecutiveOdds.three_consecutive_odds`

LeetCode problem `three-consecutive-odds`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.ThreeConsecutiveOdds

namespace AegisSpec.ThreeConsecutiveOdds

@[reducible] def OddInt (x : Int) : Prop := ¬ (2 ∣ x)

def AllPositive (l : List I64) : Prop := ∀ (i : Nat) (h : i < l.length), 1 ≤ (l[i]'h).val

def TripleOddAt (l : List I64) (i : Nat) (h : i + 2 < l.length) : Prop :=
  OddInt (l[i]'(by omega)).val ∧ OddInt (l[i + 1]'(by omega)).val ∧ OddInt (l[i + 2]'h).val

def HasOddTriple (l : List I64) : Prop :=
  ∃ (i : Nat) (h : i + 2 < l.length), TripleOddAt l i h

def LastTwoOdd (l : List I64) : Prop :=
  ∃ (h : 2 ≤ l.length),
    OddInt (l[l.length - 2]'(by omega)).val ∧ OddInt (l[l.length - 1]'(by omega)).val

def FirstTwoOdd (l : List I64) : Prop :=
  ∃ (h : 2 ≤ l.length), OddInt (l[0]'(by omega)).val ∧ OddInt (l[1]'(by omega)).val

def numOdd (l : List I64) : Nat := l.countP (fun x => decide (OddInt x.val))

/-- The function returns a boolean result r and does not fail. The value r is true if and only if there exists an index i such that 0 <= i, i + 2 < len(arr), and arr[i], arr[i+1], arr[i+2] are all odd. If no such index exists, r is false. An integer x is odd here iff x is not divisible by 2; for the positive inputs considered this is equivalent to x % 2 = 1.
  Preconditions: 1 <= len(arr) <= 1000 and, for every index i with 0 <= i < len(arr), 1 <= arr[i]. The original upper bound arr[i] <= 1000 is not needed for parity and is relaxed here; the provided example [1001,1003,1005] is covered. -/
theorem spec_1 (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val) :
    ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ (r = true ↔ HasOddTriple arr.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val), ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ (r = true ↔ HasOddTriple arr.val)) := by
  sorry

/-- The function returns r and r = true if and only if arr[0], arr[1], and arr[2] are all odd; otherwise r = false. Here odd means not divisible by 2.
  Preconditions: len(arr) = 3 and all elements of arr are positive. -/
theorem spec_2 (arr : Slice I64)
    (hlen : arr.val.length = 3) (hpos : AllPositive arr.val) :
    ∃ (r : Bool), three_consecutive_odds arr = ok r ∧
      (r = true ↔
        OddInt (arr.val[0]'(by omega)).val ∧
        OddInt (arr.val[1]'(by omega)).val ∧
        OddInt (arr.val[2]'(by omega)).val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen : arr.val.length = 3) (hpos : AllPositive arr.val), ∃ (r : Bool), three_consecutive_odds arr = ok r ∧
      (r = true ↔
        OddInt (arr.val[0]'(by omega)).val ∧
        OddInt (arr.val[1]'(by omega)).val ∧
        OddInt (arr.val[2]'(by omega)).val)) := by
  sorry

/-- If there exists an index i with 0 <= i and i + 2 < len(arr) such that arr[i], arr[i+1], and arr[i+2] are all odd, then the function returns r = true.
  Preconditions: 1 <= len(arr) <= 1000, len(arr) >= 3, and all elements of arr are positive. -/
theorem spec_3 (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hlen_three : 3 ≤ arr.val.length) (hpos : AllPositive arr.val)
    (hwitness : HasOddTriple arr.val) :
    ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hlen_three : 3 ≤ arr.val.length) (hpos : AllPositive arr.val)
    (hwitness : HasOddTriple arr.val), ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ r = true) := by
  sorry

/-- If for every index i with 0 <= i and i + 2 < len(arr), at least one of arr[i], arr[i+1], arr[i+2] is even, then the function returns r = false.
  Preconditions: 1 <= len(arr) <= 1000 and all elements of arr are positive. -/
theorem spec_4 (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val)
    (hno_odd_triple : ∀ (i : Nat) (h : i + 2 < arr.val.length),
      ¬ TripleOddAt arr.val i h) :
    ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val)
    (hno_odd_triple : ∀ (i : Nat) (h : i + 2 < arr.val.length),
      ¬ TripleOddAt arr.val i h), ∃ (r : Bool), three_consecutive_odds arr = ok r ∧ r = false) := by
  sorry

/-- If for every index i with 0 <= i < len(arr), arr[i] is odd if and only if brr[i] is odd, then the boolean result returned for arr equals the boolean result returned for brr. Here odd means not divisible by 2.
  Preconditions: 1 <= len(arr) <= 1000, all arr[i] are positive, and brr is any slice with len(brr) = len(arr), 1 <= len(brr) <= 1000, and every brr[i] positive. -/
theorem spec_5 (arr brr : Slice I64)
    (harr_lower : 1 ≤ arr.val.length) (harr_upper : arr.val.length ≤ 1000)
    (harr_pos : AllPositive arr.val)
    (hbrr_len : brr.val.length = arr.val.length)
    (hbrr_lower : 1 ≤ brr.val.length) (hbrr_upper : brr.val.length ≤ 1000)
    (hbrr_pos : AllPositive brr.val)
    (hodd_iff : ∀ (i : Nat) (h : i < arr.val.length),
      (OddInt (arr.val[i]'h).val ↔ OddInt (brr.val[i]'(by omega)).val)) :
    ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ ra = rb := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr brr : Slice I64)
    (harr_lower : 1 ≤ arr.val.length) (harr_upper : arr.val.length ≤ 1000)
    (harr_pos : AllPositive arr.val)
    (hbrr_len : brr.val.length = arr.val.length)
    (hbrr_lower : 1 ≤ brr.val.length) (hbrr_upper : brr.val.length ≤ 1000)
    (hbrr_pos : AllPositive brr.val)
    (hodd_iff : ∀ (i : Nat) (h : i < arr.val.length),
      (OddInt (arr.val[i]'h).val ↔ OddInt (brr.val[i]'(by omega)).val)), ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ ra = rb) := by
  sorry

/-- Let brr be the slice obtained by appending e to arr, so len(brr) = len(arr) + 1, brr[i] = arr[i] for 0 <= i < len(arr), and brr[len(arr)] = e. Then the boolean result returned for brr equals the boolean result returned for arr.
  Preconditions: 1 <= len(arr) <= 999, all arr[i] are positive, and e is a positive even integer. -/
theorem spec_6 (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_even : 2 ∣ e.val)
    (hbrr : brr.val = arr.val ++ [e]) :
    ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ rb = ra := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_even : 2 ∣ e.val)
    (hbrr : brr.val = arr.val ++ [e]), ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ rb = ra) := by
  sorry

/-- Let brr be the slice obtained by prepending e to arr, so len(brr) = len(arr) + 1, brr[0] = e, and brr[i+1] = arr[i] for 0 <= i < len(arr). Then the boolean result returned for brr equals the boolean result returned for arr.
  Preconditions: 1 <= len(arr) <= 999, all arr[i] are positive, and e is a positive even integer. -/
theorem spec_7 (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_even : 2 ∣ e.val)
    (hbrr : brr.val = e :: arr.val) :
    ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ rb = ra := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_even : 2 ∣ e.val)
    (hbrr : brr.val = e :: arr.val), ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧ rb = ra) := by
  sorry

/-- Let brr be the slice obtained by appending e to arr, so len(brr) = len(arr) + 1, brr[i] = arr[i] for 0 <= i < len(arr), and brr[len(arr)] = e. Then the result for brr is true if and only if either (a) the result for arr is true, or (b) len(arr) >= 2 and arr[len(arr)-2] and arr[len(arr)-1] are both odd.
  Preconditions: 1 <= len(arr) <= 999, all arr[i] are positive, and e is a positive odd integer. -/
theorem spec_8 (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_odd : OddInt e.val)
    (hbrr : brr.val = arr.val ++ [e]) :
    ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧
        (rb = true ↔ ra = true ∨ LastTwoOdd arr.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_odd : OddInt e.val)
    (hbrr : brr.val = arr.val ++ [e]), ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧
        (rb = true ↔ ra = true ∨ LastTwoOdd arr.val)) := by
  sorry

/-- Let brr be the slice obtained by prepending e to arr, so len(brr) = len(arr) + 1, brr[0] = e, and brr[i+1] = arr[i] for 0 <= i < len(arr). Then the result for brr is true if and only if either (a) the result for arr is true, or (b) len(arr) >= 2 and arr[0] and arr[1] are both odd.
  Preconditions: 1 <= len(arr) <= 999, all arr[i] are positive, and e is a positive odd integer. -/
theorem spec_9 (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_odd : OddInt e.val)
    (hbrr : brr.val = e :: arr.val) :
    ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧
        (rb = true ↔ ra = true ∨ FirstTwoOdd arr.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr brr : Slice I64) (e : I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 999)
    (hpos : AllPositive arr.val)
    (he_pos : 0 < e.val) (he_odd : OddInt e.val)
    (hbrr : brr.val = e :: arr.val), ∃ (ra rb : Bool),
      three_consecutive_odds arr = ok ra ∧ three_consecutive_odds brr = ok rb ∧
        (rb = true ↔ ra = true ∨ FirstTwoOdd arr.val)) := by
  sorry

/-- If the function returns r = true, then len(arr) >= 3 and the number of indices i with 0 <= i < len(arr) and arr[i] odd is at least 3.
  Preconditions: 1 <= len(arr) <= 1000 and all elements of arr are positive. -/
theorem spec_10 (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val)
    (r : Bool) (hres : three_consecutive_odds arr = ok r) (hr : r = true) :
    3 ≤ arr.val.length ∧ 3 ≤ numOdd arr.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice I64)
    (hlen_lower : 1 ≤ arr.val.length) (hlen_upper : arr.val.length ≤ 1000)
    (hpos : AllPositive arr.val)
    (r : Bool) (hres : three_consecutive_odds arr = ok r) (hr : r = true), 3 ≤ arr.val.length ∧ 3 ≤ numOdd arr.val) := by
  sorry

end AegisSpec.ThreeConsecutiveOdds
