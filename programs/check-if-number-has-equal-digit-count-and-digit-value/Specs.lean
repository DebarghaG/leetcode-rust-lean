import Aegis.DigitCount.Code.Funs

/-!
# Specifications of `Aegis.DigitCount.digit_count`

LeetCode problem `check-if-number-has-equal-digit-count-and-digit-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DigitCount

open Aegis.DigitCount (digit_count)

def byteAt (l : List Std.U8) (i : Nat) : Nat := (l.getD i 0#u8).val

def countOf (l : List Std.U8) (b : Nat) : Nat := (l.filter (fun x => x.val = b)).length

def occursIn (l : List Std.U8) (b : Nat) : Prop := ∃ x ∈ l, x.val = b

/-- The function returns a result r (it does not fail). For each i with 0 <= i < n, let cnt(i) be the number of indices j with 0 <= j < n and num[j] = 48 + i. Then r = true if and only if for every i with 0 <= i < n, cnt(i) = num[i] - 48.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10 and for every i with 0 <= i < n, 48 <= num[i] <= 57 (each byte is an ASCII decimal digit). -/
theorem spec_1 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔ ∀ i, i < num.val.length →
        countOf num.val (48 + i) = byteAt num.val i - 48) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔ ∀ i, i < num.val.length →
        countOf num.val (48 + i) = byteAt num.val i - 48)) := by
  sorry

/-- The function returns a result r; it does not panic, overflow, or go out of bounds.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10 and for every i with 0 <= i < n, 48 <= num[i] <= 57 (each byte is an ASCII decimal digit). -/
theorem spec_2 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∃ r : Bool, digit_count num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∃ r : Bool, digit_count num = ok r) := by
  sorry

/-- The function returns a result r with r = false.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10, n = 1, and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_3 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 1)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∃ r : Bool, digit_count num = ok r ∧ r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 1)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∃ r : Bool, digit_count num = ok r ∧ r = false) := by
  sorry

/-- The function returns a result r, and r = true if and only if the byte sequence num is exactly [49, 50, 49, 48] (the ASCII codes of "1210") or [50, 48, 50, 48] (the ASCII codes of "2020").
  Preconditions: Let n = len(num). Assume 1 <= n <= 10, n = 4, and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_4 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 4)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔
        num.val = [49#u8, 50#u8, 49#u8, 48#u8] ∨
        num.val = [50#u8, 48#u8, 50#u8, 48#u8]) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 4)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔
        num.val = [49#u8, 50#u8, 49#u8, 48#u8] ∨
        num.val = [50#u8, 48#u8, 50#u8, 48#u8])) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every i with 0 <= i < n, the numeric value num[i] - 48 is at most n.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10 and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_5 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∀ r : Bool, digit_count num = ok r → r = true →
      ∀ i, i < num.val.length → byteAt num.val i - 48 ≤ num.val.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∀ r : Bool, digit_count num = ok r → r = true →
      ∀ i, i < num.val.length → byteAt num.val i - 48 ≤ num.val.length) := by
  sorry

/-- Whenever the function returns a result r with r = true, the sum over i = 0 to n-1 of (num[i] - 48) equals the number of indices j with 0 <= j < n and (num[j] - 48) < n.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10 and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_6 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∀ r : Bool, digit_count num = ok r → r = true →
      (∑ i ∈ Finset.range num.val.length, (byteAt num.val i - 48)) =
        ((List.range num.val.length).filter
          (fun j => byteAt num.val j - 48 < num.val.length)).length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∀ r : Bool, digit_count num = ok r → r = true →
      (∑ i ∈ Finset.range num.val.length, (byteAt num.val i - 48)) =
        ((List.range num.val.length).filter
          (fun j => byteAt num.val j - 48 < num.val.length)).length) := by
  sorry

/-- Whenever the function returns a result r with r = true, for every i with 0 <= i < n, the ASCII character 48+i occurs at least once in num if and only if num[i] != 48.
  Preconditions: Let n = len(num). Assume 1 <= n <= 10 and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_7 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∀ r : Bool, digit_count num = ok r → r = true →
      ∀ i, i < num.val.length → (occursIn num.val (48 + i) ↔ byteAt num.val i ≠ 48) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∀ r : Bool, digit_count num = ok r → r = true →
      ∀ i, i < num.val.length → (occursIn num.val (48 + i) ↔ byteAt num.val i ≠ 48)) := by
  sorry

/-- The function returns a result r with r = true.
  Preconditions: num is the five-byte slice [50, 49, 50, 48, 48] (the ASCII codes of "21200"). -/
theorem spec_8 (num : Slice Std.U8)
    (hnum : num.val = [50#u8, 49#u8, 50#u8, 48#u8, 48#u8]) :
    ∃ r : Bool, digit_count num = ok r ∧ r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hnum : num.val = [50#u8, 49#u8, 50#u8, 48#u8, 48#u8]), ∃ r : Bool, digit_count num = ok r ∧ r = true) := by
  sorry

/-- The function returns a result r, and r = true if and only if the byte sequence num is exactly [54, 50, 49, 48, 48, 48, 49, 48, 48, 48] (the ASCII codes of "6210001000").
  Preconditions: Let n = len(num). Assume 1 <= n <= 10, n = 10, and for every i with 0 <= i < n, 48 <= num[i] <= 57. -/
theorem spec_9 (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57) :
    ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔
        num.val = [54#u8, 50#u8, 49#u8, 48#u8, 48#u8, 48#u8, 49#u8, 48#u8, 48#u8, 48#u8]) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Slice Std.U8)
    (hlen_lo : 1 ≤ num.val.length) (hlen_hi : num.val.length ≤ 10)
    (hlen : num.val.length = 10)
    (hdigits : ∀ i, i < num.val.length → 48 ≤ byteAt num.val i ∧ byteAt num.val i ≤ 57), ∃ r : Bool, digit_count num = ok r ∧
      (r = true ↔
        num.val = [54#u8, 50#u8, 49#u8, 48#u8, 48#u8, 48#u8, 49#u8, 48#u8, 48#u8, 48#u8])) := by
  sorry

end AegisSpec.DigitCount
