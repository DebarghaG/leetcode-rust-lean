import Aegis.DaysBetweenDates.Code.Funs

/-!
# Specifications of `Aegis.DaysBetweenDates.days_between_dates`

LeetCode problem `number-of-days-between-two-dates`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.DaysBetweenDates

namespace AegisSpec.DaysBetweenDates

def IsLeapYear (y : ℕ) : Prop :=
  y % 4 = 0 ∧ (y % 100 ≠ 0 ∨ y % 400 = 0)

instance instDecidableIsLeapYear (y : ℕ) : Decidable (IsLeapYear y) := by
  unfold IsLeapYear
  infer_instance

def daysInYear (y : ℕ) : ℕ :=
  if IsLeapYear y then 366 else 365

def daysInMonth (y m : ℕ) : ℕ :=
  if m = 1 ∨ m = 3 ∨ m = 5 ∨ m = 7 ∨ m = 8 ∨ m = 10 ∨ m = 12 then 31
  else if m = 4 ∨ m = 6 ∨ m = 9 ∨ m = 11 then 30
  else if m = 2 then if IsLeapYear y then 29 else 28
  else 0

def ord (y m d : ℕ) : ℤ :=
  Finset.sum (Finset.range (y - 1970)) (fun i => (daysInYear (1970 + i) : ℤ)) +
    Finset.sum (Finset.range (m - 1)) (fun i => (daysInMonth y (i + 1) : ℤ)) +
    ((d : ℤ) - 1)

def succDate (y m d : ℕ) : ℕ × ℕ × ℕ :=
  if d < daysInMonth y m then (y, m, d + 1)
  else if m < 12 then (y, m + 1, 1)
  else (y + 1, 1, 1)

def iabs (z : ℤ) : ℕ :=
  z.natAbs

def byte (n : ℕ) : Std.U8 :=
  ⟨BitVec.ofNat 8 n⟩

def asciiBytes (s : String) : List Std.U8 :=
  s.toList.map (fun c => byte c.toNat)

def digit? (b : Std.U8) : Option ℕ :=
  if 48 ≤ b.val ∧ b.val ≤ 57 then some (b.val - 48) else none

def twoDigits (b0 b1 : Std.U8) : Option ℕ :=
  match digit? b0, digit? b1 with
  | some x, some y => some (10 * x + y)
  | _, _ => none

def fourDigits (b0 b1 b2 b3 : Std.U8) : Option ℕ :=
  match digit? b0, digit? b1, digit? b2, digit? b3 with
  | some a, some b, some c, some d => some (1000 * a + 100 * b + 10 * c + d)
  | _, _, _, _ => none

def parseDate (s : List Std.U8) : Option (ℕ × ℕ × ℕ) :=
  match s with
  | [b0, b1, b2, b3, dash1, b5, b6, dash2, b8, b9] =>
      if dash1.val = 45 ∧ dash2.val = 45 then
        match fourDigits b0 b1 b2 b3, twoDigits b5 b6, twoDigits b8 b9 with
        | some y, some m, some d => some (y, m, d)
        | _, _, _ => none
      else none
  | _ => none

def IsValidDate (y m d : ℕ) : Prop :=
  1971 ≤ y ∧ y ≤ 2100 ∧ 1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth y m

instance instDecidableIsValidDate (y m d : ℕ) : Decidable (IsValidDate y m d) := by
  unfold IsValidDate
  infer_instance

def EncodesDate (s : Slice Std.U8) (y m d : ℕ) : Prop :=
  parseDate s.val = some (y, m, d) ∧ IsValidDate y m d

def DateLE (y1 m1 d1 y2 m2 d2 : ℕ) : Prop :=
  y1 < y2 ∨ (y1 = y2 ∧ (m1 < m2 ∨ (m1 = m2 ∧ d1 ≤ d2)))

instance instDecidableDateLE (y1 m1 d1 y2 m2 d2 : ℕ) : Decidable (DateLE y1 m1 d1 y2 m2 d2) := by
  unfold DateLE
  infer_instance

/-- Whenever days_between_dates(date1, date2) returns a result r, r = |ord(Y2, M2, D2) - ord(Y1, M1, D1)|, where ord(y,m,d) is the ordinal day number of the date (y,m,d) in the proleptic Gregorian calendar, defined by ord(1970,1,1) = 0 and ord increasing by exactly 1 when moving to the next calendar day.
  Preconditions: Both date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives dates (Y1, M1, D1) and (Y2, M2, D2) that are valid proleptic Gregorian calendar dates with years in [1971, 2100]: 1 <= M <= 12, 1 <= D <= days_in_month(Y, M), where days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m = 2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_1 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2) :
    ∀ r : Std.I64,
      days_between_dates date1 date2 = ok r →
        r.val = ((iabs (ord Y2 M2 D2 - ord Y1 M1 D1) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2), ∀ r : Std.I64,
      days_between_dates date1 date2 = ok r →
        r.val = ((iabs (ord Y2 M2 D2 - ord Y1 M1 D1) : ℕ) : ℤ)) := by
  sorry

/-- For every date1 and date2 satisfying the preconditions, days_between_dates(date1, date2) returns a result r (it does not fail, panic, or overflow).
  Preconditions: Both date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives dates (Y1, M1, D1) and (Y2, M2, D2) that are valid proleptic Gregorian calendar dates with years in [1971, 2100]: 1 <= M <= 12, 1 <= D <= days_in_month(Y, M), where days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m = 2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_2 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2) :
    ∃ r : Std.I64, days_between_dates date1 date2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2), ∃ r : Std.I64, days_between_dates date1 date2 = ok r) := by
  sorry

/-- Whenever days_between_dates(date1, date2) returns a result r, r <= 47481, which equals the number of days from 1971-01-01 to 2100-12-31.
  Preconditions: Both date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives dates (Y1, M1, D1) and (Y2, M2, D2) that are valid proleptic Gregorian calendar dates with years in [1971, 2100]: 1 <= M <= 12, 1 <= D <= days_in_month(Y, M), where days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m = 2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_3 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2) :
    ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val ≤ 47481 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2), ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val ≤ 47481) := by
  sorry

/-- Whenever days_between_dates(date1, date2) returns a result r, r = 0 if and only if (Y1, M1, D1) = (Y2, M2, D2), i.e., the two strings encode the same calendar date.
  Preconditions: Both date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives dates (Y1, M1, D1) and (Y2, M2, D2) that are valid proleptic Gregorian calendar dates with years in [1971, 2100]: 1 <= M <= 12, 1 <= D <= days_in_month(Y, M), where days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m = 2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_4 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2) :
    ∀ r : Std.I64,
      days_between_dates date1 date2 = ok r → (r.val = 0 ↔ (Y1 = Y2 ∧ M1 = M2 ∧ D1 = D2)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2), ∀ r : Std.I64,
      days_between_dates date1 date2 = ok r → (r.val = 0 ↔ (Y1 = Y2 ∧ M1 = M2 ∧ D1 = D2))) := by
  sorry

/-- For any valid date strings date1 and date2 satisfying the preconditions, if days_between_dates(date1, date2) returns r and days_between_dates(date2, date1) returns r', then r = r'.
  Preconditions: Both date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives dates (Y1, M1, D1) and (Y2, M2, D2) that are valid proleptic Gregorian calendar dates with years in [1971, 2100]: 1 <= M <= 12, 1 <= D <= days_in_month(Y, M), where days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m = 2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_5 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2) :
    ∀ r r' : Std.I64,
      days_between_dates date1 date2 = ok r →
        days_between_dates date2 date1 = ok r' → r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2), ∀ r r' : Std.I64,
      days_between_dates date1 date2 = ok r →
        days_between_dates date2 date1 = ok r' → r.val = r'.val) := by
  sorry

/-- If (Y1,M1,D1) <= (Y2,M2,D2) <= (Y3,M3,D3) in chronological order (compare years, then months, then days), and if r12 = days_between_dates(date1, date2), r23 = days_between_dates(date2, date3), and r13 = days_between_dates(date1, date3) are all returned, then r13 = r12 + r23.
  Preconditions: Each of date1, date2, date3 is a byte array of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives valid proleptic Gregorian calendar dates (Y1,M1,D1), (Y2,M2,D2), (Y3,M3,D3) with years in [1971,2100], where a date (Y,M,D) is valid iff 1 <= M <= 12, 1 <= D <= days_in_month(Y,M), with days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m=2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_6 (date1 date2 date3 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 Y3 M3 D3 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (h3 : EncodesDate date3 Y3 M3 D3)
    (hord : DateLE Y1 M1 D1 Y2 M2 D2 ∧ DateLE Y2 M2 D2 Y3 M3 D3) :
    ∀ r12 r23 r13 : Std.I64,
      days_between_dates date1 date2 = ok r12 →
        days_between_dates date2 date3 = ok r23 →
          days_between_dates date1 date3 = ok r13 → r13.val = r12.val + r23.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (date1 date2 date3 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 Y3 M3 D3 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (h3 : EncodesDate date3 Y3 M3 D3)
    (hord : DateLE Y1 M1 D1 Y2 M2 D2 ∧ DateLE Y2 M2 D2 Y3 M3 D3), ∀ r12 r23 r13 : Std.I64,
      days_between_dates date1 date2 = ok r12 →
        days_between_dates date2 date3 = ok r23 →
          days_between_dates date1 date3 = ok r13 → r13.val = r12.val + r23.val) := by
  sorry

/-- If (Y1,M1,D1) <= (Y2,M2,D2) <= (Y3,M3,D3) in chronological order, and if r12 = days_between_dates(date1, date2) and r13 = days_between_dates(date1, date3) are returned, then r12 <= r13.
  Preconditions: Each of date1, date2, date3 is a byte array of length 10 in the format YYYY-MM-DD: positions 4 and 7 are the ASCII character '-' (45), and the remaining eight positions are ASCII digits (48..57). Parsing the digit fields as decimal numbers gives valid proleptic Gregorian calendar dates (Y1,M1,D1), (Y2,M2,D2), (Y3,M3,D3) with years in [1971,2100], where a date (Y,M,D) is valid iff 1 <= M <= 12, 1 <= D <= days_in_month(Y,M), with days_in_month(y,m) = 31 for m in {1,3,5,7,8,10,12}, 30 for m in {4,6,9,11}, and for m=2 it is 29 when y is a leap year (y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)) and 28 otherwise. -/
theorem spec_7 (date1 date2 date3 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 Y3 M3 D3 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (h3 : EncodesDate date3 Y3 M3 D3)
    (hord : DateLE Y1 M1 D1 Y2 M2 D2 ∧ DateLE Y2 M2 D2 Y3 M3 D3) :
    ∀ r12 r13 : Std.I64,
      days_between_dates date1 date2 = ok r12 →
        days_between_dates date1 date3 = ok r13 → r12.val ≤ r13.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (date1 date2 date3 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 Y3 M3 D3 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (h3 : EncodesDate date3 Y3 M3 D3)
    (hord : DateLE Y1 M1 D1 Y2 M2 D2 ∧ DateLE Y2 M2 D2 Y3 M3 D3), ∀ r12 r13 : Std.I64,
      days_between_dates date1 date2 = ok r12 →
        days_between_dates date1 date3 = ok r13 → r12.val ≤ r13.val) := by
  sorry

/-- Whenever days_between_dates(date1, date2) returns a result r, r = 1.
  Preconditions: date1 and date2 are byte arrays of length 10 in the format YYYY-MM-DD (positions 4 and 7 are '-', the rest are ASCII digits) encoding valid proleptic Gregorian dates with years in [1971,2100] (1 <= M <= 12, 1 <= D <= days_in_month(Y,M), with the leap-year rule y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0)); additionally, the date encoded by date2 is the calendar day immediately following the date encoded by date1. -/
theorem spec_8 (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (hnext : (Y2, M2, D2) = succDate Y1 M1 D1) :
    ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8) (Y1 M1 D1 Y2 M2 D2 : ℕ)
    (h1 : EncodesDate date1 Y1 M1 D1) (h2 : EncodesDate date2 Y2 M2 D2)
    (hnext : (Y2, M2, D2) = succDate Y1 M1 D1), ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 1) := by
  sorry

/-- Whenever days_between_dates(date1, date2) returns a result r, r = 2.
  Preconditions: date1 is the 10-byte ASCII string "2020-02-28" and date2 is the 10-byte ASCII string "2020-03-01". -/
theorem spec_9 (date1 date2 : Slice Std.U8)
    (h1 : date1.val = asciiBytes "2020-02-28") (h2 : date2.val = asciiBytes "2020-03-01") :
    ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8)
    (h1 : date1.val = asciiBytes "2020-02-28") (h2 : date2.val = asciiBytes "2020-03-01"), ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 2) := by
  sorry

/-- Whenever days_between_dates(date1, date2) returns a result r, r = 15.
  Preconditions: date1 is the 10-byte ASCII string "2020-01-15" and date2 is the 10-byte ASCII string "2019-12-31". -/
theorem spec_10 (date1 date2 : Slice Std.U8)
    (h1 : date1.val = asciiBytes "2020-01-15") (h2 : date2.val = asciiBytes "2019-12-31") :
    ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 15 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (date1 date2 : Slice Std.U8)
    (h1 : date1.val = asciiBytes "2020-01-15") (h2 : date2.val = asciiBytes "2019-12-31"), ∀ r : Std.I64, days_between_dates date1 date2 = ok r → r.val = 15) := by
  sorry

end AegisSpec.DaysBetweenDates
