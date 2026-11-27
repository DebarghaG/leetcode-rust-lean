import Aegis.NumberOfDays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfDays.number_of_days`

LeetCode problem `number-of-days-in-a-month`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfDays

open Aegis.NumberOfDays

def IsLeapYear (year : ℤ) : Prop :=
  year % 400 = 0 ∨ (year % 4 = 0 ∧ year % 100 ≠ 0)

def IsMonthOf31 (month : ℤ) : Prop :=
  month = 1 ∨ month = 3 ∨ month = 5 ∨ month = 7 ∨ month = 8 ∨ month = 10 ∨ month = 12

def IsMonthOf30 (month : ℤ) : Prop :=
  month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11

instance instDecidableIsLeapYear (year : ℤ) : Decidable (IsLeapYear year) := by
  unfold IsLeapYear; infer_instance

instance instDecidableIsMonthOf31 (month : ℤ) : Decidable (IsMonthOf31 month) := by
  unfold IsMonthOf31; infer_instance

instance instDecidableIsMonthOf30 (month : ℤ) : Decidable (IsMonthOf30 month) := by
  unfold IsMonthOf30; infer_instance

def days (year month : ℤ) : ℤ :=
  if month = 2 then
    if IsLeapYear year then 29 else 28
  else if IsMonthOf30 month then 30
  else 31

/-- The function returns a result r and r = days(year, month), where days(y, m) is defined as follows. If m is 1, 3, 5, 7, 8, 10, or 12, then days(y, m) = 31. If m is 4, 6, 9, or 11, then days(y, m) = 30. If m = 2, then days(y, m) = 29 when y is divisible by 400, or when y is divisible by 4 and not divisible by 100; otherwise days(y, m) = 28.
  Preconditions: 1583 <= year <= 2100 and 1 <= month <= 12. Month numbers are 1-based, so month = 2 means February. -/
theorem spec_1 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = days year.val month.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12), ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = days year.val month.val) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, or panic for any input satisfying the preconditions.
  Preconditions: 1583 <= year <= 2100 and 1 <= month <= 12. -/
theorem spec_2 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) :
    ∃ r : Std.I64, number_of_days year month = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12), ∃ r : Std.I64, number_of_days year month = ok r) := by
  sorry

/-- The function returns a result r and 28 <= r <= 31.
  Preconditions: 1583 <= year <= 2100 and 1 <= month <= 12. -/
theorem spec_3 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ 28 ≤ r.val ∧ r.val ≤ 31 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12), ∃ r : Std.I64, number_of_days year month = ok r ∧ 28 ≤ r.val ∧ r.val ≤ 31) := by
  sorry

/-- The function returns a result r and r = 29.
  Preconditions: 1583 <= year <= 2100, year is divisible by 400, and month = 2. -/
theorem spec_4 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hy_400 : year.val % 400 = 0) (hm : month.val = 2) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 29 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hy_400 : year.val % 400 = 0) (hm : month.val = 2), ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 29) := by
  sorry

/-- The function returns a result r and r = 28.
  Preconditions: 1583 <= year <= 2100, year is divisible by 100, year is not divisible by 400, and month = 2. -/
theorem spec_5 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hy_100 : year.val % 100 = 0) (hy_400 : year.val % 400 ≠ 0) (hm : month.val = 2) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 28 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hy_100 : year.val % 100 = 0) (hy_400 : year.val % 400 ≠ 0) (hm : month.val = 2), ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 28) := by
  sorry

/-- The function returns a result r and r = 31.
  Preconditions: 1583 <= year <= 2100 and month is one of 1, 3, 5, 7, 8, 10, or 12 (January, March, May, July, August, October, December). -/
theorem spec_6 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm : IsMonthOf31 month.val) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 31 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm : IsMonthOf31 month.val), ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 31) := by
  sorry

/-- The function returns a result r and r = 30.
  Preconditions: 1583 <= year <= 2100 and month is one of 4, 6, 9, or 11 (April, June, September, November). -/
theorem spec_7 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm : IsMonthOf30 month.val) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 30 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm : IsMonthOf30 month.val), ∃ r : Std.I64, number_of_days year month = ok r ∧ r.val = 30) := by
  sorry

/-- If the function returns r1 for (year1, month) and returns r2 for (year2, month), then r1 = r2.
  Preconditions: 1583 <= year1 <= 2100, 1583 <= year2 <= 2100, 1 <= month <= 12, and month is not 2 (so month is one of 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, or 12). -/
theorem spec_8 (year1 year2 month : Std.I64)
    (hy1_low : 1583 ≤ year1.val) (hy1_high : year1.val ≤ 2100)
    (hy2_low : 1583 ≤ year2.val) (hy2_high : year2.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) (hm_ne : month.val ≠ 2) :
    ∀ r1 r2 : Std.I64,
      number_of_days year1 month = ok r1 → number_of_days year2 month = ok r2 → r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (year1 year2 month : Std.I64)
    (hy1_low : 1583 ≤ year1.val) (hy1_high : year1.val ≤ 2100)
    (hy2_low : 1583 ≤ year2.val) (hy2_high : year2.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) (hm_ne : month.val ≠ 2), ∀ r1 r2 : Std.I64,
      number_of_days year1 month = ok r1 → number_of_days year2 month = ok r2 → r1 = r2) := by
  sorry

/-- If the function returns r1 for (year1, 2) and returns r2 for (year2, 2), then r1 = r2.
  Preconditions: 1583 <= year1 <= 2100, 1583 <= year2 <= 2100, month1 = 2, month2 = 2, and year1 and year2 have the same leap status, where a year y is leap exactly when y is divisible by 400, or y is divisible by 4 and not divisible by 100. -/
theorem spec_9 (year1 year2 month1 month2 : Std.I64)
    (hy1_low : 1583 ≤ year1.val) (hy1_high : year1.val ≤ 2100)
    (hy2_low : 1583 ≤ year2.val) (hy2_high : year2.val ≤ 2100)
    (hm1 : month1.val = 2) (hm2 : month2.val = 2)
    (hleap : IsLeapYear year1.val ↔ IsLeapYear year2.val) :
    ∀ r1 r2 : Std.I64,
      number_of_days year1 month1 = ok r1 → number_of_days year2 month2 = ok r2 → r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (year1 year2 month1 month2 : Std.I64)
    (hy1_low : 1583 ≤ year1.val) (hy1_high : year1.val ≤ 2100)
    (hy2_low : 1583 ≤ year2.val) (hy2_high : year2.val ≤ 2100)
    (hm1 : month1.val = 2) (hm2 : month2.val = 2)
    (hleap : IsLeapYear year1.val ↔ IsLeapYear year2.val), ∀ r1 r2 : Std.I64,
      number_of_days year1 month1 = ok r1 → number_of_days year2 month2 = ok r2 → r1 = r2) := by
  sorry

/-- The function returns a result r and r is either 28 or 29.
  Preconditions: 1583 <= year <= 2100 and month = 2. -/
theorem spec_10 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100) (hm : month.val = 2) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ (r.val = 28 ∨ r.val = 29) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100) (hm : month.val = 2), ∃ r : Std.I64, number_of_days year month = ok r ∧ (r.val = 28 ∨ r.val = 29)) := by
  sorry

/-- The function returns a result r and r is either 30 or 31.
  Preconditions: 1583 <= year <= 2100 and 1 <= month <= 12 and month is not 2. -/
theorem spec_11 (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) (hm_ne : month.val ≠ 2) :
    ∃ r : Std.I64, number_of_days year month = ok r ∧ (r.val = 30 ∨ r.val = 31) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (year month : Std.I64)
    (hy_low : 1583 ≤ year.val) (hy_high : year.val ≤ 2100)
    (hm_low : 1 ≤ month.val) (hm_high : month.val ≤ 12) (hm_ne : month.val ≠ 2), ∃ r : Std.I64, number_of_days year month = ok r ∧ (r.val = 30 ∨ r.val = 31)) := by
  sorry

/-- Each possible day count occurs: the function returns 28 for (1900, 2), 29 for (2000, 2), 30 for (2020, 4), and 31 for (2023, 12).
  Preconditions: Only inputs with 1583 <= year <= 2100 and 1 <= month <= 12 are considered. -/
theorem spec_12 :
    (∃ r : Std.I64, number_of_days 1900#i64 2#i64 = ok r ∧ r.val = 28) ∧
    (∃ r : Std.I64, number_of_days 2000#i64 2#i64 = ok r ∧ r.val = 29) ∧
    (∃ r : Std.I64, number_of_days 2020#i64 4#i64 = ok r ∧ r.val = 30) ∧
    (∃ r : Std.I64, number_of_days 2023#i64 12#i64 = ok r ∧ r.val = 31) := by
  sorry

theorem spec_12_neg :
    ¬ ((∃ r : Std.I64, number_of_days 1900#i64 2#i64 = ok r ∧ r.val = 28) ∧
    (∃ r : Std.I64, number_of_days 2000#i64 2#i64 = ok r ∧ r.val = 29) ∧
    (∃ r : Std.I64, number_of_days 2020#i64 4#i64 = ok r ∧ r.val = 30) ∧
    (∃ r : Std.I64, number_of_days 2023#i64 12#i64 = ok r ∧ r.val = 31)) := by
  sorry

end AegisSpec.NumberOfDays
