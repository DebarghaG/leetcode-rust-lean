import Aegis.CountDaysTogether.Code.Funs

/-!
# Specifications of `Aegis.CountDaysTogether.count_days_together`

LeetCode problem `count-days-spent-together`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountDaysTogether

open Aegis.CountDaysTogether (count_days_together)

def byteVal (s : Slice Std.U8) (i : Nat) : Option Nat := (s.val[i]?).map (fun b => b.val)

def IsDigitAt (s : Slice Std.U8) (i : Nat) : Prop :=
  ∃ d : Nat, byteVal s i = some d ∧ 48 ≤ d ∧ d ≤ 57

def nonLeapMonthLengths : List Nat := [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]

def daysBeforeMonth (m : Nat) : Nat := (nonLeapMonthLengths.take (m - 1)).sum

def monthLength (m : Nat) : Nat := nonLeapMonthLengths.getD (m - 1) 0

def digitAt (s : Slice Std.U8) (i : Nat) : Nat := (byteVal s i).getD 48 - 48

def monthOf (s : Slice Std.U8) : Nat := 10 * digitAt s 0 + digitAt s 1

def dayOf (s : Slice Std.U8) : Nat := 10 * digitAt s 3 + digitAt s 4

def D (s : Slice Std.U8) : Int := ((daysBeforeMonth (monthOf s) + dayOf s : Nat) : Int)

def ValidDateSlice (s : Slice Std.U8) : Prop :=
  s.val.length = 5 ∧
  byteVal s 2 = some 45 ∧
  IsDigitAt s 0 ∧ IsDigitAt s 1 ∧ IsDigitAt s 3 ∧ IsDigitAt s 4 ∧
  1 ≤ monthOf s ∧ monthOf s ≤ 12 ∧
  1 ≤ dayOf s ∧ dayOf s ≤ monthLength (monthOf s)

def countInInterval (lo hi : Int) : Nat := (hi - lo + 1).toNat

/-- Let sA=D(arriveAlice), eA=D(leaveAlice), sB=D(arriveBob), and eB=D(leaveBob). The function returns a result r, and r equals the number of integers k such that max(sA,sB) <= k <= min(eA,eB). Equivalently, r = max(0, min(eA,eB) - max(sA,sB) + 1).
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_1 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = ((countInInterval (max (D arriveAlice) (D arriveBob))
          (min (D leaveAlice) (D leaveBob)) : Nat) : Int) ∧
      r.val = max 0
        (min (D leaveAlice) (D leaveBob) - max (D arriveAlice) (D arriveBob) + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = ((countInInterval (max (D arriveAlice) (D arriveBob))
          (min (D leaveAlice) (D leaveBob)) : Nat) : Int) ∧
      r.val = max 0
        (min (D leaveAlice) (D leaveBob) - max (D arriveAlice) (D arriveBob) + 1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_2 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64, count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64, count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and 0 <= r.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_3 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and r <= 365.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_4 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ r.val ≤ 365 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ r.val ≤ 365) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and r <= D(leaveAlice) - D(arriveAlice) + 1.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_5 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val ≤ D leaveAlice - D arriveAlice + 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val ≤ D leaveAlice - D arriveAlice + 1) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and r <= D(leaveBob) - D(arriveBob) + 1.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_6 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val ≤ D leaveBob - D arriveBob + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val ≤ D leaveBob - D arriveBob + 1) := by
  sorry

/-- For every input satisfying the preconditions, let r be the result of count_days_together(arriveAlice, leaveAlice, arriveBob, leaveBob) and let r2 be the result of count_days_together(arriveBob, leaveBob, arriveAlice, leaveAlice). Then r = r2.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_7 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveBob leaveBob arriveAlice leaveAlice = ok r2 ∧
      r = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveBob leaveBob arriveAlice leaveAlice = ok r2 ∧
      r = r2) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and r = 0 if and only if D(leaveAlice) < D(arriveBob) or D(leaveBob) < D(arriveAlice).
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_8 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      (r.val = 0 ↔ D leaveAlice < D arriveBob ∨ D leaveBob < D arriveAlice) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      (r.val = 0 ↔ D leaveAlice < D arriveBob ∨ D leaveBob < D arriveAlice)) := by
  sorry

/-- For every input satisfying the preconditions, if D(arriveBob) <= D(arriveAlice) and D(leaveAlice) <= D(leaveBob), then the function returns a result r and r = D(leaveAlice) - D(arriveAlice) + 1.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_9 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_cover_start : D arriveBob ≤ D arriveAlice)
    (h_cover_end : D leaveAlice ≤ D leaveBob) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = D leaveAlice - D arriveAlice + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_cover_start : D arriveBob ≤ D arriveAlice)
    (h_cover_end : D leaveAlice ≤ D leaveBob), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = D leaveAlice - D arriveAlice + 1) := by
  sorry

/-- For every input satisfying the preconditions, if D(arriveAlice) <= D(arriveBob) and D(leaveBob) <= D(leaveAlice), then the function returns a result r and r = D(leaveBob) - D(arriveBob) + 1.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_10 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_cover_start : D arriveAlice ≤ D arriveBob)
    (h_cover_end : D leaveBob ≤ D leaveAlice) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = D leaveBob - D arriveBob + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_cover_start : D arriveAlice ≤ D arriveBob)
    (h_cover_end : D leaveBob ≤ D leaveAlice), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      r.val = D leaveBob - D arriveBob + 1) := by
  sorry

/-- For every input satisfying the preconditions and every valid date slice a2 with D(arriveBob) <= D(a2) <= D(leaveBob), let r be the result of count_days_together(arriveAlice, leaveAlice, arriveBob, leaveBob) and let r2 be the result of count_days_together(arriveAlice, leaveAlice, a2, leaveBob). Then r >= r2.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_11 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (a2 : Slice Std.U8) (h_a2 : ValidDateSlice a2)
    (h_a2_start : D arriveBob ≤ D a2) (h_a2_end : D a2 ≤ D leaveBob) :
    ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveAlice leaveAlice a2 leaveBob = ok r2 ∧
      r ≥ r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (a2 : Slice Std.U8) (h_a2 : ValidDateSlice a2)
    (h_a2_start : D arriveBob ≤ D a2) (h_a2_end : D a2 ≤ D leaveBob), ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveAlice leaveAlice a2 leaveBob = ok r2 ∧
      r ≥ r2) := by
  sorry

/-- For every input satisfying the preconditions and every valid date slice l2 with D(arriveBob) <= D(l2) <= D(leaveBob), let r be the result of count_days_together(arriveAlice, leaveAlice, arriveBob, leaveBob) and let r2 be the result of count_days_together(arriveAlice, leaveAlice, arriveBob, l2). Then r2 <= r.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_12 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (l2 : Slice Std.U8) (h_l2 : ValidDateSlice l2)
    (h_l2_start : D arriveBob ≤ D l2) (h_l2_end : D l2 ≤ D leaveBob) :
    ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveAlice leaveAlice arriveBob l2 = ok r2 ∧
      r2 ≤ r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (l2 : Slice Std.U8) (h_l2 : ValidDateSlice l2)
    (h_l2_start : D arriveBob ≤ D l2) (h_l2_end : D l2 ≤ D leaveBob), ∃ r r2 : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧
      count_days_together arriveAlice leaveAlice arriveBob l2 = ok r2 ∧
      r2 ≤ r) := by
  sorry

/-- For every input satisfying the preconditions, if max(D(arriveAlice),D(arriveBob)) = min(D(leaveAlice),D(leaveBob)), then the function returns a result r and r = 1.
  Preconditions: Define a valid date slice s to be a byte slice with len(s)=5, s[2]=45 (the hyphen byte), and s[0],s[1],s[3],s[4] in 48..57 (ASCII digits); the two-digit month and day encoded by s form a valid date in a non-leap year, with month lengths [31,28,31,30,31,30,31,31,30,31,30,31]. For such s, D(s) is its 1-based day-of-year in that non-leap year (Jan 1 has D=1, Dec 31 has D=365). Precondition: arriveAlice, leaveAlice, arriveBob, and leaveBob are valid date slices, and D(arriveAlice)<=D(leaveAlice), D(arriveBob)<=D(leaveBob). -/
theorem spec_13 (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_single : max (D arriveAlice) (D arriveBob) =
      min (D leaveAlice) (D leaveBob)) :
    ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ r.val = 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arriveAlice leaveAlice arriveBob leaveBob : Slice Std.U8)
    (h_arriveAlice : ValidDateSlice arriveAlice)
    (h_leaveAlice : ValidDateSlice leaveAlice)
    (h_arriveBob : ValidDateSlice arriveBob)
    (h_leaveBob : ValidDateSlice leaveBob)
    (h_orderAlice : D arriveAlice ≤ D leaveAlice)
    (h_orderBob : D arriveBob ≤ D leaveBob)
    (h_single : max (D arriveAlice) (D arriveBob) =
      min (D leaveAlice) (D leaveBob)), ∃ r : Std.I64,
      count_days_together arriveAlice leaveAlice arriveBob leaveBob = ok r ∧ r.val = 1) := by
  sorry

end AegisSpec.CountDaysTogether
