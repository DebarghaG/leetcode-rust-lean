import Aegis.CountTime.Code.Funs

/-!
# Specifications of `Aegis.CountTime.count_time`

LeetCode problem `number-of-valid-clock-times`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountTime

namespace AegisSpec.CountTime

def byteAt (time : Slice U8) (i : Nat) : Option Nat :=
  (time.val[i]?).map (fun b => b.val)

def render (h m : Nat) : List Nat :=
  [48 + h / 10, 48 + h % 10, 58, 48 + m / 10, 48 + m % 10]

def agrees (time : Slice U8) (h m : Nat) : Bool :=
  (List.range 5).all (fun i =>
    (byteAt time i == some 63) || (byteAt time i == some ((render h m).getD i 0)))

def Agrees (time : Slice U8) (h m : Nat) : Prop := agrees time h m = true

def candidates (time : Slice U8) : Finset (Nat × Nat) :=
  ((Finset.range 24).product (Finset.range 60)).filter (fun p => agrees time p.1 p.2 = true)

def hourOK (time : Slice U8) (h : Nat) : Bool :=
  ((byteAt time 0 == some 63) || (byteAt time 0 == some (48 + h / 10))) &&
    ((byteAt time 1 == some 63) || (byteAt time 1 == some (48 + h % 10)))

def minuteOK (time : Slice U8) (m : Nat) : Bool :=
  ((byteAt time 3 == some 63) || (byteAt time 3 == some (48 + m / 10))) &&
    ((byteAt time 4 == some 63) || (byteAt time 4 == some (48 + m % 10)))

def countH (time : Slice U8) : Nat :=
  ((Finset.range 24).filter (fun h => hourOK time h = true)).card

def countM (time : Slice U8) : Nat :=
  ((Finset.range 60).filter (fun m => minuteOK time m = true)).card

def qmarkCount (time : Slice U8) : Nat :=
  (([0, 1, 3, 4] : List Nat).filter (fun i => byteAt time i == some 63)).length

def digitOrQmark (o : Option Nat) : Prop :=
  o = some 63 ∨ ∃ d : Nat, o = some d ∧ 48 ≤ d ∧ d ≤ 57

def patternOK (time : Slice U8) : Prop :=
  time.val.length = 5 ∧
    byteAt time 2 = some 58 ∧
    (∀ i ∈ ([0, 1, 3, 4] : List Nat), digitOrQmark (byteAt time i))

def solvable (time : Slice U8) : Prop :=
  ∃ h m : Nat, h ≤ 23 ∧ m ≤ 59 ∧ agrees time h m = true

/-- Let render(h,m) be the 5-byte sequence [48 + h div 10, 48 + h mod 10, 58, 48 + m div 10, 48 + m mod 10] for 0 <= h <= 23 and 0 <= m <= 59. Let C be the set of pairs (h,m) in that range such that for every i in {0,1,2,3,4}, either time[i] = 63 ('?') or time[i] = render(h,m)[i]. The function returns a result r and r = |C|, the number of elements of C.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_1 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧ r.val = ((candidates time).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧ r.val = ((candidates time).card : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_2 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r) := by
  sorry

/-- The returned value r is an integer satisfying 1 <= r <= 1440.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_3 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧ 1 ≤ r.val ∧ r.val ≤ 1440 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧ 1 ≤ r.val ∧ r.val ≤ 1440) := by
  sorry

/-- Let q be the number of indices i in {0,1,3,4} for which time[i] = 63 ('?'). The returned value r satisfies r <= 10^q.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_4 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧ r.val ≤ (10 : Int) ^ qmarkCount time := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧ r.val ≤ (10 : Int) ^ qmarkCount time) := by
  sorry

/-- The returned value r equals 1 if and only if none of time[0], time[1], time[3], time[4] is 63 ('?').
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_5 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (r.val = 1 ↔ ∀ i ∈ ([0, 1, 3, 4] : List Nat), byteAt time i ≠ some 63) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (r.val = 1 ↔ ∀ i ∈ ([0, 1, 3, 4] : List Nat), byteAt time i ≠ some 63)) := by
  sorry

/-- The returned value r equals 1440 if and only if time[0] = time[1] = time[3] = time[4] = 63 ('?').
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_6 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (r.val = 1440 ↔ ∀ i ∈ ([0, 1, 3, 4] : List Nat), byteAt time i = some 63) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (r.val = 1440 ↔ ∀ i ∈ ([0, 1, 3, 4] : List Nat), byteAt time i = some 63)) := by
  sorry

/-- Let M be the number of m with 0 <= m <= 59 such that (time[3] = 63 or time[3] = 48 + m div 10) and (time[4] = 63 or time[4] = 48 + m mod 10). If time[0] = 63 and time[1] = 63, then the returned value r equals 24 * M.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_7 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 = some 63 → byteAt time 1 = some 63 →
        r.val = 24 * (countM time : Int)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 = some 63 → byteAt time 1 = some 63 →
        r.val = 24 * (countM time : Int))) := by
  sorry

/-- Let H be the number of h with 0 <= h <= 23 such that (time[0] = 63 or time[0] = 48 + h div 10) and (time[1] = 63 or time[1] = 48 + h mod 10). If time[3] = 63 and time[4] = 63, then the returned value r equals 60 * H.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_8 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 = some 63 → byteAt time 4 = some 63 →
        r.val = 60 * (countH time : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 = some 63 → byteAt time 4 = some 63 →
        r.val = 60 * (countH time : Int))) := by
  sorry

/-- Let M be the number of m with 0 <= m <= 59 such that (time[3] = 63 or time[3] = 48 + m div 10) and (time[4] = 63 or time[4] = 48 + m mod 10). If time[0] != 63 and time[1] != 63, then the returned value r equals M.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_9 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 ≠ some 63 → byteAt time 1 ≠ some 63 → r.val = (countM time : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 ≠ some 63 → byteAt time 1 ≠ some 63 → r.val = (countM time : Int))) := by
  sorry

/-- Let H be the number of h with 0 <= h <= 23 such that (time[0] = 63 or time[0] = 48 + h div 10) and (time[1] = 63 or time[1] = 48 + h mod 10). If time[3] != 63 and time[4] != 63, then the returned value r equals H.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_10 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 ≠ some 63 → byteAt time 4 ≠ some 63 → r.val = (countH time : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 ≠ some 63 → byteAt time 4 ≠ some 63 → r.val = (countH time : Int))) := by
  sorry

/-- Let M be the number of m with 0 <= m <= 59 such that (time[3] = 63 or time[3] = 48 + m div 10) and (time[4] = 63 or time[4] = 48 + m mod 10). If time[0] = 63 and time[1] is an ASCII digit d with 48 <= d <= 57, then the returned value r equals H * M, where H = 3 if 48 <= d <= 51, and H = 2 if 52 <= d <= 57.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_11 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 = some 63 →
        ∀ d : Nat, byteAt time 1 = some d → 48 ≤ d → d ≤ 57 →
          r.val = (if d ≤ 51 then (3 : Int) else 2) * (countM time : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 0 = some 63 →
        ∀ d : Nat, byteAt time 1 = some d → 48 ≤ d → d ≤ 57 →
          r.val = (if d ≤ 51 then (3 : Int) else 2) * (countM time : Int))) := by
  sorry

/-- Let M be the number of m with 0 <= m <= 59 such that (time[3] = 63 or time[3] = 48 + m div 10) and (time[4] = 63 or time[4] = 48 + m mod 10). If time[1] = 63 and time[0] is an ASCII digit a (under the preconditions a is 48, 49, or 50), then the returned value r equals H * M, where H = 10 if a is 48 or 49, and H = 4 if a = 50.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_12 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 1 = some 63 →
        ∀ a : Nat, byteAt time 0 = some a → 48 ≤ a → a ≤ 50 →
          r.val = (if a ≤ 49 then (10 : Int) else 4) * (countM time : Int)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 1 = some 63 →
        ∀ a : Nat, byteAt time 0 = some a → 48 ≤ a → a ≤ 50 →
          r.val = (if a ≤ 49 then (10 : Int) else 4) * (countM time : Int))) := by
  sorry

/-- Let H be the number of h with 0 <= h <= 23 such that (time[0] = 63 or time[0] = 48 + h div 10) and (time[1] = 63 or time[1] = 48 + h mod 10). If time[3] = 63 and time[4] is an ASCII digit d with 48 <= d <= 57, then the returned value r equals 6 * H.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_13 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 = some 63 →
        ∀ d : Nat, byteAt time 4 = some d → 48 ≤ d → d ≤ 57 →
          r.val = 6 * (countH time : Int)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 3 = some 63 →
        ∀ d : Nat, byteAt time 4 = some d → 48 ≤ d → d ≤ 57 →
          r.val = 6 * (countH time : Int))) := by
  sorry

/-- Let H be the number of h with 0 <= h <= 23 such that (time[0] = 63 or time[0] = 48 + h div 10) and (time[1] = 63 or time[1] = 48 + h mod 10). If time[4] = 63 and time[3] is an ASCII digit a (under the preconditions a is in 48..53), then the returned value r equals 10 * H.
  Preconditions: time is a 5-byte ASCII string satisfying the problem constraints: len(time) = 5; time[2] = 58 (':'); for each i in {0,1,3,4}, time[i] is either 63 ('?') or an ASCII digit in 48..57; and there exists at least one pair (h,m) with 0 <= h <= 23 and 0 <= m <= 59 whose zero-padded two-digit hh and mm agree with time at every non-'?' byte. -/
theorem spec_14 (time : Slice U8) (hpat : patternOK time) (hsol : solvable time) :
    ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 4 = some 63 →
        ∀ a : Nat, byteAt time 3 = some a → 48 ≤ a → a ≤ 57 →
          r.val = 10 * (countH time : Int)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (time : Slice U8) (hpat : patternOK time) (hsol : solvable time), ∃ r : I64, count_time time = Result.ok r ∧
      (byteAt time 4 = some 63 →
        ∀ a : Nat, byteAt time 3 = some a → 48 ≤ a → a ≤ 57 →
          r.val = 10 * (countH time : Int))) := by
  sorry

/-- Whenever count_time returns r for time and r' for time', we have r' <= r.
  Preconditions: time and time' are two 5-byte ASCII strings both satisfying the problem constraints: len = 5; the third byte is 58 (':'); the other four bytes are each 63 ('?') or ASCII digits in 48..57; and each fixed pattern admits at least one valid clock time. For some j in {0,1,3,4}, time[j] = 63 and time' is obtained from time by replacing only that byte with an ASCII digit d in 48..57; all other bytes are equal. -/
theorem spec_15 (time time' : Slice U8)
    (hpat : patternOK time) (hsol : solvable time)
    (hpat' : patternOK time') (hsol' : solvable time')
    (j : Nat) (hj : j ∈ ([0, 1, 3, 4] : List Nat))
    (hjq : byteAt time j = some 63)
    (d : Nat) (hd : 48 ≤ d) (hd' : d ≤ 57) (hj' : byteAt time' j = some d)
    (hother : ∀ i : Nat, i < 5 → i ≠ j → byteAt time' i = byteAt time i)
    (r r' : I64) (hr : count_time time = Result.ok r) (hr' : count_time time' = Result.ok r') :
    r' ≤ r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (time time' : Slice U8)
    (hpat : patternOK time) (hsol : solvable time)
    (hpat' : patternOK time') (hsol' : solvable time')
    (j : Nat) (hj : j ∈ ([0, 1, 3, 4] : List Nat))
    (hjq : byteAt time j = some 63)
    (d : Nat) (hd : 48 ≤ d) (hd' : d ≤ 57) (hj' : byteAt time' j = some d)
    (hother : ∀ i : Nat, i < 5 → i ≠ j → byteAt time' i = byteAt time i)
    (r r' : I64) (hr : count_time time = Result.ok r) (hr' : count_time time' = Result.ok r'), r' ≤ r) := by
  sorry

end AegisSpec.CountTime
