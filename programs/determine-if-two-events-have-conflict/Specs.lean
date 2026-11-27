import Aegis.HaveConflict.Code.Funs

/-!
# Specifications of `Aegis.HaveConflict.have_conflict`

LeetCode problem `determine-if-two-events-have-conflict`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result
open Aegis.HaveConflict

namespace AegisSpec.HaveConflict

def evStr (e : Slice (alloc.vec.Vec U8)) (i : Nat) : List U8 :=
  ((e.val[i]?).map (fun v => v.val)).getD []

def digit (x : List U8) (i : Nat) : Int :=
  ((x.getD i (default : U8)).val : Int) - 48

def hour (x : List U8) : Int := 10 * digit x 0 + digit x 1

def minute (x : List U8) : Int := 10 * digit x 3 + digit x 4

def mins (x : List U8) : Int := 60 * hour x + minute x

def IsAsciiDigit (c : U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def HasDigitAt (x : List U8) (i : Nat) : Prop := ∃ c, x[i]? = some c ∧ IsAsciiDigit c

def HasColonAt (x : List U8) (i : Nat) : Prop := x[i]? = some 58#u8

def ValidTimeStr (x : List U8) : Prop :=
  x.length = 5 ∧
  HasColonAt x 2 ∧
  HasDigitAt x 0 ∧
  HasDigitAt x 1 ∧
  HasDigitAt x 3 ∧
  HasDigitAt x 4 ∧
  0 ≤ hour x ∧ hour x ≤ 23 ∧
  0 ≤ minute x ∧ minute x ≤ 59

/-- The function returns a result r and r = true if and only if s1 <= e2 and s2 <= e1; equivalently, the inclusive minute intervals [s1,e1] and [s2,e2] have a non-empty intersection.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_1 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∃ r, have_conflict event1 event2 = ok r ∧
      (r = true ↔
        mins (evStr event1 0) ≤ mins (evStr event2 1) ∧
        mins (evStr event2 0) ≤ mins (evStr event1 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∃ r, have_conflict event1 event2 = ok r ∧
      (r = true ↔
        mins (evStr event1 0) ≤ mins (evStr event2 1) ∧
        mins (evStr event2 0) ≤ mins (evStr event1 1))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_2 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∃ r, have_conflict event1 event2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∃ r, have_conflict event1 event2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r = true then there exists an integer m such that 0 <= m <= 1439, s1 <= m <= e1, and s2 <= m <= e2.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_3 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∀ r, have_conflict event1 event2 = ok r → r = true →
      ∃ m : Int, 0 ≤ m ∧ m ≤ 1439 ∧
        mins (evStr event1 0) ≤ m ∧ m ≤ mins (evStr event1 1) ∧
        mins (evStr event2 0) ≤ m ∧ m ≤ mins (evStr event2 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∀ r, have_conflict event1 event2 = ok r → r = true →
      ∃ m : Int, 0 ≤ m ∧ m ≤ 1439 ∧
        mins (evStr event1 0) ≤ m ∧ m ≤ mins (evStr event1 1) ∧
        mins (evStr event2 0) ≤ m ∧ m ≤ mins (evStr event2 1)) := by
  sorry

/-- Whenever the function returns a result r, if r = false then e1 < s2 or e2 < s1.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_4 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∀ r, have_conflict event1 event2 = ok r → r = false →
      mins (evStr event1 1) < mins (evStr event2 0) ∨
      mins (evStr event2 1) < mins (evStr event1 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∀ r, have_conflict event1 event2 = ok r → r = false →
      mins (evStr event1 1) < mins (evStr event2 0) ∨
      mins (evStr event2 1) < mins (evStr event1 0)) := by
  sorry

/-- Whenever the function returns a result r on (event1,event2) and also returns a result r' on the swapped arguments (event2,event1), we have r = r'.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_5 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∀ r r', have_conflict event1 event2 = ok r →
      have_conflict event2 event1 = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∀ r r', have_conflict event1 event2 = ok r →
      have_conflict event2 event1 = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, if r = true then max(s1,s2) <= min(e1,e2), and for every integer m with max(s1,s2) <= m <= min(e1,e2), we have s1 <= m <= e1 and s2 <= m <= e2; moreover, 0 <= max(s1,s2) and min(e1,e2) <= 1439.
  Preconditions: Assume event1 and event2 have length 2. Define digit(x,i)=x[i]-48 and mins(x)=60*(10*digit(x,0)+digit(x,1))+(10*digit(x,3)+digit(x,4)); set s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). Assume each of the four strings has length 5, has the ASCII colon (58) at index 2, has ASCII digits ('0'..'9') at indices 0,1,3,4, has hour in 0..23 and minute in 0..59, and satisfies s1 <= e1 and s2 <= e2. -/
theorem spec_6 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∀ r, have_conflict event1 event2 = ok r → r = true →
      max (mins (evStr event1 0)) (mins (evStr event2 0)) ≤
        min (mins (evStr event1 1)) (mins (evStr event2 1)) ∧
      (∀ m : Int,
        max (mins (evStr event1 0)) (mins (evStr event2 0)) ≤ m →
        m ≤ min (mins (evStr event1 1)) (mins (evStr event2 1)) →
        mins (evStr event1 0) ≤ m ∧ m ≤ mins (evStr event1 1) ∧
        mins (evStr event2 0) ≤ m ∧ m ≤ mins (evStr event2 1)) ∧
      0 ≤ max (mins (evStr event1 0)) (mins (evStr event2 0)) ∧
      min (mins (evStr event1 1)) (mins (evStr event2 1)) ≤ 1439 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∀ r, have_conflict event1 event2 = ok r → r = true →
      max (mins (evStr event1 0)) (mins (evStr event2 0)) ≤
        min (mins (evStr event1 1)) (mins (evStr event2 1)) ∧
      (∀ m : Int,
        max (mins (evStr event1 0)) (mins (evStr event2 0)) ≤ m →
        m ≤ min (mins (evStr event1 1)) (mins (evStr event2 1)) →
        mins (evStr event1 0) ≤ m ∧ m ≤ mins (evStr event1 1) ∧
        mins (evStr event2 0) ≤ m ∧ m ≤ mins (evStr event2 1)) ∧
      0 ≤ max (mins (evStr event1 0)) (mins (evStr event2 0)) ∧
      min (mins (evStr event1 1)) (mins (evStr event2 1)) ≤ 1439) := by
  sorry

/-- Whenever the function returns a result r, r = false if and only if e1 < s2 or e2 < s1 (the inclusive intervals are disjoint).
  Preconditions: Assume event1 and event2 have length 2; each of the four strings has length 5, ASCII colon at index 2, ASCII digits at indices 0,1,3,4, hour in 0..23, minute in 0..59; and s1<=e1, s2<=e2, where s1=mins(event1[0]), e1=mins(event1[1]), s2=mins(event2[0]), e2=mins(event2[1]). -/
theorem spec_7 (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)) :
    ∀ r, have_conflict event1 event2 = ok r →
      (r = false ↔
        mins (evStr event1 1) < mins (evStr event2 0) ∨
        mins (evStr event2 1) < mins (evStr event1 0)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (event1 event2 : Slice (alloc.vec.Vec U8))
    (h1 : event1.val.length = 2) (h2 : event2.val.length = 2)
    (hs1 : ValidTimeStr (evStr event1 0))
    (he1 : ValidTimeStr (evStr event1 1))
    (hs2 : ValidTimeStr (evStr event2 0))
    (he2 : ValidTimeStr (evStr event2 1))
    (hord1 : mins (evStr event1 0) ≤ mins (evStr event1 1))
    (hord2 : mins (evStr event2 0) ≤ mins (evStr event2 1)), ∀ r, have_conflict event1 event2 = ok r →
      (r = false ↔
        mins (evStr event1 1) < mins (evStr event2 0) ∨
        mins (evStr event2 1) < mins (evStr event1 0))) := by
  sorry

end AegisSpec.HaveConflict
