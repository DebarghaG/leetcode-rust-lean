import Aegis.IsRectangleOverlap.Code.Funs

/-!
# Specifications of `Aegis.IsRectangleOverlap.is_rectangle_overlap`

LeetCode problem `rectangle-overlap`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsRectangleOverlap

namespace AegisSpec.IsRectangleOverlap

def coord (r : Slice I64) (i : Nat) : Int :=
  match r.val[i]? with
  | some x => x.val
  | none => 0

def RectOk (r : Slice I64) : Prop :=
  r.val.length = 4 ∧
    ∀ i : Nat, i < 4 → -1000000000 ≤ coord r i ∧ coord r i ≤ 1000000000

def RectValid (r : Slice I64) : Prop :=
  RectOk r ∧ coord r 0 < coord r 2 ∧ coord r 1 < coord r 3

/-- Whenever `is_rectangle_overlap rec1 rec2` returns a result r, r is true if and only if `rec1[0] < rec2[2]` and `rec2[0] < rec1[2]` and `rec1[1] < rec2[3]` and `rec2[1] < rec1[3]`. Equivalently, r is true if and only if the open x-interval `(rec1[0], rec1[2])` overlaps `(rec2[0], rec2[2])` with positive length and the open y-interval `(rec1[1], rec1[3])` overlaps `(rec2[1], rec2[3])` with positive length; touching only at an edge or corner gives r = false.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_1 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r →
      (r = true ↔
        (coord rec1 0 < coord rec2 2 ∧ coord rec2 0 < coord rec1 2 ∧
          coord rec1 1 < coord rec2 3 ∧ coord rec2 1 < coord rec1 3)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2), ∀ r, is_rectangle_overlap rec1 rec2 = ok r →
      (r = true ↔
        (coord rec1 0 < coord rec2 2 ∧ coord rec2 0 < coord rec1 2 ∧
          coord rec1 1 < coord rec2 3 ∧ coord rec2 1 < coord rec1 3))) := by
  sorry

/-- The call `is_rectangle_overlap rec1 rec2` returns a result (a Bool); it does not fail, panic, or go out of bounds.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_2 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2) :
    ∃ r : Bool, is_rectangle_overlap rec1 rec2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2), ∃ r : Bool, is_rectangle_overlap rec1 rec2 = ok r) := by
  sorry

/-- Let r12 be the result of `is_rectangle_overlap rec1 rec2` and r21 be the result of `is_rectangle_overlap rec2 rec1`. Whenever both calls return results, r12 = r21.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_3 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2) :
    ∀ r12 r21, is_rectangle_overlap rec1 rec2 = ok r12 →
      is_rectangle_overlap rec2 rec1 = ok r21 → r12 = r21 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2), ∀ r12 r21, is_rectangle_overlap rec1 rec2 = ok r12 →
      is_rectangle_overlap rec2 rec1 = ok r21 → r12 = r21) := by
  sorry

/-- Define length-4 slices rec1' and rec2' by rec1'[0] = rec1[0] + dx, rec1'[1] = rec1[1] + dy, rec1'[2] = rec1[2] + dx, rec1'[3] = rec1[3] + dy, and similarly rec2'[i] = rec2[i] + dx for i = 0,2 and rec2'[i] = rec2[i] + dy for i = 1,3. Whenever `is_rectangle_overlap rec1 rec2` returns r and `is_rectangle_overlap rec1' rec2'` returns r', we have r = r'.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. Additionally, dx and dy are integers such that all shifted coordinates defined in the statement lie in [-10^9, 10^9]. -/
theorem spec_4 (rec1 rec2 rec1' rec2' : Slice I64) (dx dy : Int)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hd10 : coord rec1' 0 = coord rec1 0 + dx)
    (hd11 : coord rec1' 1 = coord rec1 1 + dy)
    (hd12 : coord rec1' 2 = coord rec1 2 + dx)
    (hd13 : coord rec1' 3 = coord rec1 3 + dy)
    (hd20 : coord rec2' 0 = coord rec2 0 + dx)
    (hd21 : coord rec2' 1 = coord rec2 1 + dy)
    (hd22 : coord rec2' 2 = coord rec2 2 + dx)
    (hd23 : coord rec2' 3 = coord rec2 3 + dy) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rec1 rec2 rec1' rec2' : Slice I64) (dx dy : Int)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hd10 : coord rec1' 0 = coord rec1 0 + dx)
    (hd11 : coord rec1' 1 = coord rec1 1 + dy)
    (hd12 : coord rec1' 2 = coord rec1 2 + dx)
    (hd13 : coord rec1' 3 = coord rec1 3 + dy)
    (hd20 : coord rec2' 0 = coord rec2 0 + dx)
    (hd21 : coord rec2' 1 = coord rec2 1 + dy)
    (hd22 : coord rec2' 2 = coord rec2 2 + dx)
    (hd23 : coord rec2' 3 = coord rec2 3 + dy), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r') := by
  sorry

/-- Define length-4 slices rec1' and rec2' by rec1'[i] = k*rec1[i] and rec2'[i] = k*rec2[i] for i = 0,1,2,3. Whenever `is_rectangle_overlap rec1 rec2` returns r and `is_rectangle_overlap rec1' rec2'` returns r', we have r = r'.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. Additionally, k is a positive integer such that -10^9 <= k*rec1[i] <= 10^9 and -10^9 <= k*rec2[i] <= 10^9 for every i with 0 <= i < 4. -/
theorem spec_5 (rec1 rec2 rec1' rec2' : Slice I64) (k : Int)
    (h1 : RectValid rec1) (h2 : RectValid rec2) (hk : 0 < k)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hc1 : ∀ i : Nat, i < 4 → coord rec1' i = k * coord rec1 i)
    (hc2 : ∀ i : Nat, i < 4 → coord rec2' i = k * coord rec2 i) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rec1 rec2 rec1' rec2' : Slice I64) (k : Int)
    (h1 : RectValid rec1) (h2 : RectValid rec2) (hk : 0 < k)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hc1 : ∀ i : Nat, i < 4 → coord rec1' i = k * coord rec1 i)
    (hc2 : ∀ i : Nat, i < 4 → coord rec2' i = k * coord rec2 i), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r') := by
  sorry

/-- Define length-4 slices rec1' and rec2' by rec1' = [-rec1[2], rec1[1], -rec1[0], rec1[3]] and rec2' = [-rec2[2], rec2[1], -rec2[0], rec2[3]]. Whenever `is_rectangle_overlap rec1 rec2` returns r and `is_rectangle_overlap rec1' rec2'` returns r', we have r = r'.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_6 (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hr10 : coord rec1' 0 = -coord rec1 2) (hr11 : coord rec1' 1 = coord rec1 1)
    (hr12 : coord rec1' 2 = -coord rec1 0) (hr13 : coord rec1' 3 = coord rec1 3)
    (hr20 : coord rec2' 0 = -coord rec2 2) (hr21 : coord rec2' 1 = coord rec2 1)
    (hr22 : coord rec2' 2 = -coord rec2 0) (hr23 : coord rec2' 3 = coord rec2 3) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hr10 : coord rec1' 0 = -coord rec1 2) (hr11 : coord rec1' 1 = coord rec1 1)
    (hr12 : coord rec1' 2 = -coord rec1 0) (hr13 : coord rec1' 3 = coord rec1 3)
    (hr20 : coord rec2' 0 = -coord rec2 2) (hr21 : coord rec2' 1 = coord rec2 1)
    (hr22 : coord rec2' 2 = -coord rec2 0) (hr23 : coord rec2' 3 = coord rec2 3), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r') := by
  sorry

/-- Define length-4 slices rec1' and rec2' by rec1' = [rec1[1], rec1[0], rec1[3], rec1[2]] and rec2' = [rec2[1], rec2[0], rec2[3], rec2[2]]. Whenever `is_rectangle_overlap rec1 rec2` returns r and `is_rectangle_overlap rec1' rec2'` returns r', we have r = r'.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_7 (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hs10 : coord rec1' 0 = coord rec1 1) (hs11 : coord rec1' 1 = coord rec1 0)
    (hs12 : coord rec1' 2 = coord rec1 3) (hs13 : coord rec1' 3 = coord rec1 2)
    (hs20 : coord rec2' 0 = coord rec2 1) (hs21 : coord rec2' 1 = coord rec2 0)
    (hs22 : coord rec2' 2 = coord rec2 3) (hs23 : coord rec2' 3 = coord rec2 2) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectOk rec1') (h2' : RectOk rec2')
    (hs10 : coord rec1' 0 = coord rec1 1) (hs11 : coord rec1' 1 = coord rec1 0)
    (hs12 : coord rec1' 2 = coord rec1 3) (hs13 : coord rec1' 3 = coord rec1 2)
    (hs20 : coord rec2' 0 = coord rec2 1) (hs21 : coord rec2' 1 = coord rec2 0)
    (hs22 : coord rec2' 2 = coord rec2 3) (hs23 : coord rec2' 3 = coord rec2 2), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = r') := by
  sorry

/-- If `rec1[2] <= rec2[0]` or `rec2[2] <= rec1[0]`, then whenever `is_rectangle_overlap rec1 rec2` returns r, r = false.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_8 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hsep : coord rec1 2 ≤ coord rec2 0 ∨ coord rec2 2 ≤ coord rec1 0) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hsep : coord rec1 2 ≤ coord rec2 0 ∨ coord rec2 2 ≤ coord rec1 0), ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false) := by
  sorry

/-- If `rec1[3] <= rec2[1]` or `rec2[3] <= rec1[1]`, then whenever `is_rectangle_overlap rec1 rec2` returns r, r = false.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_9 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hsep : coord rec1 3 ≤ coord rec2 1 ∨ coord rec2 3 ≤ coord rec1 1) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hsep : coord rec1 3 ≤ coord rec2 1 ∨ coord rec2 3 ≤ coord rec1 1), ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false) := by
  sorry

/-- If either (a) `rec2[0] <= rec1[0]` and `rec1[2] <= rec2[2]` and `rec2[1] <= rec1[1]` and `rec1[3] <= rec2[3]`, or (b) `rec1[0] <= rec2[0]` and `rec2[2] <= rec1[2]` and `rec1[1] <= rec2[1]` and `rec2[3] <= rec1[3]`, then whenever `is_rectangle_overlap rec1 rec2` returns r, r = true.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_10 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hcont :
      (coord rec2 0 ≤ coord rec1 0 ∧ coord rec1 2 ≤ coord rec2 2 ∧
          coord rec2 1 ≤ coord rec1 1 ∧ coord rec1 3 ≤ coord rec2 3) ∨
        (coord rec1 0 ≤ coord rec2 0 ∧ coord rec2 2 ≤ coord rec1 2 ∧
          coord rec1 1 ≤ coord rec2 1 ∧ coord rec2 3 ≤ coord rec1 3)) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2)
    (hcont :
      (coord rec2 0 ≤ coord rec1 0 ∧ coord rec1 2 ≤ coord rec2 2 ∧
          coord rec2 1 ≤ coord rec1 1 ∧ coord rec1 3 ≤ coord rec2 3) ∨
        (coord rec1 0 ≤ coord rec2 0 ∧ coord rec2 2 ≤ coord rec1 2 ∧
          coord rec1 1 ≤ coord rec2 1 ∧ coord rec2 3 ≤ coord rec1 3)), ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = true) := by
  sorry

/-- Let r be the result of `is_rectangle_overlap rec1 rec2` and let r' be the result of `is_rectangle_overlap rec1 rec2'`. Whenever both calls return results, if r = true then r' = true.
  Preconditions: len(rec1) = 4, len(rec2) = 4, and len(rec2') = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9, -10^9 <= rec2[i] <= 10^9, and -10^9 <= rec2'[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3], rec2'[0] < rec2'[2], rec2'[1] < rec2'[3]; and rec2'[0] <= rec2[0], rec2'[1] <= rec2[1], rec2'[2] >= rec2[2], rec2'[3] >= rec2[3]. -/
theorem spec_11 (rec1 rec2 rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2) (h2' : RectValid rec2')
    (hcont : coord rec2' 0 ≤ coord rec2 0 ∧ coord rec2' 1 ≤ coord rec2 1 ∧
      coord rec2 2 ≤ coord rec2' 2 ∧ coord rec2 3 ≤ coord rec2' 3) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1 rec2' = ok r' → r = true → r' = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rec1 rec2 rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2) (h2' : RectValid rec2')
    (hcont : coord rec2' 0 ≤ coord rec2 0 ∧ coord rec2' 1 ≤ coord rec2 1 ∧
      coord rec2 2 ≤ coord rec2' 2 ∧ coord rec2 3 ≤ coord rec2' 3), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1 rec2' = ok r' → r = true → r' = true) := by
  sorry

/-- Let r be the result of `is_rectangle_overlap rec1 rec2` and let r' be the result of `is_rectangle_overlap rec1' rec2'`. Whenever both calls return results, if r = false then r' = false.
  Preconditions: len(rec1) = 4, len(rec2) = 4, len(rec1') = 4, and len(rec2') = 4; for every i with 0 <= i < 4, all four coordinate arrays lie in [-10^9, 10^9]; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3], rec1'[0] < rec1'[2], rec1'[1] < rec1'[3], rec2'[0] < rec2'[2], rec2'[1] < rec2'[3]; rec1[0] <= rec1'[0], rec1'[2] <= rec1[2], rec1[1] <= rec1'[1], rec1'[3] <= rec1[3]; and rec2[0] <= rec2'[0], rec2'[2] <= rec2[2], rec2[1] <= rec2'[1], rec2'[3] <= rec2[3]. -/
theorem spec_12 (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectValid rec1') (h2' : RectValid rec2')
    (hnest1 : coord rec1 0 ≤ coord rec1' 0 ∧ coord rec1' 2 ≤ coord rec1 2 ∧
      coord rec1 1 ≤ coord rec1' 1 ∧ coord rec1' 3 ≤ coord rec1 3)
    (hnest2 : coord rec2 0 ≤ coord rec2' 0 ∧ coord rec2' 2 ≤ coord rec2 2 ∧
      coord rec2 1 ≤ coord rec2' 1 ∧ coord rec2' 3 ≤ coord rec2 3) :
    ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = false → r' = false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rec1 rec2 rec1' rec2' : Slice I64)
    (h1 : RectValid rec1) (h2 : RectValid rec2)
    (h1' : RectValid rec1') (h2' : RectValid rec2')
    (hnest1 : coord rec1 0 ≤ coord rec1' 0 ∧ coord rec1' 2 ≤ coord rec1 2 ∧
      coord rec1 1 ≤ coord rec1' 1 ∧ coord rec1' 3 ≤ coord rec1 3)
    (hnest2 : coord rec2 0 ≤ coord rec2' 0 ∧ coord rec2' 2 ≤ coord rec2 2 ∧
      coord rec2 1 ≤ coord rec2' 1 ∧ coord rec2' 3 ≤ coord rec2 3), ∀ r r', is_rectangle_overlap rec1 rec2 = ok r →
      is_rectangle_overlap rec1' rec2' = ok r' → r = false → r' = false) := by
  sorry

/-- If `is_rectangle_overlap rec1 rec2` returns r and r = true, then the four strict inequalities `rec1[0] < rec2[2]`, `rec2[0] < rec1[2]`, `rec1[1] < rec2[3]`, and `rec2[1] < rec1[3]` all hold. Consequently the open intersection rectangle `(max(rec1[0], rec2[0]), min(rec1[2], rec2[2])) × (max(rec1[1], rec2[1]), min(rec1[3], rec2[3]))` is nonempty.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_13 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = true →
      (coord rec1 0 < coord rec2 2 ∧ coord rec2 0 < coord rec1 2 ∧
          coord rec1 1 < coord rec2 3 ∧ coord rec2 1 < coord rec1 3) ∧
        max (coord rec1 0) (coord rec2 0) < min (coord rec1 2) (coord rec2 2) ∧
        max (coord rec1 1) (coord rec2 1) < min (coord rec1 3) (coord rec2 3) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2), ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = true →
      (coord rec1 0 < coord rec2 2 ∧ coord rec2 0 < coord rec1 2 ∧
          coord rec1 1 < coord rec2 3 ∧ coord rec2 1 < coord rec1 3) ∧
        max (coord rec1 0) (coord rec2 0) < min (coord rec1 2) (coord rec2 2) ∧
        max (coord rec1 1) (coord rec2 1) < min (coord rec1 3) (coord rec2 3)) := by
  sorry

/-- If `is_rectangle_overlap rec1 rec2` returns r and r = false, then at least one of the four separation inequalities holds: `rec1[2] <= rec2[0]`, `rec2[2] <= rec1[0]`, `rec1[3] <= rec2[1]`, or `rec2[3] <= rec1[1]`.
  Preconditions: len(rec1) = 4 and len(rec2) = 4; for every i with 0 <= i < 4, -10^9 <= rec1[i] <= 10^9 and -10^9 <= rec2[i] <= 10^9; rec1[0] < rec1[2], rec1[1] < rec1[3], rec2[0] < rec2[2], rec2[1] < rec2[3]. -/
theorem spec_14 (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2) :
    ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false →
      (coord rec1 2 ≤ coord rec2 0 ∨ coord rec2 2 ≤ coord rec1 0 ∨
        coord rec1 3 ≤ coord rec2 1 ∨ coord rec2 3 ≤ coord rec1 1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (rec1 rec2 : Slice I64) (h1 : RectValid rec1) (h2 : RectValid rec2), ∀ r, is_rectangle_overlap rec1 rec2 = ok r → r = false →
      (coord rec1 2 ≤ coord rec2 0 ∨ coord rec2 2 ≤ coord rec1 0 ∨
        coord rec1 3 ≤ coord rec2 1 ∨ coord rec2 3 ≤ coord rec1 1)) := by
  sorry

end AegisSpec.IsRectangleOverlap
