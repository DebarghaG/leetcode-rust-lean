import Aegis.CanBeEqual.Code.Funs

/-!
# Specifications of `Aegis.CanBeEqual.can_be_equal`

LeetCode problem `check-if-strings-can-be-made-equal-with-operations-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanBeEqual

def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def Lower4 (s : Slice Std.U8) : Prop :=
  s.val.length = 4 ∧ ∀ i, i < 4 → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

def SamePair (a b c d : Nat) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def evenClass (s1 s2 : Slice Std.U8) : Prop :=
  SamePair (byteAt s1 0) (byteAt s1 2) (byteAt s2 0) (byteAt s2 2)

def oddClass (s1 s2 : Slice Std.U8) : Prop :=
  SamePair (byteAt s1 1) (byteAt s1 3) (byteAt s2 1) (byteAt s2 3)

/-- The function returns a result r, and r = true if and only if both: (a) the two bytes s1[0] and s1[2] form the same multiset as s2[0] and s2[2], i.e. (s1[0] = s2[0] and s1[2] = s2[2]) or (s1[0] = s2[2] and s1[2] = s2[0]); and (b) the two bytes s1[1] and s1[3] form the same multiset as s2[1] and s2[3], i.e. (s1[1] = s2[1] and s1[3] = s2[3]) or (s1[1] = s2[3] and s1[3] = s2[1]).
  Preconditions: len(s1) = 4 and len(s2) = 4, and for every i with 0 <= i < 4, 97 <= s1[i] <= 122 and 97 <= s2[i] <= 122 (both are length-4 lowercase ASCII strings). -/
theorem spec_1 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2) :
    ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      (r = true ↔ (evenClass s1 s2 ∧ oddClass s1 s2)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2), ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      (r = true ↔ (evenClass s1 s2 ∧ oddClass s1 s2))) := by
  sorry

/-- The function returns a result r (it does not fail) for these inputs.
  Preconditions: len(s1) = 4 and len(s2) = 4, and for every i with 0 <= i < 4, 97 <= s1[i] <= 122 and 97 <= s2[i] <= 122 (both are length-4 lowercase ASCII strings). -/
theorem spec_2 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2) :
    ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2), ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r) := by
  sorry

/-- Let r be the result of can_be_equal(s1, s2) and let r' be the result of can_be_equal(s2, s1). Then both calls return results and r = r'.
  Preconditions: len(s1) = 4 and len(s2) = 4, and for every i with 0 <= i < 4, 97 <= s1[i] <= 122 and 97 <= s2[i] <= 122 (both are length-4 lowercase ASCII strings). -/
theorem spec_3 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2) :
    ∃ r r', Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      Aegis.CanBeEqual.can_be_equal s2 s1 = ok r' ∧ r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2), ∃ r r', Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      Aegis.CanBeEqual.can_be_equal s2 s1 = ok r' ∧ r = r') := by
  sorry

/-- Let s1' be any length-4 lowercase byte string such that the multiset {s1'[0], s1'[2]} equals {s1[0], s1[2]} and the multiset {s1'[1], s1'[3]} equals {s1[1], s1[3]}; let s2' be any length-4 lowercase byte string with the analogous property relative to s2. Then can_be_equal(s1, s2) and can_be_equal(s1', s2') both return results and are equal.
  Preconditions: len(s1) = 4 and len(s2) = 4, and for every i with 0 <= i < 4, 97 <= s1[i] <= 122 and 97 <= s2[i] <= 122 (both are length-4 lowercase ASCII strings). -/
theorem spec_4 (s1 s2 s1' s2' : Slice Std.U8)
    (h1 : Lower4 s1) (h2 : Lower4 s2) (h1' : Lower4 s1') (h2' : Lower4 s2')
    (hev1 : SamePair (byteAt s1' 0) (byteAt s1' 2) (byteAt s1 0) (byteAt s1 2))
    (hod1 : SamePair (byteAt s1' 1) (byteAt s1' 3) (byteAt s1 1) (byteAt s1 3))
    (hev2 : SamePair (byteAt s2' 0) (byteAt s2' 2) (byteAt s2 0) (byteAt s2 2))
    (hod2 : SamePair (byteAt s2' 1) (byteAt s2' 3) (byteAt s2 1) (byteAt s2 3)) :
    ∃ r r', Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      Aegis.CanBeEqual.can_be_equal s1' s2' = ok r' ∧ r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 s2 s1' s2' : Slice Std.U8)
    (h1 : Lower4 s1) (h2 : Lower4 s2) (h1' : Lower4 s1') (h2' : Lower4 s2')
    (hev1 : SamePair (byteAt s1' 0) (byteAt s1' 2) (byteAt s1 0) (byteAt s1 2))
    (hod1 : SamePair (byteAt s1' 1) (byteAt s1' 3) (byteAt s1 1) (byteAt s1 3))
    (hev2 : SamePair (byteAt s2' 0) (byteAt s2' 2) (byteAt s2 0) (byteAt s2 2))
    (hod2 : SamePair (byteAt s2' 1) (byteAt s2' 3) (byteAt s2 1) (byteAt s2 3)), ∃ r r', Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧
      Aegis.CanBeEqual.can_be_equal s1' s2' = ok r' ∧ r = r') := by
  sorry

/-- The function returns false.
  Preconditions: len(s1) = 4 and len(s2) = 4, all bytes are lowercase ASCII, and the multisets {s1[0], s1[2]} and {s2[0], s2[2]} are not equal (equivalently, neither (s1[0] = s2[0] and s1[2] = s2[2]) nor (s1[0] = s2[2] and s1[2] = s2[0]) holds). -/
theorem spec_5 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2)
    (hne : ¬ SamePair (byteAt s1 0) (byteAt s1 2) (byteAt s2 0) (byteAt s2 2)) :
    ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧ r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2)
    (hne : ¬ SamePair (byteAt s1 0) (byteAt s1 2) (byteAt s2 0) (byteAt s2 2)), ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧ r = false) := by
  sorry

/-- The function returns true.
  Preconditions: len(s1) = 4 and len(s2) = 4, all bytes are lowercase ASCII, and both parity-class conditions hold: the multisets {s1[0], s1[2]} and {s2[0], s2[2]} are equal, and the multisets {s1[1], s1[3]} and {s2[1], s2[3]} are equal. -/
theorem spec_6 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2)
    (hev : evenClass s1 s2) (hod : oddClass s1 s2) :
    ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧ r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2)
    (hev : evenClass s1 s2) (hod : oddClass s1 s2), ∃ r, Aegis.CanBeEqual.can_be_equal s1 s2 = ok r ∧ r = true) := by
  sorry

/-- Whenever the function returns true, there exists a length-4 lowercase byte string t such that the multiset {t[0], t[2]} equals both {s1[0], s1[2]} and {s2[0], s2[2]}, and the multiset {t[1], t[3]} equals both {s1[1], s1[3]} and {s2[1], s2[3]}.
  Preconditions: len(s1) = 4 and len(s2) = 4, and for every i with 0 <= i < 4, 97 <= s1[i] <= 122 and 97 <= s2[i] <= 122 (both are length-4 lowercase ASCII strings). -/
theorem spec_7 (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2) :
    Aegis.CanBeEqual.can_be_equal s1 s2 = ok true →
      ∃ t : Slice Std.U8, Lower4 t ∧
        SamePair (byteAt t 0) (byteAt t 2) (byteAt s1 0) (byteAt s1 2) ∧
        SamePair (byteAt t 0) (byteAt t 2) (byteAt s2 0) (byteAt s2 2) ∧
        SamePair (byteAt t 1) (byteAt t 3) (byteAt s1 1) (byteAt s1 3) ∧
        SamePair (byteAt t 1) (byteAt t 3) (byteAt s2 1) (byteAt s2 3) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (h1 : Lower4 s1) (h2 : Lower4 s2), Aegis.CanBeEqual.can_be_equal s1 s2 = ok true →
      ∃ t : Slice Std.U8, Lower4 t ∧
        SamePair (byteAt t 0) (byteAt t 2) (byteAt s1 0) (byteAt s1 2) ∧
        SamePair (byteAt t 0) (byteAt t 2) (byteAt s2 0) (byteAt s2 2) ∧
        SamePair (byteAt t 1) (byteAt t 3) (byteAt s1 1) (byteAt s1 3) ∧
        SamePair (byteAt t 1) (byteAt t 3) (byteAt s2 1) (byteAt s2 3)) := by
  sorry

end AegisSpec.CanBeEqual
