import Aegis.CheckRecord.Code.Funs

/-!
# Specifications of `Aegis.CheckRecord.check_record`

LeetCode problem `student-attendance-record-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckRecord

abbrev byteA : Std.U8 := 65#u8

abbrev byteL : Std.U8 := 76#u8

abbrev byteP : Std.U8 := 80#u8

abbrev byteAt (l : List Std.U8) (i : Nat) (c : Std.U8) : Prop := l[i]? = some c

def AllowedBytes (l : List Std.U8) : Prop :=
  ∀ i, i < l.length → byteAt l i byteA ∨ byteAt l i byteL ∨ byteAt l i byteP

def countA (l : List Std.U8) : Nat := (l.filter (fun c => c = byteA)).length

def HasThreeL (l : List Std.U8) : Prop :=
  ∃ i, i + 2 < l.length ∧ byteAt l i byteL ∧ byteAt l (i + 1) byteL ∧
    byteAt l (i + 2) byteL

def NoA (l : List Std.U8) : Prop := ∀ i, i < l.length → ¬ byteAt l i byteA

/-- Whenever check_record(s) returns a result r, r = true if and only if both: (1) the number of indices i with 0 <= i < len(s) and s[i] = 65 ('A') is strictly less than 2; and (2) there is no index i with 0 <= i, i + 2 < len(s), and s[i] = s[i+1] = s[i+2] = 76 ('L').
  Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val) :
    ∀ r, Aegis.CheckRecord.check_record s = ok r →
      (r = true ↔ countA s.val < 2 ∧ ¬ HasThreeL s.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val), ∀ r, Aegis.CheckRecord.check_record s = ok r →
      (r = true ↔ countA s.val < 2 ∧ ¬ HasThreeL s.val)) := by
  sorry

/-- For every s satisfying the preconditions, check_record(s) returns a Bool result; it does not fail (no out-of-bounds access, arithmetic overflow, or panic).
  Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val) :
    ∃ r, Aegis.CheckRecord.check_record s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val), ∃ r, Aegis.CheckRecord.check_record s = ok r) := by
  sorry

/-- Whenever check_record(s) returns a result r, if the number of indices i with 0 <= i < len(s) and s[i] = 65 ('A') is at least 2, then r = false.
  Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val) :
    ∀ r, Aegis.CheckRecord.check_record s = ok r → 2 ≤ countA s.val → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val), ∀ r, Aegis.CheckRecord.check_record s = ok r → 2 ≤ countA s.val → r = false) := by
  sorry

/-- Whenever check_record(s) returns a result r, if there exists an index i with 0 <= i, i + 2 < len(s), and s[i] = s[i+1] = s[i+2] = 76 ('L'), then r = false.
  Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val) :
    ∀ r, Aegis.CheckRecord.check_record s = ok r → HasThreeL s.val → r = false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val), ∀ r, Aegis.CheckRecord.check_record s = ok r → HasThreeL s.val → r = false) := by
  sorry

/-- Whenever check_record(s) returns a result r, if the number of indices i with 0 <= i < len(s) and s[i] = 65 ('A') is at most 1 and there is no index i with 0 <= i, i + 2 < len(s), and s[i] = s[i+1] = s[i+2] = 76 ('L'), then r = true.
  Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val) :
    ∀ r, Aegis.CheckRecord.check_record s = ok r → countA s.val ≤ 1 →
      ¬ HasThreeL s.val → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hallowed : AllowedBytes s.val), ∀ r, Aegis.CheckRecord.check_record s = ok r → countA s.val ≤ 1 →
      ¬ HasThreeL s.val → r = true) := by
  sorry

/-- Let t be the byte sequence of length len(s) + 1 with t[i] = s[i] for every i with 0 <= i < len(s), and t[len(s)] = 80 ('P'). Both calls check_record(s) and check_record(t) return Boolean results r and r', and r = r'.
  Preconditions: len(s) >= 1, len(s) <= 999, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = s.val ++ [byteP]) :
    ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = s.val ++ [byteP]), ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r') := by
  sorry

/-- Let t be the byte sequence of length len(s) + 1 with t[0] = 80 ('P'), and t[i+1] = s[i] for every i with 0 <= i < len(s). Both calls check_record(s) and check_record(t) return Boolean results r and r', and r = r'.
  Preconditions: len(s) >= 1, len(s) <= 999, and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = byteP :: s.val) :
    ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = byteP :: s.val), ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r') := by
  sorry

/-- Let t be the byte sequence of length len(s) + 1 with t[i] = s[i] for every i with 0 <= i < len(s), and t[len(s)] = 65 ('A'). Both calls check_record(s) and check_record(t) return Boolean results r and r', and r = r'.
  Preconditions: len(s) >= 1, len(s) <= 999, there is no index i with 0 <= i < len(s) and s[i] = 65 ('A'), and for every i with 0 <= i < len(s), s[i] is one of 65 ('A'), 76 ('L'), 80 ('P'). -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hnoA : NoA s.val) (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = s.val ++ [byteA]) :
    ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
    (hnoA : NoA s.val) (hallowed : AllowedBytes s.val) (t : Slice Std.U8)
    (ht : t.val = s.val ++ [byteA]), ∃ r r', Aegis.CheckRecord.check_record s = ok r ∧
      Aegis.CheckRecord.check_record t = ok r' ∧ r = r') := by
  sorry

end AegisSpec.CheckRecord
