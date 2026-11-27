import Aegis.FindLuSlength.Code.Funs

/-!
# Specifications of `Aegis.FindLuSlength.find_lu_slength`

LeetCode problem `longest-uncommon-subsequence-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLuSlength

def LowerBytes (a : Slice Std.U8) : Prop :=
  ∀ (i : Nat) (h : i < a.val.length), 97 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 122

def ByteEq (a b : Slice Std.U8) : Prop :=
  a.val.length = b.val.length ∧
    ∀ (i : Nat) (ha : i < a.val.length) (hb : i < b.val.length), a.val[i] = b.val[i]

def IsSubseq (s t : List Std.U8) : Prop :=
  ∃ f : Fin s.length → Fin t.length,
    (∀ i j : Fin s.length, i < j → f i < f j) ∧
      ∀ i : Fin s.length, t.get (f i) = s.get i

/-- The function returns a result r and r = -1 exactly when a and b are equal byte strings, meaning len(a) = len(b) and a[i] = b[i] for every i with 0 <= i < len(a). When a and b are not equal byte strings, r = max(len(a), len(b)), i.e. r = len(a) if len(a) >= len(b) and r = len(b) if len(a) < len(b).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_1 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (r.val = -1 ↔ ByteEq a b) ∧
      (¬ ByteEq a b → r.val = ((max a.val.length b.val.length : Nat) : Int)) ∧
      (¬ ByteEq a b → b.val.length ≤ a.val.length → r.val = (a.val.length : Int)) ∧
      (¬ ByteEq a b → a.val.length < b.val.length → r.val = (b.val.length : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (r.val = -1 ↔ ByteEq a b) ∧
      (¬ ByteEq a b → r.val = ((max a.val.length b.val.length : Nat) : Int)) ∧
      (¬ ByteEq a b → b.val.length ≤ a.val.length → r.val = (a.val.length : Int)) ∧
      (¬ ByteEq a b → a.val.length < b.val.length → r.val = (b.val.length : Int))) := by
  sorry

/-- The function returns a result r for every pair a,b satisfying the preconditions; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_2 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r) := by
  sorry

/-- The function returns a result r and -1 <= r <= max(len(a), len(b)); in particular, -1 <= r <= 100.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_3 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      -1 ≤ r.val ∧
      r.val ≤ ((max a.val.length b.val.length : Nat) : Int) ∧
      r.val ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      -1 ≤ r.val ∧
      r.val ≤ ((max a.val.length b.val.length : Nat) : Int) ∧
      r.val ≤ 100) := by
  sorry

/-- The function returns a result r and r is either -1 or exactly max(len(a), len(b)); no other value is possible.
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_4 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (r.val = -1 ∨ r.val = ((max a.val.length b.val.length : Nat) : Int)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (r.val = -1 ∨ r.val = ((max a.val.length b.val.length : Nat) : Int))) := by
  sorry

/-- Swapping the two arguments does not change the answer: the result returned for (a,b) equals the result returned for (b,a).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_5 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      Aegis.FindLuSlength.find_lu_slength b a = ok r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      Aegis.FindLuSlength.find_lu_slength b a = ok r) := by
  sorry

/-- Let c and d be byte arrays satisfying the same constraints as a and b (1 <= len(c), len(d) <= 100 and all bytes in 97..122). If len(c) = len(a), len(d) = len(b), and (c and d are equal byte strings exactly when a and b are equal byte strings), then the result returned for (c,d) equals the result returned for (a,b).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_6 (a b c d : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b)
    (hlen_c : 1 ≤ c.val.length) (hlen_d : 1 ≤ d.val.length)
    (hmax_c : c.val.length ≤ 100) (hmax_d : d.val.length ≤ 100)
    (hbyte_c : LowerBytes c) (hbyte_d : LowerBytes d)
    (hlen_ca : c.val.length = a.val.length) (hlen_db : d.val.length = b.val.length)
    (heq : ByteEq c d ↔ ByteEq a b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength c d = ok r ∧
      Aegis.FindLuSlength.find_lu_slength a b = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b c d : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b)
    (hlen_c : 1 ≤ c.val.length) (hlen_d : 1 ≤ d.val.length)
    (hmax_c : c.val.length ≤ 100) (hmax_d : d.val.length ≤ 100)
    (hbyte_c : LowerBytes c) (hbyte_d : LowerBytes d)
    (hlen_ca : c.val.length = a.val.length) (hlen_db : d.val.length = b.val.length)
    (heq : ByteEq c d ↔ ByteEq a b), ∃ r, Aegis.FindLuSlength.find_lu_slength c d = ok r ∧
      Aegis.FindLuSlength.find_lu_slength a b = ok r) := by
  sorry

/-- Define s to be a subsequence of t iff there exist indices 0 <= i_1 < ... < i_k < len(t) with k = len(s) and t[i_j] = s[j] for every 1 <= j <= k. The function returns a result r and, whenever a and b are not equal byte strings, taking s = a if len(a) >= len(b) and s = b otherwise, we have len(s) = r and s is a subsequence of exactly one of a and b (it is a subsequence of its source and not of the other).
  Preconditions: len(a) >= 1, len(b) >= 1, len(a) <= 100, len(b) <= 100; for every i with 0 <= i < len(a), 97 <= a[i] <= 122; for every i with 0 <= i < len(b), 97 <= b[i] <= 122. -/
theorem spec_7 (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b) :
    ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (¬ ByteEq a b →
        let s : Slice Std.U8 := if b.val.length ≤ a.val.length then a else b
        let o : Slice Std.U8 := if b.val.length ≤ a.val.length then b else a
        r.val = (s.val.length : Int) ∧ IsSubseq s.val s.val ∧ ¬ IsSubseq s.val o.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice Std.U8)
    (hlen_a : 1 ≤ a.val.length) (hlen_b : 1 ≤ b.val.length)
    (hmax_a : a.val.length ≤ 100) (hmax_b : b.val.length ≤ 100)
    (hbyte_a : LowerBytes a) (hbyte_b : LowerBytes b), ∃ r, Aegis.FindLuSlength.find_lu_slength a b = ok r ∧
      (¬ ByteEq a b →
        let s : Slice Std.U8 := if b.val.length ≤ a.val.length then a else b
        let o : Slice Std.U8 := if b.val.length ≤ a.val.length then b else a
        r.val = (s.val.length : Int) ∧ IsSubseq s.val s.val ∧ ¬ IsSubseq s.val o.val)) := by
  sorry

end AegisSpec.FindLuSlength
