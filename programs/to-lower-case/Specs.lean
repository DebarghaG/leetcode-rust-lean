import Aegis.ToLowerCase.Code.Funs

/-!
# Specifications of `Aegis.ToLowerCase.to_lower_case`

LeetCode problem `to-lower-case`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.ToLowerCase

namespace AegisSpec.ToLowerCase

def code (b : U8) : Nat := b.val

def isUpper (b : U8) : Prop := 65 ≤ code b ∧ code b ≤ 90

def isLower (b : U8) : Prop := 97 ≤ code b ∧ code b ≤ 122

instance (b : U8) : Decidable (isUpper b) := by
  unfold isUpper
  infer_instance

instance (b : U8) : Decidable (isLower b) := by
  unfold isLower
  infer_instance

def PrintableAscii (v : List U8) : Prop :=
  ∀ (i : Nat) (b : U8), v[i]? = some b → 32 ≤ code b ∧ code b ≤ 126

def countIn (lo hi : Nat) (v : List U8) : Nat :=
  ((v.map code).filter (fun c => lo ≤ c ∧ c ≤ hi)).length

def lowerCount (v : List U8) : Nat := countIn 97 122 v

def upperCount (v : List U8) : Nat := countIn 65 90 v

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, len(r) = len(s) and for every i with 0 <= i < len(s): if 65 <= code(s[i]) <= 90 then code(r[i]) = code(s[i]) + 32, and otherwise code(r[i]) = code(s[i]).
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_1 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      r.val.length = (Slice.len s).val ∧
        ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
          code b = (if isUpper (s.val[i]'hi) then code (s.val[i]'hi) + 32
                    else code (s.val[i]'hi)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      r.val.length = (Slice.len s).val ∧
        ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
          code b = (if isUpper (s.val[i]'hi) then code (s.val[i]'hi) + 32
                    else code (s.val[i]'hi))) := by
  sorry

/-- For every input s satisfying the preconditions, the function returns a result r (some vector of bytes); it does not fail, panic, overflow, or access memory out of bounds.
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_2 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∃ (r : alloc.vec.Vec U8), to_lower_case s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∃ (r : alloc.vec.Vec U8), to_lower_case s = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(s).
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_3 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      r.val.length = (Slice.len s).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      r.val.length = (Slice.len s).val) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, for every i with 0 <= i < len(s) such that 65 <= code(s[i]) <= 90, we have code(r[i]) = code(s[i]) + 32.
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_4 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        isUpper (s.val[i]'hi) → code b = code (s.val[i]'hi) + 32 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        isUpper (s.val[i]'hi) → code b = code (s.val[i]'hi) + 32) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, for every i with 0 <= i < len(s) such that not (65 <= code(s[i]) <= 90), we have r[i] = s[i].
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_5 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        ¬ isUpper (s.val[i]'hi) → b = s.val[i]'hi := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        ¬ isUpper (s.val[i]'hi) → b = s.val[i]'hi) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, for every i with 0 <= i < len(r), not (65 <= code(r[i]) <= 90).
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_6 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), ¬ isUpper (r.val[i]'hi) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), ¬ isUpper (r.val[i]'hi)) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, for every i with 0 <= i < len(r), 32 <= code(r[i]) <= 126.
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_7 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        32 ≤ code (r.val[i]'hi) ∧ code (r.val[i]'hi) ≤ 126 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < r.val.length),
        32 ≤ code (r.val[i]'hi) ∧ code (r.val[i]'hi) ≤ 126) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, whenever the function returns a result r, for every i with 0 <= i < len(s), we have r[i] != s[i] if and only if 65 <= code(s[i]) <= 90.
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_8 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        (b ≠ s.val[i]'hi ↔ isUpper (s.val[i]'hi)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), r.val[i]? = some b →
        (b ≠ s.val[i]'hi ↔ isUpper (s.val[i]'hi))) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, let lower_count(v) be the number of indices i with 0 <= i < len(v) and 97 <= code(v[i]) <= 122, and upper_count(v) be the number of indices i with 0 <= i < len(v) and 65 <= code(v[i]) <= 90. Whenever the function returns a result r, lower_count(r) = lower_count(s) + upper_count(s).
  Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), the integer ASCII value of s[i] is between 32 and 126 inclusive (printable ASCII). -/
theorem spec_9 (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val) :
    ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      lowerCount r.val = lowerCount s.val + upperCount s.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (h_len_lo : 1 ≤ (Slice.len s).val) (h_len_hi : (Slice.len s).val ≤ 100)
    (h_print : PrintableAscii s.val), ∀ (r : alloc.vec.Vec U8), to_lower_case s = ok r →
      lowerCount r.val = lowerCount s.val + upperCount s.val) := by
  sorry

/-- Writing code(b) for the integer ASCII value of byte b, let s and t be any two inputs satisfying the preconditions with len(s) = len(t). Suppose that for every i with 0 <= i < len(s), either code(s[i]) = code(t[i]), or 65 <= code(s[i]) <= 90 and code(t[i]) = code(s[i]) + 32, or 65 <= code(t[i]) <= 90 and code(s[i]) = code(t[i]) + 32. Then whenever the function returns a result r_s for s and a result r_t for t, len(r_s) = len(r_t) and for every i with 0 <= i < len(r_s), r_s[i] = r_t[i].
  Preconditions: Both s and t satisfy: len is between 1 and 100 inclusive, and every byte has integer ASCII value between 32 and 126 inclusive (printable ASCII). -/
theorem spec_10 (s t : Slice U8)
    (h_len_lo_s : 1 ≤ (Slice.len s).val) (h_len_hi_s : (Slice.len s).val ≤ 100)
    (h_print_s : PrintableAscii s.val)
    (h_len_lo_t : 1 ≤ (Slice.len t).val) (h_len_hi_t : (Slice.len t).val ≤ 100)
    (h_print_t : PrintableAscii t.val)
    (h_len_eq : (Slice.len s).val = (Slice.len t).val)
    (h_rel : ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), t.val[i]? = some b →
      code (s.val[i]'hi) = code b ∨
        (isUpper (s.val[i]'hi) ∧ code b = code (s.val[i]'hi) + 32) ∨
        (isUpper b ∧ code (s.val[i]'hi) = code b + 32)) :
    ∀ (r_s r_t : alloc.vec.Vec U8), to_lower_case s = ok r_s → to_lower_case t = ok r_t →
      r_s.val.length = r_t.val.length ∧
        ∀ (i : Nat), i < r_s.val.length → r_s.val[i]? = r_t.val[i]? := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_lo_s : 1 ≤ (Slice.len s).val) (h_len_hi_s : (Slice.len s).val ≤ 100)
    (h_print_s : PrintableAscii s.val)
    (h_len_lo_t : 1 ≤ (Slice.len t).val) (h_len_hi_t : (Slice.len t).val ≤ 100)
    (h_print_t : PrintableAscii t.val)
    (h_len_eq : (Slice.len s).val = (Slice.len t).val)
    (h_rel : ∀ (i : Nat) (hi : i < (Slice.len s).val) (b : U8), t.val[i]? = some b →
      code (s.val[i]'hi) = code b ∨
        (isUpper (s.val[i]'hi) ∧ code b = code (s.val[i]'hi) + 32) ∨
        (isUpper b ∧ code (s.val[i]'hi) = code b + 32)), ∀ (r_s r_t : alloc.vec.Vec U8), to_lower_case s = ok r_s → to_lower_case t = ok r_t →
      r_s.val.length = r_t.val.length ∧
        ∀ (i : Nat), i < r_s.val.length → r_s.val[i]? = r_t.val[i]?) := by
  sorry

end AegisSpec.ToLowerCase
