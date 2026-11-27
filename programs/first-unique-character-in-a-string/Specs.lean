import Aegis.FirstUniqChar.Code.Funs

/-!
# Specifications of `Aegis.FirstUniqChar.first_uniq_char`

LeetCode problem `first-unique-character-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FirstUniqChar

def ByteAt (s : Slice Std.U8) (i : ℕ) (b : Std.U8) : Prop :=
  s.val[i]? = some b

def AllLower (s : Slice Std.U8) : Prop :=
  ∀ i, i < s.length → ∃ b, ByteAt s i b ∧ 97 ≤ b.val ∧ b.val ≤ 122

def OccursOnce (s : Slice Std.U8) (i : ℕ) : Prop :=
  i < s.length ∧ ∀ j, j < s.length → (s.val[j]? = s.val[i]? ↔ j = i)

def OccursAtLeastTwice (s : Slice Std.U8) (i : ℕ) : Prop :=
  ∃ j, j < s.length ∧ j ≠ i ∧ s.val[j]? = s.val[i]?

def HasUniqueByte (s : Slice Std.U8) : Prop :=
  ∃ i, OccursOnce s i

def AllRepeated (s : Slice Std.U8) : Prop :=
  ∀ i, i < s.length → OccursAtLeastTwice s i

def IsLowerBij (f : Std.U8 → Std.U8) : Prop :=
  (∀ b, 97 ≤ b.val → b.val ≤ 122 → 97 ≤ (f b).val ∧ (f b).val ≤ 122) ∧
    ∃ g : Std.U8 → Std.U8,
      (∀ b, 97 ≤ b.val → b.val ≤ 122 → g (f b) = b) ∧
        ∀ b, 97 ≤ b.val → b.val ≤ 122 → f (g b) = b

/-- Whenever first_uniq_char(s) returns a successful result r, the following holds. If there exists an index i with 0 <= i < len(s) such that s[i] occurs exactly once in s (meaning: for every j with 0 <= j < len(s), s[j] = s[i] if and only if j = i), then r is the smallest such index: 0 <= r < len(s), s[r] occurs exactly once in s, and for every k with 0 <= k < r, s[k] occurs at least twice in s (meaning: there exists j with 0 <= j < len(s), j != k, and s[j] = s[k]). Otherwise (no index in s has a byte occurring exactly once), r = -1.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (so every byte is a lowercase ASCII letter). -/
theorem spec_1 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) :
    (HasUniqueByte s →
        (0 ≤ r.val ∧ r.val < (s.length : ℤ) ∧ OccursOnce s r.val.toNat ∧
          ∀ k : ℕ, (k : ℤ) < r.val → OccursAtLeastTwice s k)) ∧
      (AllRepeated s → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r), (HasUniqueByte s →
        (0 ≤ r.val ∧ r.val < (s.length : ℤ) ∧ OccursOnce s r.val.toNat ∧
          ∀ k : ℕ, (k : ℤ) < r.val → OccursAtLeastTwice s k)) ∧
      (AllRepeated s → r.val = -1)) := by
  sorry

/-- For every valid s, first_uniq_char(s) returns a successful result r; in particular it does not fail, panic, or overflow.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) :
    ∃ r : Std.I64, Aegis.FirstUniqChar.first_uniq_char s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s), ∃ r : Std.I64, Aegis.FirstUniqChar.first_uniq_char s = ok r) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, either r = -1 or 0 <= r < len(s).
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (s.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (s.length : ℤ))) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and 0 <= r < len(s), the byte s[r] occurs exactly once in s; that is, for every j with 0 <= j < len(s), s[j] = s[r] if and only if j = r.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)) :
    OccursOnce s r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)), OccursOnce s r.val.toNat) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and 0 <= r < len(s), for every i with 0 <= i < r, the byte s[i] occurs at least twice in s; that is, there exists j with 0 <= j < len(s), j != i, and s[j] = s[i].
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)) :
    ∀ i : ℕ, (i : ℤ) < r.val → OccursAtLeastTwice s i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)), ∀ i : ℕ, (i : ℤ) < r.val → OccursAtLeastTwice s i) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, r = -1 if and only if for every i with 0 <= i < len(s), the byte s[i] occurs at least twice in s; that is, there exists j with 0 <= j < len(s), j != i, and s[j] = s[i].
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) :
    r.val = -1 ↔ AllRepeated s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r), r.val = -1 ↔ AllRepeated s) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and 0 <= r < len(s), for every i with 0 <= i < len(s), if s[i] occurs exactly once in s (for every j with 0 <= j < len(s), s[j] = s[i] if and only if j = i), then r <= i.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)) :
    ∀ i : ℕ, i < s.length → OccursOnce s i → r.val ≤ (i : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_pos : 0 ≤ r.val)
    (h_bound : r.val < (s.length : ℤ)), ∀ i : ℕ, i < s.length → OccursOnce s i → r.val ≤ (i : ℤ)) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and len(s) = 1, r = 0.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : s.length = 1) :
    r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : s.length = 1), r.val = 0) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, if len(s) > 1 and s[i] = s[0] for every i with 0 <= i < len(s), then r = -1.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : 1 < s.length)
    (h_const : ∀ i, i < s.length → s.val[i]? = s.val[0]?) :
    r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : 1 < s.length)
    (h_const : ∀ i, i < s.length → s.val[i]? = s.val[0]?), r.val = -1) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and len(s) = 2, then if s[0] = s[1] we have r = -1, and if s[0] != s[1] we have r = 0.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : s.length = 2) :
    (s.val[0]? = s.val[1]? → r.val = -1) ∧ (s.val[0]? ≠ s.val[1]? → r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_len : s.length = 2), (s.val[0]? = s.val[1]? → r.val = -1) ∧ (s.val[0]? ≠ s.val[1]? → r.val = 0)) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, if s[0] occurs exactly once in s (for every j with 0 <= j < len(s), s[j] = s[0] if and only if j = 0), then r = 0.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_first : OccursOnce s 0) :
    r.val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_first : OccursOnce s 0), r.val = 0) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, if for every i and j with 0 <= i < j < len(s) we have s[i] != s[j], then r = 0.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r)
    (h_distinct : ∀ i j, i < j → j < s.length → s.val[i]? ≠ s.val[j]?) :
    r.val = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r)
    (h_distinct : ∀ i j, i < j → j < s.length → s.val[i]? ≠ s.val[j]?), r.val = 0) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r, if r = -1 then len(s) >= 2.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_13 (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_neg : r.val = -1) :
    2 ≤ s.length := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (r : Std.I64)
    (h_r : Aegis.FirstUniqChar.first_uniq_char s = ok r) (h_neg : r.val = -1), 2 ≤ s.length) := by
  sorry

/-- Whenever first_uniq_char(s) returns a successful result r and first_uniq_char(t) returns a successful result r', we have r = r'.
  Preconditions: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Also f is a bijection of the set {97, ..., 122} onto itself, and t is a slice with len(t) = len(s) and t[i] = f(s[i]) for every i with 0 <= i < len(s). -/
theorem spec_14 (s t : Slice Std.U8) (f : Std.U8 → Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (h_bij : IsLowerBij f)
    (h_len_t : t.length = s.length)
    (h_map : ∀ i, i < s.length → t.val[i]? = (s.val[i]?).map f) :
    ∀ r r' : Std.I64,
      Aegis.FirstUniqChar.first_uniq_char s = ok r →
        Aegis.FirstUniqChar.first_uniq_char t = ok r' → r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s t : Slice Std.U8) (f : Std.U8 → Std.U8) (h_len_lo : 1 ≤ s.length)
    (h_len_hi : s.length ≤ 100000) (h_lower : AllLower s) (h_bij : IsLowerBij f)
    (h_len_t : t.length = s.length)
    (h_map : ∀ i, i < s.length → t.val[i]? = (s.val[i]?).map f), ∀ r r' : Std.I64,
      Aegis.FirstUniqChar.first_uniq_char s = ok r →
        Aegis.FirstUniqChar.first_uniq_char t = ok r' → r = r') := by
  sorry

end AegisSpec.FirstUniqChar
