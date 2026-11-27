import Aegis.MaxSubstringLength.Code.Funs

/-!
# Specifications of `Aegis.MaxSubstringLength.max_substring_length`

LeetCode problem `find-longest-self-contained-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxSubstringLength

  namespace AegisSpec.MaxSubstringLength

  def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ :=
    match s.val[i]? with
    | some b => b.val
    | none => 0

  def byteAtInt (s : Slice Std.U8) (i : ℤ) : ℕ := byteAt s i.toNat

  def countByte (s : Slice Std.U8) (c : ℕ) : ℕ :=
    s.val.countP fun b => b.val == c

  def Admissible (s : Slice Std.U8) (l e : ℤ) : Prop :=
    0 ≤ l ∧ l < e ∧ e ≤ (s.val.length : ℤ) ∧
      (0 < l ∨ e < (s.val.length : ℤ)) ∧
        ∀ i j : ℤ, l ≤ i → i < e →
          ((0 ≤ j ∧ j < l) ∨ (e ≤ j ∧ j < (s.val.length : ℤ))) →
            byteAtInt s i ≠ byteAtInt s j

  def IsMaxAdmissibleLen (s : Slice Std.U8) (d : ℤ) : Prop :=
    (∃ l e : ℤ, Admissible s l e ∧ d = e - l) ∧
      ∀ l e : ℤ, Admissible s l e → e - l ≤ d

  /-- Call an interval (l,e) admissible when 0 <= l < e <= n, (l > 0 or e < n), and for every i and j with l <= i < e and (0 <= j < l or e <= j < n), s[i] != s[j]. Whenever max_substring_length(s) returns a result res, if some admissible interval exists then res = max { e - l | (l,e) is admissible }, and if no admissible interval exists then res = -1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_1 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r →
        (((∃ l e : ℤ, Admissible s l e) → IsMaxAdmissibleLen s r.val) ∧
          ((¬ ∃ l e : ℤ, Admissible s l e) → r.val = -1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r →
          (((∃ l e : ℤ, Admissible s l e) → IsMaxAdmissibleLen s r.val) ∧
            ((¬ ∃ l e : ℤ, Admissible s l e) → r.val = -1))) := by
    sorry

  /-- For every input satisfying the preconditions, max_substring_length(s) returns a result res; it does not fail by integer overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_2 (s : Slice Std.U8)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : Std.I64, max_substring_length s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Std.I64, max_substring_length s = ok r) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, either res = -1 or 1 <= res <= n - 1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_3 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r →
        (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r →
          (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1))) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, res = -1 if and only if there are no integers l and e such that 0 <= l < e <= n, (l > 0 or e < n), and for every i and j with l <= i < e and (0 <= j < l or e <= j < n), s[i] != s[j].
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_4 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r →
        (r.val = -1 ↔ ¬ ∃ l e : ℤ, Admissible s l e) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r →
          (r.val = -1 ↔ ¬ ∃ l e : ℤ, Admissible s l e)) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res with res >= 0, there exist integers l and e such that 0 <= l < e <= n, e - l = res, (l > 0 or e < n), and for every i and j with l <= i < e and (0 <= j < l or e <= j < n), s[i] != s[j].
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_5 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r → 0 ≤ r.val →
        ∃ l e : ℤ, Admissible s l e ∧ e - l = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r → 0 ≤ r.val →
          ∃ l e : ℤ, Admissible s l e ∧ e - l = r.val) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res with res >= 0, for every pair of integers l and e satisfying 0 <= l < e <= n, (l > 0 or e < n), and for every i and j with l <= i < e and (0 <= j < l or e <= j < n), s[i] != s[j], it holds that e - l <= res.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_6 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r → 0 ≤ r.val →
        ∀ l e : ℤ, Admissible s l e → e - l ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r → 0 ≤ r.val →
          ∀ l e : ℤ, Admissible s l e → e - l ≤ r.val) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, res = -1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). In addition, for every i with 0 <= i < n, s[i] = s[0]. -/
  theorem spec_7 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_const : ∀ i : ℕ, i < s.val.length → byteAt s i = byteAt s 0) :
      max_substring_length s = ok r → r.val = -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_const : ∀ i : ℕ, i < s.val.length → byteAt s i = byteAt s 0), max_substring_length s = ok r → r.val = -1) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, res >= 1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). In addition, there exists a byte c such that exactly one index i with 0 <= i < n satisfies s[i] = c. -/
  theorem spec_8 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_unique : ∃ c : ℕ, countByte s c = 1) :
      max_substring_length s = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_unique : ∃ c : ℕ, countByte s c = 1), max_substring_length s = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res with res = 1, there exists a byte c such that exactly one index i with 0 <= i < n satisfies s[i] = c.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_9 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r → r.val = 1 → ∃ c : ℕ, countByte s c = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r → r.val = 1 → ∃ c : ℕ, countByte s c = 1) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, res = n - 1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). In addition, for every i with 0 <= i < n - 1, s[i] != s[n - 1]. -/
  theorem spec_10 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_last : ∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (s.val.length - 1)) :
      max_substring_length s = ok r → r.val = (s.val.length : ℤ) - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_last : ∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (s.val.length - 1)), max_substring_length s = ok r → r.val = (s.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res with res = n - 1, either (for every i with 0 <= i < n - 1, s[i] != s[n - 1]) or (for every i with 1 <= i < n, s[i] != s[0]).
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_11 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      max_substring_length s = ok r → r.val = (s.val.length : ℤ) - 1 →
        ((∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (s.val.length - 1)) ∨
          (∀ i : ℕ, 1 ≤ i → i < s.val.length → byteAt s i ≠ byteAt s 0)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), max_substring_length s = ok r → r.val = (s.val.length : ℤ) - 1 →
          ((∀ i : ℕ, i < s.val.length - 1 → byteAt s i ≠ byteAt s (s.val.length - 1)) ∨
            (∀ i : ℕ, 1 ≤ i → i < s.val.length → byteAt s i ≠ byteAt s 0))) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, if s[0] = s[1] then res = -1, and if s[0] != s[1] then res = 1.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). In addition, n = 2. -/
  theorem spec_12 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_n : s.val.length = 2) :
      max_substring_length s = ok r →
        ((byteAt s 0 = byteAt s 1 → r.val = -1) ∧
          (byteAt s 0 ≠ byteAt s 1 → r.val = 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_n : s.val.length = 2), max_substring_length s = ok r →
          ((byteAt s 0 = byteAt s 1 → r.val = -1) ∧
            (byteAt s 0 ≠ byteAt s 1 → r.val = 1))) := by
    sorry

  /-- Whenever max_substring_length(s) returns a result res, either res = -1 or (2 <= res <= n - 2).
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). In addition, for every byte c, the number of indices i with 0 <= i < n and s[i] = c is not equal to 1. -/
  theorem spec_13 (s : Slice Std.U8) (r : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_no_single : ∀ c : ℕ, countByte s c ≠ 1) :
      max_substring_length s = ok r →
        (r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 2)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (r : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_no_single : ∀ c : ℕ, countByte s c ≠ 1), max_substring_length s = ok r →
          (r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 2))) := by
    sorry

  /-- Let rev be the byte slice of length n defined by rev[i] = s[n - 1 - i] for every 0 <= i < n. Whenever max_substring_length(s) returns a result res and max_substring_length(rev) returns a result res_rev, res = res_rev.
    Preconditions: Let n = len(s). The slice s represents a string of length n with 2 <= n <= 50000, and every byte s[i] for 0 <= i < n is an ASCII lowercase letter (97 <= s[i] <= 122). -/
  theorem spec_14 (s rev : Slice Std.U8) (r r_rev : Std.I64)
      (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
      (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_rev : rev.val = s.val.reverse) :
      max_substring_length s = ok r → max_substring_length rev = ok r_rev →
        r.val = r_rev.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s rev : Slice Std.U8) (r r_rev : Std.I64)
        (h_len : 2 ≤ s.val.length) (h_len_max : s.val.length ≤ 50000)
        (h_bytes : ∀ i : ℕ, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_rev : rev.val = s.val.reverse), max_substring_length s = ok r → max_substring_length rev = ok r_rev →
          r.val = r_rev.val) := by
    sorry

  end AegisSpec.MaxSubstringLength
