import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-longest-special-substring-that-occurs-thrice-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumLength

def byte (s : Slice Std.U8) (i : ℕ) : ℕ :=
  ((s.val[i]?).map (fun b => b.val)).getD 0

def Occ (s : Slice Std.U8) (c : ℕ) (L : ℕ) : ℕ :=
  (List.range (s.val.length + 1 - L)).countP fun p =>
    (List.range L).all fun t => byte s (p + t) == c

def Count (s : Slice Std.U8) (c : ℕ) : ℕ :=
  s.val.countP fun b => b.val == c

def IsSpecial (s : Slice Std.U8) (L : ℕ) : Prop :=
  1 ≤ L ∧ L ≤ s.val.length ∧ ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Occ s c L

noncomputable def maxSpecialLength (s : Slice Std.U8) : ℕ :=
  @Nat.findGreatest (IsSpecial s) (fun L => Classical.propDecidable (IsSpecial s L))
    s.val.length

/-- For every lowercase ASCII byte c (97 <= c <= 122) and integer L with 1 <= L <= len(s), define Occ(c,L) to be the number of indices p such that 0 <= p <= len(s)-L and s[p+t] = c for every t with 0 <= t < L. Let S = { L | 1 <= L <= len(s) and there exists a lowercase ASCII byte c with Occ(c,L) >= 3 }. The function returns a result r and: if S is nonempty, then r = max S; if S is empty, then r = -1. Occurrences are counted by distinct start indices p, so overlapping occurrences are allowed, and substrings are non-empty.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), the byte s[i] is an ASCII lowercase English letter, i.e. 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r ∧
      ((∃ L, IsSpecial s L) → r.val = (maxSpecialLength s : ℤ)) ∧
      ((∀ L, ¬ IsSpecial s L) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r ∧
      ((∃ L, IsSpecial s L) → r.val = (maxSpecialLength s : ℤ)) ∧
      ((∀ L, ¬ IsSpecial s L) → r.val = -1)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(s)-2.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 2) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 2)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists a lowercase ASCII byte c (97 <= c <= 122) such that Occ(c,r) >= 3, where Occ(c,L) is the number of indices p with 0 <= p <= len(s)-L and s[p+t] = c for every t with 0 <= t < L. Equivalently, the all-c substring of length r occurs at least three times in s.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 0 < r.val →
      ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Occ s c r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 0 < r.val →
      ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Occ s c r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every integer L with 1 <= L <= len(s) and L > r, and for every lowercase ASCII byte c (97 <= c <= 122), Occ(c,L) < 3, where Occ(c,L) is the number of indices p with 0 <= p <= len(s)-L and s[p+t] = c for every t with 0 <= t < L. Thus no special substring longer than r occurs at least three times; when r = -1 this says no non-empty special substring occurs at least three times.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length → r.val < (L : ℤ) →
        ∀ c, 97 ≤ c → c ≤ 122 → Occ s c L < 3 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length → r.val < (L : ℤ) →
        ∀ c, 97 ≤ c → c ≤ 122 → Occ s c L < 3) := by
  sorry

/-- Whenever the function returns a result r, for every integer L with 1 <= L <= len(s) and every lowercase ASCII byte c (97 <= c <= 122), if Occ(c,L) >= 3, where Occ(c,L) is the number of indices p with 0 <= p <= len(s)-L and s[p+t] = c for every t with 0 <= t < L, then r >= L. Equivalently, r is at least the length of every special substring that occurs at least three times.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length → ∀ c, 97 ≤ c → c ≤ 122 →
        3 ≤ Occ s c L → (L : ℤ) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length → ∀ c, 97 ≤ c → c ≤ 122 →
        3 ≤ Occ s c L → (L : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 1, for every integer L with 1 <= L <= r there exists a lowercase ASCII byte c (97 <= c <= 122) such that the all-c substring of length L occurs at least three times in s, i.e. Occ(c,L) >= 3 for the start-index count Occ.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 1 ≤ r.val →
      ∀ L : ℕ, 1 ≤ L → (L : ℤ) ≤ r.val →
        ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Occ s c L := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 1 ≤ r.val →
      ∀ L : ℕ, 1 ≤ L → (L : ℤ) ≤ r.val →
        ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Occ s c L) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every lowercase ASCII byte c (97 <= c <= 122), the number of indices i with 0 <= i < len(s) and s[i] = c is at most 2. Equivalently, the answer is -1 exactly when no character occurs three or more times in s.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (r.val = -1 ↔ ∀ c, 97 ≤ c → c ≤ 122 → Count s c ≤ 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (r.val = -1 ↔ ∀ c, 97 ≤ c → c ≤ 122 → Count s c ≤ 2)) := by
  sorry

/-- Whenever the function returns a result r with r >= 1, for every lowercase ASCII byte c (97 <= c <= 122) such that Occ(c,r) >= 3, where Occ(c,L) is the number of indices p with 0 <= p <= len(s)-L and s[p+t] = c for every t with 0 <= t < L, the number of indices i with 0 <= i < len(s) and s[i] = c is at least r+2.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 1 ≤ r.val →
      ∀ c, 97 ≤ c → c ≤ 122 → 3 ≤ Occ s c r.val.toNat →
        r.val + 2 ≤ (Count s c : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r → 1 ≤ r.val →
      ∀ c, 97 ≤ c → c ≤ 122 → 3 ≤ Occ s c r.val.toNat →
        r.val + 2 ≤ (Count s c : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every interval [a,b) with 0 <= a < b <= len(s), if b-a >= 3 and s[i] = s[a] for every i with a <= i < b, then r >= (b-a)-2.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ a b : ℕ, a < b → b ≤ s.val.length → 3 ≤ b - a →
        (∀ i, a ≤ i → i < b → byte s i = byte s a) →
          ((b - a : ℕ) : ℤ) - 2 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      ∀ a b : ℕ, a < b → b ≤ s.val.length → 3 ≤ b - a →
        (∀ i, a ≤ i → i < b → byte s i = byte s a) →
          ((b - a : ℕ) : ℤ) - 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if both of the following hold: (1) there exists a lowercase ASCII byte c (97 <= c <= 122) with at least three indices i such that s[i] = c; and (2) for every lowercase ASCII byte c (97 <= c <= 122), Occ(c,2) < 3, where Occ(c,2) is the number of indices p with 0 <= p <= len(s)-2 and s[p] = s[p+1] = c.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (r.val = 1 ↔ (∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Count s c) ∧
        (∀ c, 97 ≤ c → c ≤ 122 → Occ s c 2 < 3)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (r.val = 1 ↔ (∃ c, 97 ≤ c ∧ c ≤ 122 ∧ 3 ≤ Count s c) ∧
        (∀ c, 97 ≤ c → c ≤ 122 → Occ s c 2 < 3))) := by
  sorry

/-- Whenever the function returns a result r, if all bytes of s are equal to each other, i.e. s[i] = s[0] for every i with 0 <= i < len(s), then r = len(s)-2.
  Preconditions: 3 <= len(s) <= 50 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (∀ i, i < s.val.length → byte s i = byte s 0) →
        r.val = (s.val.length : ℤ) - 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (h3 : 3 ≤ s.val.length) (h50 : s.val.length ≤ 50)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length s = ok r →
      (∀ i, i < s.val.length → byte s i = byte s 0) →
        r.val = (s.val.length : ℤ) - 2) := by
  sorry

end AegisSpec.MaximumLength
