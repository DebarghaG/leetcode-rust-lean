import Aegis.IsPalindrome.Code.Funs

/-!
# Specifications of `Aegis.IsPalindrome.is_palindrome`

LeetCode problem `valid-palindrome`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsPalindrome

def IsAlnum (b : Std.U8) : Prop :=
  (48 ≤ b.val ∧ b.val ≤ 57) ∨ (65 ≤ b.val ∧ b.val ≤ 90) ∨ (97 ≤ b.val ∧ b.val ≤ 122)

def isAlnum (b : Std.U8) : Bool :=
  (48 ≤ b.val && b.val ≤ 57) || (65 ≤ b.val && b.val ≤ 90) || (97 ≤ b.val && b.val ≤ 122)

def low (b : Std.U8) : Nat :=
  if 65 ≤ b.val ∧ b.val ≤ 90 then b.val + 32 else b.val

def T (s : Slice Std.U8) : List Nat :=
  (s.val.filter isAlnum).map low

def PrintableASCII (s : Slice Std.U8) : Prop :=
  ∀ b ∈ s.val, 32 ≤ b.val ∧ b.val ≤ 126

def AgreesUpToCase (a c : Nat) : Prop :=
  a = c ∨
    (((65 ≤ a ∧ a ≤ 90) ∨ (97 ≤ a ∧ a ≤ 122)) ∧
      ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) ∧
      (a + 32 = c ∨ c + 32 = a))

def alnumSeq (s : Slice Std.U8) : List Std.U8 :=
  s.val.filter isAlnum

def NonAlnumEdits (s t : Slice Std.U8) : Prop :=
  alnumSeq s = alnumSeq t

/-- Define T(s) to be the byte sequence obtained from s by scanning s from left to right, keeping exactly those bytes b that are alphanumeric (i.e., 48 <= b <= 57, or 65 <= b <= 90, or 97 <= b <= 122), and replacing each kept byte b by low(b), where low(b) = b + 32 if 65 <= b <= 90, and low(b) = b otherwise. The function returns a result r (it does not fail), and r = true if and only if T(s) is a palindrome, meaning T(s) = reverse(T(s)), where reverse is the sequence reversal. Equivalently, r = true iff for every i with 0 <= i < floor(len(T(s))/2), T(s)[i] = T(s)[len(T(s))-1-i].
  Preconditions: 1 <= len(s) <= 200000, and for every i with 0 <= i < len(s), 32 <= s[i] <= 126 (s is printable ASCII). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s) :
    ∃ r : Bool,
      Aegis.IsPalindrome.is_palindrome s = ok r ∧ (r = true ↔ T s = (T s).reverse) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s), ∃ r : Bool,
      Aegis.IsPalindrome.is_palindrome s = ok r ∧ (r = true ↔ T s = (T s).reverse)) := by
  sorry

/-- For every input s satisfying the preconditions, the function returns a Bool result; it never fails, panics, overflows, or indexes out of bounds.
  Preconditions: 1 <= len(s) <= 200000, and for every i with 0 <= i < len(s), 32 <= s[i] <= 126 (s is printable ASCII). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s) :
    ∃ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s), ∃ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r) := by
  sorry

/-- Let T be defined as in spec_1. If T(s) = T(t), then the result of the function on s equals the result of the function on t.
  Preconditions: For byte slices s and t, each satisfying 1 <= len <= 200000 and printable ASCII. -/
theorem spec_3 (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 200000)
    (ht_print : PrintableASCII t)
    (hT : T s = T t) :
    Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 200000)
    (ht_print : PrintableASCII t)
    (hT : T s = T t), Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t) := by
  sorry

/-- The result of the function on s equals the result of the function on s'.
  Preconditions: s is a printable ASCII byte slice with 1 <= len(s) <= 200000. s' is any printable ASCII byte slice of the same length such that for every i with 0 <= i < len(s), either s'[i] = s[i], or both s[i] and s'[i] are ASCII letters and one is the uppercase form of the other (i.e., they differ by exactly 32 in the letter ranges). -/
theorem spec_4 (s s' : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (hs'_print : PrintableASCII s')
    (hlen : s'.val.length = s.val.length)
    (hcase : ∀ (i : Nat) (hi : i < s.val.length) (hi' : i < s'.val.length),
      AgreesUpToCase (s.val.get ⟨i, hi⟩).val (s'.val.get ⟨i, hi'⟩).val) :
    Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome s' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s s' : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (hs'_print : PrintableASCII s')
    (hlen : s'.val.length = s.val.length)
    (hcase : ∀ (i : Nat) (hi : i < s.val.length) (hi' : i < s'.val.length),
      AgreesUpToCase (s.val.get ⟨i, hi⟩).val (s'.val.get ⟨i, hi'⟩).val), Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome s') := by
  sorry

/-- Let rev(s) be the byte slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for all i with 0 <= i < len(s). Then the result of the function on s equals the result of the function on rev(s).
  Preconditions: s is a printable ASCII byte slice with 1 <= len(s) <= 200000. -/
theorem spec_5 (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (hrev : t.val = s.val.reverse) :
    Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (hrev : t.val = s.val.reverse), Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t) := by
  sorry

/-- The result of the function on s equals the result of the function on t.
  Preconditions: s and t are printable ASCII byte slices with lengths in [1, 200000], and t is obtained from s by inserting or deleting zero or more bytes that are not alphanumeric. -/
theorem spec_6 (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 200000)
    (ht_print : PrintableASCII t)
    (hedit : NonAlnumEdits s t) :
    Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice Std.U8)
    (hs_lo : 1 ≤ s.val.length) (hs_hi : s.val.length ≤ 200000)
    (hs_print : PrintableASCII s)
    (ht_lo : 1 ≤ t.val.length) (ht_hi : t.val.length ≤ 200000)
    (ht_print : PrintableASCII t)
    (hedit : NonAlnumEdits s t), Aegis.IsPalindrome.is_palindrome s = Aegis.IsPalindrome.is_palindrome t) := by
  sorry

/-- The function returns a result r and r = true.
  Preconditions: s is printable ASCII, 1 <= len(s) <= 200000, and s is a palindrome as raw bytes: for every i with 0 <= i < len(s), s[i] = s[len(s)-1-i]. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s)
    (hpal : s.val = s.val.reverse) :
    ∃ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r ∧ r = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s)
    (hpal : s.val = s.val.reverse), ∃ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r ∧ r = true) := by
  sorry

/-- Whenever the function returns a result r, if r = true then low(s[i0]) = low(s[i1]), where low is defined as in spec_1.
  Preconditions: s is printable ASCII, 1 <= len(s) <= 200000, and s contains at least one alphanumeric byte. Let i0 be the smallest index with an alphanumeric byte, and i1 the largest such index. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s)
    (halnum : ∃ (i : Nat) (hi : i < s.val.length), IsAlnum (s.val.get ⟨i, hi⟩)) :
    ∀ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r → r = true →
      ∀ (i0 i1 : Nat) (h0 : i0 < s.val.length) (h1 : i1 < s.val.length),
        IsAlnum (s.val.get ⟨i0, h0⟩) →
        IsAlnum (s.val.get ⟨i1, h1⟩) →
        (∀ (j : Nat) (hj : j < s.val.length), j < i0 → ¬ IsAlnum (s.val.get ⟨j, hj⟩)) →
        (∀ (j : Nat) (hj : j < s.val.length), i1 < j → ¬ IsAlnum (s.val.get ⟨j, hj⟩)) →
        low (s.val.get ⟨i0, h0⟩) = low (s.val.get ⟨i1, h1⟩) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s)
    (halnum : ∃ (i : Nat) (hi : i < s.val.length), IsAlnum (s.val.get ⟨i, hi⟩)), ∀ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r → r = true →
      ∀ (i0 i1 : Nat) (h0 : i0 < s.val.length) (h1 : i1 < s.val.length),
        IsAlnum (s.val.get ⟨i0, h0⟩) →
        IsAlnum (s.val.get ⟨i1, h1⟩) →
        (∀ (j : Nat) (hj : j < s.val.length), j < i0 → ¬ IsAlnum (s.val.get ⟨j, hj⟩)) →
        (∀ (j : Nat) (hj : j < s.val.length), i1 < j → ¬ IsAlnum (s.val.get ⟨j, hj⟩)) →
        low (s.val.get ⟨i0, h0⟩) = low (s.val.get ⟨i1, h1⟩)) := by
  sorry

/-- Whenever the function returns a result r, r = false if and only if there exists an index k with 0 <= k < floor(len(T(s))/2) such that T(s)[k] != T(s)[len(T(s))-1-k].
  Preconditions: s is printable ASCII, 1 <= len(s) <= 200000. Let T(s) be as defined in spec_1. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s) :
    ∀ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r →
      (r = false ↔ ∃ k : Nat, k < (T s).length / 2 ∧
        (T s)[k]? ≠ (T s)[(T s).length - 1 - k]?) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 200000)
    (hprint : PrintableASCII s), ∀ r : Bool, Aegis.IsPalindrome.is_palindrome s = ok r →
      (r = false ↔ ∃ k : Nat, k < (T s).length / 2 ∧
        (T s)[k]? ≠ (T s)[(T s).length - 1 - k]?)) := by
  sorry

end AegisSpec.IsPalindrome
