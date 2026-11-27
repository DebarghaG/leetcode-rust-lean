import Aegis.MakePalindrome.Code.Funs

/-!
# Specifications of `Aegis.MakePalindrome.make_palindrome`

LeetCode problem `valid-palindrome-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MakePalindrome

namespace AegisSpec.MakePalindrome

def len (s : Slice U8) : ℕ := s.val.length

def byteAt (s : Slice U8) (i : ℕ) : ℕ := (s.val.getD i 0#u8).val

def IsLower (s : Slice U8) : Prop :=
  ∀ i, i < len s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

abbrev MismatchAt (s : Slice U8) (i : ℕ) : Prop := byteAt s i ≠ byteAt s (len s - 1 - i)

def mismatchIndices (s : Slice U8) : Finset ℕ :=
  (Finset.range (len s / 2)).filter (MismatchAt s)

def mismatchCount (s : Slice U8) : ℕ := (mismatchIndices s).card

def IsPalindrome (s : Slice U8) : Prop :=
  ∀ i, i < len s → byteAt s i = byteAt s (len s - 1 - i)

def diffCount (s t : Slice U8) : ℕ :=
  ((Finset.range (len s)).filter (fun i => byteAt s i ≠ byteAt t i)).card

def ofBytes (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def rev (s : Slice U8) : Slice U8 :=
  ofBytes s.val.reverse (by
    rw [List.length_reverse]
    simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

def setMiddle (s : Slice U8) (c : U8) : Slice U8 :=
  ofBytes (s.val.set (len s / 2) c) (by
    rw [List.length_set]
    simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using s.bound)

@[simp] theorem rev_val (s : Slice U8) : (rev s).val = s.val.reverse := by
  simp [rev, ofBytes, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

@[simp] theorem len_rev (s : Slice U8) : len (rev s) = len s := by
  simp [len]

@[simp] theorem len_setMiddle (s : Slice U8) (c : U8) : len (setMiddle s c) = len s := by
  simp [len, setMiddle, ofBytes, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- Whenever make_palindrome(s) returns a result r, r = true if and only if the number of indices i with 0 <= i < n/2 (integer division, i.e. 0 <= i < floor(n/2)) and s[i] != s[n-1-i] is at most 2.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] for 0 <= i < n is a lowercase ASCII letter (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    ∀ (r : Bool), make_palindrome s = ok r → (r = true ↔ mismatchCount s ≤ 2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), ∀ (r : Bool), make_palindrome s = ok r → (r = true ↔ mismatchCount s ≤ 2)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_2 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    ∃ (r : Bool), make_palindrome s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), ∃ (r : Bool), make_palindrome s = ok r) := by
  sorry

/-- Whenever make_palindrome(s) returns a result r, if r = false then the number of indices i with 0 <= i < n/2 and s[i] != s[n-1-i] is at least 3.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_3 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    ∀ (r : Bool), make_palindrome s = ok r → r = false → 3 ≤ mismatchCount s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), ∀ (r : Bool), make_palindrome s = ok r → r = false → 3 ≤ mismatchCount s) := by
  sorry

/-- Let rev(s) be the byte slice of length n defined by rev(s)[i] = s[n-1-i] for all 0 <= i < n. Whenever make_palindrome(s) returns r1 and make_palindrome(rev(s)) returns r2, we have r1 = r2.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_4 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome (rev s) = ok r2 → r1 = r2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome (rev s) = ok r2 → r1 = r2) := by
  sorry

/-- For every lowercase ASCII byte c, let t be the byte slice of length n with t[n/2] = c (integer division gives the middle index) and t[i] = s[i] for all i != n/2. Whenever make_palindrome(s) returns r1 and make_palindrome(t) returns r2, we have r1 = r2.
  Preconditions: s is a byte slice with n = len(s), n is odd, 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_5 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hodd : len s % 2 = 1) (hlower : IsLower s) :
    ∀ (c : U8), 97 ≤ c.val → c.val ≤ 122 →
      ∀ (r1 r2 : Bool), make_palindrome s = ok r1 →
        make_palindrome (setMiddle s c) = ok r2 → r1 = r2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hodd : len s % 2 = 1) (hlower : IsLower s), ∀ (c : U8), 97 ≤ c.val → c.val ≤ 122 →
      ∀ (r1 r2 : Bool), make_palindrome s = ok r1 →
        make_palindrome (setMiddle s c) = ok r2 → r1 = r2) := by
  sorry

/-- Assume that for every i with 0 <= i < n/2, (s[i] = s[n-1-i]) if and only if (t[i] = t[n-1-i]). Then whenever make_palindrome(s) returns r1 and make_palindrome(t) returns r2, we have r1 = r2.
  Preconditions: s and t are byte slices with n = len(s) = len(t), 1 <= n <= 100000, and all bytes of s and t are lowercase ASCII letters. -/
theorem spec_6 (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hhalf : ∀ i, i < len s / 2 →
      (byteAt s i = byteAt s (len s - 1 - i) ↔ byteAt t i = byteAt t (len t - 1 - i))) :
    ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome t = ok r2 → r1 = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hhalf : ∀ i, i < len s / 2 →
      (byteAt s i = byteAt s (len s - 1 - i) ↔ byteAt t i = byteAt t (len t - 1 - i))), ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome t = ok r2 → r1 = r2) := by
  sorry

/-- Assume that the number of indices i with 0 <= i < n/2 and s[i] != s[n-1-i] equals the number of indices i with 0 <= i < n/2 and t[i] != t[n-1-i]. Then whenever make_palindrome(s) returns r1 and make_palindrome(t) returns r2, we have r1 = r2.
  Preconditions: s and t are byte slices with n = len(s) = len(t), 1 <= n <= 100000, and all bytes are lowercase ASCII letters. -/
theorem spec_7 (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hcount : mismatchCount s = mismatchCount t) :
    ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome t = ok r2 → r1 = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hcount : mismatchCount s = mismatchCount t), ∀ (r1 r2 : Bool), make_palindrome s = ok r1 → make_palindrome t = ok r2 → r1 = r2) := by
  sorry

/-- Whenever make_palindrome(s) returns true, there exists a byte slice t of length n such that: (a) every byte of t is a lowercase ASCII letter; (b) t is a palindrome, i.e. t[i] = t[n-1-i] for all 0 <= i < n; and (c) the number of indices i with 0 <= i < n and s[i] != t[i] is either 1 or 2.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_8 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    make_palindrome s = ok true →
      ∃ (t : Slice U8), len t = len s ∧ IsLower t ∧ IsPalindrome t ∧
        (diffCount s t = 1 ∨ diffCount s t = 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), make_palindrome s = ok true →
      ∃ (t : Slice U8), len t = len s ∧ IsLower t ∧ IsPalindrome t ∧
        (diffCount s t = 1 ∨ diffCount s t = 2)) := by
  sorry

/-- Whenever make_palindrome(s) returns false, for every byte slice t of length n such that every byte of t is a lowercase ASCII letter and t is a palindrome (t[i] = t[n-1-i] for all 0 <= i < n), the number of indices i with 0 <= i < n and s[i] != t[i] is neither 1 nor 2.
  Preconditions: s is a byte slice with n = len(s), 1 <= n <= 100000, and every byte s[i] is a lowercase ASCII letter. -/
theorem spec_9 (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s) :
    make_palindrome s = ok false →
      ∀ (t : Slice U8), len t = len s → IsLower t → IsPalindrome t →
        diffCount s t ≠ 1 ∧ diffCount s t ≠ 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (hpos : 1 ≤ len s) (hbound : len s ≤ 100000)
    (hlower : IsLower s), make_palindrome s = ok false →
      ∀ (t : Slice U8), len t = len s → IsLower t → IsPalindrome t →
        diffCount s t ≠ 1 ∧ diffCount s t ≠ 2) := by
  sorry

/-- Assume that make_palindrome(s) returns true, and that for every i with 0 <= i < n/2, if t[i] != t[n-1-i] then s[i] != s[n-1-i] (every mismatched pair of t is also a mismatched pair of s). Then whenever make_palindrome(t) returns a result r, r = true.
  Preconditions: s and t are byte slices with n = len(s) = len(t), 1 <= n <= 100000, and all bytes are lowercase ASCII letters. -/
theorem spec_10 (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hs : make_palindrome s = ok true)
    (hmono : ∀ i, i < len s / 2 →
      byteAt t i ≠ byteAt t (len t - 1 - i) → byteAt s i ≠ byteAt s (len s - 1 - i)) :
    ∀ (r : Bool), make_palindrome t = ok r → r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hs : make_palindrome s = ok true)
    (hmono : ∀ i, i < len s / 2 →
      byteAt t i ≠ byteAt t (len t - 1 - i) → byteAt s i ≠ byteAt s (len s - 1 - i)), ∀ (r : Bool), make_palindrome t = ok r → r = true) := by
  sorry

/-- Assume that make_palindrome(s) returns false, and that for every i with 0 <= i < n/2, if s[i] != s[n-1-i] then t[i] != t[n-1-i] (every mismatched pair of s is also a mismatched pair of t). Then whenever make_palindrome(t) returns a result r, r = false.
  Preconditions: s and t are byte slices with n = len(s) = len(t), 1 <= n <= 100000, and all bytes are lowercase ASCII letters. -/
theorem spec_11 (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hs : make_palindrome s = ok false)
    (hmono : ∀ i, i < len s / 2 →
      byteAt s i ≠ byteAt s (len s - 1 - i) → byteAt t i ≠ byteAt t (len t - 1 - i)) :
    ∀ (r : Bool), make_palindrome t = ok r → r = false := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8) (hpos : 1 ≤ len s) (hlen : len t = len s)
    (hbound : len s ≤ 100000) (hlowers : IsLower s) (hlowert : IsLower t)
    (hs : make_palindrome s = ok false)
    (hmono : ∀ i, i < len s / 2 →
      byteAt s i ≠ byteAt s (len s - 1 - i) → byteAt t i ≠ byteAt t (len t - 1 - i)), ∀ (r : Bool), make_palindrome t = ok r → r = false) := by
  sorry

end AegisSpec.MakePalindrome
