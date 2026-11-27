import Aegis.LongestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindrome.longest_palindrome`

LeetCode problem `longest-palindrome-by-concatenating-two-letter-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestPalindrome (longest_palindrome)

namespace AegisSpec.LongestPalindrome

def wordByte (w : List ℕ) (j : ℕ) : ℕ := w.getD j 0

def wordBytes (w : alloc.vec.Vec Std.U8) : List ℕ :=
  w.slice.list.toList.map (fun b => b.val)

def wordsList (ws : Slice (alloc.vec.Vec Std.U8)) : List (List ℕ) :=
  ws.list.toList.map wordBytes

def len (ws : Slice (alloc.vec.Vec Std.U8)) : ℕ := (wordsList ws).length

def wordAt (ws : Slice (alloc.vec.Vec Std.U8)) (i : ℕ) : List ℕ := (wordsList ws).getD i []

def byteAt (ws : Slice (alloc.vec.Vec Std.U8)) (i j : ℕ) : ℕ := wordByte (wordAt ws i) j

def LowerByte (x : ℕ) : Prop := 97 ≤ x ∧ x ≤ 122

def IsPalindrome (l : List ℕ) : Prop := l.reverse = l

def letters : Finset ℕ := Finset.Icc 97 122

def count (ws : Slice (alloc.vec.Vec Std.U8)) (a b : ℕ) : ℕ :=
  ((wordsList ws).filter (fun w => wordByte w 0 = a ∧ wordByte w 1 = b)).length

def diagSum (ws : Slice (alloc.vec.Vec Std.U8)) : ℕ := ∑ a ∈ letters, count ws a a

def oddCount (ws : Slice (alloc.vec.Vec Std.U8)) : ℕ := ∑ a ∈ letters, count ws a a % 2

def pairSum (ws : Slice (alloc.vec.Vec Std.U8)) : ℕ :=
  ∑ a ∈ letters, ∑ b ∈ letters, if a < b then min (count ws a b) (count ws b a) else 0

def ValidInput (ws : Slice (alloc.vec.Vec Std.U8)) : Prop :=
  1 ≤ len ws ∧ len ws ≤ 100000 ∧
    ∀ i : ℕ, i < len ws →
      (wordAt ws i).length = 2 ∧ LowerByte (byteAt ws i 0) ∧ LowerByte (byteAt ws i 1)

/-- Let c(a,b) be the number of indices i with 0 <= i < len(words), words[i][0] = a, and words[i][1] = b, for a,b in 97..122. Let S = sum over a in 97..122 of c(a,a). Let O be the number of letters a in 97..122 for which c(a,a) is odd. Let P = sum over 97 <= a < b <= 122 of min(c(a,b), c(b,a)). The function returns a result r and r = 4*P + 2*(S - max(0, O - 1)).
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_1 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      r.val = 4 * (pairSum ws : ℤ)
        + 2 * ((diagSum ws : ℤ) - max 0 ((oddCount ws : ℤ) - 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      r.val = 4 * (pairSum ws : ℤ)
        + 2 * ((diagSum ws : ℤ) - max 0 ((oddCount ws : ℤ) - 1))) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, read outside a word, or overflow 64-bit arithmetic.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_2 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∃ r : Std.I64, longest_palindrome ws = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∃ r : Std.I64, longest_palindrome ws = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 2 * len(words).
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_3 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      0 ≤ r.val ∧ r.val ≤ 2 * (len ws : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      0 ≤ r.val ∧ r.val ≤ 2 * (len ws : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r is even; equivalently r mod 2 = 0.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_4 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r → r.val % 2 = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r → r.val % 2 = 0) := by
  sorry

/-- The function returns a result r and r = 2 if words[0][0] = words[0][1], and r = 0 otherwise.
  Preconditions: len(words) = 1. The single word satisfies len(words[0]) = 2 and both bytes words[0][0] and words[0][1] are in 97..122. -/
theorem spec_5 (ws : Slice (alloc.vec.Vec Std.U8))
    (h1 : len ws = 1) (h2 : (wordAt ws 0).length = 2)
    (h3 : LowerByte (byteAt ws 0 0)) (h4 : LowerByte (byteAt ws 0 1)) :
    ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      (byteAt ws 0 0 = byteAt ws 0 1 → r.val = 2) ∧
      (byteAt ws 0 0 ≠ byteAt ws 0 1 → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8))
    (h1 : len ws = 1) (h2 : (wordAt ws 0).length = 2)
    (h3 : LowerByte (byteAt ws 0 0)) (h4 : LowerByte (byteAt ws 0 1)), ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      (byteAt ws 0 0 = byteAt ws 0 1 → r.val = 2) ∧
      (byteAt ws 0 0 ≠ byteAt ws 0 1 → r.val = 0)) := by
  sorry

/-- Let c(a,a) be the number of i with words[i][0] = words[i][1] = a, for a in 97..122, let S = sum over a of c(a,a), and let O be the number of a for which c(a,a) is odd. The function returns r and r = 2*(S - max(0, O - 1)).
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2, both bytes are in 97..122, and words[i][0] = words[i][1]. -/
theorem spec_6 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws)
    (hdiag : ∀ i : ℕ, i < len ws → byteAt ws i 0 = byteAt ws i 1) :
    ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      r.val = 2 * ((diagSum ws : ℤ) - max 0 ((oddCount ws : ℤ) - 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws)
    (hdiag : ∀ i : ℕ, i < len ws → byteAt ws i 0 = byteAt ws i 1), ∃ r : Std.I64, longest_palindrome ws = ok r ∧
      r.val = 2 * ((diagSum ws : ℤ) - max 0 ((oddCount ws : ℤ) - 1))) := by
  sorry

/-- Let c(a,b) count indices i with words[i][0]=a and words[i][1]=b, and let P = sum over 97 <= a < b <= 122 of min(c(a,b), c(b,a)). The function returns r and r = 4*P.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2, both bytes are in 97..122, and words[i][0] != words[i][1]. -/
theorem spec_7 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws)
    (hoff : ∀ i : ℕ, i < len ws → byteAt ws i 0 ≠ byteAt ws i 1) :
    ∃ r : Std.I64, longest_palindrome ws = ok r ∧ r.val = 4 * (pairSum ws : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws)
    (hoff : ∀ i : ℕ, i < len ws → byteAt ws i 0 ≠ byteAt ws i 1), ∃ r : Std.I64, longest_palindrome ws = ok r ∧ r.val = 4 * (pairSum ws : ℤ)) := by
  sorry

/-- Let c(a,b) be the number of indices i with words[i][0]=a and words[i][1]=b. Whenever the function returns a result r, r = 0 if and only if both: (1) c(a,a) = 0 for every a in 97..122; and (2) for every 97 <= a < b <= 122, min(c(a,b), c(b,a)) = 0.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_8 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      (r.val = 0 ↔
        (∀ a ∈ letters, count ws a a = 0) ∧
        (∀ a ∈ letters, ∀ b ∈ letters,
          a < b → min (count ws a b) (count ws b a) = 0)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      (r.val = 0 ↔
        (∀ a ∈ letters, count ws a a = 0) ∧
        (∀ a ∈ letters, ∀ b ∈ letters,
          a < b → min (count ws a b) (count ws b a) = 0))) := by
  sorry

/-- If longest_palindrome(words) returns r and longest_palindrome(words') returns r', then r = r'.
  Preconditions: words and words' are slices of Vec U8, each satisfying: len between 1 and 100000; each entry has length 2 with bytes in 97..122; and words' is a permutation of words as a multiset of two-byte strings. -/
theorem spec_9 (ws ws' : Slice (alloc.vec.Vec Std.U8))
    (h : ValidInput ws) (h' : ValidInput ws')
    (hperm : List.Perm (wordsList ws) (wordsList ws')) :
    ∀ r r' : Std.I64, longest_palindrome ws = ok r → longest_palindrome ws' = ok r' →
      r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ws ws' : Slice (alloc.vec.Vec Std.U8))
    (h : ValidInput ws) (h' : ValidInput ws')
    (hperm : List.Perm (wordsList ws) (wordsList ws')), ∀ r r' : Std.I64, longest_palindrome ws = ok r → longest_palindrome ws' = ok r' →
      r = r') := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k >= 0 and distinct indices i_1,...,i_k in [0, len(words)) such that r = 2*k and the byte string words[i_1] ++ words[i_2] ++ ... ++ words[i_k] is a palindrome; k = 0 is allowed, meaning the empty string.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_10 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∃ idx : List ℕ,
        idx.Nodup ∧ (∀ i ∈ idx, i < len ws) ∧
        IsPalindrome (idx.map (fun i => wordAt ws i)).flatten ∧
        r.val = 2 * (idx.length : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∃ idx : List ℕ,
        idx.Nodup ∧ (∀ i ∈ idx, i < len ws) ∧
        IsPalindrome (idx.map (fun i => wordAt ws i)).flatten ∧
        r.val = 2 * (idx.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every integer k >= 0 and every sequence of distinct indices i_1,...,i_k in [0, len(words)) such that words[i_1] ++ ... ++ words[i_k] is a palindrome, we have 2*k <= r.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_11 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ idx : List ℕ,
        idx.Nodup → (∀ i ∈ idx, i < len ws) →
        IsPalindrome (idx.map (fun i => wordAt ws i)).flatten →
        2 * (idx.length : ℤ) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ idx : List ℕ,
        idx.Nodup → (∀ i ∈ idx, i < len ws) →
        IsPalindrome (idx.map (fun i => wordAt ws i)).flatten →
        2 * (idx.length : ℤ) ≤ r.val) := by
  sorry

/-- Let c(a,b) be the number of indices i with words[i][0]=a and words[i][1]=b. Whenever the function returns a result r, for every 97 <= a < b <= 122, r >= 4 * min(c(a,b), c(b,a)).
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_12 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ a ∈ letters, ∀ b ∈ letters,
        a < b → 4 * (min (count ws a b) (count ws b a) : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ a ∈ letters, ∀ b ∈ letters,
        a < b → 4 * (min (count ws a b) (count ws b a) : ℤ) ≤ r.val) := by
  sorry

/-- Let c(a,a) be the number of indices i with 0 <= i < len(words) and words[i][0] = words[i][1] = a. Whenever the function returns a result r, for every a in 97..122, r >= 2 * c(a,a).
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_13 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ a ∈ letters, 2 * (count ws a a : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      ∀ a ∈ letters, 2 * (count ws a a : ℤ) ≤ r.val) := by
  sorry

/-- Let c(a,b) be the number of indices i with 0 <= i < len(words), words[i][0] = a, and words[i][1] = b. Let O be the number of letters a in 97..122 for which c(a,a) is odd. Whenever the function returns a result r, if O = 0 then r mod 4 = 0, and if O > 0 then r mod 4 = 2.
  Preconditions: len(words) is between 1 and 100000 inclusive. For every i with 0 <= i < len(words), len(words[i]) = 2 and both bytes words[i][0] and words[i][1] are in the range 97..122 (lowercase English letters 'a'..'z'). -/
theorem spec_14 (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws) :
    ∀ r : Std.I64, longest_palindrome ws = ok r →
      (oddCount ws = 0 → r.val % 4 = 0) ∧
      (0 < oddCount ws → r.val % 4 = 2) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (ws : Slice (alloc.vec.Vec Std.U8)) (h : ValidInput ws), ∀ r : Std.I64, longest_palindrome ws = ok r →
      (oddCount ws = 0 → r.val % 4 = 0) ∧
      (0 < oddCount ws → r.val % 4 = 2)) := by
  sorry

end AegisSpec.LongestPalindrome
