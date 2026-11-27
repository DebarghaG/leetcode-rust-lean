import Aegis.LongestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindrome.longest_palindrome`

LeetCode problem `maximize-palindrome-length-from-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestPalindrome

  open Aegis

  def IsSubseq (t s : List Std.U8) : Prop :=
    ∃ f : Fin t.length → Fin s.length,
      StrictMono f ∧ ∀ j : Fin t.length, t.get j = s.get (f j)

  def IsPalindrome (p : List Std.U8) : Prop :=
    ∀ (j : ℕ) (hj : j < p.length),
      p.get ⟨j, hj⟩ = p.get ⟨p.length - 1 - j, by omega⟩

  def OccursIn (c : Std.U8) (s : List Std.U8) : Prop :=
    ∃ i : Fin s.length, s.get i = c

  def countByte (s : List Std.U8) (c : Std.U8) : ℕ :=
    match s with
    | [] => 0
    | x :: xs => (if x = c then 1 else 0) + countByte xs c

  def reverseSlice (s : Slice Std.U8) : Slice Std.U8 :=
    Slice.mk s.val.reverse.length (Aeneas.Data.ListN.ListN.fromList s.val.reverse) (by
      have hlen : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
      have hrev : s.val.reverse.length = s.val.length := List.length_reverse
      rw [hrev, hlen]
      exact s.bound)

  def IsLowercaseASCII (w : Slice Std.U8) : Prop :=
    ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122

  def ValidInput (w : Slice Std.U8) : Prop :=
    1 ≤ w.val.length ∧ w.val.length ≤ 1000 ∧ IsLowercaseASCII w

  def IsGreatestPalSubseqLen (w : List Std.U8) (L : ℕ) : Prop :=
    (∃ p : List Std.U8, IsSubseq p w ∧ IsPalindrome p ∧ p.length = L) ∧
      ∀ p : List Std.U8, IsSubseq p w → IsPalindrome p → p.length ≤ L

  def UsesBothParts (w1 w2 p : List Std.U8) : Prop :=
    ∃ f : Fin p.length → Fin (w1 ++ w2).length,
      StrictMono f ∧ (∀ j : Fin p.length, p.get j = (w1 ++ w2).get (f j)) ∧
        (∃ j : Fin p.length, (f j).val < w1.length) ∧
          (∃ j : Fin p.length, w1.length ≤ (f j).val)

  /-- The function returns a result r and r is exactly the maximum, over all byte sequences a and b with len(a) >= 1, len(b) >= 1, a a subsequence of word1, b a subsequence of word2, and a++b a palindrome, of len(a)+len(b); if there are no such sequences a and b, then r = 0. Here a subsequence of s means a sequence obtainable from s by deleting zero or more bytes without changing order (equivalently, there are indices 0 <= i_0 < i_1 < ... < i_{len(t)-1} < len(s) with t[j] = s[i_j] for all j), ++ denotes concatenation, and a byte sequence p is a palindrome if for every j with 0 <= j < len(p), p[j] = p[len(p)-1-j].
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122 (lowercase English letters). All positions mentioned are 0-based. -/
  theorem spec_1 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∃ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r ∧
          (∀ (a b : List Std.U8), 1 ≤ a.length → 1 ≤ b.length →
            IsSubseq a word1.val → IsSubseq b word2.val → IsPalindrome (a ++ b) →
              ((a.length + b.length : ℕ) : ℤ) ≤ r.val) ∧
            ((∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
                IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b) ∧
                  r.val = ((a.length + b.length : ℕ) : ℤ)) ∨
              (¬ (∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
                  IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b)) ∧
                r.val = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∃ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r ∧
            (∀ (a b : List Std.U8), 1 ≤ a.length → 1 ≤ b.length →
              IsSubseq a word1.val → IsSubseq b word2.val → IsPalindrome (a ++ b) →
                ((a.length + b.length : ℕ) : ℤ) ≤ r.val) ∧
              ((∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
                  IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b) ∧
                    r.val = ((a.length + b.length : ℕ) : ℤ)) ∨
                (¬ (∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
                    IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b)) ∧
                  r.val = 0))) := by
    sorry

  /-- For every input satisfying the preconditions, the function does not fail: there exists an integer r of type Std.I64 such that the function returns Ok(r).
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_2 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∃ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∃ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(word1) + len(word2).
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_3 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        0 ≤ r.val ∧ r.val ≤ (word1.val.length : ℤ) + (word2.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          0 ≤ r.val ∧ r.val ≤ (word1.val.length : ℤ) + (word2.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, either r = 0 or r >= 2; in particular, the function never returns 1.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_4 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        r.val = 0 ∨ 2 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          r.val = 0 ∨ 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exist non-empty byte sequences a and b such that a is a subsequence of word1, b is a subsequence of word2, a++b is a palindrome, and len(a)+len(b) = r.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_5 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        0 < r.val →
          ∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
            IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b) ∧
              r.val = ((a.length + b.length : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          0 < r.val →
            ∃ (a b : List Std.U8), 1 ≤ a.length ∧ 1 ≤ b.length ∧
              IsSubseq a word1.val ∧ IsSubseq b word2.val ∧ IsPalindrome (a ++ b) ∧
                r.val = ((a.length + b.length : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every non-empty byte sequence a that is a subsequence of word1 and every non-empty byte sequence b that is a subsequence of word2, if a++b is a palindrome then len(a)+len(b) <= r.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_6 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        ∀ (a b : List Std.U8), 1 ≤ a.length → 1 ≤ b.length →
          IsSubseq a word1.val → IsSubseq b word2.val → IsPalindrome (a ++ b) →
            ((a.length + b.length : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          ∀ (a b : List Std.U8), 1 ≤ a.length → 1 ≤ b.length →
            IsSubseq a word1.val → IsSubseq b word2.val → IsPalindrome (a ++ b) →
              ((a.length + b.length : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no byte value c such that c occurs in word1 and c also occurs in word2. A byte c occurs in a string s if there is an index i with 0 <= i < len(s) and s[i] = c.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_7 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        (r.val = 0 ↔ ¬ (∃ c : Std.U8, OccursIn c word1.val ∧ OccursIn c word2.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          (r.val = 0 ↔ ¬ (∃ c : Std.U8, OccursIn c word1.val ∧ OccursIn c word2.val))) := by
    sorry

  /-- Whenever the function returns a result r, for every byte value c that occurs in both word1 and word2, r >= count(word1,c) + count(word2,c), where count(s,c) is the number of indices i with 0 <= i < len(s) and s[i] = c.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_8 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        ∀ c : Std.U8, OccursIn c word1.val → OccursIn c word2.val →
          ((countByte word1.val c + countByte word2.val c : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          ∀ c : Std.U8, OccursIn c word1.val → OccursIn c word2.val →
            ((countByte word1.val c + countByte word2.val c : ℕ) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(word1) + len(word2) if and only if word1++word2 is a palindrome, where word1++word2 is the concatenation of the two byte strings.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_9 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        (r.val = ((word1.val.length + word2.val.length : ℕ) : ℤ) ↔
          IsPalindrome (word1.val ++ word2.val)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          (r.val = ((word1.val.length + word2.val.length : ℕ) : ℤ) ↔
            IsPalindrome (word1.val ++ word2.val))) := by
    sorry

  /-- Whenever the function returns a result r, r is at most L, where L is the greatest length of a possibly empty palindrome that is a subsequence of the concatenated byte string word1++word2.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_10 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        ∀ L : ℕ, IsGreatestPalSubseqLen (word1.val ++ word2.val) L → r.val ≤ (L : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          ∀ L : ℕ, IsGreatestPalSubseqLen (word1.val ++ word2.val) L → r.val ≤ (L : ℤ)) := by
    sorry

  /-- For every pair of non-empty byte strings u1 and u2 satisfying the same length and lowercase constraints as word1 and word2, if u1 is a subsequence of word1 and u2 is a subsequence of word2, then whenever longest_palindrome(u1,u2) returns r' and longest_palindrome(word1,word2) returns r, one has r' <= r.
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_11 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ (u1 u2 : Slice Std.U8), ValidInput u1 → ValidInput u2 →
        IsSubseq u1.val word1.val → IsSubseq u2.val word2.val →
          ∀ r r' : Std.I64,
            Aegis.LongestPalindrome.longest_palindrome u1 u2 = ok r' →
            Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r → r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ (u1 u2 : Slice Std.U8), ValidInput u1 → ValidInput u2 →
          IsSubseq u1.val word1.val → IsSubseq u2.val word2.val →
            ∀ r r' : Std.I64,
              Aegis.LongestPalindrome.longest_palindrome u1 u2 = ok r' →
              Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r → r'.val ≤ r.val) := by
    sorry

  /-- Whenever longest_palindrome(word1,word2) returns r and longest_palindrome(reverse(word2),reverse(word1)) returns r', we have r = r'. Here reverse(s) is the byte string of length len(s) whose i-th byte is s[len(s)-1-i].
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122. -/
  theorem spec_12 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r r' : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        Aegis.LongestPalindrome.longest_palindrome (reverseSlice word2) (reverseSlice word1) =
          ok r' →
        r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r r' : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          Aegis.LongestPalindrome.longest_palindrome (reverseSlice word2) (reverseSlice word1) =
            ok r' →
          r = r') := by
    sorry

  /-- The function returns a result r and r is exactly the maximum, over all byte sequences p such that p is a palindrome, p is a subsequence of word1++word2, and p uses at least one byte from word1 and at least one byte from word2, of len(p); if no such p exists, then r = 0. Here p uses a byte from word1 if some selected index is < len(word1), and from word2 if some selected index is >= len(word1).
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122 (lowercase English letters). All positions mentioned are 0-based. -/
  theorem spec_13 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∃ r : Std.I64,
        Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r ∧
          (∀ p : List Std.U8, IsPalindrome p → UsesBothParts word1.val word2.val p →
            (p.length : ℤ) ≤ r.val) ∧
            ((∃ p : List Std.U8, IsPalindrome p ∧ UsesBothParts word1.val word2.val p ∧
                r.val = (p.length : ℤ)) ∨
              (¬ (∃ p : List Std.U8, IsPalindrome p ∧ UsesBothParts word1.val word2.val p) ∧
                r.val = 0)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∃ r : Std.I64,
          Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r ∧
            (∀ p : List Std.U8, IsPalindrome p → UsesBothParts word1.val word2.val p →
              (p.length : ℤ) ≤ r.val) ∧
              ((∃ p : List Std.U8, IsPalindrome p ∧ UsesBothParts word1.val word2.val p ∧
                  r.val = (p.length : ℤ)) ∨
                (¬ (∃ p : List Std.U8, IsPalindrome p ∧ UsesBothParts word1.val word2.val p) ∧
                  r.val = 0))) := by
    sorry

  /-- Whenever the function returns a result r, for every non-empty byte sequence z that is a palindrome and is a subsequence of both word1 and word2, r >= 2*len(z).
    Preconditions: word1 and word2 are byte slices (ASCII strings) with 1 <= len(word1) <= 1000 and 1 <= len(word2) <= 1000, and every byte of word1 and word2 lies in the inclusive range 97 through 122 (lowercase English letters). All positions mentioned are 0-based. -/
  theorem spec_14 (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2) :
      ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
        ∀ z : List Std.U8, 1 ≤ z.length → IsPalindrome z →
          IsSubseq z word1.val → IsSubseq z word2.val → ((2 * z.length : ℕ) : ℤ) ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (word1 word2 : Slice Std.U8) (h1 : ValidInput word1) (h2 : ValidInput word2), ∀ r : Std.I64, Aegis.LongestPalindrome.longest_palindrome word1 word2 = ok r →
          ∀ z : List Std.U8, 1 ≤ z.length → IsPalindrome z →
            IsSubseq z word1.val → IsSubseq z word2.val → ((2 * z.length : ℕ) : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.LongestPalindrome
