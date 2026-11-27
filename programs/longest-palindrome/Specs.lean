import Aegis.LongestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindrome.longest_palindrome`

LeetCode problem `longest-palindrome`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestPalindrome

  def cntList (l : List Aeneas.Std.U8) (b : Nat) : Nat :=
    (l.filter (fun x => x.val = b)).length

  def cnt (s : Aeneas.Std.Slice Aeneas.Std.U8) (b : Nat) : Nat :=
    cntList s.val b

  def IsLetter (b : Nat) : Prop :=
    (65 ≤ b ∧ b ≤ 90) ∨ (97 ≤ b ∧ b ≤ 122)

  def basePre (s : Aeneas.Std.Slice Aeneas.Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 2000 ∧ ∀ x ∈ s.val, IsLetter x.val

  def pairedE (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat :=
    ((List.range 256).map (fun b => 2 * (cnt s b / 2))).sum

  def oddCount (s : Aeneas.Std.Slice Aeneas.Std.U8) : Nat :=
    ((List.range 256).filter (fun b => cnt s b % 2 = 1)).length

  def IsPalindrome (l : List Aeneas.Std.U8) : Prop :=
    ∀ j : Nat, j < l.length → l[j]? = l[l.length - 1 - j]?

  def swapCase (b : Nat) : Nat :=
    if 97 ≤ b ∧ b ≤ 122 then b - 32 else if 65 ≤ b ∧ b ≤ 90 then b + 32 else b

  /-- Let cnt(b) be the number of indices i with 0 <= i < len(s) and s[i] = b, for every byte value b with 0 <= b < 256. Let E = sum over all b of 2 * floor(cnt(b) / 2), and let O be the number of byte values b for which cnt(b) is odd. The function returns a result r (not a failure) and r = E + 1 if O > 0, while r = E if O = 0. Equivalently, r = len(s) - max(0, O - 1). This r is exactly the length of the longest palindrome that can be constructed using the multiset of letters in s, with letters compared case-sensitively.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter: 65..90 for A..Z or 97..122 for a..z. -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∃ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r ∧
        r.val = (if 0 < oddCount s then (pairedE s : Int) + 1 else (pairedE s : Int)) ∧
        r.val = (s.val.length : Int) - max 0 ((oddCount s : Int) - 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∃ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r ∧
          r.val = (if 0 < oddCount s then (pairedE s : Int) + 1 else (pairedE s : Int)) ∧
          r.val = (s.val.length : Int) - max 0 ((oddCount s : Int) - 1)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result (Ok r); it does not fail by arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∃ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∃ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(s).
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          1 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Let O be the number of byte values whose number of occurrences in s is odd. Whenever the function returns a result r, r is odd if and only if O > 0; equivalently, r is even if and only if O = 0.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        (r.val % 2 = 1 ↔ 0 < oddCount s) ∧ (r.val % 2 = 0 ↔ oddCount s = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          (r.val % 2 = 1 ↔ 0 < oddCount s) ∧ (r.val % 2 = 0 ↔ oddCount s = 0)) := by
    sorry

  /-- Let O be the number of byte values whose number of occurrences in s is odd. Whenever the function returns a result r, r = len(s) if and only if O <= 1. Equivalently, all letters of s can be used in a palindrome exactly when at most one character has an odd count.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        (r.val = (s.val.length : Int) ↔ oddCount s ≤ 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          (r.val = (s.val.length : Int) ↔ oddCount s ≤ 1)) := by
    sorry

  /-- Let O be the number of byte values whose number of occurrences in s is odd. Whenever the function returns a result r, the number of occurrences from s that are not used in the constructed longest palindrome is len(s) - r = max(0, O - 1).
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        (s.val.length : Int) - r.val = max 0 ((oddCount s : Int) - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          (s.val.length : Int) - r.val = max 0 ((oddCount s : Int) - 1)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a byte array t of length r such that: (i) t is a palindrome, meaning t[j] = t[r - 1 - j] for every j with 0 <= j < r; and (ii) for every byte value b with 0 <= b < 256, the number of indices j with 0 <= j < r and t[j] = b is at most the number of indices i with 0 <= i < len(s) and s[i] = b. Thus a palindrome of length r can actually be built from letters of s.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        ∃ t : List Aeneas.Std.U8,
          (t.length : Int) = r.val ∧
          IsPalindrome t ∧
          ∀ b : Nat, b < 256 → cntList t b ≤ cnt s b := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          ∃ t : List Aeneas.Std.U8,
            (t.length : Int) = r.val ∧
            IsPalindrome t ∧
            ∀ b : Nat, b < 256 → cntList t b ≤ cnt s b) := by
    sorry

  /-- Whenever the function returns a result r, for every byte array t that is a palindrome and whose byte counts are bounded by those of s (for every byte b, the number of occurrences of b in t is at most the number of occurrences of b in s), the length of t is at most r. In particular, no palindrome longer than r can be built from the letters of s.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        ∀ t : List Aeneas.Std.U8, IsPalindrome t →
          (∀ b : Nat, b < 256 → cntList t b ≤ cnt s b) → (t.length : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          ∀ t : List Aeneas.Std.U8, IsPalindrome t →
            (∀ b : Nat, b < 256 → cntList t b ≤ cnt s b) → (t.length : Int) ≤ r.val) := by
    sorry

  /-- Let cnt(b) be the number of occurrences of byte value b in s, and let P = sum over all byte values b of 2 * floor(cnt(b) / 2). Whenever the function returns a result r, P <= r <= P + 1; moreover r = P exactly when every count cnt(b) is even, and r = P + 1 exactly when some count cnt(b) is odd.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        (pairedE s : Int) ≤ r.val ∧
        r.val ≤ (pairedE s : Int) + 1 ∧
        (r.val = (pairedE s : Int) ↔ ∀ b : Nat, b < 256 → cnt s b % 2 = 0) ∧
        (r.val = (pairedE s : Int) + 1 ↔ ∃ b : Nat, b < 256 ∧ cnt s b % 2 = 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          (pairedE s : Int) ≤ r.val ∧
          r.val ≤ (pairedE s : Int) + 1 ∧
          (r.val = (pairedE s : Int) ↔ ∀ b : Nat, b < 256 → cnt s b % 2 = 0) ∧
          (r.val = (pairedE s : Int) + 1 ↔ ∃ b : Nat, b < 256 ∧ cnt s b % 2 = 1)) := by
    sorry

  /-- If for every byte value b with 0 <= b < 256 the number of occurrences of b in s1 equals the number of occurrences of b in s2, then the results returned for s1 and s2 are equal (and, by no-failure, both are returned).
    Preconditions: s1 and s2 both satisfy the base preconditions: each has length between 1 and 2000 and consists only of English letters. -/
  theorem spec_10 (s1 s2 : Aeneas.Std.Slice Aeneas.Std.U8)
      (h1 : basePre s1) (h2 : basePre s2)
      (hc : ∀ b : Nat, b < 256 → cnt s1 b = cnt s2 b) :
      ∀ r1 : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s1 = ok r1 →
      ∀ r2 : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s1 s2 : Aeneas.Std.Slice Aeneas.Std.U8)
        (h1 : basePre s1) (h2 : basePre s2)
        (hc : ∀ b : Nat, b < 256 → cnt s1 b = cnt s2 b), ∀ r1 : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s1 = ok r1 →
        ∀ r2 : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s2 = ok r2 → r1 = r2) := by
    sorry

  /-- If no byte value occurs more than once in s, then whenever the function returns a result r, r = 1.
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_11 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
      (h : ∀ b : Nat, cnt s b ≤ 1) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        r.val = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
        (h : ∀ b : Nat, cnt s b ≤ 1), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          r.val = 1) := by
    sorry

  /-- If all bytes of s are equal to the same byte value b, then whenever the function returns a result r, r = len(s).
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_12 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
      (h : ∃ b : Aeneas.Std.U8, ∀ x ∈ s.val, x = b) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        r.val = (s.val.length : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
        (h : ∃ b : Aeneas.Std.U8, ∀ x ∈ s.val, x = b), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          r.val = (s.val.length : Int)) := by
    sorry

  /-- If s is itself a palindrome, meaning s[i] = s[len(s) - 1 - i] for every i with 0 <= i < len(s), then whenever the function returns a result r, r = len(s).
    Preconditions: 1 <= len(s) <= 2000, and for every i with 0 <= i < len(s), s[i] is the ASCII code of an English letter. -/
  theorem spec_13 (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
      (h : IsPalindrome s.val) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        r.val = (s.val.length : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (hpre : basePre s)
        (h : IsPalindrome s.val), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
          r.val = (s.val.length : Int)) := by
    sorry

  /-- If s' is obtained from s by swapping the case of every letter, i.e. for every index i, s'[i] is the uppercase form of s[i] when s[i] is lowercase and the lowercase form of s[i] when s[i] is uppercase, then the results returned for s and s' are equal.
    Preconditions: s and s' both satisfy the base preconditions: length between 1 and 2000 and only English letters. -/
  theorem spec_14 (s s' : Aeneas.Std.Slice Aeneas.Std.U8)
      (h1 : basePre s) (h2 : basePre s')
      (hc : s'.val.map (fun x => x.val) = s.val.map (fun x => swapCase x.val)) :
      ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
      ∀ r' : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s' = ok r' → r = r' := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s s' : Aeneas.Std.Slice Aeneas.Std.U8)
        (h1 : basePre s) (h2 : basePre s')
        (hc : s'.val.map (fun x => x.val) = s.val.map (fun x => swapCase x.val)), ∀ r : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s = ok r →
        ∀ r' : Aeneas.Std.I64, Aegis.LongestPalindrome.longest_palindrome s' = ok r' → r = r') := by
    sorry

  end AegisSpec.LongestPalindrome
