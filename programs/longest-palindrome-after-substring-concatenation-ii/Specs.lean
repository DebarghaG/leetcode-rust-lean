import Aegis.LongestPalindrome.Code.Funs

/-!
# Specifications of `Aegis.LongestPalindrome.longest_palindrome`

LeetCode problem `longest-palindrome-after-substring-concatenation-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.LongestPalindrome

def bytes (x : Slice U8) : List ℕ := x.val.map (fun b => b.val)

def substr (x : List ℕ) (i j : ℕ) : List ℕ := (x.drop i).take (j - i)

def IsPalindrome (x : List ℕ) : Prop := ∀ q : ℕ, q < x.length → x[q]? = x[x.length - 1 - q]?

noncomputable def LPS (x : List ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun m => ∃ i : ℕ, i + m ≤ x.length ∧ IsPalindrome (substr x i (i + m))) x.length

def OccursIn (x y : List ℕ) : Prop :=
  ∃ i : ℕ, i + x.length ≤ y.length ∧ substr y i (i + x.length) = x

/-- Using the following definitions, the function returns a result r and r is the exact maximum. For a byte string x of length n, x is a palindrome iff for every q with 0 <= q < n, x[q] = x[n-1-q] (so empty and length-one strings are palindromes). For indices 0 <= i <= j <= len(s), s[i..j] denotes the contiguous substring of s of length j-i whose p-th byte, for 0 <= p < j-i, is s[i+p]; s[i..i] is empty. Similarly t[k..l] for 0 <= k <= l <= len(t). Then r is the greatest integer m for which there exist 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t) such that the concatenation s[i..j] ++ t[k..l] is a palindrome and m = (j-i)+(l-k).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_1 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122) :
    ∃ r : I64,
      Aegis.LongestPalindrome.longest_palindrome s t = ok r ∧
        (∃ i j k l : ℕ,
          i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
            IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) ∧
            r.val = ↑((j - i) + (l - k))) ∧
        (∀ i j k l : ℕ,
          i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
            IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) →
            ↑((j - i) + (l - k)) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122), ∃ r : I64,
      Aegis.LongestPalindrome.longest_palindrome s t = ok r ∧
        (∃ i j k l : ℕ,
          i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
            IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) ∧
            r.val = ↑((j - i) + (l - k))) ∧
        (∀ i j k l : ℕ,
          i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
            IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) →
            ↑((j - i) + (l - k)) ≤ r.val)) := by
  sorry

/-- For every s and t satisfying the preconditions, the function terminates successfully and returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_2 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122) :
    ∃ r : I64, Aegis.LongestPalindrome.longest_palindrome s t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122), ∃ r : I64, Aegis.LongestPalindrome.longest_palindrome s t = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= len(s) + len(t).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_3 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    r.val ≤ (s.val.length : ℤ) + (t.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), r.val ≤ (s.val.length : ℤ) + (t.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_4 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t) such that s[i..j] ++ t[k..l] is a palindrome and (j-i)+(l-k) = r.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_5 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    ∃ i j k l : ℕ,
      i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
        IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) ∧
        ↑((j - i) + (l - k)) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), ∃ i j k l : ℕ,
      i ≤ j ∧ j ≤ s.val.length ∧ k ≤ l ∧ l ≤ t.val.length ∧
        IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) ∧
        ↑((j - i) + (l - k)) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every choice of indices 0 <= i <= j <= len(s) and 0 <= k <= l <= len(t), if s[i..j] ++ t[k..l] is a palindrome, then (j-i)+(l-k) <= r.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_6 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    ∀ i j k l : ℕ,
      i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
        IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) →
        ↑((j - i) + (l - k)) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), ∀ i j k l : ℕ,
      i ≤ j → j ≤ s.val.length → k ≤ l → l ≤ t.val.length →
        IsPalindrome (substr (bytes s) i j ++ substr (bytes t) k l) →
        ↑((j - i) + (l - k)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= max(LPS(s), LPS(t)), where for a byte slice x, LPS(x) is the greatest length of a contiguous substring of x that is a palindrome (equivalently, the greatest (j-i) with 0 <= i <= j <= len(x) and x[i..j] a palindrome; empty substrings are allowed, so LPS(x) >= 0).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_7 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    max (LPS (bytes s)) (LPS (bytes t)) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), max (LPS (bytes s)) (LPS (bytes t)) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if s[0] = t[0], and r = 1 otherwise.
  Preconditions: len(s) = 1, len(t) = 1, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_8 (s t : Slice U8)
    (h_len_s : s.val.length = 1) (h_len_t : t.val.length = 1)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    ((bytes s)[0]? = (bytes t)[0]? → r.val = 2) ∧
      ((bytes s)[0]? ≠ (bytes t)[0]? → r.val = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : s.val.length = 1) (h_len_t : t.val.length = 1)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), ((bytes s)[0]? = (bytes t)[0]? → r.val = 2) ∧
      ((bytes s)[0]? ≠ (bytes t)[0]? → r.val = 1)) := by
  sorry

/-- Whenever the function returns a result r, r = len(s) + len(t).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, every byte of s and every byte of t is one of the lowercase English letters 97 through 122, and there exists a byte c such that for every i with 0 <= i < len(s), s[i] = c, and for every j with 0 <= j < len(t), t[j] = c. -/
theorem spec_9 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_const : ∃ c : ℕ,
      (∀ i : ℕ, i < s.val.length → (bytes s)[i]? = some c) ∧
        (∀ j : ℕ, j < t.val.length → (bytes t)[j]? = some c))
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    r.val = (s.val.length : ℤ) + (t.val.length : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_const : ∃ c : ℕ,
      (∀ i : ℕ, i < s.val.length → (bytes s)[i]? = some c) ∧
        (∀ j : ℕ, j < t.val.length → (bytes t)[j]? = some c))
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), r.val = (s.val.length : ℤ) + (t.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = max(len(s), len(t)).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, every byte of s and every byte of t is one of the lowercase English letters 97 through 122, and there exist bytes a and b with a != b such that for every i with 0 <= i < len(s), s[i] = a, and for every j with 0 <= j < len(t), t[j] = b. -/
theorem spec_10 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_const : ∃ a b : ℕ,
      a ≠ b ∧
        (∀ i : ℕ, i < s.val.length → (bytes s)[i]? = some a) ∧
        (∀ j : ℕ, j < t.val.length → (bytes t)[j]? = some b))
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    r.val = max (s.val.length : ℤ) (t.val.length : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_const : ∃ a b : ℕ,
      a ≠ b ∧
        (∀ i : ℕ, i < s.val.length → (bytes s)[i]? = some a) ∧
        (∀ j : ℕ, j < t.val.length → (bytes t)[j]? = some b))
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), r.val = max (s.val.length : ℤ) (t.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, every byte of s and every byte of t is one of the lowercase English letters 97 through 122, and all bytes occurring in s and t are pairwise distinct: for every 0 <= i < len(s) and 0 <= j < len(t), s[i] != t[j]; for every 0 <= i < i' < len(s), s[i] != s[i']; and for every 0 <= j < j' < len(t), t[j] != t[j']. -/
theorem spec_11 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_disj_st : ∀ i : ℕ, i < s.val.length → ∀ j : ℕ, j < t.val.length →
      (bytes s)[i]? ≠ (bytes t)[j]?)
    (h_disj_s : ∀ i : ℕ, i < s.val.length → ∀ i' : ℕ, i' < s.val.length → i ≠ i' →
      (bytes s)[i]? ≠ (bytes s)[i']?)
    (h_disj_t : ∀ j : ℕ, j < t.val.length → ∀ j' : ℕ, j' < t.val.length → j ≠ j' →
      (bytes t)[j]? ≠ (bytes t)[j']?)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    r.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_disj_st : ∀ i : ℕ, i < s.val.length → ∀ j : ℕ, j < t.val.length →
      (bytes s)[i]? ≠ (bytes t)[j]?)
    (h_disj_s : ∀ i : ℕ, i < s.val.length → ∀ i' : ℕ, i' < s.val.length → i ≠ i' →
      (bytes s)[i]? ≠ (bytes s)[i']?)
    (h_disj_t : ∀ j : ℕ, j < t.val.length → ∀ j' : ℕ, j' < t.val.length → j ≠ j' →
      (bytes t)[j]? ≠ (bytes t)[j']?)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), r.val = 1) := by
  sorry

/-- Let rev(x) denote the byte slice obtained by reversing x. Whenever the function returns r on inputs (s,t), the function on inputs (rev(t), rev(s)) (which also satisfies the preconditions) returns the same value r; equivalently, r(s,t) = r(rev(t), rev(s)).
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_12 (s t s' t' : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_rev_s' : bytes s' = (bytes t).reverse)
    (h_rev_t' : bytes t' = (bytes s).reverse)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    ∃ r' : I64, Aegis.LongestPalindrome.longest_palindrome s' t' = ok r' ∧ r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t s' t' : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_rev_s' : bytes s' = (bytes t).reverse)
    (h_rev_t' : bytes t' = (bytes s).reverse)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), ∃ r' : I64, Aegis.LongestPalindrome.longest_palindrome s' t' = ok r' ∧ r' = r) := by
  sorry

/-- Whenever the function returns a result r, r = len(s) + len(t) if and only if the full concatenation s[0..len(s)] ++ t[0..len(t)] (i.e., s followed by t) is a palindrome.
  Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 1000, len(t) <= 1000, and every byte of s and every byte of t is one of the lowercase English letters 97 through 122. -/
theorem spec_13 (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r) :
    (r.val = (s.val.length : ℤ) + (t.val.length : ℤ) ↔
      IsPalindrome (bytes s ++ bytes t)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (r : I64) (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r), (r.val = (s.val.length : ℤ) + (t.val.length : ℤ) ↔
      IsPalindrome (bytes s ++ bytes t))) := by
  sorry

/-- For any such s,t,s',t', whenever the function returns r on (s,t) and r' on (s',t'), r <= r'.
  Preconditions: s,t,s',t' all satisfy the same constraints: lengths between 1 and 1000, and all bytes are lowercase English letters 97 through 122. Moreover, s occurs as a contiguous substring of s', and t occurs as a contiguous substring of t'. -/
theorem spec_14 (s t s' t' : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_len_s' : 1 ≤ s'.val.length) (h_len_t' : 1 ≤ t'.val.length)
    (h_le_s' : s'.val.length ≤ 1000) (h_le_t' : t'.val.length ≤ 1000)
    (h_bytes_s' : ∀ b ∈ bytes s', 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t' : ∀ b ∈ bytes t', 97 ≤ b ∧ b ≤ 122)
    (h_occ_s : OccursIn (bytes s) (bytes s'))
    (h_occ_t : OccursIn (bytes t) (bytes t'))
    (r r' : I64)
    (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r)
    (hr' : Aegis.LongestPalindrome.longest_palindrome s' t' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s t s' t' : Slice U8)
    (h_len_s : 1 ≤ s.val.length) (h_len_t : 1 ≤ t.val.length)
    (h_le_s : s.val.length ≤ 1000) (h_le_t : t.val.length ≤ 1000)
    (h_bytes_s : ∀ b ∈ bytes s, 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t : ∀ b ∈ bytes t, 97 ≤ b ∧ b ≤ 122)
    (h_len_s' : 1 ≤ s'.val.length) (h_len_t' : 1 ≤ t'.val.length)
    (h_le_s' : s'.val.length ≤ 1000) (h_le_t' : t'.val.length ≤ 1000)
    (h_bytes_s' : ∀ b ∈ bytes s', 97 ≤ b ∧ b ≤ 122)
    (h_bytes_t' : ∀ b ∈ bytes t', 97 ≤ b ∧ b ≤ 122)
    (h_occ_s : OccursIn (bytes s) (bytes s'))
    (h_occ_t : OccursIn (bytes t) (bytes t'))
    (r r' : I64)
    (hr : Aegis.LongestPalindrome.longest_palindrome s t = ok r)
    (hr' : Aegis.LongestPalindrome.longest_palindrome s' t' = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.LongestPalindrome
