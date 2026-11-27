import Aegis.MaxPalindromes.Code.Funs

/-!
# Specifications of `Aegis.MaxPalindromes.max_palindromes`

LeetCode problem `maximum-number-of-non-overlapping-palindrome-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxPalindromes

namespace AegisSpec.MaxPalindromes

def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def IsPalindrome (s : Slice Std.U8) (l u : Nat) : Prop :=
  ∀ j, j < u - l → byteAt s (l + j) = byteAt s (u - 1 - j)

def IsGoodSubstring (s : Slice Std.U8) (k : Int) (l u : Nat) : Prop :=
  l < u ∧ u ≤ s.val.length ∧ k ≤ ((u - l : Nat) : Int) ∧ IsPalindrome s l u

def NonOverlapping (p q : Nat × Nat) : Prop :=
  p.2 ≤ q.1 ∨ q.2 ≤ p.1

def IsFamily (s : Slice Std.U8) (k : Int) (f : List (Nat × Nat)) : Prop :=
  (∀ p ∈ f, IsGoodSubstring s k p.1 p.2) ∧ f.Pairwise NonOverlapping

def revBytes (s : Slice Std.U8) : Slice Std.U8 where
  leng := s.val.reverse.length
  list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
  bound := by
    have hlen : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    have hrev : s.val.reverse.length ≤ Aeneas.Std.Usize.max := by
      rw [List.length_reverse, hlen]
      exact s.bound
    exact hrev

/-- The function returns a result r (it does not fail) and r is the maximum cardinality of a family of pairwise non-overlapping substrings of s each of length at least k and each a palindrome. Formally, a substring is a pair (l,u) with 0 <= l < u <= len(s); its length is u-l; it is a palindrome when for every j with 0 <= j < u-l, s[l+j] = s[u-1-j]. Two substrings (l1,u1) and (l2,u2) are non-overlapping when u1 <= l2 or u2 <= l1. Then r = max { q | there exist q such substrings that are pairwise non-overlapping, each has length at least k, and each is a palindrome }.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_1
    (s : Slice Std.U8) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r : Std.I64,
      max_palindromes s k = ok r ∧
        (∃ f : List (Nat × Nat), IsFamily s k.val f ∧ (f.length : Int) = r.val) ∧
        (∀ f : List (Nat × Nat), IsFamily s k.val f → (f.length : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Std.I64,
      max_palindromes s k = ok r ∧
        (∃ f : List (Nat × Nat), IsFamily s k.val f ∧ (f.length : Int) = r.val) ∧
        (∀ f : List (Nat × Nat), IsFamily s k.val f → (f.length : Int) ≤ r.val)) := by
  sorry

/-- For every s and k satisfying the preconditions, the function returns some result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2
    (s : Slice Std.U8) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r : Std.I64, max_palindromes s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Std.I64, max_palindromes s k = ok r) := by
  sorry

/-- Whenever the function returns r, 0 <= r.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns r, r * k <= len(s), equivalently r <= floor(len(s)/k).
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    r.val * k.val ≤ (s.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), r.val * k.val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns r, r = len(s).
  Preconditions: 1 <= k <= len(s) <= 2000, k = 1, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hk_eq : k.val = 1)
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    r.val = (s.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hk_eq : k.val = 1)
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns r, r = 1 if for every j with 0 <= j < len(s), s[j] = s[len(s)-1-j], and r = 0 otherwise.
  Preconditions: 1 <= k <= len(s) <= 2000, k = len(s), and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hk_eq : k.val = (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    (IsPalindrome s 0 s.val.length → r.val = 1) ∧
      (¬ IsPalindrome s 0 s.val.length → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hk_eq : k.val = (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), (IsPalindrome s 0 s.val.length → r.val = 1) ∧
      (¬ IsPalindrome s 0 s.val.length → r.val = 0)) := by
  sorry

/-- Whenever the function returns r, r = 0 if and only if there is no pair (l,u) with 0 <= l < u <= len(s), u-l >= k, and s[l..u) a palindrome (that is, for every j with 0 <= j < u-l, s[l+j] = s[u-1-j]).
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    (r.val = 0 ↔ ¬ ∃ l u : Nat, IsGoodSubstring s k.val l u) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), (r.val = 0 ↔ ¬ ∃ l u : Nat, IsGoodSubstring s k.val l u)) := by
  sorry

/-- Whenever the function returns r, r = floor(len(s)/k).
  Preconditions: 1 <= k <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i and j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
theorem spec_8
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hconst : ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j)
    (hr : max_palindromes s k = ok r) :
    r.val = (s.val.length : Int) / k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hconst : ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j)
    (hr : max_palindromes s k = ok r), r.val = (s.val.length : Int) / k.val) := by
  sorry

/-- Whenever the function returns r, r >= 1.
  Preconditions: 1 <= k <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every j with 0 <= j < len(s), s[j] = s[len(s)-1-j]. -/
theorem spec_9
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hpal : IsPalindrome s 0 s.val.length)
    (hr : max_palindromes s k = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hpal : IsPalindrome s 0 s.val.length)
    (hr : max_palindromes s k = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns r, r = 0.
  Preconditions: 2 <= k <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i and j with 0 <= i < j < len(s), s[i] != s[j]. -/
theorem spec_10
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 2 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hdistinct : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j)
    (hr : max_palindromes s k = ok r) :
    r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 2 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hdistinct : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j)
    (hr : max_palindromes s k = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns r, for every q >= 0 and every sequences l_1,...,l_q and u_1,...,u_q such that for each t with 1 <= t <= q we have 0 <= l_t < u_t <= len(s), u_t-l_t >= k, s[l_t..u_t) is a palindrome, and for every distinct a,b the two substrings are non-overlapping (u_a <= l_b or u_b <= l_a), we have q <= r.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_11
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    ∀ (q : Nat) (f : List (Nat × Nat)), f.length = q → IsFamily s k.val f → (q : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), ∀ (q : Nat) (f : List (Nat × Nat)), f.length = q → IsFamily s k.val f → (q : Int) ≤ r.val) := by
  sorry

/-- If the function returns r1 on input (s,k1) and returns r2 on input (s,k2), then r2 <= r1.
  Preconditions: 1 <= k1 <= k2 <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_12
    (s : Slice Std.U8) (k1 k2 : Std.I64) (r1 r2 : Std.I64)
    (hk1_pos : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2_le : k2.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr1 : max_palindromes s k1 = ok r1)
    (hr2 : max_palindromes s k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64) (r1 r2 : Std.I64)
    (hk1_pos : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2_le : k2.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr1 : max_palindromes s k1 = ok r1)
    (hr2 : max_palindromes s k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Let rev(s) be the byte slice of length len(s) with rev(s)[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). If the function returns r on input (s,k) and returns r' on input (rev(s),k), then r = r'.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_13
    (s : Slice Std.U8) (k : Std.I64) (r r' : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r)
    (hr' : max_palindromes (revBytes s) k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r r' : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r)
    (hr' : max_palindromes (revBytes s) k = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r, r <= 1.
  Preconditions: 1 <= k <= len(s) <= 2000, 2*k > len(s), and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_14
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hbig : (s.val.length : Int) < 2 * k.val)
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r) :
    r.val ≤ 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hbig : (s.val.length : Int) < 2 * k.val)
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r), r.val ≤ 1) := by
  sorry

/-- Whenever the function returns r and r = len(s), we have k = 1.
  Preconditions: 1 <= k <= len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_15
    (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r)
    (hrmax : r.val = (s.val.length : Int)) :
    k.val = 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Std.I64)
    (hk_pos : 1 ≤ k.val)
    (hk_le : k.val ≤ (s.val.length : Int))
    (hlen : s.val.length ≤ 2000)
    (hbytes : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hr : max_palindromes s k = ok r)
    (hrmax : r.val = (s.val.length : Int)), k.val = 1) := by
  sorry

end AegisSpec.MaxPalindromes
