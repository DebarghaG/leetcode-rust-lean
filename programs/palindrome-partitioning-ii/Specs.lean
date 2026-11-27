import Aegis.MinCut.Code.Funs

/-!
# Specifications of `Aegis.MinCut.min_cut`

LeetCode problem `palindrome-partitioning-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCut

def byteAt (s : Slice U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def PalinAt (s : Slice U8) (l r : Nat) : Prop :=
  l < r ∧ r ≤ s.val.length ∧ ∀ t, t < r - l → byteAt s (l + t) = byteAt s (r - 1 - t)

def Letters (s : Slice U8) (n : Nat) : Prop :=
  ∀ i, i < n → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122

def IsPartition (s : Slice U8) (m : Nat) (p : Nat → Nat) : Prop :=
  p 0 = 0 ∧ p m = s.val.length ∧ ∀ j, j < m → p j < p (j + 1)

def IsPalindromicPartition (s : Slice U8) (m : Nat) (p : Nat → Nat) : Prop :=
  IsPartition s m p ∧ ∀ j, j < m → PalinAt s (p j) (p (j + 1))

def CutsFor (s : Slice U8) (c : Nat) : Prop :=
  ∃ p : Nat → Nat, IsPalindromicPartition s (c + 1) p

/-- The function returns a result r, and r (viewed as a mathematical integer) is the least integer c for which there exist indices 0 = p_0 < p_1 < ... < p_{c+1} = n such that, for every j with 0 <= j <= c, the substring s[p_j .. p_{j+1}) is a palindrome. Here a substring s[l..r) with 0 <= l < r <= n is a palindrome exactly when s[l+t] = s[r-1-t] for every t with 0 <= t < r-l. Equivalently, r is the minimum number of cuts over all partitions of s into contiguous nonempty substrings each of which is a palindrome, where a partition into m substrings uses m-1 cuts.
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive (the ASCII code of a lowercase English letter). -/
theorem spec_1 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ CutsFor s r.val.toNat ∧
      ∀ c : Nat, CutsFor s c → r.val.toNat ≤ c := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ CutsFor s r.val.toNat ∧
      ∀ c : Nat, CutsFor s c → r.val.toNat ≤ c) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_2 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r) := by
  sorry

/-- The function returns a result r, and 0 <= r <= len(s) - 1, with r and len(s)-1 interpreted as mathematical integers.
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_3 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if the whole string s is a palindrome, that is, if and only if s[t] = s[len(s)-1-t] for every t with 0 <= t < len(s).
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_4 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (r.val = 0 ↔ ∀ t, t < n → byteAt s t = byteAt s (n - 1 - t)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (r.val = 0 ↔ ∀ t, t < n → byteAt s t = byteAt s (n - 1 - t))) := by
  sorry

/-- The function returns r, with r = 0 if s[0] = s[1], and r = 1 if s[0] != s[1].
  Preconditions: len(s) = 2, and s[0] and s[1] are between 97 and 122 inclusive. -/
theorem spec_5 (s : Slice U8) (hlen : s.val.length = 2)
    (h0 : 97 ≤ byteAt s 0 ∧ byteAt s 0 ≤ 122)
    (h1 : 97 ≤ byteAt s 1 ∧ byteAt s 1 ≤ 122) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (byteAt s 0 = byteAt s 1 → r.val = 0) ∧
      (byteAt s 0 ≠ byteAt s 1 → r.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hlen : s.val.length = 2)
    (h0 : 97 ≤ byteAt s 0 ∧ byteAt s 0 ≤ 122)
    (h1 : 97 ≤ byteAt s 1 ∧ byteAt s 1 ≤ 122), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (byteAt s 0 = byteAt s 1 → r.val = 0) ∧
      (byteAt s 0 ≠ byteAt s 1 → r.val = 1)) := by
  sorry

/-- The function returns a result r; write c for r viewed as a nonnegative integer (so this also asserts r >= 0). There exist indices 0 = p_0 < p_1 < ... < p_{c+1} = len(s) such that every substring s[p_j .. p_{j+1}) for 0 <= j <= c is a palindrome, where palindrome means s[l+t] = s[r-1-t] for all 0 <= t < r-l.
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_6 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ CutsFor s r.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧ 0 ≤ r.val ∧ CutsFor s r.val.toNat) := by
  sorry

/-- The function returns a result r, and for every integer m >= 1 and every sequence of indices 0 = p_0 < p_1 < ... < p_m = len(s) such that every substring s[p_j .. p_{j+1}) for 0 <= j < m is a palindrome, we have m - 1 >= r.
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_7 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      ∀ (m : Nat) (p : Nat → Nat), 1 ≤ m → IsPalindromicPartition s m p →
        (m : Int) - 1 ≥ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 1 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      ∀ (m : Nat) (p : Nat → Nat), 1 ≤ m → IsPalindromicPartition s m p →
        (m : Int) - 1 ≥ r.val) := by
  sorry

/-- Let t be the byte slice of the same length as s defined by t[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). The function returns r on input s and returns r' on input t, and r = r'.
  Preconditions: len(s) is an integer n with 1 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_8 (s t : Slice U8) (n : Nat) (hs : s.val.length = n) (ht : t.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletters : Letters s n)
    (htrev : ∀ i, i < n → byteAt t i = byteAt s (n - 1 - i)) :
    ∃ r r' : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8) (n : Nat) (hs : s.val.length = n) (ht : t.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletters : Letters s n)
    (htrev : ∀ i, i < n → byteAt t i = byteAt s (n - 1 - i)), ∃ r r' : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok r' ∧ r = r') := by
  sorry

/-- The function returns r on input s and returns r' on input t, and r = r'.
  Preconditions: len(s) = len(t) = n with 1 <= n <= 2000; every byte of s and t is between 97 and 122 inclusive; and for every i and j with 0 <= i < n and 0 <= j < n, s[i] = s[j] if and only if t[i] = t[j]. -/
theorem spec_9 (s t : Slice U8) (n : Nat) (hs : s.val.length = n) (ht : t.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletterss : Letters s n) (hletterst : Letters t n)
    (hsame : ∀ i j, i < n → j < n → (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j)) :
    ∃ r r' : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice U8) (n : Nat) (hs : s.val.length = n) (ht : t.val.length = n)
    (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletterss : Letters s n) (hletterst : Letters t n)
    (hsame : ∀ i j, i < n → j < n → (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j)), ∃ r r' : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok r' ∧ r = r') := by
  sorry

/-- Let t be the byte slice of length n+1 with t[i] = s[i] for 0 <= i < n and t[n] = b. The function returns r on input s and r_t on input t, and r_t <= r + 1.
  Preconditions: s has length n with 1 <= n <= 2000 and all its bytes are between 97 and 122 inclusive; b is an integer with 97 <= b <= 122; and n + 1 <= 2000. -/
theorem spec_10 (s t : Slice U8) (n b : Nat) (hs : s.val.length = n)
    (ht : t.val.length = n + 1) (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletters : Letters s n)
    (hb : 97 ≤ b ∧ b ≤ 122) (hbn : n + 1 ≤ 2000)
    (hpre : ∀ i, i < n → byteAt t i = byteAt s i) (hlast : byteAt t n = b) :
    ∃ r rt : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok rt ∧
      rt.val ≤ r.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8) (n b : Nat) (hs : s.val.length = n)
    (ht : t.val.length = n + 1) (hlo : 1 ≤ n) (hhi : n ≤ 2000) (hletters : Letters s n)
    (hb : 97 ≤ b ∧ b ≤ 122) (hbn : n + 1 ≤ 2000)
    (hpre : ∀ i, i < n → byteAt t i = byteAt s i) (hlast : byteAt t n = b), ∃ r rt : I64, Aegis.MinCut.min_cut s = ok r ∧ Aegis.MinCut.min_cut t = ok rt ∧
      rt.val ≤ r.val + 1) := by
  sorry

/-- The function returns a result r, and r <= len(s) - 2 if and only if there exist indices l and u with 0 <= l < u <= len(s), u - l >= 2, such that the substring s[l..u) is a palindrome, that is, s[l+t] = s[u-1-t] for every t with 0 <= t < u-l.
  Preconditions: len(s) is an integer n with 2 <= n <= 2000, and for every i with 0 <= i < n, s[i] is between 97 and 122 inclusive. -/
theorem spec_11 (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 2 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n) :
    ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (r.val ≤ (n : Int) - 2 ↔ ∃ l u : Nat, l < u ∧ u ≤ n ∧ 2 ≤ u - l ∧ PalinAt s l u) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (n : Nat) (hlen : s.val.length = n) (hlo : 2 ≤ n)
    (hhi : n ≤ 2000) (hletters : Letters s n), ∃ r : I64, Aegis.MinCut.min_cut s = ok r ∧
      (r.val ≤ (n : Int) - 2 ↔ ∃ l u : Nat, l < u ∧ u ≤ n ∧ 2 ≤ u - l ∧ PalinAt s l u)) := by
  sorry

end AegisSpec.MinCut
