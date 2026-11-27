import Aegis.MinInsertions.Code.Funs

/-!
# Specifications of `Aegis.MinInsertions.min_insertions`

LeetCode problem `minimum-insertion-steps-to-make-a-string-palindrome`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.MinInsertions

  theorem slice_length_eq_val {α : Type} (s : Slice α) : s.length = s.val.length := by
    simp [Slice.length]

  def isLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def isPalindrome (l : List U8) : Prop :=
    ∀ (j : Nat), (hj : j < l.length) → l[j] = l[l.length - 1 - j]

  def isSubsequence (s t : List U8) : Prop :=
    ∃ idx : Nat → Nat,
      (∀ (a : Nat), a < s.length → idx a < t.length) ∧
        (∀ (a b : Nat), a < b → b < s.length → idx a < idx b) ∧
          (∀ (a : Nat), a < s.length → t[idx a]? = s[a]?)

  def hasPalindromicSupersequence (s : List U8) (k : Nat) : Prop :=
    ∃ t : List U8, t.length = s.length + k ∧ isPalindrome t ∧ isSubsequence s t

  def isPalindromicSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → s[i a]? = s[i (m - 1 - a)]?)

  def isCommonSubseqSize (s : List U8) (m : Nat) : Prop :=
    ∃ i j : Nat → Nat,
      (∀ (a : Nat), a < m → i a < s.length) ∧
        (∀ (a b : Nat), a < b → b < m → i a < i b) ∧
          (∀ (a : Nat), a < m → j a < s.length) ∧
            (∀ (a b : Nat), a < b → b < m → j a < j b) ∧
              (∀ (a : Nat), a < m → s[i a]? = s[s.length - 1 - j a]?)

  /-- Whenever min_insertions(s) returns a result r, r is the least nonnegative integer k such that there exists a byte string t with len(t) = len(s) + k, t is a palindrome (for every j with 0 <= j < len(t), t[j] = t[len(t)-1-j]), and s is a subsequence of t (there exist indices 0 <= j_0 < j_1 < ... < j_{len(s)-1} < len(t) with t[j_i] = s[i] for every i with 0 <= i < len(s)).
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter). -/
  theorem spec_1 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧
          hasPalindromicSupersequence s.val r.val.toNat ∧
            (∀ k, hasPalindromicSupersequence s.val k → r.val.toNat ≤ k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
          0 ≤ r.val ∧
            hasPalindromicSupersequence s.val r.val.toNat ∧
              (∀ k, hasPalindromicSupersequence s.val k → r.val.toNat ≤ k)) := by
    sorry

  /-- For every s satisfying the preconditions, min_insertions(s) returns a result r (the Result is ok); it does not fail, panic, overflow, or access out of bounds.
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∃ r, Aegis.MinInsertions.min_insertions s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∃ r, Aegis.MinInsertions.min_insertions s = ok r) := by
    sorry

  /-- Whenever min_insertions(s) returns a result r, 0 <= r <= len(s) - 1.
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
          0 ≤ r.val ∧ r.val ≤ (s.val.length : Int) - 1) := by
    sorry

  /-- Whenever min_insertions(s) returns a result r, r = 0 if and only if s is a palindrome (for every i with 0 <= i < len(s), s[i] = s[len(s)-1-i]).
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r → (r.val = 0 ↔ isPalindrome s.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∀ r, Aegis.MinInsertions.min_insertions s = ok r → (r.val = 0 ↔ isPalindrome s.val)) := by
    sorry

  /-- Whenever min_insertions(s) returns a result r, r = len(s) - L, where L is the largest integer m for which there exist indices 0 <= i_0 < i_1 < ... < i_{m-1} < len(s) such that s[i_a] = s[i_{m-1-a}] for every a with 0 <= a < m.
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ L : Nat,
          isPalindromicSubseqSize s.val L ∧
            (∀ m, isPalindromicSubseqSize s.val m → m ≤ L) ∧
              r.val = (s.val.length : Int) - (L : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
          ∃ L : Nat,
            isPalindromicSubseqSize s.val L ∧
              (∀ m, isPalindromicSubseqSize s.val m → m ≤ L) ∧
                r.val = (s.val.length : Int) - (L : Int)) := by
    sorry

  /-- Whenever min_insertions(s) returns a result r and min_insertions(t) returns a result q, r = q.
    Preconditions: 1 <= len(s) <= 500; 1 <= len(t) <= 500; len(t) = len(s); for every i with 0 <= i < len(s), s[i] and t[i] are lowercase English ASCII codes; and for every i with 0 <= i < len(s), t[i] = s[len(s)-1-i] (t is the reversal of s). -/
  theorem spec_6 (s t : Slice U8)
      (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 500)
      (ht_lower : 1 ≤ t.val.length) (ht_upper : t.val.length ≤ 500)
      (hlen : t.val.length = s.val.length)
      (hlower_s : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlower_t : ∀ (i : Nat), (hi : i < t.val.length) → isLowerAscii (t.val[i]))
      (hrev : ∀ (i : Nat), (hi : i < s.val.length) →
        t.val[i] = s.val[s.val.length - 1 - i]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions t = ok q → r = q := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice U8)
        (hs_lower : 1 ≤ s.val.length) (hs_upper : s.val.length ≤ 500)
        (ht_lower : 1 ≤ t.val.length) (ht_upper : t.val.length ≤ 500)
        (hlen : t.val.length = s.val.length)
        (hlower_s : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
        (hlower_t : ∀ (i : Nat), (hi : i < t.val.length) → isLowerAscii (t.val[i]))
        (hrev : ∀ (i : Nat), (hi : i < s.val.length) →
          t.val[i] = s.val[s.val.length - 1 - i]), ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
          Aegis.MinInsertions.min_insertions t = ok q → r = q) := by
    sorry

  /-- Let u be the slice of length len(s)-2 with u[i] = s[i+1] for every i with 0 <= i < len(s)-2. Whenever min_insertions(s) returns a result r and min_insertions(u) returns a result q, r = q.
    Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(s) >= 3; and s[0] = s[len(s)-1]. -/
  theorem spec_7 (s u : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen3 : 3 ≤ s.val.length)
      (hends : s.val[0] = s.val[s.val.length - 1])
      (hu_len : u.val.length = s.val.length - 2)
      (hu_val : ∀ (i : Nat), (hi : i < u.val.length) → u.val[i] = s.val[i + 1]) :
      ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions u = ok q → r = q := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s u : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
        (hlen3 : 3 ≤ s.val.length)
        (hends : s.val[0] = s.val[s.val.length - 1])
        (hu_len : u.val.length = s.val.length - 2)
        (hu_val : ∀ (i : Nat), (hi : i < u.val.length) → u.val[i] = s.val[i + 1]), ∀ r q, Aegis.MinInsertions.min_insertions s = ok r →
          Aegis.MinInsertions.min_insertions u = ok q → r = q) := by
    sorry

  /-- Let a be the slice of length len(s)-1 with a[i] = s[i+1] for every i with 0 <= i < len(s)-1, and let b be the slice of length len(s)-1 with b[i] = s[i] for every i with 0 <= i < len(s)-1. Whenever min_insertions(s) returns r, min_insertions(a) returns ra, and min_insertions(b) returns rb, we have r = 1 + min(ra, rb).
    Preconditions: 1 <= len(s) <= 500; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(s) >= 2; and s[0] != s[len(s)-1]. -/
  theorem spec_8 (s a b : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
      (hlen2 : 2 ≤ s.val.length)
      (hne : s.val[0] ≠ s.val[s.val.length - 1])
      (ha_len : a.val.length = s.val.length - 1)
      (ha_val : ∀ (i : Nat), (hi : i < a.val.length) → a.val[i] = s.val[i + 1])
      (hb_len : b.val.length = s.val.length - 1)
      (hb_val : ∀ (i : Nat), (hi : i < b.val.length) → b.val[i] = s.val[i]) :
      ∀ r ra rb, Aegis.MinInsertions.min_insertions s = ok r →
        Aegis.MinInsertions.min_insertions a = ok ra →
          Aegis.MinInsertions.min_insertions b = ok rb → r.val = 1 + min ra.val rb.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s a b : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i]))
        (hlen2 : 2 ≤ s.val.length)
        (hne : s.val[0] ≠ s.val[s.val.length - 1])
        (ha_len : a.val.length = s.val.length - 1)
        (ha_val : ∀ (i : Nat), (hi : i < a.val.length) → a.val[i] = s.val[i + 1])
        (hb_len : b.val.length = s.val.length - 1)
        (hb_val : ∀ (i : Nat), (hi : i < b.val.length) → b.val[i] = s.val[i]), ∀ r ra rb, Aegis.MinInsertions.min_insertions s = ok r →
          Aegis.MinInsertions.min_insertions a = ok ra →
            Aegis.MinInsertions.min_insertions b = ok rb → r.val = 1 + min ra.val rb.val) := by
    sorry

  /-- Whenever min_insertions(s) returns a result r, r = len(s) - C, where C is the largest integer m for which there exist indices 0 <= i_0 < i_1 < ... < i_{m-1} < len(s) and 0 <= j_0 < j_1 < ... < j_{m-1} < len(s) such that s[i_a] = s[len(s)-1-j_a] for every a with 0 <= a < m.
    Preconditions: 1 <= len(s) <= 500 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice U8)
      (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
      (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])) :
      ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
        ∃ C : Nat,
          isCommonSubseqSize s.val C ∧
            (∀ m, isCommonSubseqSize s.val m → m ≤ C) ∧
              r.val = (s.val.length : Int) - (C : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_lower : 1 ≤ s.val.length) (hlen_upper : s.val.length ≤ 500)
        (hlower : ∀ (i : Nat), (hi : i < s.val.length) → isLowerAscii (s.val[i])), ∀ r, Aegis.MinInsertions.min_insertions s = ok r →
          ∃ C : Nat,
            isCommonSubseqSize s.val C ∧
              (∀ m, isCommonSubseqSize s.val m → m ≤ C) ∧
                r.val = (s.val.length : Int) - (C : Int)) := by
    sorry

  end AegisSpec.MinInsertions
