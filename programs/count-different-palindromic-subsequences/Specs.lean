import Aegis.CountPalindromicSubsequences.Code.Funs

/-!
# Specifications of `Aegis.CountPalindromicSubsequences.count_palindromic_subsequences`

LeetCode problem `count-different-palindromic-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountPalindromicSubsequences

  open Aeneas.Std
  open Aegis.CountPalindromicSubsequences

  def modulus : ℤ := 1000000007

  def bytesOf (s : Slice U8) : List Nat := s.val.map (fun b => b.val)

  def onlyLetters (l : List Nat) : Prop := ∀ b ∈ l, b = 97 ∨ b = 98 ∨ b = 99 ∨ b = 100

  def IsSubseq {α : Type} (w l : List α) : Prop := w.Sublist l

  def IsPalindrome {α : Type} (w : List α) : Prop := w.reverse = w

  instance decidableIsPalindrome (w : List Nat) : Decidable (IsPalindrome w) :=
    (inferInstance : Decidable (w.reverse = w))

  instance decidableIsSubseq (u R : List Nat) : Decidable (IsSubseq u R) :=
    (inferInstance : Decidable (u.Sublist R))

  def palSubseqSet (l : List Nat) : Finset (List Nat) :=
    l.sublists.toFinset.filter (fun w => w ≠ [] ∧ IsPalindrome w)

  def palCount (l : List Nat) : Nat := (palSubseqSet l).card

  def bridgeSet (L R : List Nat) : Finset (List Nat) :=
    L.sublists.toFinset.filter (fun u => u ≠ [] ∧ IsSubseq u.reverse R)

  def bridgeCount (L R : List Nat) : Nat := (bridgeSet L R).card

  def prefixUpTo (l : List Nat) (k : Nat) : List Nat := l.take k

  def suffixAfter (l : List Nat) (k : Nat) : List Nat := l.drop (k + 1)

  def removeAt (l : List Nat) (k : Nat) : List Nat := l.take k ++ l.drop (k + 1)

  def middle (l : List Nat) : List Nat := (l.drop 1).dropLast

  /-- Whenever the function returns a result r, r is the unique integer satisfying 0 <= r < M and r ≡ C(s) (mod M), where M = 1000000007 and C(s) is the cardinality of the set P(s) of all non-empty byte strings w such that: (i) w is a subsequence of s, meaning there are indices 0 <= i1 < ... < ik < len(s) with w[j] = s[i_j] for each j; (ii) w equals its reverse; and (iii) different index choices giving the same byte sequence are not distinguished, so each distinct palindromic byte sequence contributes exactly once.
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'). -/
  theorem spec_1 (s : Slice U8) (r : I64)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hret : count_palindromic_subsequences s = Result.ok r) :
      0 ≤ r.val ∧ r.val < modulus ∧ Int.ModEq modulus r.val (palCount (bytesOf s) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (r : I64)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hret : count_palindromic_subsequences s = Result.ok r), 0 ≤ r.val ∧ r.val < modulus ∧ Int.ModEq modulus r.val (palCount (bytesOf s) : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, out-of-bounds slice access, or any other panic.
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'). -/
  theorem spec_2 (s : Slice U8)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s)) :
      ∃ r : I64, count_palindromic_subsequences s = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s)), ∃ r : I64, count_palindromic_subsequences s = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'). -/
  theorem spec_3 (s : Slice U8) (r : I64)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hret : count_palindromic_subsequences s = Result.ok r) :
      0 ≤ r.val ∧ r.val < modulus := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (r : I64)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hret : count_palindromic_subsequences s = Result.ok r), 0 ≤ r.val ∧ r.val < modulus) := by
    sorry

  /-- Whenever the function returns a result r, if C(s) < 1000000007 then r = C(s), where C(s) is the true count of distinct non-empty palindromic subsequences of s as defined in spec_1.
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'). -/
  theorem spec_4 (s : Slice U8) (r : I64)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hret : count_palindromic_subsequences s = Result.ok r)
      (hsmall : (palCount (bytesOf s) : ℤ) < modulus) :
      r.val = (palCount (bytesOf s) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (r : I64)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hret : count_palindromic_subsequences s = Result.ok r)
        (hsmall : (palCount (bytesOf s) : ℤ) < modulus), r.val = (palCount (bytesOf s) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s).
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100; there is a byte c such that s[i] = c for every i with 0 <= i < len(s). -/
  theorem spec_5 (s : Slice U8) (r : I64) (c : Nat)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hconst : ∀ b ∈ bytesOf s, b = c)
      (hret : count_palindromic_subsequences s = Result.ok r) :
      r.val = ((bytesOf s).length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (r : I64) (c : Nat)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hconst : ∀ b ∈ bytesOf s, b = c)
        (hret : count_palindromic_subsequences s = Result.ok r), r.val = ((bytesOf s).length : ℤ)) := by
    sorry

  /-- Whenever the function on s returns a result r, r ≡ C(reverse(s)) (mod 1000000007), where reverse(s) is the byte string of length len(s) with reverse(s)[i] = s[len(s)-1-i], and C is the count of distinct non-empty palindromic subsequences defined in spec_1.
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'). -/
  theorem spec_6 (s : Slice U8) (r : I64)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hret : count_palindromic_subsequences s = Result.ok r) :
      Int.ModEq modulus r.val (palCount (bytesOf s).reverse : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (r : I64)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hret : count_palindromic_subsequences s = Result.ok r), Int.ModEq modulus r.val (palCount (bytesOf s).reverse : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r ≡ C(t) + 1 + D (mod 1000000007), where C(t) is the number of distinct non-empty palindromic subsequences of t and C(empty)=0; D is the cardinality of the set of non-empty byte strings u such that u is a subsequence of L and reverse(u) is a subsequence of R, with reverse(u)[j] = u[len(u)-1-j].
    Preconditions: len(s) >= 1; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100; there is a byte c and an index k with 0 <= k < len(s) such that s[k]=c and s[i]!=c for every i != k; let t be the byte string obtained from s by deleting position k; let L = s[0..k] and R = s[k+1..len(s)] (empty when k=0 or k=len(s)-1 respectively). -/
  theorem spec_7 (s : Slice U8) (r : I64) (k : Nat) (c : Nat)
      (hlen : 1 ≤ (bytesOf s).length)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hk : k < (bytesOf s).length)
      (hc : (bytesOf s)[k]? = some c)
      (honly : ∀ i : Nat, i < (bytesOf s).length → i ≠ k → (bytesOf s)[i]? ≠ some c)
      (hret : count_palindromic_subsequences s = Result.ok r) :
      Int.ModEq modulus r.val
        ((palCount (removeAt (bytesOf s) k) + 1 +
            bridgeCount (prefixUpTo (bytesOf s) k) (suffixAfter (bytesOf s) k) : Nat) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (r : I64) (k : Nat) (c : Nat)
        (hlen : 1 ≤ (bytesOf s).length)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hk : k < (bytesOf s).length)
        (hc : (bytesOf s)[k]? = some c)
        (honly : ∀ i : Nat, i < (bytesOf s).length → i ≠ k → (bytesOf s)[i]? ≠ some c)
        (hret : count_palindromic_subsequences s = Result.ok r), Int.ModEq modulus r.val
          ((palCount (removeAt (bytesOf s) k) + 1 +
              bridgeCount (prefixUpTo (bytesOf s) k) (suffixAfter (bytesOf s) k) : Nat) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r ≡ 2*C(t) + 2 (mod 1000000007), where C(t) is the number of distinct non-empty palindromic subsequences of t, and C(empty) = 0.
    Preconditions: len(s) >= 2; len(s) <= 1000; for every i with 0 <= i < len(s), s[i] is one of the byte values 97, 98, 99, 100 (the ASCII codes of 'a','b','c','d'); let c = s[0] = s[len(s)-1]; c does not occur among s[1], ..., s[len(s)-2]; let t be the middle byte string s[1..len(s)-2], which is empty when len(s) = 2. -/
  theorem spec_8 (s : Slice U8) (r : I64) (c : Nat)
      (hlen_le : (bytesOf s).length ≤ 1000)
      (hab : onlyLetters (bytesOf s))
      (hlen2 : 2 ≤ (bytesOf s).length)
      (hfirst : (bytesOf s).head? = some c)
      (hlast : (bytesOf s).getLast? = some c)
      (hnomid : ∀ b ∈ middle (bytesOf s), b ≠ c)
      (hret : count_palindromic_subsequences s = Result.ok r) :
      Int.ModEq modulus r.val ((2 * palCount (middle (bytesOf s)) + 2 : Nat) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (r : I64) (c : Nat)
        (hlen_le : (bytesOf s).length ≤ 1000)
        (hab : onlyLetters (bytesOf s))
        (hlen2 : 2 ≤ (bytesOf s).length)
        (hfirst : (bytesOf s).head? = some c)
        (hlast : (bytesOf s).getLast? = some c)
        (hnomid : ∀ b ∈ middle (bytesOf s), b ≠ c)
        (hret : count_palindromic_subsequences s = Result.ok r), Int.ModEq modulus r.val ((2 * palCount (middle (bytesOf s)) + 2 : Nat) : ℤ)) := by
    sorry

  end AegisSpec.CountPalindromicSubsequences
