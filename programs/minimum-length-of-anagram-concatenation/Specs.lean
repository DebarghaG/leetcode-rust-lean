import Aegis.MinAnagramLength.Code.Funs

/-!
# Specifications of `Aegis.MinAnagramLength.min_anagram_length`

LeetCode problem `minimum-length-of-anagram-concatenation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinAnagramLength

namespace AegisSpec.MinAnagramLength

open Aeneas Aeneas.Std Result

def byteAt (s : Slice U8) (i : Nat) : Nat :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def countByte (l : List U8) (c : Nat) : Nat :=
  match l with
  | [] => 0
  | b :: bs => (if b.val = c then 1 else 0) + countByte bs c

def cntList (l : List U8) (c : Nat) (a b : Nat) : Nat :=
  countByte ((l.drop a).take (b - a)) c

def cnt (s : Slice U8) (c : Nat) (a b : Nat) : Nat :=
  cntList s.val c a b

def uniformBlocks (l : List U8) (L : Nat) : Prop :=
  0 < L ∧ L ∣ l.length ∧
    ∀ j, j < l.length / L → ∀ c, cntList l c (j * L) ((j + 1) * L) = cntList l c 0 L

def IsMinAnagramLength (l : List U8) (L : Nat) : Prop :=
  uniformBlocks l L ∧ ∀ L' : Nat, L' < L → ¬ uniformBlocks l L'

def revBytes (s : Slice U8) : List U8 := s.val.reverse

def countsGcd (l : List U8) : Nat :=
  ((l.map (fun b => b.val)).eraseDups).foldr (fun c acc => Nat.gcd (countByte l c) acc) 0

/-- Let n = len(s). For a byte c and integers a,b, let cnt(c,a,b) be the number of indices i with a <= i < b and s[i] = c. The function returns a result r, and r is the least positive integer L such that: (1) L divides n; (2) for every j with 0 <= j < n/L and every byte c, cnt(c, j*L, (j+1)*L) = cnt(c, 0, L). Equivalently, r is the minimum possible length of a string t such that s is the concatenation of n/L consecutive length-L blocks, all anagrams of t, i.e. all having the same byte multiset.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r : I64, min_anagram_length s = ok r ∧ IsMinAnagramLength s.val r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : I64, min_anagram_length s = ok r ∧ IsMinAnagramLength s.val r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(s).
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r → 1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r → 1 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1 and len(s) is divisible by r, i.e. len(s) mod r = 0.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      1 ≤ r.val ∧ (s.val.length : Int) % r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      1 ≤ r.val ∧ (s.val.length : Int) % r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, let n = len(s) and m = n/r. Then r >= 1 and r divides n, and there exists a byte string t of length r such that for every j with 0 <= j < m, the block s[j*r .. (j+1)*r) is an anagram of t: for every byte c, the number of occurrences of c in that block equals the number of occurrences of c in t.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      1 ≤ r.val ∧ (r.val ∣ (s.val.length : Int)) ∧
        ∃ t : List U8, t.length = r.val.toNat ∧
          ∀ j, j < s.val.length / r.val.toNat → ∀ c,
            cnt s c (j * r.val.toNat) ((j + 1) * r.val.toNat) = countByte t c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      1 ≤ r.val ∧ (r.val ∣ (s.val.length : Int)) ∧
        ∃ t : List U8, t.length = r.val.toNat ∧
          ∀ j, j < s.val.length / r.val.toNat → ∀ c,
            cnt s c (j * r.val.toNat) ((j + 1) * r.val.toNat) = countByte t c) := by
  sorry

/-- Whenever the function returns a result r, for every integer L with 1 <= L < r that divides len(s), the len(s)/L consecutive blocks s[j*L .. (j+1)*L), 0 <= j < len(s)/L, do not all have the same byte multiset. That is, there exist block indices j,k and a byte c such that the number of c's in block j differs from the number of c's in block k.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ∀ L : Nat, 1 ≤ L → L < r.val.toNat → L ∣ s.val.length →
        ¬ (∀ j, j < s.val.length / L → ∀ c,
            cnt s c (j * L) ((j + 1) * L) = cnt s c 0 L) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ∀ L : Nat, 1 ≤ L → L < r.val.toNat → L ∣ s.val.length →
        ¬ (∀ j, j < s.val.length / L → ∀ c,
            cnt s c (j * L) ((j + 1) * L) = cnt s c 0 L)) := by
  sorry

/-- Whenever the function returns a result r, let n = len(s) and m = n/r. For every byte c, the total number of occurrences of c in s is divisible by m. Equivalently, if cnt(c) is the number of positions i with 0 <= i < n and s[i] = c, then cnt(c) mod m = 0.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ∀ c : Nat, countByte s.val c % (s.val.length / r.val.toNat) = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ∀ c : Nat, countByte s.val c % (s.val.length / r.val.toNat) = 0) := by
  sorry

/-- Whenever the function returns a result r, let n = len(s) and m = n/r. For every byte c and every j with 0 <= j < m, the number of occurrences of c in s[j*r .. (j+1)*r) equals cnt(c,0,n)/m, where cnt(c,0,n) is the total number of occurrences of c in s and the quotient is the exact integer quotient.
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ∀ c j : Nat, j < s.val.length / r.val.toNat →
        cnt s c (j * r.val.toNat) ((j + 1) * r.val.toNat)
          = countByte s.val c / (s.val.length / r.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ∀ c j : Nat, j < s.val.length / r.val.toNat →
        cnt s c (j * r.val.toNat) ((j + 1) * r.val.toNat)
          = countByte s.val c / (s.val.length / r.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(s) >= 1, len(s) <= 100000, every byte is an ASCII lowercase letter, and for all i,j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
theorem spec_8 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (heq : ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) :
    ∀ r : I64, min_anagram_length s = ok r → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (heq : ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j), ∀ r : I64, min_anagram_length s = ok r → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = len(s).
  Preconditions: len(s) >= 1, len(s) <= 100000, every byte is an ASCII lowercase letter, and for all i,j with 0 <= i < j < len(s), s[i] != s[j]. -/
theorem spec_9 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hne : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j) :
    ∀ r : I64, min_anagram_length s = ok r → r.val = (s.val.length : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
    (hne : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j), ∀ r : I64, min_anagram_length s = ok r → r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, if all bytes of s are equal then r = 1, and if not all bytes of s are equal then r = len(s).
  Preconditions: len(s) >= 2, len(s) <= 100000, len(s) is prime, and every byte of s is an ASCII lowercase letter. -/
theorem spec_10 (s : Slice U8)
    (hlen1 : 2 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hprime : Nat.Prime s.val.length)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ((∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) → r.val = 1) ∧
      ((¬ ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) →
        r.val = (s.val.length : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 2 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hprime : Nat.Prime s.val.length)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ((∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) → r.val = 1) ∧
      ((¬ ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) →
        r.val = (s.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r, for every positive integer d that divides len(s), if s[i] = s[i mod d] for every i with 0 <= i < len(s), then r <= d.
  Preconditions: len(s) >= 1, len(s) <= 100000, and every byte of s is an ASCII lowercase letter. -/
theorem spec_11 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ∀ d : Nat, 0 < d → d ∣ s.val.length →
        (∀ i, i < s.val.length → byteAt s i = byteAt s (i % d)) → r.val ≤ (d : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ∀ d : Nat, 0 < d → d ∣ s.val.length →
        (∀ i, i < s.val.length → byteAt s i = byteAt s (i % d)) → r.val ≤ (d : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every L with 1 <= L <= len(s) such that L divides len(s), if all len(s)/L blocks s[j*L .. (j+1)*L) for 0 <= j < len(s)/L have the same byte multiset, then r <= L.
  Preconditions: len(s) >= 1, len(s) <= 100000, and every byte of s is an ASCII lowercase letter. -/
theorem spec_12 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      ∀ L : Nat, 1 ≤ L → L ≤ s.val.length → L ∣ s.val.length →
        (∀ j, j < s.val.length / L → ∀ c,
            cnt s c (j * L) ((j + 1) * L) = cnt s c 0 L) → r.val ≤ (L : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      ∀ L : Nat, 1 ≤ L → L ≤ s.val.length → L ∣ s.val.length →
        (∀ j, j < s.val.length / L → ∀ c,
            cnt s c (j * L) ((j + 1) * L) = cnt s c 0 L) → r.val ≤ (L : Int)) := by
  sorry

/-- Let n = len(s) and define the reversed byte string s_rev by s_rev[i] = s[n-1-i] for 0 <= i < n. Whenever the function returns a result r, r is also the least positive integer L such that L divides n and all n/L consecutive blocks of s_rev of length L have the same byte multiset. Equivalently, reversing the input string does not change the minimum anagram length.
  Preconditions: len(s) >= 1, len(s) <= 100000, and every byte of s is an ASCII lowercase letter. -/
theorem spec_13 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r → IsMinAnagramLength (revBytes s) r.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r → IsMinAnagramLength (revBytes s) r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, let G be the greatest common divisor of all positive numbers cnt(c,0,len(s)) over bytes c that occur in s, where cnt(c,0,len(s)) is the total number of occurrences of c in s. Then r >= len(s)/G.
  Preconditions: len(s) >= 1, len(s) <= 100000, and every byte of s is an ASCII lowercase letter. -/
theorem spec_14 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      s.val.length / countsGcd s.val ≤ r.val.toNat := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      s.val.length / countsGcd s.val ≤ r.val.toNat) := by
  sorry

/-- The function returns a result r; it does not fail due to panic, out-of-bounds access, or 64-bit integer overflow.
  Preconditions: len(s) >= 1, len(s) <= 100000, and every byte of s is an ASCII lowercase letter. -/
theorem spec_15 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∃ r : I64, min_anagram_length s = ok r := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : I64, min_anagram_length s = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if for all i,j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j].
  Preconditions: len(s) >= 1, len(s) <= 100000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_16 (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
    ∀ r : I64, min_anagram_length s = ok r →
      (r.val = 1 ↔ ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice U8)
    (hlen1 : 1 ≤ s.val.length) (hlen2 : s.val.length ≤ 100000)
    (hlower : ∀ i, i < s.val.length → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : I64, min_anagram_length s = ok r →
      (r.val = 1 ↔ ∀ i j, i < s.val.length → j < s.val.length → byteAt s i = byteAt s j)) := by
  sorry

end AegisSpec.MinAnagramLength
