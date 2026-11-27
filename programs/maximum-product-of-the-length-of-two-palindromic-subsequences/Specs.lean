import Aegis.MaxProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxProduct.max_product`

LeetCode problem `maximum-product-of-the-length-of-two-palindromic-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxProduct

abbrev IsLowerAscii (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def seqOf (s : Slice U8) (I : Finset (Fin s.val.length)) : List U8 :=
  ((List.finRange s.val.length).filter (fun i => decide (i ∈ I))).map (fun i => s.val.get i)

abbrev PalindromicFor (s : Slice U8) (I : Finset (Fin s.val.length)) : Prop :=
  seqOf s I = (seqOf s I).reverse

abbrev IsAdmissiblePair (s : Slice U8) (I J : Finset (Fin s.val.length)) : Prop :=
  I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ PalindromicFor s I ∧ PalindromicFor s J

def maxPalProduct (s : Slice U8) : ℕ :=
  ((Finset.univ : Finset (Fin s.val.length)).powerset.product
      (Finset.univ : Finset (Fin s.val.length)).powerset).sup
    (fun p : Finset (Fin s.val.length) × Finset (Fin s.val.length) =>
      if IsAdmissiblePair s p.1 p.2 then p.1.card * p.2.card else 0)

def IsSubsequenceOf (s t : List U8) : Prop :=
  ∃ k : Fin s.length → ℕ, ∃ hk : ∀ i, k i < t.length,
    StrictMono k ∧ ∀ i, s.get i = t.get ⟨k i, hk i⟩

/-- Let n = len(s). For an index set I subset of {0,...,n-1}, let seq(s,I) be the byte sequence obtained by listing s[i] for i in I in increasing order, and call I palindromic for s if seq(s,I) equals its reverse. Whenever max_product(s) returns a result r, r is exactly the maximum of |I| * |J| over all ordered pairs (I,J) of nonempty finite subsets of {0,...,n-1} such that I and J are disjoint and both I and J are palindromic for s. The order of the two subsequences is irrelevant, so using an ordered pair does not change the maximum.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'). -/
theorem spec_1 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      r.val = (maxPalProduct s : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      r.val = (maxPalProduct s : ℤ)) := by
  sorry

/-- For every s satisfying the preconditions, max_product(s) returns a result r (there is an I64 value r such that the call succeeds); it does not fail, panic, overflow, or access out of bounds.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'). -/
theorem spec_2 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) :
    ∃ r : I64, Aegis.MaxProduct.max_product s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b), ∃ r : I64, Aegis.MaxProduct.max_product s = ok r) := by
  sorry

/-- Whenever max_product(s) returns a result r, 0 <= r and r <= floor(len(s)^2 / 4), where floor(x) is the greatest integer not exceeding x. Equivalently, r <= (len(s) * len(s)) / 4 using integer division.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'). -/
theorem spec_3 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * s.val.length / 4 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length * s.val.length / 4 : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_product(s) returns a result r, r >= 1.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'). -/
theorem spec_4 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever max_product(s) returns a result r, r = 1.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'), and len(s) = 2. -/
theorem spec_5 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) (hlen_two : s.val.length = 2) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) (hlen_two : s.val.length = 2), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → r.val = 1) := by
  sorry

/-- Whenever max_product(s) returns a result r, r = floor(len(s)^2 / 4), where floor(x) is the greatest integer not exceeding x.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'), and there exists a byte c such that for every i with 0 <= i < len(s), s[i] = c. -/
theorem spec_6 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b)
    (hconst : ∃ c : U8, ∀ b ∈ s.val, b = c) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      r.val = ((s.val.length * s.val.length / 4 : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b)
    (hconst : ∃ c : U8, ∀ b ∈ s.val, b = c), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      r.val = ((s.val.length * s.val.length / 4 : ℕ) : ℤ)) := by
  sorry

/-- Whenever max_product(s) returns a result r, r >= 2.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'), len(s) >= 3, and there exist indices i,j with 0 <= i < j < len(s) and s[i] = s[j]. -/
theorem spec_7 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) (hlen_three : 3 ≤ s.val.length)
    (hrepeat : ∃ i j : Fin s.val.length, i < j ∧ s.val.get i = s.val.get j) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → 2 ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) (hlen_three : 3 ≤ s.val.length)
    (hrepeat : ∃ i j : Fin s.val.length, i < j ∧ s.val.get i = s.val.get j), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r → 2 ≤ r.val) := by
  sorry

/-- Whenever max_product(s) returns a result r and max_product(t) returns a result r', it holds that r = r'.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'), and t is the reversal of s, meaning len(t) = len(s) and t[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). -/
theorem spec_8 (s t : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b)
    (hrev : t.val = s.val.reverse) :
    ∀ r r' : I64, Aegis.MaxProduct.max_product s = ok r →
      Aegis.MaxProduct.max_product t = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b)
    (hrev : t.val = s.val.reverse), ∀ r r' : I64, Aegis.MaxProduct.max_product s = ok r →
      Aegis.MaxProduct.max_product t = ok r' → r = r') := by
  sorry

/-- Whenever max_product(s) returns a result r_s and max_product(t) returns a result r_t, it holds that r_t >= r_s.
  Preconditions: s and t both satisfy 2 <= len(s) <= 12, 2 <= len(t) <= 12, and consist only of ASCII lowercase English letters; and s is a subsequence of t, meaning there exist indices 0 <= k_0 < k_1 < ... < k_{len(s)-1} < len(t) such that s[i] = t[k_i] for every i with 0 <= i < len(s). -/
theorem spec_9 (s t : Slice U8)
    (hs_lo : 2 ≤ s.val.length) (hs_hi : s.val.length ≤ 12)
    (hs_lower : ∀ b ∈ s.val, IsLowerAscii b)
    (ht_lo : 2 ≤ t.val.length) (ht_hi : t.val.length ≤ 12)
    (ht_lower : ∀ b ∈ t.val, IsLowerAscii b)
    (hsub : IsSubsequenceOf s.val t.val) :
    ∀ rs rt : I64, Aegis.MaxProduct.max_product s = ok rs →
      Aegis.MaxProduct.max_product t = ok rt → rs.val ≤ rt.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice U8)
    (hs_lo : 2 ≤ s.val.length) (hs_hi : s.val.length ≤ 12)
    (hs_lower : ∀ b ∈ s.val, IsLowerAscii b)
    (ht_lo : 2 ≤ t.val.length) (ht_hi : t.val.length ≤ 12)
    (ht_lower : ∀ b ∈ t.val, IsLowerAscii b)
    (hsub : IsSubsequenceOf s.val t.val), ∀ rs rt : I64, Aegis.MaxProduct.max_product s = ok rs →
      Aegis.MaxProduct.max_product t = ok rt → rs.val ≤ rt.val) := by
  sorry

/-- Whenever max_product(s) returns a result r, there exist nonempty disjoint finite index sets I,J subset of {0,...,len(s)-1} such that |I| * |J| = r and both I and J are palindromic for s, where an index set I is palindromic for s if, when its elements are written in increasing order, the corresponding bytes s[i] form a palindrome.
  Preconditions: len(s) is an integer with 2 <= len(s) <= 12, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase English letter ('a' through 'z'). -/
theorem spec_10 (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b) :
    ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      ∃ I J : Finset (Fin s.val.length),
        I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ PalindromicFor s I ∧
          PalindromicFor s J ∧ ((I.card * J.card : ℕ) : ℤ) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8)
    (hlen_lo : 2 ≤ s.val.length) (hlen_hi : s.val.length ≤ 12)
    (hlower : ∀ b ∈ s.val, IsLowerAscii b), ∀ r : I64, Aegis.MaxProduct.max_product s = ok r →
      ∃ I J : Finset (Fin s.val.length),
        I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧ PalindromicFor s I ∧
          PalindromicFor s J ∧ ((I.card * J.card : ℕ) : ℤ) = r.val) := by
  sorry

end AegisSpec.MaxProduct
