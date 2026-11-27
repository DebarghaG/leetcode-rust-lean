import Aegis.DistinctSubseqIi.Code.Funs

/-!
# Specifications of `Aegis.DistinctSubseqIi.distinct_subseq_ii`

LeetCode problem `distinct-subsequences-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistinctSubseqIi

def modulus : Nat := 1000000007

def InAlphabet (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def IsAlphabetPermutation (π : U8 → U8) : Prop :=
  (∀ b, InAlphabet b → InAlphabet (π b)) ∧
  (∀ b, InAlphabet b → ∃ a, InAlphabet a ∧ π a = b) ∧
  (∀ a b, InAlphabet a → InAlphabet b → π a = π b → a = b)

def subsequences : List U8 → Finset (List U8)
  | [] => {[]}
  | a :: l => subsequences l ∪ (subsequences l).image (fun t => a :: t)

def D (l : List U8) : Nat := ((subsequences l).erase []).card

/-- Let D(s) be the number of distinct non-empty byte sequences t such that there exist indices i_0,...,i_{len(t)-1} with 0 <= i_0 < ... < i_{len(t)-1} < len(s) and t[j] = s[i_j] for every 0 <= j < len(t). The function returns a result r and 0 <= r < 1_000_000_007 and r = D(s) mod 1_000_000_007.
  Preconditions: 1 <= len(s) <= 2000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_1 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b) :
    ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      0 ≤ r.val ∧ r.val < (modulus : Int) ∧
      r.val = ((D s.val % modulus : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b), ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      0 ≤ r.val ∧ r.val < (modulus : Int) ∧
      r.val = ((D s.val % modulus : Nat) : Int)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: 1 <= len(s) <= 2000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b) :
    ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b), ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < 1_000_000_007.
  Preconditions: 1 <= len(s) <= 2000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b) :
    ∀ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      0 ≤ r.val ∧ r.val < (modulus : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b), ∀ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      0 ≤ r.val ∧ r.val < (modulus : Int)) := by
  sorry

/-- Let D(s) be the number of distinct non-empty byte sequences t such that there exist indices i_0,...,i_{len(t)-1} with 0 <= i_0 < ... < i_{len(t)-1} < len(s) and t[j] = s[i_j] for every 0 <= j < len(t). The function returns r and r = D(s) exactly (not merely modulo).
  Preconditions: 1 <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and len(s) <= 29. -/
theorem spec_4 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b) (hlen29 : s.val.length ≤ 29) :
    ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (D s.val : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b) (hlen29 : s.val.length ≤ 29), ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (D s.val : Int)) := by
  sorry

/-- The function returns r and r = len(s).
  Preconditions: 1 <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i with 0 <= i < len(s), s[i] = s[0]. -/
theorem spec_5 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hconst : ∀ (i : Nat) (hi : i < s.val.length),
      s.val.get ⟨i, hi⟩ = s.val.get ⟨0, by omega⟩) :
    ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (s.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hconst : ∀ (i : Nat) (hi : i < s.val.length),
      s.val.get ⟨i, hi⟩ = s.val.get ⟨0, by omega⟩), ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (s.val.length : Int)) := by
  sorry

/-- The function returns r and r = (2^len(s) - 1) mod 1_000_000_007.
  Preconditions: 1 <= len(s) <= 2000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i, j with 0 <= i < j < len(s), s[i] != s[j]. -/
theorem spec_6 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < s.val.length),
      s.val.get ⟨i, by omega⟩ ≠ s.val.get ⟨j, hj⟩) :
    ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (((2 ^ s.val.length - 1) % modulus : Nat) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hdistinct : ∀ (i j : Nat) (hij : i < j) (hj : j < s.val.length),
      s.val.get ⟨i, by omega⟩ ≠ s.val.get ⟨j, hj⟩), ∃ r : I64, Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r ∧
      r.val = (((2 ^ s.val.length - 1) % modulus : Nat) : Int)) := by
  sorry

/-- Let rev(s) be the byte sequence of length len(s) with rev(s)[i] = s[len(s)-1-i] for 0 <= i < len(s). If r = distinct_subseq_ii(s) and r' = distinct_subseq_ii(rev(s)), then r = r'.
  Preconditions: 1 <= len(s) <= 2000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
theorem spec_7 (s srev : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hrev : srev.val = s.val.reverse) :
    ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii srev = ok r' → r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s srev : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hrev : srev.val = s.val.reverse), ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii srev = ok r' → r = r') := by
  sorry

/-- If r = distinct_subseq_ii(s) and r' = distinct_subseq_ii(t), then r = r'.
  Preconditions: s and t both satisfy 1 <= len <= 2000 and have all bytes in the range 97..122; len(s) = len(t); there exists a bijection π from {97,...,122} to itself such that t[i] = π(s[i]) for every 0 <= i < len(s). -/
theorem spec_8 (s t : Slice U8) (π : U8 → U8)
    (hlen_s : 1 ≤ s.val.length) (hlen_s2000 : s.val.length ≤ 2000)
    (hrange_s : ∀ b ∈ s.val, InAlphabet b)
    (hlen_t : 1 ≤ t.val.length) (hlen_t2000 : t.val.length ≤ 2000)
    (hrange_t : ∀ b ∈ t.val, InAlphabet b)
    (hlen_eq : s.val.length = t.val.length)
    (hπ : IsAlphabetPermutation π)
    (hmap : t.val = s.val.map π) :
    ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii t = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8) (π : U8 → U8)
    (hlen_s : 1 ≤ s.val.length) (hlen_s2000 : s.val.length ≤ 2000)
    (hrange_s : ∀ b ∈ s.val, InAlphabet b)
    (hlen_t : 1 ≤ t.val.length) (hlen_t2000 : t.val.length ≤ 2000)
    (hrange_t : ∀ b ∈ t.val, InAlphabet b)
    (hlen_eq : s.val.length = t.val.length)
    (hπ : IsAlphabetPermutation π)
    (hmap : t.val = s.val.map π), ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii t = ok r' → r = r') := by
  sorry

/-- Let s' be the byte sequence of length len(s)+1 with s'[i] = s[i] for 0 <= i < len(s) and s'[len(s)] = c. If r = distinct_subseq_ii(s) and r' = distinct_subseq_ii(s'), then r' = (2*r + 1) mod 1_000_000_007.
  Preconditions: s satisfies 1 <= len(s) <= 2000 and all bytes are in 97..122; len(s) < 2000; c is a byte with 97 <= c <= 122; and c != s[i] for every 0 <= i < len(s). -/
theorem spec_9 (s s' : Slice U8) (c : U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hfresh : ∀ b ∈ s.val, b ≠ c)
    (hs' : s'.val = s.val ++ [c]) :
    ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val + 1) % (modulus : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s s' : Slice U8) (c : U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hfresh : ∀ b ∈ s.val, b ≠ c)
    (hs' : s'.val = s.val ++ [c]), ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val + 1) % (modulus : Int)) := by
  sorry

/-- Let s' be the byte sequence of length len(s)+1 with s'[0] = c and s'[i+1] = s[i] for 0 <= i < len(s). If r = distinct_subseq_ii(s) and r' = distinct_subseq_ii(s'), then r' = (2*r + 1) mod 1_000_000_007.
  Preconditions: s satisfies 1 <= len(s) <= 2000 and all bytes are in 97..122; len(s) < 2000; c is a byte with 97 <= c <= 122; and c != s[i] for every 0 <= i < len(s). -/
theorem spec_10 (s s' : Slice U8) (c : U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hfresh : ∀ b ∈ s.val, b ≠ c)
    (hs' : s'.val = c :: s.val) :
    ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val + 1) % (modulus : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s s' : Slice U8) (c : U8)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hfresh : ∀ b ∈ s.val, b ≠ c)
    (hs' : s'.val = c :: s.val), ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val + 1) % (modulus : Int)) := by
  sorry

/-- If r_s = distinct_subseq_ii(s) and r_t = distinct_subseq_ii(t), then r_s <= r_t.
  Preconditions: s and t both satisfy 1 <= len <= 2000 and have all bytes in the range 97..122; len(t) <= 29; and s is a subsequence of t, meaning there exist indices i_0,...,i_{len(s)-1} with 0 <= i_0 < ... < i_{len(s)-1} < len(t) and s[j] = t[i_j] for every 0 <= j < len(s). -/
theorem spec_11 (s t : Slice U8)
    (hlen_s : 1 ≤ s.val.length) (hlen_s2000 : s.val.length ≤ 2000)
    (hrange_s : ∀ b ∈ s.val, InAlphabet b)
    (hlen_t : 1 ≤ t.val.length) (hlen_t2000 : t.val.length ≤ 2000)
    (hrange_t : ∀ b ∈ t.val, InAlphabet b)
    (hlen_t29 : t.val.length ≤ 29)
    (hsub : List.Sublist s.val t.val) :
    ∀ r_s r_t : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r_s →
      Aegis.DistinctSubseqIi.distinct_subseq_ii t = ok r_t →
      r_s.val ≤ r_t.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen_s : 1 ≤ s.val.length) (hlen_s2000 : s.val.length ≤ 2000)
    (hrange_s : ∀ b ∈ s.val, InAlphabet b)
    (hlen_t : 1 ≤ t.val.length) (hlen_t2000 : t.val.length ≤ 2000)
    (hrange_t : ∀ b ∈ t.val, InAlphabet b)
    (hlen_t29 : t.val.length ≤ 29)
    (hsub : List.Sublist s.val t.val), ∀ r_s r_t : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r_s →
      Aegis.DistinctSubseqIi.distinct_subseq_ii t = ok r_t →
      r_s.val ≤ r_t.val) := by
  sorry

/-- Let k be the largest index with s[k] = c, and let p be the prefix of s of length k, so p[i] = s[i] for 0 <= i < k. Let s' be the byte sequence of length len(s)+1 with s'[i] = s[i] for 0 <= i < len(s) and s'[len(s)] = c. Let D(p) be the number of distinct non-empty subsequences of p, with D(p) = 0 when p is empty. If r = distinct_subseq_ii(s) and r' = distinct_subseq_ii(s'), then r' = (2*r - (D(p) mod 1_000_000_007)) mod 1_000_000_007.
  Preconditions: s satisfies 1 <= len(s) <= 2000 and all bytes are in 97..122; len(s) < 2000; c is a byte with 97 <= c <= 122; and c occurs in s. -/
theorem spec_12 (s s' : Slice U8) (c : U8) (k : Nat)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hocc : c ∈ s.val)
    (hk : k < s.val.length)
    (hlast : s.val.get ⟨k, hk⟩ = c)
    (hmax : ∀ (j : Nat) (hj : j < s.val.length), k < j →
      s.val.get ⟨j, hj⟩ ≠ c)
    (hs' : s'.val = s.val ++ [c]) :
    ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val - ((D (s.val.take k) % modulus : Nat) : Int)) %
        (modulus : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s s' : Slice U8) (c : U8) (k : Nat)
    (hlen : 1 ≤ s.val.length) (hlen2000 : s.val.length ≤ 2000)
    (hlenlt : s.val.length < 2000)
    (hrange : ∀ b ∈ s.val, InAlphabet b)
    (hc : InAlphabet c) (hocc : c ∈ s.val)
    (hk : k < s.val.length)
    (hlast : s.val.get ⟨k, hk⟩ = c)
    (hmax : ∀ (j : Nat) (hj : j < s.val.length), k < j →
      s.val.get ⟨j, hj⟩ ≠ c)
    (hs' : s'.val = s.val ++ [c]), ∀ r r' : I64,
      Aegis.DistinctSubseqIi.distinct_subseq_ii s = ok r →
      Aegis.DistinctSubseqIi.distinct_subseq_ii s' = ok r' →
      r'.val = (2 * r.val - ((D (s.val.take k) % modulus : Nat) : Int)) %
        (modulus : Int)) := by
  sorry

end AegisSpec.DistinctSubseqIi
