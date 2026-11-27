import Aegis.CountLetters.Code.Funs

/-!
# Specifications of `Aegis.CountLetters.count_letters`

LeetCode problem `count-substrings-with-only-one-distinct-letter`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountLetters

def IsLowerByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def AllLower (s : Slice U8) : Prop := ∀ b ∈ s.val, IsLowerByte b

def ConstSubstring (s : List U8) (i j : ℕ) : Prop :=
  i ≤ j ∧ j < s.length ∧ ∀ k ∈ Finset.range s.length, i ≤ k → k ≤ j → s[k]? = s[i]?

noncomputable def constSubstringCount (s : List U8) : ℕ := by
  classical
  exact (((Finset.range s.length) ×ˢ (Finset.range s.length)).filter
    (fun q => ConstSubstring s q.1 q.2)).card

def tri (n : ℕ) : ℕ := n * (n + 1) / 2

def adjacentEqualCount (s : List U8) : ℕ :=
  ((Finset.range (s.length - 1)).filter (fun i => s[i]? = s[i + 1]?)).card

def runLengthsGo (prev : U8) (k : ℕ) : List U8 → List ℕ
  | [] => [k]
  | b :: bs => if b = prev then runLengthsGo prev (k + 1) bs else k :: runLengthsGo b 1 bs

def runLengths : List U8 → List ℕ
  | [] => []
  | b :: bs => runLengthsGo b 1 bs

def runSum (l : List ℕ) : ℕ := (l.map (fun k => k * (k + 1) / 2)).sum

/-- The function returns an integer result r (it does not fail), and r equals the number of pairs (i, j) of indices such that 0 <= i <= j < len(s) and s[k] = s[i] for every k with i <= k <= j. Equivalently, r is the number of nonempty contiguous substrings of s that contain only one distinct byte value.
  Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter (ASCII code 97 through 122). -/
theorem spec_1 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (constSubstringCount s.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (constSubstringCount s.val : ℤ)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail (no overflow, out-of-bounds access, or panic) on every input satisfying the preconditions.
  Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter. -/
theorem spec_2 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r) := by
  sorry

/-- Let E be the number of indices i with 0 <= i < len(s)-1 and s[i] = s[i+1]. The function returns an integer result r, and r >= len(s) + E.
  Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter. -/
theorem spec_3 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val ≥ ((s.val.length + adjacentEqualCount s.val : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val ≥ ((s.val.length + adjacentEqualCount s.val : ℕ) : ℤ)) := by
  sorry

/-- The function returns an integer result r, and r <= len(s) * (len(s) + 1) / 2.
  Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), s[i] is a lowercase English letter. -/
theorem spec_4 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val ≤ (tri s.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val ≤ (tri s.val.length : ℤ)) := by
  sorry

/-- The function returns an integer result r, and r = len(s) * (len(s) + 1) / 2.
  Preconditions: 1 <= len(s) <= 1000, all bytes of s are lowercase English letters, and for all i, j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j]. -/
theorem spec_5 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hall : ∀ i, i < s.val.length → ∀ j, j < s.val.length →
      s.val[i]? = s.val[j]?) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (tri s.val.length : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hall : ∀ i, i < s.val.length → ∀ j, j < s.val.length →
      s.val[i]? = s.val[j]?), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (tri s.val.length : ℤ)) := by
  sorry

/-- The function returns an integer result r, and r = len(s).
  Preconditions: 1 <= len(s) <= 1000, all bytes of s are lowercase English letters, and for every i with 0 <= i < len(s)-1, s[i] != s[i+1]. -/
theorem spec_6 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hadj : ∀ i, i + 1 < s.val.length → s.val[i]? ≠ s.val[i + 1]?) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (s.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hadj : ∀ i, i + 1 < s.val.length → s.val[i]? ≠ s.val[i + 1]?), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (s.val.length : ℤ)) := by
  sorry

/-- Let rev be the byte slice with len(rev) = len(s) and rev[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). The function returns results for s and rev, and count_letters(s) = count_letters(rev).
  Preconditions: 1 <= len(s) <= 1000 and all bytes of s are lowercase English letters. -/
theorem spec_7 (s rev : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) (hrev : rev.val = s.val.reverse) :
    ∃ r_s r_rev : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters rev = ok r_rev ∧ r_s = r_rev := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s rev : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) (hrev : rev.val = s.val.reverse), ∃ r_s r_rev : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters rev = ok r_rev ∧ r_s = r_rev) := by
  sorry

/-- If for all i, j with 0 <= i < len(s) and 0 <= j < len(s), s[i] = s[j] if and only if t[i] = t[j], then the function returns results for s and t, and count_letters(s) = count_letters(t).
  Preconditions: s and t are byte slices with 1 <= len(s) = len(t) <= 1000, and all bytes of both are lowercase English letters. -/
theorem spec_8 (s t : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen_eq : s.val.length = t.val.length)
    (hlen' : s.val.length ≤ 1000)
    (hlower_s : AllLower s) (hlower_t : AllLower t)
    (hsame : ∀ i, i < s.val.length → ∀ j, j < s.val.length →
      (s.val[i]? = s.val[j]? ↔ t.val[i]? = t.val[j]?)) :
    ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧ r_s = r_t := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s t : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen_eq : s.val.length = t.val.length)
    (hlen' : s.val.length ≤ 1000)
    (hlower_s : AllLower s) (hlower_t : AllLower t)
    (hsame : ∀ i, i < s.val.length → ∀ j, j < s.val.length →
      (s.val[i]? = s.val[j]? ↔ t.val[i]? = t.val[j]?)), ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧ r_s = r_t) := by
  sorry

/-- Let n = len(s), and let L be the positive integer such that s[n-L] = ... = s[n-1] and either L = n or s[n-L-1] != s[n-1]. Let t be the byte slice obtained by appending c to s, so len(t) = n+1, t[i] = s[i] for 0 <= i < n, and t[n] = c. The function does not fail on s or t; let r_s and r_t be the integers it returns for s and t respectively. If c = s[n-1], then r_t = r_s + L + 1; if c != s[n-1], then r_t = r_s + 1.
  Preconditions: 1 <= len(s) < 1000, all bytes of s are lowercase English letters, and c is a lowercase English letter. -/
theorem spec_9 (s t : Slice U8) (c : U8) (L : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length < 1000)
    (hlower : AllLower s) (hc : IsLowerByte c)
    (hL_pos : 0 < L) (hL_le : L ≤ s.val.length)
    (hL_all : ∀ k, s.val.length - L ≤ k → k < s.val.length →
      s.val[k]? = s.val[s.val.length - 1]?)
    (hL_max : L = s.val.length ∨
      s.val[s.val.length - L - 1]? ≠ s.val[s.val.length - 1]?)
    (ht : t.val = s.val ++ [c]) :
    ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧
      (s.val[s.val.length - 1]? = some c → r_t.val = r_s.val + (L : ℤ) + 1) ∧
      (s.val[s.val.length - 1]? ≠ some c → r_t.val = r_s.val + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s t : Slice U8) (c : U8) (L : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length < 1000)
    (hlower : AllLower s) (hc : IsLowerByte c)
    (hL_pos : 0 < L) (hL_le : L ≤ s.val.length)
    (hL_all : ∀ k, s.val.length - L ≤ k → k < s.val.length →
      s.val[k]? = s.val[s.val.length - 1]?)
    (hL_max : L = s.val.length ∨
      s.val[s.val.length - L - 1]? ≠ s.val[s.val.length - 1]?)
    (ht : t.val = s.val ++ [c]), ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧
      (s.val[s.val.length - 1]? = some c → r_t.val = r_s.val + (L : ℤ) + 1) ∧
      (s.val[s.val.length - 1]? ≠ some c → r_t.val = r_s.val + 1)) := by
  sorry

/-- Let t be the byte slice obtained by inserting c at position p: len(t) = len(s)+1, t[k] = s[k] for 0 <= k < p, t[p] = c, and t[k] = s[k-1] for p < k <= len(s). The function does not fail on s or t; let r_s and r_t be the integers it returns for s and t respectively. Then r_t = r_s + 1.
  Preconditions: 1 <= len(s) < 1000, all bytes of s are lowercase English letters, c is a lowercase English letter, p is an integer with 0 < p < len(s), s[p-1] != s[p], c != s[p-1], and c != s[p]. -/
theorem spec_10 (s t : Slice U8) (c : U8) (p : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) (hc : IsLowerByte c)
    (hp_pos : 0 < p) (hp_lt : p < s.val.length)
    (hne_adj : s.val[p - 1]? ≠ s.val[p]?)
    (hne_c_prev : s.val[p - 1]? ≠ some c)
    (hne_c_cur : s.val[p]? ≠ some c)
    (ht : t.val = s.val.take p ++ [c] ++ s.val.drop p) :
    ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧ r_t.val = r_s.val + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8) (c : U8) (p : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) (hc : IsLowerByte c)
    (hp_pos : 0 < p) (hp_lt : p < s.val.length)
    (hne_adj : s.val[p - 1]? ≠ s.val[p]?)
    (hne_c_prev : s.val[p - 1]? ≠ some c)
    (hne_c_cur : s.val[p]? ≠ some c)
    (ht : t.val = s.val.take p ++ [c] ++ s.val.drop p), ∃ r_s r_t : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters t = ok r_t ∧ r_t.val = r_s.val + 1) := by
  sorry

/-- Let p be the prefix of s of length k, so p[i] = s[i] for every i with 0 <= i < k. The function does not fail on s or p; let r_s and r_p be the integers it returns for s and p respectively. Then r_p <= r_s.
  Preconditions: 1 <= len(s) <= 1000, all bytes of s are lowercase English letters, and k is an integer with 1 <= k <= len(s). -/
theorem spec_11 (s p : Slice U8) (k : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ s.val.length)
    (hp : p.val = s.val.take k) :
    ∃ r_s r_p : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters p = ok r_p ∧ r_p.val ≤ r_s.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s p : Slice U8) (k : ℕ)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s)
    (hk_pos : 1 ≤ k) (hk_le : k ≤ s.val.length)
    (hp : p.val = s.val.take k), ∃ r_s r_p : I64,
      Aegis.CountLetters.count_letters s = ok r_s ∧
      Aegis.CountLetters.count_letters p = ok r_p ∧ r_p.val ≤ r_s.val) := by
  sorry

/-- Let l_1, ..., l_m be the lengths of the maximal contiguous runs of equal bytes in s, in order. The function returns an integer result r (it does not fail), and r = sum_{j=1}^{m} l_j * (l_j + 1) / 2.
  Preconditions: 1 <= len(s) <= 1000 and every byte of s is a lowercase English letter. -/
theorem spec_12 (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s) :
    ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (runSum (runLengths s.val) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8)
    (hlen : 1 ≤ s.val.length) (hlen' : s.val.length ≤ 1000)
    (hlower : AllLower s), ∃ r : I64, Aegis.CountLetters.count_letters s = ok r ∧
      r.val = (runSum (runLengths s.val) : ℤ)) := by
  sorry

end AegisSpec.CountLetters
