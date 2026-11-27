import Aegis.LongestRepeatingSubstring.Code.Funs

/-!
# Specifications of `Aegis.LongestRepeatingSubstring.longest_repeating_substring`

LeetCode problem `longest-repeating-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestRepeatingSubstring

namespace AegisSpec.LongestRepeatingSubstring

def byte (s : Slice U8) (i : ℕ) : ℕ :=
  match s.val[i]? with
  | some b => b.val
  | none => 0

def Pre (s : Slice U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 2000 ∧
    ∀ i, i < s.val.length → 97 ≤ byte s i ∧ byte s i ≤ 122

def SameBlock (s : Slice U8) (i j L : ℕ) : Prop :=
  ∀ k, k < L → byte s (i + k) = byte s (j + k)

def Repeats (s : Slice U8) (L : ℕ) : Prop :=
  ∃ i j, i < j ∧ i + L ≤ s.val.length ∧ j + L ≤ s.val.length ∧ SameBlock s i j L

def IsLongestRepeatingSubstring (s : Slice U8) (r : ℤ) : Prop :=
  0 ≤ r ∧ r ≤ (s.val.length : ℤ) ∧
    (r = 0 ∨ Repeats s r.toNat) ∧
    ∀ L : ℕ, L ≤ s.val.length → (L = 0 ∨ Repeats s L) → (L : ℤ) ≤ r

def Reversed (s t : Slice U8) : Prop :=
  t.val = s.val.reverse

/-- Let n = len(s). Whenever the call returns Result.ok r, r is the largest integer L with 0 <= L <= n such that either L = 0, or there exist integers i and j with 0 <= i < j, i+L <= n, j+L <= n, and for every k with 0 <= k < L, s[i+k] = s[j+k]. Equivalently, r is 0 if no nonempty contiguous substring of s occurs at two distinct starting positions; otherwise r is the maximum length of a nonempty contiguous substring of s that occurs at two distinct starting positions (the two occurrences may overlap).
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_1 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r → IsLongestRepeatingSubstring s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r → IsLongestRepeatingSubstring s r.val) := by
  sorry

/-- For every s satisfying the preconditions, the call longest_repeating_substring(s) returns Result.ok r for some I64 value r; it does not fail (no overflow, out-of-bounds indexing, or panic).
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_2 (s : Slice U8) (hpre : Pre s) :
    ∃ r : I64, longest_repeating_substring s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∃ r : I64, longest_repeating_substring s = ok r) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, 0 <= r <= n-1. In particular r < n.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_3 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) - 1) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r with r > 0, there exist integers i and j with 0 <= i < j, i+r <= n, j+r <= n, and for every k with 0 <= k < r, s[i+k] = s[j+k]. Thus a length-r contiguous substring actually occurs at two distinct starting positions.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_4 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r → 0 < r.val → Repeats s r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r → 0 < r.val → Repeats s r.val.toNat) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, for every integer L with 0 <= L <= n and every pair of integers i and j with 0 <= i < j, i+L <= n, j+L <= n, if s[i+k] = s[j+k] for every k with 0 <= k < L, then L <= r. Equivalently, no contiguous substring of length greater than r occurs at two distinct starting positions.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_5 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, L ≤ s.val.length → Repeats s L → (L : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, L ≤ s.val.length → Repeats s L → (L : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, for every integer L with 1 <= L <= n-1, the following are equivalent: (a) L <= r; (b) there exist integers i and j with 0 <= i < j, i+L <= n, j+L <= n, and s[i+k] = s[j+k] for every k with 0 <= k < L. In words, the set of positive repeated lengths is exactly {1, 2, ..., r}, empty when r = 0.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_6 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length - 1 → ((L : ℤ) ≤ r.val ↔ Repeats s L) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, 1 ≤ L → L ≤ s.val.length - 1 → ((L : ℤ) ≤ r.val ↔ Repeats s L)) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, r = 0 if and only if for every pair of indices i and j with 0 <= i < j < n, s[i] != s[j]. Equivalently, r > 0 if and only if some byte value occurs at least twice in s.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_7 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j < s.val.length → byte s i ≠ byte s j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      (r.val = 0 ↔ ∀ i j : ℕ, i < j → j < s.val.length → byte s i ≠ byte s j)) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, for every integer interval [a,b] with 0 <= a <= b < n such that s[t] = s[a] for every t with a <= t <= b, if k = b-a+1, then r >= k-1. In particular, a contiguous run of k identical bytes forces a repeated substring of length k-1.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_8 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ a b : ℕ, a ≤ b → b < s.val.length →
        (∀ t, a ≤ t → t ≤ b → byte s t = byte s a) →
        ((b - a + 1 : ℕ) : ℤ) - 1 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ a b : ℕ, a ≤ b → b < s.val.length →
        (∀ t, a ≤ t → t ≤ b → byte s t = byte s a) →
        ((b - a + 1 : ℕ) : ℤ) - 1 ≤ r.val) := by
  sorry

/-- Let n = len(s). Whenever the call returns Result.ok r, for every integer L with 1 <= L < n such that s[k] = s[n-L+k] for every k with 0 <= k < L (i.e. a proper prefix of s of length L equals the suffix of s of length L), we have r >= L.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_9 (s : Slice U8) (hpre : Pre s) :
    ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, 1 ≤ L → L < s.val.length →
        (∀ k, k < L → byte s k = byte s (s.val.length - L + k)) → (L : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ r : I64, longest_repeating_substring s = ok r →
      ∀ L : ℕ, 1 ≤ L → L < s.val.length →
        (∀ k, k < L → byte s k = byte s (s.val.length - L + k)) → (L : ℤ) ≤ r.val) := by
  sorry

/-- Let n = len(s). Define rev(s) to be the length-n byte slice with rev(s)[i] = s[n-1-i] for every i with 0 <= i < n. If the call on s returns Result.ok r and the call on rev(s) returns Result.ok r', then r = r'.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_10 (s : Slice U8) (hpre : Pre s) :
    ∀ t : Slice U8, Reversed s t →
      ∀ r r' : I64, longest_repeating_substring s = ok r →
        longest_repeating_substring t = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ t : Slice U8, Reversed s t →
      ∀ r r' : I64, longest_repeating_substring s = ok r →
        longest_repeating_substring t = ok r' → r = r') := by
  sorry

/-- Let n = len(s). Let t be any byte slice of length n that also satisfies the lowercase precondition (1 <= n <= 2000 and all its bytes are in 97..122). Suppose that for all indices p and q with 0 <= p < q < n, s[p] = s[q] if and only if t[p] = t[q]. If the call on s returns Result.ok r and the call on t returns Result.ok r', then r = r'.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_11 (s t : Slice U8) (hpre_s : Pre s) (hpre_t : Pre t)
    (hlen : t.val.length = s.val.length)
    (hpat : ∀ p q : ℕ, p < q → q < s.val.length →
      (byte s p = byte s q ↔ byte t p = byte t q)) :
    ∀ r r' : I64, longest_repeating_substring s = ok r →
      longest_repeating_substring t = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8) (hpre_s : Pre s) (hpre_t : Pre t)
    (hlen : t.val.length = s.val.length)
    (hpat : ∀ p q : ℕ, p < q → q < s.val.length →
      (byte s p = byte s q ↔ byte t p = byte t q)), ∀ r r' : I64, longest_repeating_substring s = ok r →
      longest_repeating_substring t = ok r' → r = r') := by
  sorry

/-- Let n = len(s). For any integers a and b with 0 <= a <= b < n, let t be the contiguous substring of s defined by len(t) = b-a+1 and t[k] = s[a+k] for 0 <= k < len(t). If the call on s returns Result.ok r and the call on t returns Result.ok r_t, then r_t <= r.
  Preconditions: Let n = len(s). The preconditions are: 1 <= n <= 2000, and for every i with 0 <= i < n, the byte s[i] is a lowercase English letter (97 <= s[i] <= 122). -/
theorem spec_12 (s : Slice U8) (hpre : Pre s) :
    ∀ (u : Slice U8) (a b : ℕ), a ≤ b → b < s.val.length →
      u.val.length = b - a + 1 →
      (∀ k, k < u.val.length → byte u k = byte s (a + k)) →
      ∀ r r_t : I64, longest_repeating_substring s = ok r →
        longest_repeating_substring u = ok r_t → r_t.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (hpre : Pre s), ∀ (u : Slice U8) (a b : ℕ), a ≤ b → b < s.val.length →
      u.val.length = b - a + 1 →
      (∀ k, k < u.val.length → byte u k = byte s (a + k)) →
      ∀ r r_t : I64, longest_repeating_substring s = ok r →
        longest_repeating_substring u = ok r_t → r_t.val ≤ r.val) := by
  sorry

end AegisSpec.LongestRepeatingSubstring
