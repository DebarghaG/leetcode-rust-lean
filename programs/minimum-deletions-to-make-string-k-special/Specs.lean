import Aegis.MinimumDeletions.Code.Funs

/-!
# Specifications of `Aegis.MinimumDeletions.minimum_deletions`

LeetCode problem `minimum-deletions-to-make-string-k-special`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumDeletions

namespace AegisSpec.MinimumDeletions

def cnt (word : Slice Std.U8) (c : Fin 26) : ℕ :=
  (word.val.filter (fun b : Std.U8 => b.val = 97 + c.val)).length

def maxCnt (word : Slice Std.U8) : ℕ :=
  Finset.univ.sup (cnt word)

def admissible (word : Slice Std.U8) (k : Std.I64) (g : Fin 26 → ℕ) : Prop :=
  (∀ c, g c ≤ cnt word c) ∧
    (∀ c d, 1 ≤ g c → 1 ≤ g d → |(g c : ℤ) - (g d : ℤ)| ≤ k.val)

def keep (k : Std.I64) (t x : ℕ) : ℕ :=
  if x < t then 0 else if x ≤ t + k.val.toNat then x else t + k.val.toNat

def countFreq (word : Slice Std.U8) (v : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Fin 26 => cnt word c = v)).card

def freq (s : List Std.U8) (c : Fin 26) : ℕ :=
  (s.filter (fun b : Std.U8 => b.val = 97 + c.val)).length

def KSpecial (k : Std.I64) (s : List Std.U8) : Prop :=
  ∀ c d : Fin 26, 1 ≤ freq s c → 1 ≤ freq s d →
    |(freq s c : ℤ) - (freq s d : ℤ)| ≤ k.val

/-- Let cnt(c), for a lowercase letter c, be the number of indices i with 0 <= i < len(word) and word[i] = c. Call a function g from the 26 lowercase letters to the non-negative integers admissible when (a) g(c) <= cnt(c) for every lowercase letter c, and (b) |g(c) - g(d)| <= k for all lowercase letters c, d with g(c) >= 1 and g(d) >= 1. The function returns a result r, and r = len(word) - M, where M = max { (sum over the 26 lowercase letters c of g(c)) : g is admissible } (this maximum exists, because the identically zero function is admissible).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_1 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r : Std.I64,
      minimum_deletions word k = ok r ∧
        (∃ g : Fin 26 → ℕ,
          admissible word k g ∧
            (r.val : ℤ) = (word.val.length : ℤ) - (∑ c : Fin 26, (g c : ℤ)) ∧
              (∀ g' : Fin 26 → ℕ, admissible word k g' →
                (∑ c : Fin 26, (g' c : ℤ)) ≤ (∑ c : Fin 26, (g c : ℤ)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64,
      minimum_deletions word k = ok r ∧
        (∃ g : Fin 26 → ℕ,
          admissible word k g ∧
            (r.val : ℤ) = (word.val.length : ℤ) - (∑ c : Fin 26, (g c : ℤ)) ∧
              (∀ g' : Fin 26 → ℕ, admissible word k g' →
                (∑ c : Fin 26, (g' c : ℤ)) ≤ (∑ c : Fin 26, (g c : ℤ))))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r: it does not fail (no arithmetic overflow, no out-of-bounds access, no panic).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_2 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∃ r : Std.I64, minimum_deletions word k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, minimum_deletions word k = ok r) := by
  sorry

/-- For an integer t >= 1 and an integer x >= 0 put keep_t(x) = x when t <= x <= t + k, keep_t(x) = t + k when x > t + k, and keep_t(x) = 0 when x < t; let cnt(c) be the number of occurrences of the lowercase letter c in word and let maxcnt = max { cnt(c) : c a lowercase letter }. Whenever the function returns a result r, there exists an integer t with 1 <= t <= maxcnt such that (sum over the 26 lowercase letters c of keep_t(cnt(c))) = len(word) - r. Equivalently: deleting every occurrence of each letter c with cnt(c) < t, and deleting exactly cnt(c) - (t + k) occurrences of each letter c with cnt(c) > t + k, deletes precisely r characters and leaves a string in which every occurring letter has between t and t + k occurrences.
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_3 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ maxCnt word ∧
        (∑ c : Fin 26, (keep k t (cnt word c) : ℤ)) =
          (word.val.length : ℤ) - r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ maxCnt word ∧
        (∑ c : Fin 26, (keep k t (cnt word c) : ℤ)) =
          (word.val.length : ℤ) - r.val) := by
  sorry

/-- Let cnt(c) be the number of occurrences of the lowercase letter c in word, and call a function g from the 26 lowercase letters to the non-negative integers admissible when g(c) <= cnt(c) for every lowercase letter c and |g(c) - g(d)| <= k for all c, d with g(c) >= 1 and g(d) >= 1. Whenever the function returns a result r, every admissible g satisfies (sum over the 26 lowercase letters c of g(c)) <= len(word) - r.
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_4 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∀ g : Fin 26 → ℕ, admissible word k g →
        (∑ c : Fin 26, (g c : ℤ)) ≤ (word.val.length : ℤ) - r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∀ g : Fin 26 → ℕ, admissible word k g →
        (∑ c : Fin 26, (g c : ℤ)) ≤ (word.val.length : ℤ) - r.val) := by
  sorry

/-- Let cnt(c) be the number of occurrences of the lowercase letter c in word. Whenever the function returns a result r, we have r = 0 if and only if |cnt(c) - cnt(d)| <= k for all lowercase letters c, d with cnt(c) >= 1 and cnt(d) >= 1 (that is, word itself is already k-special).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_5 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      (r.val = 0 ↔
        ∀ c d : Fin 26, 1 ≤ cnt word c → 1 ≤ cnt word d →
          |(cnt word c : ℤ) - (cnt word d : ℤ)| ≤ k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      (r.val = 0 ↔
        ∀ c d : Fin 26, 1 ≤ cnt word c → 1 ≤ cnt word d →
          |(cnt word c : ℤ) - (cnt word d : ℤ)| ≤ k.val)) := by
  sorry

/-- Let 0 <= k1 <= k2 <= 100000 and let word satisfy the preconditions. Whenever the function returns r1 on the inputs (word, k1) and r2 on the inputs (word, k2), we have r1 >= r2.
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k1 <= k2 <= 100000. -/
theorem spec_6 (word : Slice Std.U8) (k1 k2 : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ 100000) :
    ∀ r1 r2 : Std.I64,
      minimum_deletions word k1 = ok r1 →
      minimum_deletions word k2 = ok r2 →
      r1.val ≥ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8) (k1 k2 : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ 100000), ∀ r1 r2 : Std.I64,
      minimum_deletions word k1 = ok r1 →
      minimum_deletions word k2 = ok r2 →
      r1.val ≥ r2.val) := by
  sorry

/-- For a byte array w and a byte b let counts(w, b) be the number of indices i with 0 <= i < len(w) and w[i] = b. Whenever both calls return, for every byte array word' satisfying the preconditions (with the same k) such that for every integer v >= 0 the number of bytes b with counts(word', b) = v equals the number of bytes b with counts(word, b) = v, we have minimum_deletions(word', k) = minimum_deletions(word, k).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. The same conditions hold for word' below. -/
theorem spec_7 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ (word' : Slice Std.U8),
      (1 ≤ word'.val.length) →
      (word'.val.length ≤ 100000) →
      (∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122) →
      (∀ v : ℕ, countFreq word' v = countFreq word v) →
      ∀ r r' : Std.I64,
        minimum_deletions word k = ok r →
        minimum_deletions word' k = ok r' →
        r' = r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ (word' : Slice Std.U8),
      (1 ≤ word'.val.length) →
      (word'.val.length ≤ 100000) →
      (∀ b ∈ word'.val, 97 ≤ b.val ∧ b.val ≤ 122) →
      (∀ v : ℕ, countFreq word' v = countFreq word v) →
      ∀ r r' : Std.I64,
        minimum_deletions word k = ok r →
        minimum_deletions word' k = ok r' →
        r' = r) := by
  sorry

/-- Let cnt(c) be the number of occurrences of the lowercase letter c in word. Whenever the function returns a result r, there exists a function g from the 26 lowercase letters to the non-negative integers such that g(c) <= cnt(c) for every c, |g(c) - g(d)| <= k whenever g(c) >= 1 and g(d) >= 1, (sum over the 26 lowercase letters c of g(c)) = len(word) - r, and g is monotone with respect to the letter counts: for all lowercase letters c, d, cnt(c) <= cnt(d) implies g(c) <= g(d).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_8 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∃ g : Fin 26 → ℕ,
        admissible word k g ∧
          (r.val : ℤ) = (word.val.length : ℤ) - (∑ c : Fin 26, (g c : ℤ)) ∧
            (∀ c d : Fin 26, cnt word c ≤ cnt word d → g c ≤ g d) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∃ g : Fin 26 → ℕ,
        admissible word k g ∧
          (r.val : ℤ) = (word.val.length : ℤ) - (∑ c : Fin 26, (g c : ℤ)) ∧
            (∀ c d : Fin 26, cnt word c ≤ cnt word d → g c ≤ g d)) := by
  sorry

/-- For an integer t >= 1 and an integer x >= 0 put keep_t(x) = x when t <= x <= t + k, keep_t(x) = t + k when x > t + k, and keep_t(x) = 0 when x < t; let cnt(c) be the number of occurrences of the lowercase letter c in word. Whenever the function returns a result r, for every integer t >= 1 we have r <= len(word) - (sum over the 26 lowercase letters c of keep_t(cnt(c))).
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_9 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∀ t : ℕ, 1 ≤ t →
        r.val ≤ (word.val.length : ℤ) -
          (∑ c : Fin 26, (keep k t (cnt word c) : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      ∀ t : ℕ, 1 ≤ t →
        r.val ≤ (word.val.length : ℤ) -
          (∑ c : Fin 26, (keep k t (cnt word c) : ℤ))) := by
  sorry

/-- Whenever the function returns a result r: there is a subsequence s of word with len(s) = len(word) - r such that all frequencies of letters occurring in s differ by at most k (i.e. |freq_s(c) - freq_s(d)| <= k for all letters c, d occurring in s, where freq_s(x) is the number of occurrences of x in s), and every subsequence s' of word with len(s') > len(word) - r is not of this kind. In other words, len(word) - r is the maximum length of a k-special subsequence of word.
  Preconditions: len(word) >= 1 and len(word) <= 100000; every byte of word is a lowercase English letter, i.e. 97 <= word[i] <= 122 for every i with 0 <= i < len(word); 0 <= k <= 100000. -/
theorem spec_10 (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000) :
    ∀ r : Std.I64, minimum_deletions word k = ok r →
      (∃ s : List Std.U8,
        List.Sublist s word.val ∧
          (s.length : ℤ) = (word.val.length : ℤ) - r.val ∧
            KSpecial k s) ∧
        (∀ s' : List Std.U8,
          List.Sublist s' word.val →
            (s'.length : ℤ) > (word.val.length : ℤ) - r.val →
              ¬ KSpecial k s') := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
    (h_len_ge : 1 ≤ word.val.length)
    (h_len_le : word.val.length ≤ 100000)
    (h_letters : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
    (h_k : 0 ≤ k.val ∧ k.val ≤ 100000), ∀ r : Std.I64, minimum_deletions word k = ok r →
      (∃ s : List Std.U8,
        List.Sublist s word.val ∧
          (s.length : ℤ) = (word.val.length : ℤ) - r.val ∧
            KSpecial k s) ∧
        (∀ s' : List Std.U8,
          List.Sublist s' word.val →
            (s'.length : ℤ) > (word.val.length : ℤ) - r.val →
              ¬ KSpecial k s')) := by
  sorry

end AegisSpec.MinimumDeletions
