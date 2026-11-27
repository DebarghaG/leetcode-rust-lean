import Aegis.NumOfStrings.Code.Funs

/-!
# Specifications of `Aegis.NumOfStrings.num_of_strings`

LeetCode problem `number-of-strings-that-appear-as-substrings-in-word`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumOfStrings

def pats (patterns : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  patterns.val.map (fun v => v.val)

def AllLower (l : List Std.U8) : Prop :=
  ∀ (j : ℕ) (hj : j < l.length), 97 ≤ (l[j]).val ∧ (l[j]).val ≤ 122

def OccursAt (p w : List Std.U8) (k : ℕ) : Prop :=
  k + p.length ≤ w.length ∧ ∀ (j : ℕ) (_hj : j < p.length), p[j]? = w[k + j]?

def Occurs (p w : List Std.U8) : Prop :=
  ∃ k, OccursAt p w k

noncomputable def countOccurs (ps : List (List Std.U8)) (w : List Std.U8) : ℕ := by
  classical
  exact (ps.filter (fun p => decide (Occurs p w))).length

def FirstByteOccurs (p w : List Std.U8) : Prop :=
  ∃ k, k < w.length ∧ p[0]? = w[k]?

noncomputable def countFirstByte (ps : List (List Std.U8)) (w : List Std.U8) : ℕ := by
  classical
  exact (ps.filter (fun p => decide (FirstByteOccurs p w))).length

noncomputable def countIn (p : List Std.U8) (ps : List (List Std.U8)) : ℕ := by
  classical
  exact (ps.filter (fun q => decide (q = p))).length

/-- The function returns a result r (it does not fail) and r equals the number of indices i with 0 <= i < len(patterns) such that patterns[i] occurs in word, where a byte sequence p occurs in word iff there exists an integer k with 0 <= k <= len(word) - len(p) and for every j with 0 <= j < len(p), p[j] = word[k+j]. Patterns are counted with multiplicity: if the same byte sequence appears at several indices in patterns, each such index contributes 1 to r.
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_1 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∃ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r ∧
        r.val = ((countOccurs (pats patterns) word.val : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∃ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r ∧
        r.val = ((countOccurs (pats patterns) word.val : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, overflow, panic, or get stuck) for every input satisfying the preconditions.
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_2 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∃ r : Std.I64, Aegis.NumOfStrings.num_of_strings patterns word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∃ r : Std.I64, Aegis.NumOfStrings.num_of_strings patterns word = ok r) := by
  sorry

/-- Whenever the function returns a result r, it holds that 0 <= r <= len(patterns).
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_3 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        0 ≤ r.val ∧ r.val ≤ ((pats patterns).length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        0 ≤ r.val ∧ r.val ≤ ((pats patterns).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, it holds that r = 0.
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). Moreover, for every i with 0 <= i < len(patterns), len(patterns[i]) > len(word). -/
theorem spec_4 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val)
    (hlarge : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      word.val.length < ((pats patterns)[i]).length) :
    ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val)
    (hlarge : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      word.val.length < ((pats patterns)[i]).length), ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → r.val = 0) := by
  sorry

/-- If num_of_strings(patterns, word) returns r and num_of_strings(patterns', word) returns r', then r = r'.
  Preconditions: patterns and patterns' are slices of Vec U8, word is a slice of U8. Both (patterns, word) and (patterns', word) satisfy the common preconditions: 1 <= len(patterns) = len(patterns') = m <= 100, 1 <= len(word) <= 100, for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100 and 1 <= len(patterns'[i]) <= 100, and every byte of every patterns[i], patterns'[i], and word is an ASCII lowercase English letter (code in [97,122]). Moreover, there exists a bijection pi on {0,...,m-1} such that patterns'[i] = patterns[pi(i)] for every i with 0 <= i < m. -/
theorem spec_5 (patterns patterns' : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hperm : ∃ π : Fin (pats patterns').length → Fin (pats patterns).length,
      Function.Bijective π ∧
        ∀ (i : Fin (pats patterns').length), (pats patterns')[i] = (pats patterns)[π i]) :
    ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (patterns patterns' : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hperm : ∃ π : Fin (pats patterns').length → Fin (pats patterns).length,
      Function.Bijective π ∧
        ∀ (i : Fin (pats patterns').length), (pats patterns')[i] = (pats patterns)[π i]), ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word = ok r' → r = r') := by
  sorry

/-- If num_of_strings(patterns1, word) returns r1 and num_of_strings(patterns2, word) returns r2, then r1 <= r2.
  Preconditions: patterns1 and patterns2 are slices of Vec U8, word is a slice of U8. Both (patterns1, word) and (patterns2, word) satisfy the common preconditions: 1 <= len(patterns1) <= 100, 1 <= len(patterns2) <= 100, 1 <= len(word) <= 100, for every i, 1 <= len(patterns1[i]) <= 100 and 1 <= len(patterns2[i]) <= 100, and every byte is an ASCII lowercase English letter (code in [97,122]). Moreover, patterns1 is a sub-multiset of patterns2: for every byte string p, the number of indices i with patterns1[i] = p is at most the number of indices i with patterns2[i] = p. -/
theorem spec_6 (patterns1 patterns2 : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm1_pos : 1 ≤ (pats patterns1).length)
    (hm1_le : (pats patterns1).length ≤ 100)
    (hm2_pos : 1 ≤ (pats patterns2).length)
    (hm2_le : (pats patterns2).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length),
      1 ≤ ((pats patterns1)[i]).length ∧ ((pats patterns1)[i]).length ≤ 100)
    (hplen2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length),
      1 ≤ ((pats patterns2)[i]).length ∧ ((pats patterns2)[i]).length ≤ 100)
    (hpat1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length), AllLower ((pats patterns1)[i]))
    (hpat2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length), AllLower ((pats patterns2)[i]))
    (hword : AllLower word.val)
    (hsub : ∀ p : List Std.U8, countIn p (pats patterns1) ≤ countIn p (pats patterns2)) :
    ∀ (r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns1 word = ok r1 →
        Aegis.NumOfStrings.num_of_strings patterns2 word = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (patterns1 patterns2 : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm1_pos : 1 ≤ (pats patterns1).length)
    (hm1_le : (pats patterns1).length ≤ 100)
    (hm2_pos : 1 ≤ (pats patterns2).length)
    (hm2_le : (pats patterns2).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length),
      1 ≤ ((pats patterns1)[i]).length ∧ ((pats patterns1)[i]).length ≤ 100)
    (hplen2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length),
      1 ≤ ((pats patterns2)[i]).length ∧ ((pats patterns2)[i]).length ≤ 100)
    (hpat1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length), AllLower ((pats patterns1)[i]))
    (hpat2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length), AllLower ((pats patterns2)[i]))
    (hword : AllLower word.val)
    (hsub : ∀ p : List Std.U8, countIn p (pats patterns1) ≤ countIn p (pats patterns2)), ∀ (r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns1 word = ok r1 →
        Aegis.NumOfStrings.num_of_strings patterns2 word = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If num_of_strings(patterns, word1) returns r1 and num_of_strings(patterns, word2) returns r2, then r1 <= r2.
  Preconditions: patterns is a slice of Vec U8, word1 and word2 are slices of U8. Both (patterns, word1) and (patterns, word2) satisfy the common preconditions: 1 <= len(patterns) <= 100, 1 <= len(word1) <= 100, 1 <= len(word2) <= 100, for every i, 1 <= len(patterns[i]) <= 100, and every byte is an ASCII lowercase English letter (code in [97,122]). Moreover, word1 is a contiguous substring of word2: there exists an integer k with 0 <= k <= len(word2) - len(word1) such that word1[j] = word2[k+j] for every j with 0 <= j < len(word1). -/
theorem spec_7 (patterns : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn1_pos : 1 ≤ word1.val.length)
    (hn1_le : word1.val.length ≤ 100)
    (hn2_pos : 1 ≤ word2.val.length)
    (hn2_le : word2.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword1 : AllLower word1.val)
    (hword2 : AllLower word2.val)
    (hsub : Occurs word1.val word2.val) :
    ∀ (r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word1 = ok r1 →
        Aegis.NumOfStrings.num_of_strings patterns word2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word1 word2 : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn1_pos : 1 ≤ word1.val.length)
    (hn1_le : word1.val.length ≤ 100)
    (hn2_pos : 1 ≤ word2.val.length)
    (hn2_le : word2.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword1 : AllLower word1.val)
    (hword2 : AllLower word2.val)
    (hsub : Occurs word1.val word2.val), ∀ (r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word1 = ok r1 →
        Aegis.NumOfStrings.num_of_strings patterns word2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If num_of_strings(patterns, word) returns r, num_of_strings(patterns1, word) returns r1, and num_of_strings(patterns2, word) returns r2, then r = r1 + r2.
  Preconditions: patterns, patterns1, patterns2 are slices of Vec U8, word is a slice of U8. Both (patterns, word), (patterns1, word), and (patterns2, word) satisfy the common preconditions: 1 <= len(patterns) <= 100, 1 <= len(patterns1) <= 100, 1 <= len(patterns2) <= 100, 1 <= len(word) <= 100, for every i, 1 <= len(patterns[i]) <= 100, 1 <= len(patterns1[i]) <= 100, 1 <= len(patterns2[i]) <= 100, and every byte is an ASCII lowercase English letter (code in [97,122]). Moreover, patterns is the concatenation of patterns1 and patterns2: len(patterns) = len(patterns1) + len(patterns2), and for every i with 0 <= i < len(patterns1), patterns[i] = patterns1[i], and for every i with 0 <= i < len(patterns2), patterns[len(patterns1) + i] = patterns2[i]. -/
theorem spec_8 (patterns patterns1 patterns2 : Slice (alloc.vec.Vec Std.U8))
    (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm1_pos : 1 ≤ (pats patterns1).length)
    (hm1_le : (pats patterns1).length ≤ 100)
    (hm2_pos : 1 ≤ (pats patterns2).length)
    (hm2_le : (pats patterns2).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length),
      1 ≤ ((pats patterns1)[i]).length ∧ ((pats patterns1)[i]).length ≤ 100)
    (hplen2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length),
      1 ≤ ((pats patterns2)[i]).length ∧ ((pats patterns2)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length), AllLower ((pats patterns1)[i]))
    (hpat2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length), AllLower ((pats patterns2)[i]))
    (hword : AllLower word.val)
    (hlen : (pats patterns).length =
      (pats patterns1).length + (pats patterns2).length)
    (hcat : pats patterns = pats patterns1 ++ pats patterns2) :
    ∀ (r r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns1 word = ok r1 →
          Aegis.NumOfStrings.num_of_strings patterns2 word = ok r2 →
            r.val = r1.val + r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (patterns patterns1 patterns2 : Slice (alloc.vec.Vec Std.U8))
    (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm1_pos : 1 ≤ (pats patterns1).length)
    (hm1_le : (pats patterns1).length ≤ 100)
    (hm2_pos : 1 ≤ (pats patterns2).length)
    (hm2_le : (pats patterns2).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length),
      1 ≤ ((pats patterns1)[i]).length ∧ ((pats patterns1)[i]).length ≤ 100)
    (hplen2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length),
      1 ≤ ((pats patterns2)[i]).length ∧ ((pats patterns2)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat1 : ∀ (i : ℕ) (hi : i < (pats patterns1).length), AllLower ((pats patterns1)[i]))
    (hpat2 : ∀ (i : ℕ) (hi : i < (pats patterns2).length), AllLower ((pats patterns2)[i]))
    (hword : AllLower word.val)
    (hlen : (pats patterns).length =
      (pats patterns1).length + (pats patterns2).length)
    (hcat : pats patterns = pats patterns1 ++ pats patterns2), ∀ (r r1 r2 : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns1 word = ok r1 →
          Aegis.NumOfStrings.num_of_strings patterns2 word = ok r2 →
            r.val = r1.val + r2.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an index i with 0 <= i < len(patterns) such that patterns[i] occurs in word (using the definition of occurs from spec_1: there exists k with 0 <= k <= len(word) - len(patterns[i]) and patterns[i][j] = word[k+j] for every j with 0 <= j < len(patterns[i])).
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_9 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → 0 < r.val →
        ∃ (i : ℕ) (hi : i < (pats patterns).length), Occurs ((pats patterns)[i]) word.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → 0 < r.val →
        ∃ (i : ℕ) (hi : i < (pats patterns).length), Occurs ((pats patterns)[i]) word.val) := by
  sorry

/-- Whenever the function returns a result r with r = 0, for every index i with 0 <= i < len(patterns), patterns[i] does not occur in word (i.e., there is no integer k with 0 <= k <= len(word) - len(patterns[i]) such that patterns[i][j] = word[k+j] for every j with 0 <= j < len(patterns[i])).
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_10 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → r.val = 0 →
        ∀ (i : ℕ) (hi : i < (pats patterns).length),
          ¬ Occurs ((pats patterns)[i]) word.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r → r.val = 0 →
        ∀ (i : ℕ) (hi : i < (pats patterns).length),
          ¬ Occurs ((pats patterns)[i]) word.val) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < len(patterns) such that there exists an integer k with 0 <= k < len(word) and patterns[i][0] = word[k].
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). Moreover, for every i with 0 <= i < len(patterns), len(patterns[i]) = 1. -/
theorem spec_11 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val)
    (hunit : ∀ (i : ℕ) (hi : i < (pats patterns).length), ((pats patterns)[i]).length = 1) :
    ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        r.val = ((countFirstByte (pats patterns) word.val : ℕ) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val)
    (hunit : ∀ (i : ℕ) (hi : i < (pats patterns).length), ((pats patterns)[i]).length = 1), ∀ r : Std.I64,
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        r.val = ((countFirstByte (pats patterns) word.val : ℕ) : ℤ)) := by
  sorry

/-- If num_of_strings(patterns, word) returns r and num_of_strings(patterns', word') returns r', then r = r'.
  Preconditions: patterns and patterns' are slices of Vec U8, word and word' are slices of U8. Both (patterns, word) and (patterns', word') satisfy the common preconditions: 1 <= len(patterns) = len(patterns') = m <= 100, 1 <= len(word) = len(word') = n <= 100, for every i with 0 <= i < m, 1 <= len(patterns[i]) = len(patterns'[i]) <= 100, and every byte is an ASCII lowercase English letter (code in [97,122]). Moreover, for every i with 0 <= i < m, len(patterns[i]) = len(patterns'[i]) and patterns'[i][j] = patterns[i][len(patterns[i])-1-j] for every j with 0 <= j < len(patterns[i]); and for every j with 0 <= j < n, word'[j] = word[n-1-j]. -/
theorem spec_12 (patterns patterns' : Slice (alloc.vec.Vec Std.U8))
    (word word' : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hn_eq : word'.val.length = word.val.length)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hword' : AllLower word'.val)
    (hrev : ∀ (i : ℕ) (hi : i < (pats patterns).length) (hi' : i < (pats patterns').length),
      (pats patterns')[i] = ((pats patterns)[i]).reverse)
    (hrevword : word'.val = word.val.reverse) :
    ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word' = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (patterns patterns' : Slice (alloc.vec.Vec Std.U8))
    (word word' : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hn_eq : word'.val.length = word.val.length)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hword' : AllLower word'.val)
    (hrev : ∀ (i : ℕ) (hi : i < (pats patterns).length) (hi' : i < (pats patterns').length),
      (pats patterns')[i] = ((pats patterns)[i]).reverse)
    (hrevword : word'.val = word.val.reverse), ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word' = ok r' → r = r') := by
  sorry

/-- For any byte string p, let m_p be the number of indices i with 0 <= i < len(patterns) such that patterns[i] = p. If p occurs in word (i.e., there exists k with 0 <= k <= len(word) - len(p) and p[j] = word[k+j] for every j with 0 <= j < len(p)), then whenever the function returns a result r, it holds that r >= m_p.
  Preconditions: patterns is a slice of Vec U8 and word is a slice of U8. Let m = len(patterns) and n = len(word). We have 1 <= m <= 100, 1 <= n <= 100, and for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100. Every byte of every patterns[i] and of word is an ASCII lowercase English letter (code in [97,122]). -/
theorem spec_13 (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val) :
    ∀ (p : List Std.U8), Occurs p word.val →
      ∀ r : Std.I64,
        Aegis.NumOfStrings.num_of_strings patterns word = ok r →
          ((countIn p (pats patterns) : ℕ) : ℤ) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (patterns : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hword : AllLower word.val), ∀ (p : List Std.U8), Occurs p word.val →
      ∀ r : Std.I64,
        Aegis.NumOfStrings.num_of_strings patterns word = ok r →
          ((countIn p (pats patterns) : ℕ) : ℤ) ≤ r.val) := by
  sorry

/-- If num_of_strings(patterns, word) returns r and num_of_strings(patterns', word) returns r', then r <= r'.
  Preconditions: patterns and patterns' are slices of Vec U8, word is a slice of U8. Both (patterns, word) and (patterns', word) satisfy the common preconditions: 1 <= len(patterns) = len(patterns') = m <= 100, 1 <= len(word) <= 100, for every i with 0 <= i < m, 1 <= len(patterns[i]) <= 100 and 1 <= len(patterns'[i]) <= 100, and every byte is an ASCII lowercase English letter (code in [97,122]). Moreover, for every i with 0 <= i < m, patterns'[i] is a contiguous substring of patterns[i]: there exists k_i with 0 <= k_i <= len(patterns[i]) - len(patterns'[i]) such that patterns'[i][j] = patterns[i][k_i + j] for every j with 0 <= j < len(patterns'[i]). -/
theorem spec_14 (patterns patterns' : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hsub : ∀ (i : ℕ) (hi : i < (pats patterns).length) (hi' : i < (pats patterns').length),
      Occurs ((pats patterns')[i]) ((pats patterns)[i])) :
    ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (patterns patterns' : Slice (alloc.vec.Vec Std.U8)) (word : Slice Std.U8)
    (hm_pos : 1 ≤ (pats patterns).length)
    (hm_le : (pats patterns).length ≤ 100)
    (hm_eq : (pats patterns').length = (pats patterns).length)
    (hn_pos : 1 ≤ word.val.length)
    (hn_le : word.val.length ≤ 100)
    (hplen : ∀ (i : ℕ) (hi : i < (pats patterns).length),
      1 ≤ ((pats patterns)[i]).length ∧ ((pats patterns)[i]).length ≤ 100)
    (hplen' : ∀ (i : ℕ) (hi : i < (pats patterns').length),
      1 ≤ ((pats patterns')[i]).length ∧ ((pats patterns')[i]).length ≤ 100)
    (hpat : ∀ (i : ℕ) (hi : i < (pats patterns).length), AllLower ((pats patterns)[i]))
    (hpat' : ∀ (i : ℕ) (hi : i < (pats patterns').length), AllLower ((pats patterns')[i]))
    (hword : AllLower word.val)
    (hsub : ∀ (i : ℕ) (hi : i < (pats patterns).length) (hi' : i < (pats patterns').length),
      Occurs ((pats patterns')[i]) ((pats patterns)[i])), ∀ (r r' : Std.I64),
      Aegis.NumOfStrings.num_of_strings patterns word = ok r →
        Aegis.NumOfStrings.num_of_strings patterns' word = ok r' → r.val ≤ r'.val) := by
  sorry

end AegisSpec.NumOfStrings
