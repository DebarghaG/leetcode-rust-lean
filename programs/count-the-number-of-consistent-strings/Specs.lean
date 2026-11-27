import Aegis.CountConsistentStrings.Code.Funs

/-!
# Specifications of `Aegis.CountConsistentStrings.count_consistent_strings`

LeetCode problem `count-the-number-of-consistent-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountConsistentStrings

  namespace AegisSpec.CountConsistentStrings

  def occursIn (a : Slice Std.U8) (c : Std.U8) : Prop :=
    ∃ (j : Nat) (hj : j < a.val.length), a.val[j]'hj = c

  def wordConsistent (allowed : Slice Std.U8) (w : alloc.vec.Vec Std.U8) : Prop :=
    ∀ (k : Nat) (hk : k < w.val.length), occursIn allowed (w.val[k]'hk)

  def anyConsistent (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∃ (i : Nat) (hi : i < words.val.length), wordConsistent allowed (words.val[i]'hi)

  def allConsistent (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    ∀ (i : Nat) (hi : i < words.val.length), wordConsistent allowed (words.val[i]'hi)

  noncomputable def countConsistent (allowed : Slice Std.U8)
      (words : Slice (alloc.vec.Vec Std.U8)) : Nat := by
    classical
    exact ((List.finRange words.val.length).filter
      (fun i => decide (wordConsistent allowed (words.val[i])))).length

  /-- Whenever the function returns a result r, the integer value of r equals the number of indices i with 0 <= i < len(words) such that for every k with 0 <= k < len(words[i]) there exists j with 0 <= j < len(allowed) and allowed[j] = words[i][k].
    Preconditions: len(allowed) >= 1 and len(allowed) <= 26; all bytes of allowed are pairwise distinct and are lowercase English letters (ASCII codes 97 through 122); len(words) >= 1 and len(words) <= 10000; for every i with 0 <= i < len(words), len(words[i]) >= 1 and len(words[i]) <= 10, and every byte of words[i] is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_1 (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r, count_consistent_strings allowed words = ok r →
        r.val = (countConsistent allowed words : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r, count_consistent_strings allowed words = ok r →
          r.val = (countConsistent allowed words : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(allowed) >= 1 and len(allowed) <= 26; all bytes of allowed are pairwise distinct and are lowercase English letters (ASCII codes 97 through 122); len(words) >= 1 and len(words) <= 10000; for every i with 0 <= i < len(words), len(words[i]) >= 1 and len(words[i]) <= 10, and every byte of words[i] is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_2 (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ r, count_consistent_strings allowed words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r, count_consistent_strings allowed words = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r satisfies 0 <= r <= len(words).
    Preconditions: len(allowed) >= 1 and len(allowed) <= 26; all bytes of allowed are pairwise distinct and are lowercase English letters (ASCII codes 97 through 122); len(words) >= 1 and len(words) <= 10000; for every i with 0 <= i < len(words), len(words[i]) >= 1 and len(words[i]) <= 10, and every byte of words[i] is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_3 (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r, count_consistent_strings allowed words = ok r →
        0 ≤ r.val ∧ r.val ≤ (words.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r, count_consistent_strings allowed words = ok r →
          0 ≤ r.val ∧ r.val ≤ (words.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is 0 if and only if there is no index i with 0 <= i < len(words) such that for every k with 0 <= k < len(words[i]) there exists j with 0 <= j < len(allowed) and allowed[j] = words[i][k].
    Preconditions: len(allowed) >= 1 and len(allowed) <= 26; all bytes of allowed are pairwise distinct and are lowercase English letters (ASCII codes 97 through 122); len(words) >= 1 and len(words) <= 10000; for every i with 0 <= i < len(words), len(words[i]) >= 1 and len(words[i]) <= 10, and every byte of words[i] is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_4 (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r, count_consistent_strings allowed words = ok r →
        (r.val = 0 ↔ ¬ anyConsistent allowed words) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r, count_consistent_strings allowed words = ok r →
          (r.val = 0 ↔ ¬ anyConsistent allowed words)) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r equals len(words) if and only if for every i with 0 <= i < len(words) and every k with 0 <= k < len(words[i]) there exists j with 0 <= j < len(allowed) and allowed[j] = words[i][k].
    Preconditions: len(allowed) >= 1 and len(allowed) <= 26; all bytes of allowed are pairwise distinct and are lowercase English letters (ASCII codes 97 through 122); len(words) >= 1 and len(words) <= 10000; for every i with 0 <= i < len(words), len(words[i]) >= 1 and len(words[i]) <= 10, and every byte of words[i] is a lowercase English letter (ASCII code 97 through 122). -/
  theorem spec_5 (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r, count_consistent_strings allowed words = ok r →
        (r.val = (words.val.length : Int) ↔ allConsistent allowed words) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (allowed : Slice Std.U8) (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r, count_consistent_strings allowed words = ok r →
          (r.val = (words.val.length : Int) ↔ allConsistent allowed words)) := by
    sorry

  /-- Whenever count_consistent_strings(allowed1, words) returns r1 and count_consistent_strings(allowed2, words) returns r2, the integer values of r1 and r2 are equal.
    Preconditions: The usual constraints hold for (allowed1, words) and for (allowed2, words): each allowed has length 1 through 26 with pairwise distinct lowercase English letters, and words has length 1 through 10000 with every word having length 1 through 10 and lowercase English letters. Additionally, allowed2 is a permutation of allowed1, meaning that for every byte c, c occurs in allowed1 if and only if c occurs in allowed2, where c occurs in an allowed slice a if there exists j with 0 <= j < len(a) and a[j] = c. -/
  theorem spec_6 (allowed1 allowed2 : Slice Std.U8)
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowed1_len_ge : 1 ≤ allowed1.val.length)
      (h_allowed1_len_le : allowed1.val.length ≤ 26)
      (h_allowed1_nodup : allowed1.val.Nodup)
      (h_allowed1_lower : ∀ c ∈ allowed1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_allowed2_len_ge : 1 ≤ allowed2.val.length)
      (h_allowed2_len_le : allowed2.val.length ≤ 26)
      (h_allowed2_nodup : allowed2.val.Nodup)
      (h_allowed2_lower : ∀ c ∈ allowed2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_perm : ∀ c : Std.U8, occursIn allowed1 c ↔ occursIn allowed2 c) :
      ∀ r1 r2, count_consistent_strings allowed1 words = ok r1 →
        count_consistent_strings allowed2 words = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (allowed1 allowed2 : Slice Std.U8)
        (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowed1_len_ge : 1 ≤ allowed1.val.length)
        (h_allowed1_len_le : allowed1.val.length ≤ 26)
        (h_allowed1_nodup : allowed1.val.Nodup)
        (h_allowed1_lower : ∀ c ∈ allowed1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_allowed2_len_ge : 1 ≤ allowed2.val.length)
        (h_allowed2_len_le : allowed2.val.length ≤ 26)
        (h_allowed2_nodup : allowed2.val.Nodup)
        (h_allowed2_lower : ∀ c ∈ allowed2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_perm : ∀ c : Std.U8, occursIn allowed1 c ↔ occursIn allowed2 c), ∀ r1 r2, count_consistent_strings allowed1 words = ok r1 →
          count_consistent_strings allowed2 words = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Whenever the two calls return r1 and r2, the integer values of r1 and r2 are equal.
    Preconditions: The usual constraints hold for (allowed, words1) and for (allowed, words2): allowed has length 1 through 26 with pairwise distinct lowercase English letters, and each word list has length 1 through 10000 with every word having length 1 through 10 and lowercase English letters. Additionally, words2 is a permutation of words1, meaning len(words1) = len(words2) and there exists a bijection pi from the index set {0,...,len(words1)-1} to itself such that for every i, words2[i] and words1[pi(i)] are the same byte sequence (same length and same bytes at each position). -/
  theorem spec_7 (allowed : Slice Std.U8)
      (words1 words2 : Slice (alloc.vec.Vec Std.U8))
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words1_len_ge : 1 ≤ words1.val.length)
      (h_words1_len_le : words1.val.length ≤ 10000)
      (h_words1_word_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_words1_lower : ∀ w ∈ words1.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words2_len_ge : 1 ≤ words2.val.length)
      (h_words2_len_le : words2.val.length ≤ 10000)
      (h_words2_word_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_words2_lower : ∀ w ∈ words2.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_perm : ∃ pi : Fin words1.val.length ≃ Fin words2.val.length,
        ∀ i : Fin words1.val.length, (words2.val[pi i]).val = (words1.val[i]).val) :
      ∀ r1 r2, count_consistent_strings allowed words1 = ok r1 →
        count_consistent_strings allowed words2 = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (allowed : Slice Std.U8)
        (words1 words2 : Slice (alloc.vec.Vec Std.U8))
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words1_len_ge : 1 ≤ words1.val.length)
        (h_words1_len_le : words1.val.length ≤ 10000)
        (h_words1_word_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_words1_lower : ∀ w ∈ words1.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words2_len_ge : 1 ≤ words2.val.length)
        (h_words2_len_le : words2.val.length ≤ 10000)
        (h_words2_word_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_words2_lower : ∀ w ∈ words2.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_perm : ∃ pi : Fin words1.val.length ≃ Fin words2.val.length,
          ∀ i : Fin words1.val.length, (words2.val[pi i]).val = (words1.val[i]).val), ∀ r1 r2, count_consistent_strings allowed words1 = ok r1 →
          count_consistent_strings allowed words2 = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Whenever count_consistent_strings(allowedA, words) returns rA and count_consistent_strings(allowedB, words) returns rB, the integer value of rA is at most the integer value of rB.
    Preconditions: The usual constraints hold for (allowedA, words) and for (allowedB, words): each allowed has length 1 through 26 with pairwise distinct lowercase English letters, and words has length 1 through 10000 with every word having length 1 through 10 and lowercase English letters. Additionally, every byte c that occurs in allowedA also occurs in allowedB, where c occurs in an allowed slice a if there exists j with 0 <= j < len(a) and a[j] = c. -/
  theorem spec_8 (allowedA allowedB : Slice Std.U8)
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_allowedA_len_ge : 1 ≤ allowedA.val.length)
      (h_allowedA_len_le : allowedA.val.length ≤ 26)
      (h_allowedA_nodup : allowedA.val.Nodup)
      (h_allowedA_lower : ∀ c ∈ allowedA.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_allowedB_len_ge : 1 ≤ allowedB.val.length)
      (h_allowedB_len_le : allowedB.val.length ≤ 26)
      (h_allowedB_nodup : allowedB.val.Nodup)
      (h_allowedB_lower : ∀ c ∈ allowedB.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_subset : ∀ c : Std.U8, occursIn allowedA c → occursIn allowedB c) :
      ∀ rA rB, count_consistent_strings allowedA words = ok rA →
        count_consistent_strings allowedB words = ok rB → rA.val ≤ rB.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (allowedA allowedB : Slice Std.U8)
        (words : Slice (alloc.vec.Vec Std.U8))
        (h_allowedA_len_ge : 1 ≤ allowedA.val.length)
        (h_allowedA_len_le : allowedA.val.length ≤ 26)
        (h_allowedA_nodup : allowedA.val.Nodup)
        (h_allowedA_lower : ∀ c ∈ allowedA.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_allowedB_len_ge : 1 ≤ allowedB.val.length)
        (h_allowedB_len_le : allowedB.val.length ≤ 26)
        (h_allowedB_nodup : allowedB.val.Nodup)
        (h_allowedB_lower : ∀ c ∈ allowedB.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_subset : ∀ c : Std.U8, occursIn allowedA c → occursIn allowedB c), ∀ rA rB, count_consistent_strings allowedA words = ok rA →
          count_consistent_strings allowedB words = ok rB → rA.val ≤ rB.val) := by
    sorry

  /-- Whenever count_consistent_strings(allowed, words) returns r, count_consistent_strings(allowed, words1) returns r1, and count_consistent_strings(allowed, words2) returns r2, the integer value of r equals the integer value of r1 plus the integer value of r2.
    Preconditions: The usual constraints hold for (allowed, words): allowed has length 1 through 26 with pairwise distinct lowercase English letters, and words has length 1 through 10000 with every word having length 1 through 10 and lowercase English letters. Let p be an integer with 1 <= p < len(words). Let words1 be the prefix words[0..p) and words2 the suffix words[p..len(words)). The usual constraints also hold for (allowed, words1) and for (allowed, words2), which are both nonempty word lists. -/
  theorem spec_9 (allowed : Slice Std.U8)
      (words words1 words2 : Slice (alloc.vec.Vec Std.U8)) (p : Nat)
      (h_allowed_len_ge : 1 ≤ allowed.val.length)
      (h_allowed_len_le : allowed.val.length ≤ 26)
      (h_allowed_nodup : allowed.val.Nodup)
      (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words_len_ge : 1 ≤ words.val.length)
      (h_words_len_le : words.val.length ≤ 10000)
      (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_ge : 1 ≤ p) (hp_lt : p < words.val.length)
      (h_words1_eq : words1.val = words.val.take p)
      (h_words2_eq : words2.val = words.val.drop p)
      (h_words1_len_ge : 1 ≤ words1.val.length)
      (h_words1_len_le : words1.val.length ≤ 10000)
      (h_words1_word_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_words1_lower : ∀ w ∈ words1.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h_words2_len_ge : 1 ≤ words2.val.length)
      (h_words2_len_le : words2.val.length ≤ 10000)
      (h_words2_word_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
      (h_words2_lower : ∀ w ∈ words2.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r r1 r2, count_consistent_strings allowed words = ok r →
        count_consistent_strings allowed words1 = ok r1 →
        count_consistent_strings allowed words2 = ok r2 → r.val = r1.val + r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (allowed : Slice Std.U8)
        (words words1 words2 : Slice (alloc.vec.Vec Std.U8)) (p : Nat)
        (h_allowed_len_ge : 1 ≤ allowed.val.length)
        (h_allowed_len_le : allowed.val.length ≤ 26)
        (h_allowed_nodup : allowed.val.Nodup)
        (h_allowed_lower : ∀ c ∈ allowed.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words_len_ge : 1 ≤ words.val.length)
        (h_words_len_le : words.val.length ≤ 10000)
        (h_word_len : ∀ w ∈ words.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_word_lower : ∀ w ∈ words.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_ge : 1 ≤ p) (hp_lt : p < words.val.length)
        (h_words1_eq : words1.val = words.val.take p)
        (h_words2_eq : words2.val = words.val.drop p)
        (h_words1_len_ge : 1 ≤ words1.val.length)
        (h_words1_len_le : words1.val.length ≤ 10000)
        (h_words1_word_len : ∀ w ∈ words1.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_words1_lower : ∀ w ∈ words1.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h_words2_len_ge : 1 ≤ words2.val.length)
        (h_words2_len_le : words2.val.length ≤ 10000)
        (h_words2_word_len : ∀ w ∈ words2.val, 1 ≤ w.val.length ∧ w.val.length ≤ 10)
        (h_words2_lower : ∀ w ∈ words2.val, ∀ c ∈ w.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r r1 r2, count_consistent_strings allowed words = ok r →
          count_consistent_strings allowed words1 = ok r1 →
          count_consistent_strings allowed words2 = ok r2 → r.val = r1.val + r2.val) := by
    sorry

  end AegisSpec.CountConsistentStrings
