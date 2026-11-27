import Aegis.MaxScoreWords.Code.Funs

/-!
# Specifications of `Aegis.MaxScoreWords.max_score_words`

LeetCode problem `maximum-score-words-formed-by-letters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScoreWords

open Aegis.MaxScoreWords

def scoreAt (score : Slice Std.I64) (k : Nat) : Int :=
  (score.val.getD k 0#i64).val

def firstByte (v : alloc.vec.Vec Std.U8) : Option Nat :=
  (v.val.map (fun b => b.val)).head?

def wordCount (w : alloc.vec.Vec Std.U8) (c : Nat) : Nat :=
  w.val.countP (fun b => b.val = c)

def letterCount (letters : Slice (alloc.vec.Vec Std.U8)) (c : Nat) : Nat :=
  letters.val.countP (fun v => firstByte v = some c)

def headCount (words : Slice (alloc.vec.Vec Std.U8)) (c : Nat) : Nat :=
  words.val.countP (fun w => firstByte w = some c)

def wordScore (score : Slice Std.I64) (w : alloc.vec.Vec Std.U8) : Int :=
  (w.val.map (fun b => scoreAt score (b.val - 97))).sum

def totalScore (score : Slice Std.I64) (words : Slice (alloc.vec.Vec Std.U8)) : Int :=
  ∑ i : Fin words.val.length, wordScore score (words.val.get i)

def totalCount (words : Slice (alloc.vec.Vec Std.U8)) (c : Nat) : Nat :=
  ∑ i : Fin words.val.length, wordCount (words.val.get i) c

def admissible (words letters : Slice (alloc.vec.Vec Std.U8))
    (S : Finset (Fin words.val.length)) : Prop :=
  ∀ c : Nat, 97 ≤ c → c ≤ 122 →
    (∑ i ∈ S, wordCount (words.val.get i) c) ≤ letterCount letters c

def subsetScore (score : Slice Std.I64) (words : Slice (alloc.vec.Vec Std.U8))
    (S : Finset (Fin words.val.length)) : Int :=
  ∑ i ∈ S, wordScore score (words.val.get i)

def Pre (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64) : Prop :=
  (1 ≤ words.val.length ∧ words.val.length ≤ 14) ∧
  (∀ w ∈ words.val,
    1 ≤ w.val.length ∧ w.val.length ≤ 15 ∧ ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧
  (1 ≤ letters.val.length ∧ letters.val.length ≤ 100) ∧
  (∀ v ∈ letters.val, v.val.length = 1 ∧ ∀ b ∈ v.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧
  score.val.length = 26 ∧
  (∀ k : Nat, k < 26 → 0 ≤ scoreAt score k ∧ scoreAt score k ≤ 10)

/-- Whenever the function returns a result r, the following holds. For a byte c with 97 <= c <= 122, let L(c) be the number of indices i with 0 <= i < len(letters) such that letters[i][0] = c. For a word index i, let W_i(c) be the number of indices j with 0 <= j < len(words[i]) such that words[i][j] = c, and let wordScore(i) = sum over j = 0 to len(words[i]) - 1 of score[words[i][j] - 97]. Call a subset S of {0, 1, ..., len(words) - 1} admissible if for every c with 97 <= c <= 122, the sum over i in S of W_i(c) is at most L(c). Then r is the maximum of sum over i in S of wordScore(i) over all admissible subsets S, including the empty subset.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_1 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∃ S : Finset (Fin words.val.length),
          admissible words letters S ∧ subsetScore score words S = r.val) ∧
      (∀ S : Finset (Fin words.val.length),
          admissible words letters S → subsetScore score words S ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∃ S : Finset (Fin words.val.length),
          admissible words letters S ∧ subsetScore score words S = r.val) ∧
      (∀ S : Finset (Fin words.val.length),
          admissible words letters S → subsetScore score words S ≤ r.val)) := by
  sorry

/-- The function returns a result r; in particular, under the preconditions it does not fail, overflow, access an out-of-bounds index, or panic.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_2 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∃ r : Std.I64, max_score_words words letters score = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∃ r : Std.I64, max_score_words words letters score = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_3 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum over c = 97 to 122 of L(c) * score[c - 97], where L(c) is the number of indices i with 0 <= i < len(letters) such that letters[i][0] = c.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_4 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      r.val ≤ ∑ c ∈ Finset.Icc 97 122, (letterCount letters c : Int) * scoreAt score (c - 97) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      r.val ≤ ∑ c ∈ Finset.Icc 97 122, (letterCount letters c : Int) * scoreAt score (c - 97)) := by
  sorry

/-- Whenever the function returns a result r, r <= sum over i = 0 to len(words) - 1 of wordScore(i), where wordScore(i) = sum over j = 0 to len(words[i]) - 1 of score[words[i][j] - 97].
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_5 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r → r.val ≤ totalScore score words := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r → r.val ≤ totalScore score words) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(words), if for every c with 97 <= c <= 122 the number of positions j with 0 <= j < len(words[i]) and words[i][j] = c is at most the number of indices k with 0 <= k < len(letters) and letters[k][0] = c, then wordScore(i) <= r, where wordScore(i) = sum over j = 0 to len(words[i]) - 1 of score[words[i][j] - 97].
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_6 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ i : Fin words.val.length,
        (∀ c : Nat, 97 ≤ c → c ≤ 122 →
          wordCount (words.val.get i) c ≤ letterCount letters c) →
        wordScore score (words.val.get i) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ i : Fin words.val.length,
        (∀ c : Nat, 97 ≤ c → c ≤ 122 →
          wordCount (words.val.get i) c ≤ letterCount letters c) →
        wordScore score (words.val.get i) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if for every i with 0 <= i < len(words) there exists a byte c with 97 <= c <= 122 such that the number of positions j with 0 <= j < len(words[i]) and words[i][j] = c is greater than the number of indices k with 0 <= k < len(letters) and letters[k][0] = c, then r = 0.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_7 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ i : Fin words.val.length,
        ∃ c : Nat, 97 ≤ c ∧ c ≤ 122 ∧ letterCount letters c < wordCount (words.val.get i) c) →
      r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ i : Fin words.val.length,
        ∃ c : Nat, 97 ≤ c ∧ c ≤ 122 ∧ letterCount letters c < wordCount (words.val.get i) c) →
      r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if for every c with 97 <= c <= 122 the sum over i = 0 to len(words) - 1 of the number of positions j with 0 <= j < len(words[i]) and words[i][j] = c is at most the number of indices k with 0 <= k < len(letters) and letters[k][0] = c, then r = sum over i = 0 to len(words) - 1 of wordScore(i), where wordScore(i) = sum over j = 0 to len(words[i]) - 1 of score[words[i][j] - 97].
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_8 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ c : Nat, 97 ≤ c → c ≤ 122 → totalCount words c ≤ letterCount letters c) →
      r.val = totalScore score words := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ c : Nat, 97 ≤ c → c ≤ 122 → totalCount words c ≤ letterCount letters c) →
      r.val = totalScore score words) := by
  sorry

/-- Whenever the function returns a result r, if len(words[i]) = 1 for every i with 0 <= i < len(words), then r = sum over c = 97 to 122 of min(L(c), M(c)) * score[c - 97], where L(c) is the number of indices k with 0 <= k < len(letters) and letters[k][0] = c, and M(c) is the number of indices i with 0 <= i < len(words) and words[i][0] = c.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_9 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ i : Fin words.val.length, (words.val.get i).val.length = 1) →
      r.val = ∑ c ∈ Finset.Icc 97 122,
        ((min (letterCount letters c) (headCount words c) : Nat) : Int) *
          scoreAt score (c - 97) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ i : Fin words.val.length, (words.val.get i).val.length = 1) →
      r.val = ∑ c ∈ Finset.Icc 97 122,
        ((min (letterCount letters c) (headCount words c) : Nat) : Int) *
          scoreAt score (c - 97)) := by
  sorry

/-- Whenever the function returns a result r, if len(words) = 1, then r = wordScore(0) if for every c with 97 <= c <= 122 the number of positions j with 0 <= j < len(words[0]) and words[0][j] = c is at most the number of indices k with 0 <= k < len(letters) and letters[k][0] = c; otherwise r = 0. Here wordScore(0) = sum over j = 0 to len(words[0]) - 1 of score[words[0][j] - 97].
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_10 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ (h1 : words.val.length = 1),
      let w0 := words.val.get ⟨0, by omega⟩
      ((∀ c : Nat, 97 ≤ c → c ≤ 122 → wordCount w0 c ≤ letterCount letters c) →
          r.val = wordScore score w0) ∧
      (¬(∀ c : Nat, 97 ≤ c → c ≤ 122 → wordCount w0 c ≤ letterCount letters c) →
          r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ (h1 : words.val.length = 1),
      let w0 := words.val.get ⟨0, by omega⟩
      ((∀ c : Nat, 97 ≤ c → c ≤ 122 → wordCount w0 c ≤ letterCount letters c) →
          r.val = wordScore score w0) ∧
      (¬(∀ c : Nat, 97 ≤ c → c ≤ 122 → wordCount w0 c ≤ letterCount letters c) →
          r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, if len(letters) = 1 and letters[0][0] = c0, then r = score[c0 - 97] if there exists an index i with 0 <= i < len(words) such that len(words[i]) = 1 and words[i][0] = c0, and otherwise r = 0.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_11 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ c0 : Nat, ∀ (h1 : letters.val.length = 1),
        firstByte (letters.val.get ⟨0, by omega⟩) = some c0 →
        ((∃ i : Fin words.val.length,
            (words.val.get i).val.length = 1 ∧ firstByte (words.val.get i) = some c0) →
          r.val = scoreAt score (c0 - 97)) ∧
        ((¬∃ i : Fin words.val.length,
            (words.val.get i).val.length = 1 ∧ firstByte (words.val.get i) = some c0) →
          r.val = 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ c0 : Nat, ∀ (h1 : letters.val.length = 1),
        firstByte (letters.val.get ⟨0, by omega⟩) = some c0 →
        ((∃ i : Fin words.val.length,
            (words.val.get i).val.length = 1 ∧ firstByte (words.val.get i) = some c0) →
          r.val = scoreAt score (c0 - 97)) ∧
        ((¬∃ i : Fin words.val.length,
            (words.val.get i).val.length = 1 ∧ firstByte (words.val.get i) = some c0) →
          r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, for every permutation pi of {0, 1, ..., len(words) - 1} and every permutation sigma of {0, 1, ..., len(letters) - 1}, the function called on the permuted input (words[pi(0)], ..., words[pi(len(words)-1)]) and (letters[sigma(0)], ..., letters[sigma(len(letters)-1)]) with the same score also returns r.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_12 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ (π : Equiv.Perm (Fin words.val.length))
        (σ : Equiv.Perm (Fin letters.val.length))
        (words' letters' : Slice (alloc.vec.Vec Std.U8)) (r' : Std.I64),
        words'.val = List.ofFn (fun i : Fin words.val.length => words.val.get (π i)) →
        letters'.val = List.ofFn (fun i : Fin letters.val.length => letters.val.get (σ i)) →
        max_score_words words' letters' score = ok r' → r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∀ (π : Equiv.Perm (Fin words.val.length))
        (σ : Equiv.Perm (Fin letters.val.length))
        (words' letters' : Slice (alloc.vec.Vec Std.U8)) (r' : Std.I64),
        words'.val = List.ofFn (fun i : Fin words.val.length => words.val.get (π i)) →
        letters'.val = List.ofFn (fun i : Fin letters.val.length => letters.val.get (σ i)) →
        max_score_words words' letters' score = ok r' → r' = r) := by
  sorry

/-- Whenever the function returns a result r, if score[k] = 0 for every k with 0 <= k < 26, then r = 0.
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_13 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ k : Nat, k < 26 → scoreAt score k = 0) → r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      (∀ k : Nat, k < 26 → scoreAt score k = 0) → r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, there exists an admissible subset S of {0, 1, ..., len(words) - 1} such that sum over i in S of wordScore(i) = r. Here a subset S is admissible if for every c with 97 <= c <= 122, the sum over i in S of the number of positions j with 0 <= j < len(words[i]) and words[i][j] = c is at most the number of indices k with 0 <= k < len(letters) and letters[k][0] = c, and wordScore(i) = sum over j = 0 to len(words[i]) - 1 of score[words[i][j] - 97].
  Preconditions: len(words) is between 1 and 14 inclusive; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 15 and every byte words[i][j] with 0 <= j < len(words[i]) satisfies 97 <= words[i][j] <= 122; len(letters) is between 1 and 100 inclusive; for every i with 0 <= i < len(letters), len(letters[i]) = 1 and 97 <= letters[i][0] <= 122; len(score) = 26; for every k with 0 <= k < 26, 0 <= score[k] <= 10. -/
theorem spec_14 (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score) :
    ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∃ S : Finset (Fin words.val.length),
        admissible words letters S ∧ subsetScore score words S = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words letters : Slice (alloc.vec.Vec Std.U8)) (score : Slice Std.I64)
    (hpre : Pre words letters score), ∀ r : Std.I64, max_score_words words letters score = ok r →
      ∃ S : Finset (Fin words.val.length),
        admissible words letters S ∧ subsetScore score words S = r.val) := by
  sorry

end AegisSpec.MaxScoreWords
