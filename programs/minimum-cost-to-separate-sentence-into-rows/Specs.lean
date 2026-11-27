import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-to-separate-sentence-into-rows`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumCost

def IsSpace (b : Std.U8) : Prop := b.val = 32

def IsLowerLetter (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def BytesLowerOrSpace (s : List Std.U8) : Prop :=
  ∀ b ∈ s, IsSpace b ∨ IsLowerLetter b

def NoAdjacentSpaces : List Std.U8 → Prop
  | [] => True
  | _ :: [] => True
  | a :: b :: rest => (IsSpace a → ¬ IsSpace b) ∧ NoAdjacentSpaces (b :: rest)

def wordSplitAux (cur : List Std.U8) : List Std.U8 → List (List Std.U8)
  | [] => [cur.reverse]
  | b :: bs =>
    if b.val = 32 then
      cur.reverse :: wordSplitAux [] bs
    else
      wordSplitAux (b :: cur) bs

def wordList (s : List Std.U8) : List (List Std.U8) := wordSplitAux [] s

def WordsWithinK (kz : ℤ) (s : List Std.U8) : Prop :=
  ∀ w ∈ wordList s, (w.length : ℤ) ≤ kz

def wordLens (W : List (List Std.U8)) : List ℕ := W.map List.length

def rowLen (g : List (List Std.U8)) : ℕ := (g.map List.length).sum + (g.length - 1)

def IsPartition (W : List (List Std.U8)) (P : List (List (List Std.U8))) : Prop :=
  P.flatten = W ∧ ∀ g ∈ P, g ≠ []

def ValidPartition (kz : ℤ) (W : List (List Std.U8)) (P : List (List (List Std.U8))) : Prop :=
  IsPartition W P ∧ ∀ g ∈ P, (rowLen g : ℤ) ≤ kz

def rowCost (kz : ℤ) (g : List (List Std.U8)) : ℤ := (kz - (rowLen g : ℤ)) ^ 2

def costOf (kz : ℤ) (P : List (List (List Std.U8))) : ℤ :=
  (P.dropLast.map (rowCost kz)).sum

def RowsFull (kz : ℤ) (P : List (List (List Std.U8))) : Prop :=
  ∀ g ∈ P.dropLast, (rowLen g : ℤ) = kz

def costOfWordLens (kz : ℤ) (lens : List ℕ) : ℤ :=
  (lens.dropLast.map (fun L => (kz - (L : ℤ)) ^ 2)).sum

def minWordLen : List (List Std.U8) → ℕ
  | [] => 0
  | w :: ws => ws.foldl (fun acc v => Nat.min acc v.length) w.length

def adjacentPairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | _ :: [] => []
  | a :: b :: rest => (a, b) :: adjacentPairs (b :: rest)

/-- Let W(sentence) = (w_0, ..., w_{m-1}) be the words of sentence in order, obtained by splitting at the single spaces. For a consecutive group of words, its row length is the sum of the lengths of its words plus one less than the number of words in the group (the spaces between them). A valid partition P is a partition of W(sentence) into consecutive nonempty groups whose row lengths are all at most k. For such a P with rows G_0, ..., G_{q-1} and row lengths L_0, ..., L_{q-1}, its total cost is C(P) = sum_{t=0}^{q-2} (k - L_t)^2, i.e. the last row G_{q-1} is not charged; if q=1 the sum is 0. Whenever the function returns a result r, r is the minimum of C(P) over all valid partitions P.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_1 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      (∃ P, ValidPartition k.val (wordList sentence.val) P ∧ r.val = costOf k.val P) ∧
      (∀ P, ValidPartition k.val (wordList sentence.val) P → r.val ≤ costOf k.val P) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      (∃ P, ValidPartition k.val (wordList sentence.val) P ∧ r.val = costOf k.val P) ∧
      (∀ P, ValidPartition k.val (wordList sentence.val) P → r.val ≤ costOf k.val P)) := by
  sorry

/-- The function returns a result r (it does not fail by overflow, out-of-bounds, or panic) for every input (sentence, k) satisfying the preconditions.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_2 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∃ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∃ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r) := by
  sorry

/-- Let W(sentence) be the word list, and define a valid partition P to be a partition of W(sentence) into consecutive nonempty groups whose row lengths are all at most k, where row length is the sum of the word lengths in the group plus the number of spaces between those words. Define C(P) as the sum of (k - row length)^2 over all rows of P except the last row (empty sum 0 if P has one row). Whenever the function returns a result r, there exists a valid partition P of W(sentence) such that C(P) = r.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_3 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ∃ P, ValidPartition k.val (wordList sentence.val) P ∧ r.val = costOf k.val P := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ∃ P, ValidPartition k.val (wordList sentence.val) P ∧ r.val = costOf k.val P) := by
  sorry

/-- Let W(sentence) be the word list, and define a valid partition P to be a partition of W(sentence) into consecutive nonempty groups whose row lengths are all at most k, where row length is the sum of the word lengths in the group plus the number of spaces between those words. Define C(P) as the sum of (k - row length)^2 over all rows of P except the last row (empty sum 0 if P has one row). Whenever the function returns a result r, for every valid partition P of W(sentence), C(P) >= r.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_4 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ∀ P, ValidPartition k.val (wordList sentence.val) P → costOf k.val P ≥ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ∀ P, ValidPartition k.val (wordList sentence.val) P → costOf k.val P ≥ r.val) := by
  sorry

/-- Let W(sentence) be the word list, and define a valid partition P and its total cost C(P) as in spec_1: consecutive nonempty groups of words with every row length at most k, and C(P) is the sum of (k - row length)^2 over all rows except the last. Whenever the function returns a result r, r = 0 if and only if there exists a valid partition P of W(sentence) such that every row of P except the last one has length exactly k (the last row still must have length at most k).
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_5 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      (r.val = 0 ↔
        ∃ P, ValidPartition k.val (wordList sentence.val) P ∧ RowsFull k.val P) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      (r.val = 0 ↔
        ∃ P, ValidPartition k.val (wordList sentence.val) P ∧ RowsFull k.val P)) := by
  sorry

/-- Let W(sentence1) = (w_0, ..., w_{m-1}) and W(sentence2) = (v_0, ..., v_{n-1}) be the word lists obtained by splitting at spaces. If m = n and |w_i| = |v_i| for every i with 0 <= i < m, then whenever the function returns r on (sentence1, k) and q on (sentence2, k), r = q.
  Preconditions: Both (sentence1, k) and (sentence2, k) satisfy the same sentence constraints: for each sentence, its length is between 1 and 5000 inclusive; 1 <= k <= 5000; bytes are lowercase English letters or spaces; there is no leading or trailing space; no two adjacent spaces occur; and every word length is at most k. The same integer k is used for both calls. -/
theorem spec_6 (sentence1 sentence2 : Slice Std.U8) (k : Std.I64)
    (hlen1 : 1 ≤ sentence1.val.length ∧ sentence1.val.length ≤ 5000)
    (hlen2 : 1 ≤ sentence2.val.length ∧ sentence2.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes1 : BytesLowerOrSpace sentence1.val)
    (hbytes2 : BytesLowerOrSpace sentence2.val)
    (hfirst1 : ∀ b, sentence1.val.head? = some b → ¬ IsSpace b)
    (hlast1 : ∀ b, sentence1.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj1 : NoAdjacentSpaces sentence1.val)
    (hwords1 : WordsWithinK k.val sentence1)
    (hfirst2 : ∀ b, sentence2.val.head? = some b → ¬ IsSpace b)
    (hlast2 : ∀ b, sentence2.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj2 : NoAdjacentSpaces sentence2.val)
    (hwords2 : WordsWithinK k.val sentence2)
    (hsame : wordLens (wordList sentence1.val) = wordLens (wordList sentence2.val)) :
    ∀ r q : Std.I64,
      Aegis.MinimumCost.minimum_cost sentence1 k = ok r →
      Aegis.MinimumCost.minimum_cost sentence2 k = ok q → r.val = q.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence1 sentence2 : Slice Std.U8) (k : Std.I64)
    (hlen1 : 1 ≤ sentence1.val.length ∧ sentence1.val.length ≤ 5000)
    (hlen2 : 1 ≤ sentence2.val.length ∧ sentence2.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes1 : BytesLowerOrSpace sentence1.val)
    (hbytes2 : BytesLowerOrSpace sentence2.val)
    (hfirst1 : ∀ b, sentence1.val.head? = some b → ¬ IsSpace b)
    (hlast1 : ∀ b, sentence1.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj1 : NoAdjacentSpaces sentence1.val)
    (hwords1 : WordsWithinK k.val sentence1)
    (hfirst2 : ∀ b, sentence2.val.head? = some b → ¬ IsSpace b)
    (hlast2 : ∀ b, sentence2.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj2 : NoAdjacentSpaces sentence2.val)
    (hwords2 : WordsWithinK k.val sentence2)
    (hsame : wordLens (wordList sentence1.val) = wordLens (wordList sentence2.val)), ∀ r q : Std.I64,
      Aegis.MinimumCost.minimum_cost sentence1 k = ok r →
      Aegis.MinimumCost.minimum_cost sentence2 k = ok q → r.val = q.val) := by
  sorry

/-- Let W(sentence) = (w_0, ..., w_{m-1}) be the word list and let Lmin = min_{0 <= i < m} |w_i| (this minimum is over a nonempty list). Whenever the function returns a result r, r <= (m - 1) * (k - Lmin)^2.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; and every maximal contiguous non-space block (word) has length at most k. -/
theorem spec_7 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      r.val ≤
        (((wordList sentence.val).length : ℤ) - 1) *
          (k.val - (minWordLen (wordList sentence.val) : ℤ)) ^ 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      r.val ≤
        (((wordList sentence.val).length : ℤ) - 1) *
          (k.val - (minWordLen (wordList sentence.val) : ℤ)) ^ 2) := by
  sorry

/-- Whenever the function returns a result r, if |w_0| + |w_1| + 1 <= k then r = 0, and if |w_0| + |w_1| + 1 > k then r = (k - |w_0|)^2.
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; every word length is at most k; and the word list W(sentence) has exactly two words w_0, w_1 (equivalently, sentence contains exactly one space). -/
theorem spec_8 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val)
    (w0 w1 : List Std.U8) (hW : wordList sentence.val = [w0, w1]) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ((w0.length : ℤ) + (w1.length : ℤ) + 1 ≤ k.val → r.val = 0) ∧
      (k.val < (w0.length : ℤ) + (w1.length : ℤ) + 1 →
        r.val = (k.val - (w0.length : ℤ)) ^ 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val)
    (w0 w1 : List Std.U8) (hW : wordList sentence.val = [w0, w1]), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      ((w0.length : ℤ) + (w1.length : ℤ) + 1 ≤ k.val → r.val = 0) ∧
      (k.val < (w0.length : ℤ) + (w1.length : ℤ) + 1 →
        r.val = (k.val - (w0.length : ℤ)) ^ 2)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{m-2} (k - |w_i|)^2 (this sum is 0 when m=1).
  Preconditions: len(sentence) is between 1 and 5000 inclusive; 1 <= k <= 5000; every byte of sentence is either a lowercase English letter (ASCII 97 through 122) or a space (ASCII 32); sentence[0] and sentence[len(sentence)-1] are not spaces; no two adjacent bytes are spaces; every word length is at most k; let W(sentence) = (w_0, ..., w_{m-1}); and for every i with 0 <= i < m-1, |w_i| + |w_{i+1}| + 1 > k. -/
theorem spec_9 (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val)
    (hpair : ∀ p ∈ adjacentPairs (wordLens (wordList sentence.val)),
      (p.1 : ℤ) + (p.2 : ℤ) + 1 > k.val) :
    ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      r.val = costOfWordLens k.val (wordLens (wordList sentence.val)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 5000)
    (hk : 1 ≤ k.val ∧ k.val ≤ 5000)
    (hbytes : BytesLowerOrSpace sentence.val)
    (hfirst : ∀ b, sentence.val.head? = some b → ¬ IsSpace b)
    (hlast : ∀ b, sentence.val.getLast? = some b → ¬ IsSpace b)
    (hnoAdj : NoAdjacentSpaces sentence.val)
    (hwords : WordsWithinK k.val sentence.val)
    (hpair : ∀ p ∈ adjacentPairs (wordLens (wordList sentence.val)),
      (p.1 : ℤ) + (p.2 : ℤ) + 1 > k.val), ∀ r : Std.I64, Aegis.MinimumCost.minimum_cost sentence k = ok r →
      r.val = costOfWordLens k.val (wordLens (wordList sentence.val))) := by
  sorry

end AegisSpec.MinimumCost
