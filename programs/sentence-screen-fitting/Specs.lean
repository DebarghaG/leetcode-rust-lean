import Aegis.WordsTyping.Code.Funs

/-!
# Specifications of `Aegis.WordsTyping.words_typing`

LeetCode problem `sentence-screen-fitting`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.WordsTyping

def IsWord (w : alloc.vec.Vec U8) : Prop :=
  1 ≤ w.val.length ∧ w.val.length ≤ 10 ∧ ∀ b ∈ w.val, 97 ≤ b.val ∧ b.val ≤ 122

def ValidSentence (sentence : Slice (alloc.vec.Vec U8)) : Prop :=
  1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100 ∧
    ∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → IsWord w

def ValidScreen (rows cols : Std.I64) : Prop :=
  1 ≤ rows.val ∧ rows.val ≤ 20000 ∧ 1 ≤ cols.val ∧ cols.val ≤ 20000

def wordLens (sentence : Slice (alloc.vec.Vec U8)) : List Nat :=
  sentence.val.map (fun w => w.val.length)

def periodLen (lens : List Nat) (j : Nat) : Nat :=
  (lens[j % lens.length]?).getD 1

def needOf (lens : List Nat) (pos j : Nat) : Nat :=
  max 1 (if pos = 0 then periodLen lens j else periodLen lens j + 1)

def fillRow (lens : List Nat) (cols : Nat) : Nat → Nat → Nat × Nat
  | pos, j =>
    if pos + needOf lens pos j ≤ cols then
      let r := fillRow lens cols (pos + needOf lens pos j) (j + 1)
      (r.1 + 1, r.2)
    else (0, j)
termination_by pos _ => cols + 1 - pos
decreasing_by
  simp only [needOf]
  have h1 : 1 ≤ max 1 (if pos = 0 then periodLen lens j else periodLen lens j + 1) := le_max_left ..
  omega

def fillRows (lens : List Nat) (cols : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | rows + 1, j =>
      let r := fillRow lens cols 0 j
      r.1 + fillRows lens cols rows r.2

def placedWords (lens : List Nat) (rows cols : Nat) : Nat :=
  fillRows lens cols rows 0

def fillState (lens : List Nat) (cols : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | T + 1 =>
      match fillState lens cols T with
      | (rowIdx, pos) =>
        if pos + needOf lens pos T ≤ cols then (rowIdx, pos + needOf lens pos T)
        else (rowIdx + 1, needOf lens 0 T)

def FitsByRows (lens : List Nat) (rows cols T : Nat) : Prop :=
  ∀ j, j < T → (fillState lens cols (j + 1)).1 < rows

/-- Let n = len(sentence). For every j >= 0 let W_j = sentence[j mod n] (0-indexed). Let T be the number of words placed by the canonical row-major filling of the infinite sequence W_0, W_1, ... on the rows x cols screen: W_0 starts at row 0, column 0; after a word, the next word is placed on the same row after exactly one empty cell iff that word plus the separating cell fits within the remaining columns of that row, otherwise it is placed at column 0 of the next row; filling stops before the first word that has length > cols or that would need a row with index >= rows. The function returns r = floor(T / n) using integer division, i.e. r is the number of complete copies of sentence contained in this maximal placed prefix.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_1 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) :
    ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (placedWords (wordLens sentence) rows.val.toNat cols.val.toNat /
          sentence.val.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols), ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (placedWords (wordLens sentence) rows.val.toNat cols.val.toNat /
          sentence.val.length)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result: there exists an integer r such that the call evaluates to Result.ok r. It does not fail by overflow, division by zero, out-of-bounds indexing, or panic.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_2 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) :
    ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols), ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r) := by
  sorry

/-- Let n = len(sentence) and q = floor((cols+1)/2). Whenever the function returns r, 0 <= r <= floor(rows * q / n).
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_3 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    0 ≤ r.val ∧
      r.val ≤ Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / 2) / sentence.val.length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), 0 ≤ r.val ∧
      r.val ≤ Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / 2) / sentence.val.length)) := by
  sorry

/-- Let L = sum_{i=0}^{len(sentence)-1} len(sentence[i]). Whenever the function returns r, r * L <= rows * cols.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_4 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    r.val * Int.ofNat (wordLens sentence).sum ≤ rows.val * cols.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), r.val * Int.ofNat (wordLens sentence).sum ≤ rows.val * cols.val) := by
  sorry

/-- If there exists i with 0 <= i < len(sentence) and len(sentence[i]) > cols, then the function returns r and r = 0.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_5 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hbig : ∃ (i : Nat) (w : alloc.vec.Vec U8),
      sentence.val[i]? = some w ∧ cols.val < Int.ofNat w.val.length) :
    ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hbig : ∃ (i : Nat) (w : alloc.vec.Vec U8),
      sentence.val[i]? = some w ∧ cols.val < Int.ofNat w.val.length), ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ r.val = 0) := by
  sorry

/-- If len(sentence) > rows * cols, then the function returns r and r = 0.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_6 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hbig : rows.val * cols.val < Int.ofNat sentence.val.length) :
    ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hbig : rows.val * cols.val < Int.ofNat sentence.val.length), ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ r.val = 0) := by
  sorry

/-- Let n = len(sentence) and q = floor((cols+1)/2). The function returns r = floor(rows * q / n).
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a byte array of length exactly 1 consisting of a lowercase ASCII letter; 1 <= rows, cols <= 20000. -/
theorem spec_7 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hunit : ∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / 2) /
          sentence.val.length) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hunit : ∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = 1), ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / 2) /
          sentence.val.length)) := by
  sorry

/-- Let L = len(sentence[0]). The function returns r = rows * floor((cols+1)/(L+1)).
  Preconditions: 1 <= len(sentence) <= 100; len(sentence) = 1; sentence[0] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_8 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hone : sentence.val.length = 1) (w0 : alloc.vec.Vec U8) (hw0 : sentence.val[0]? = some w0) :
    ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / (w0.val.length + 1))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hone : sentence.val.length = 1) (w0 : alloc.vec.Vec U8) (hw0 : sentence.val[0]? = some w0), ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / (w0.val.length + 1)))) := by
  sorry

/-- Let n = len(sentence). The function returns r = floor(rows/n) if every word has length 1, and returns r = 0 if some word has length > 1.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; rows >= 1; cols = 1. -/
theorem spec_9 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hrows : 1 ≤ rows.val) (hcols : cols.val = 1) :
    ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        ((∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = 1) →
          r.val = Int.ofNat (rows.val.toNat / sentence.val.length)) ∧
        ((∃ (i : Nat) (w : alloc.vec.Vec U8),
            sentence.val[i]? = some w ∧ 1 < w.val.length) → r.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hrows : 1 ≤ rows.val) (hcols : cols.val = 1), ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        ((∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = 1) →
          r.val = Int.ofNat (rows.val.toNat / sentence.val.length)) ∧
        ((∃ (i : Nat) (w : alloc.vec.Vec U8),
            sentence.val[i]? = some w ∧ 1 < w.val.length) → r.val = 0)) := by
  sorry

/-- Let n = len(sentence) and W = (sum_{i=0}^{n-1} len(sentence[i])) + (n-1). If W <= cols, then the function returns r and r >= rows.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_10 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hW : (wordLens sentence).sum + (sentence.val.length - 1) ≤ cols.val.toNat) :
    ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ rows.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (hW : (wordLens sentence).sum + (sentence.val.length - 1) ≤ cols.val.toNat), ∃ r : Std.I64, Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧ rows.val ≤ r.val) := by
  sorry

/-- Let n = len(sentence) and let r be the returned value. The first r*n words W_0,...,W_{r*n-1} of the infinite periodic word sequence W_j = sentence[j mod n] can be placed on the screen by the row-major filling rule: start at top-left; keep a word on the current row iff it fits after one separating space, otherwise move it to column 0 of the next row. Equivalently, at least r complete copies of sentence fit in order.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_11 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat
      (r.val.toNat * sentence.val.length) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat
      (r.val.toNat * sentence.val.length)) := by
  sorry

/-- Let n = len(sentence) and let r be the returned value. The first (r+1)*n words of the infinite periodic word sequence W_j = sentence[j mod n] cannot all be placed by the same row-major filling rule; equivalently, r+1 complete copies of sentence cannot be fitted in order by row-major filling on this screen.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_12 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    ¬ FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat
      ((r.val.toNat + 1) * sentence.val.length) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), ¬ FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat
      ((r.val.toNat + 1) * sentence.val.length)) := by
  sorry

/-- Let r be the value returned by words_typing(sentence, rows, cols) and let r' be the value returned by words_typing(sentence', rows, cols). Then r = r'.
  Preconditions: sentence and sentence' are lists of byte vectors satisfying 1 <= len(sentence) = len(sentence') <= 100, and for every i with 0 <= i < len(sentence), len(sentence[i]) = len(sentence'[i]), with all words nonempty, of length at most 10, and lowercase ASCII; 1 <= rows, cols <= 20000. -/
theorem spec_13 (sentence sentence' : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hsent' : ValidSentence sentence')
    (hscreen : ValidScreen rows cols) (hsame : wordLens sentence = wordLens sentence')
    (r r' : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r)
    (hr' : Aegis.WordsTyping.words_typing sentence' rows cols = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (sentence sentence' : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hsent' : ValidSentence sentence')
    (hscreen : ValidScreen rows cols) (hsame : wordLens sentence = wordLens sentence')
    (r r' : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r)
    (hr' : Aegis.WordsTyping.words_typing sentence' rows cols = ok r'), r.val = r'.val) := by
  sorry

/-- Let r be the value returned by words_typing(sentence, rows, cols). For every integer R with 1 <= R <= rows, the call words_typing(sentence, R, cols) returns a value r_R and r_R <= r.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_14 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    ∀ R : Std.I64, 1 ≤ R.val → R.val ≤ rows.val →
      ∃ r_R : Std.I64, Aegis.WordsTyping.words_typing sentence R cols = ok r_R ∧ r_R.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), ∀ R : Std.I64, 1 ≤ R.val → R.val ≤ rows.val →
      ∃ r_R : Std.I64, Aegis.WordsTyping.words_typing sentence R cols = ok r_R ∧ r_R.val ≤ r.val) := by
  sorry

/-- Let r be the value returned by words_typing(sentence, rows, cols). For every integer C with 1 <= C <= cols, the call words_typing(sentence, rows, C) returns a value r_C and r_C <= r.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_15 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    ∀ C : Std.I64, 1 ≤ C.val → C.val ≤ cols.val →
      ∃ r_C : Std.I64, Aegis.WordsTyping.words_typing sentence rows C = ok r_C ∧ r_C.val ≤ r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), ∀ C : Std.I64, 1 ≤ C.val → C.val ≤ cols.val →
      ∃ r_C : Std.I64, Aegis.WordsTyping.words_typing sentence rows C = ok r_C ∧ r_C.val ≤ r.val) := by
  sorry

/-- Let n = len(sentence). The function returns r = 0 if and only if the first n words W_0,...,W_{n-1} of the infinite periodic sequence W_j = sentence[j mod n] cannot all be placed by the canonical row-major filling on the rows x cols screen; equivalently, if and only if either some sentence[i] has length > cols or placing W_0,...,W_{n-1} would require a row with index >= rows.
  Preconditions: 1 <= len(sentence) <= 100; for every i with 0 <= i < len(sentence), sentence[i] is a nonempty byte array of length at most 10 consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_16 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r) :
    (r.val = 0 ↔
        ¬ FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat sentence.val.length) ∧
      (r.val = 0 ↔
        ((∃ (i : Nat) (w : alloc.vec.Vec U8),
            sentence.val[i]? = some w ∧ cols.val < Int.ofNat w.val.length) ∨
          rows.val.toNat ≤
            (fillState (wordLens sentence) cols.val.toNat sentence.val.length).1)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols) (r : Std.I64)
    (hr : Aegis.WordsTyping.words_typing sentence rows cols = ok r), (r.val = 0 ↔
        ¬ FitsByRows (wordLens sentence) rows.val.toNat cols.val.toNat sentence.val.length) ∧
      (r.val = 0 ↔
        ((∃ (i : Nat) (w : alloc.vec.Vec U8),
            sentence.val[i]? = some w ∧ cols.val < Int.ofNat w.val.length) ∨
          rows.val.toNat ≤
            (fillState (wordLens sentence) cols.val.toNat sentence.val.length).1))) := by
  sorry

/-- Let n = len(sentence) and k = floor((cols+1)/(L+1)). The function returns r = floor(rows * k / n).
  Preconditions: 1 <= len(sentence) <= 100; there exists an integer L with 1 <= L <= 10 such that for every i with 0 <= i < len(sentence), sentence[i] is a byte array of length exactly L consisting of lowercase ASCII letters; 1 <= rows, cols <= 20000. -/
theorem spec_17 (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (L : Nat) (hL : 1 ≤ L) (hL' : L ≤ 10)
    (hlens : ∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = L) :
    ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / (L + 1)) /
          sentence.val.length) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (sentence : Slice (alloc.vec.Vec U8)) (rows cols : Std.I64)
    (hsent : ValidSentence sentence) (hscreen : ValidScreen rows cols)
    (L : Nat) (hL : 1 ≤ L) (hL' : L ≤ 10)
    (hlens : ∀ (i : Nat) (w : alloc.vec.Vec U8), sentence.val[i]? = some w → w.val.length = L), ∃ r : Std.I64,
      Aegis.WordsTyping.words_typing sentence rows cols = ok r ∧
        r.val = Int.ofNat (rows.val.toNat * ((cols.val.toNat + 1) / (L + 1)) /
          sentence.val.length)) := by
  sorry

end AegisSpec.WordsTyping
