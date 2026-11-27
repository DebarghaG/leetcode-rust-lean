import Aegis.WordsAbbreviation.Code.Funs

/-!
# Specifications of `Aegis.WordsAbbreviation.words_abbreviation`

LeetCode problem `word-abbreviation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WordsAbbreviation

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def IsDigitByte (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  instance instDecidableIsLowerByte (b : Std.U8) : Decidable (IsLowerByte b) := by
    unfold IsLowerByte; infer_instance

  instance instDecidableIsDigitByte (b : Std.U8) : Decidable (IsDigitByte b) := by
    unfold IsDigitByte; infer_instance

  def inWords (words : Slice (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
    words.val.map (fun w => w.val)

  def wordBytes (words : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
    (inWords words).getD i []

  def outBytes (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
    (r.val.map (fun w => w.val)).getD i []

  def byteOf (n : Nat) : Std.U8 := UScalar.mk (BitVec.ofNat 8 n)

  def digitsRev : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, n => if n = 0 then [] else n % 10 :: digitsRev fuel (n / 10)

  def decAscii (n : Nat) : List Std.U8 :=
    let ds := digitsRev (n + 1) n
    (if ds = [] then [0] else ds.reverse).map (fun d => byteOf (48 + d))

  def abbr (w : List Std.U8) (p : Nat) : List Std.U8 :=
    w.take p ++ decAscii (w.length - p - 1) ++ w.drop (w.length - 1)

  def pick (w : List Std.U8) (p : Nat) : List Std.U8 :=
    if (abbr w p).length < w.length then abbr w p else w

  def firstByte (l : List Std.U8) : Option Std.U8 := l.head?

  def lastByte (l : List Std.U8) : Option Std.U8 := l.getLast?

  def leadingLower (l : List Std.U8) : Nat :=
    (l.takeWhile (fun b => decide (IsLowerByte b))).length

  def Free (words : Slice (alloc.vec.Vec Std.U8)) (i p : Nat) : Prop :=
    ∀ j, j ≠ i → j < words.val.length →
      ∀ q, 1 ≤ q → q ≤ (wordBytes words j).length - 1 →
        abbr (wordBytes words j) q ≠ abbr (wordBytes words i) p

  def IsLeastFree (words : Slice (alloc.vec.Vec Std.U8)) (i p : Nat) : Prop :=
    1 ≤ p ∧ p ≤ (wordBytes words i).length - 1 ∧ Free words i p ∧
      ∀ p', 1 ≤ p' → p' < p → p' ≤ (wordBytes words i).length - 1 → ¬ Free words i p'

  def FreeSameP (words : Slice (alloc.vec.Vec Std.U8)) (i p : Nat) : Prop :=
    ∀ j, j ≠ i → j < words.val.length → p < (wordBytes words j).length →
      abbr (wordBytes words j) p ≠ abbr (wordBytes words i) p

  def IsLeastFreeSameP (words : Slice (alloc.vec.Vec Std.U8)) (i p : Nat) : Prop :=
    1 ≤ p ∧ p ≤ (wordBytes words i).length - 1 ∧ FreeSameP words i p ∧
      ∀ p', 1 ≤ p' → p' < p → p' ≤ (wordBytes words i).length - 1 → ¬ FreeSameP words i p'

  /-- The function returns a result r with len(r) = len(words). For every i with 0 <= i < len(words), let w = words[i] and n = len(w). For 1 <= p <= n-1, write A(w,p) for w[0] through w[p-1], followed by the decimal ASCII representation of n-p-1 (no leading zeros; the value 0 is the single ASCII digit zero), followed by w[n-1]. Let p_i be the least p in [1,n-1] such that for every j != i and every q with 1 <= q <= len(words[j])-1, A(words[j],q) != A(w,p). Let a = A(w,p_i). Then r[i] = a if len(a) < n, and r[i] = w otherwise.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_1
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j) :
      ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r ∧
        r.val.length = words.val.length ∧
        ∀ i, i < words.val.length → ∃ p, IsLeastFree words i p ∧
          outBytes r i = pick (wordBytes words i) p := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j), ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r ∧
          r.val.length = words.val.length ∧
          ∀ i, i < words.val.length → ∃ p, IsLeastFree words i p ∧
            outBytes r i = pick (wordBytes words i) p) := by
    sorry

  /-- The function returns a result r; in particular, for every input satisfying the preconditions it does not fail, panic, or overflow.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_2
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j) :
      ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j), ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r) := by
    sorry

  /-- The function returns a result r with len(r) = len(words); for every i with 0 <= i < len(words), r[i] is nonempty and len(r[i]) <= len(words[i]).
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_3
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j) :
      ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r ∧
        r.val.length = words.val.length ∧
        ∀ i, i < words.val.length →
          1 ≤ (outBytes r i).length ∧ (outBytes r i).length ≤ (wordBytes words i).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j), ∃ r, Aegis.WordsAbbreviation.words_abbreviation words = ok r ∧
          r.val.length = words.val.length ∧
          ∀ i, i < words.val.length →
            1 ≤ (outBytes r i).length ∧ (outBytes r i).length ≤ (wordBytes words i).length) := by
    sorry

  /-- For every i with 0 <= i < len(words), if r[i] != words[i], then there exists an integer k with 1 <= k <= len(words[i])-1 such that r[i] is exactly words[i][0] through words[i][k-1], followed by the decimal ASCII representation of len(words[i])-k-1, followed by words[i][len(words[i])-1]. Moreover, k is the number of leading bytes of r[i] that are ASCII lowercase letters.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_4
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
        ∃ k, 1 ≤ k ∧ k ≤ (wordBytes words i).length - 1 ∧
          outBytes r i = abbr (wordBytes words i) k ∧
          k = leadingLower (outBytes r i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
          ∃ k, 1 ≤ k ∧ k ≤ (wordBytes words i).length - 1 ∧
            outBytes r i = abbr (wordBytes words i) k ∧
            k = leadingLower (outBytes r i)) := by
    sorry

  /-- For every i with 0 <= i < len(words), if r[i] != words[i], then len(r[i]) < len(words[i]).
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_5
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
        (outBytes r i).length < (wordBytes words i).length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
          (outBytes r i).length < (wordBytes words i).length) := by
    sorry

  /-- For every i with 0 <= i < len(words), if len(words[i]) <= 3, then r[i] = words[i].
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_6
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → (wordBytes words i).length ≤ 3 →
        outBytes r i = wordBytes words i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → (wordBytes words i).length ≤ 3 →
          outBytes r i = wordBytes words i) := by
    sorry

  /-- For every i with 0 <= i < len(words), suppose no j != i has len(words[j]) = len(words[i]), words[j][0] = words[i][0], and words[j][len(words[j])-1] = words[i][len(words[i])-1]. Let a be words[i][0], followed by the decimal ASCII representation of len(words[i])-2, followed by words[i][len(words[i])-1]. Then r[i] = a if len(a) < len(words[i]), and r[i] = words[i] otherwise.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_7
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length →
        (∀ j, j ≠ i → j < words.val.length →
          ¬ ((wordBytes words j).length = (wordBytes words i).length ∧
              firstByte (wordBytes words j) = firstByte (wordBytes words i) ∧
              lastByte (wordBytes words j) = lastByte (wordBytes words i))) →
        outBytes r i = pick (wordBytes words i) 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length →
          (∀ j, j ≠ i → j < words.val.length →
            ¬ ((wordBytes words j).length = (wordBytes words i).length ∧
                firstByte (wordBytes words j) = firstByte (wordBytes words i) ∧
                lastByte (wordBytes words j) = lastByte (wordBytes words i))) →
          outBytes r i = pick (wordBytes words i) 1) := by
    sorry

  /-- For every i with 0 <= i < len(words) such that r[i] != words[i], let k be the number of leading ASCII lowercase bytes of r[i]. Then for every integer q with 1 <= q < k, there exists j != i such that q <= len(words[j])-1 and A(words[j],q) = A(words[i],q), where A(w,p) is the first p bytes of w, followed by the decimal ASCII representation of len(w)-p-1, followed by the last byte of w.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_8
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
        ∀ q, 1 ≤ q → q < leadingLower (outBytes r i) →
          ∃ j, j ≠ i ∧ j < words.val.length ∧ q ≤ (wordBytes words j).length - 1 ∧
            abbr (wordBytes words j) q = abbr (wordBytes words i) q := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
          ∀ q, 1 ≤ q → q < leadingLower (outBytes r i) →
            ∃ j, j ≠ i ∧ j < words.val.length ∧ q ≤ (wordBytes words j).length - 1 ∧
              abbr (wordBytes words j) q = abbr (wordBytes words i) q) := by
    sorry

  /-- For every i with 0 <= i < len(words) such that r[i] != words[i], if k is the number of leading ASCII lowercase bytes of r[i], then k <= len(words[i])-1 and for every j != i with len(words[j]) > k, A(words[j],k) != A(words[i],k), where A(w,p) is the first p bytes of w, followed by the decimal ASCII representation of len(w)-p-1, followed by the last byte of w.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_9
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
        leadingLower (outBytes r i) ≤ (wordBytes words i).length - 1 ∧
        ∀ j, j ≠ i → j < words.val.length →
          leadingLower (outBytes r i) < (wordBytes words j).length →
          abbr (wordBytes words j) (leadingLower (outBytes r i)) ≠
            abbr (wordBytes words i) (leadingLower (outBytes r i)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → outBytes r i ≠ wordBytes words i →
          leadingLower (outBytes r i) ≤ (wordBytes words i).length - 1 ∧
          ∀ j, j ≠ i → j < words.val.length →
            leadingLower (outBytes r i) < (wordBytes words j).length →
            abbr (wordBytes words j) (leadingLower (outBytes r i)) ≠
              abbr (wordBytes words i) (leadingLower (outBytes r i))) := by
    sorry

  /-- For every i and j with 0 <= i < j < len(words), r[i] != r[j].
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_10
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i j, i < j → j < words.val.length → outBytes r i ≠ outBytes r j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i j, i < j → j < words.val.length → outBytes r i ≠ outBytes r j) := by
    sorry

  /-- Whenever the function returns r for words and r' for words', for every k with 0 <= k < len(words), r'[k] = r[pi(k)].
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. Also words' is a slice of the same length with the same entries as words, and pi is a bijection on the indices with words'[k] = words[pi(k)] for every k. -/
  theorem spec_11
      (words words' : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (pi : Nat → Nat)
      (h_len' : words'.val.length = words.val.length)
      (h_entry : ∀ k, k < words.val.length → wordBytes words' k = wordBytes words (pi k))
      (h_image : ∀ k, k < words.val.length → pi k < words.val.length)
      (h_inj : ∀ a b, a < words.val.length → b < words.val.length → pi a = pi b → a = b)
      (h_surj : ∀ b, b < words.val.length → ∃ a, a < words.val.length ∧ pi a = b)
      (r r' : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r)
      (hr' : Aegis.WordsAbbreviation.words_abbreviation words' = ok r') :
      ∀ k, k < words.val.length → outBytes r' k = outBytes r (pi k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (pi : Nat → Nat)
        (h_len' : words'.val.length = words.val.length)
        (h_entry : ∀ k, k < words.val.length → wordBytes words' k = wordBytes words (pi k))
        (h_image : ∀ k, k < words.val.length → pi k < words.val.length)
        (h_inj : ∀ a b, a < words.val.length → b < words.val.length → pi a = pi b → a = b)
        (h_surj : ∀ b, b < words.val.length → ∃ a, a < words.val.length ∧ pi a = b)
        (r r' : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r)
        (hr' : Aegis.WordsAbbreviation.words_abbreviation words' = ok r'), ∀ k, k < words.val.length → outBytes r' k = outBytes r (pi k)) := by
    sorry

  /-- For every i with 0 <= i < len(words), every byte of r[i] is either an ASCII lowercase letter or an ASCII decimal digit. If r[i] != words[i], then r[i] contains at least one ASCII digit; all digits of r[i] form a single contiguous block; every byte before that block is an ASCII lowercase letter; and the digit block is followed by exactly one byte, which is an ASCII lowercase letter.
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_12
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length →
        (∀ b, b ∈ outBytes r i → IsLowerByte b ∨ IsDigitByte b) ∧
        (outBytes r i ≠ wordBytes words i →
          (∃ b, b ∈ outBytes r i ∧ IsDigitByte b) ∧
          ∃ pre dig post, outBytes r i = pre ++ dig ++ post ∧
            (∀ b, b ∈ pre → IsLowerByte b) ∧
            dig ≠ [] ∧
            (∀ b, b ∈ dig → IsDigitByte b) ∧
            post.length = 1 ∧
            (∀ b, b ∈ post → IsLowerByte b)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length →
          (∀ b, b ∈ outBytes r i → IsLowerByte b ∨ IsDigitByte b) ∧
          (outBytes r i ≠ wordBytes words i →
            (∃ b, b ∈ outBytes r i ∧ IsDigitByte b) ∧
            ∃ pre dig post, outBytes r i = pre ++ dig ++ post ∧
              (∀ b, b ∈ pre → IsLowerByte b) ∧
              dig ≠ [] ∧
              (∀ b, b ∈ dig → IsDigitByte b) ∧
              post.length = 1 ∧
              (∀ b, b ∈ post → IsLowerByte b))) := by
    sorry

  /-- For every i with 0 <= i < len(words), if len(words[i]) >= 4 and r[i] = words[i], let p_i be the least p in [1,len(words[i])-1] such that A(words[i],p) is unique among all A(words[j],q) for j != i and 1 <= q <= len(words[j])-1, where A(w,p) is the first p bytes of w, followed by the decimal ASCII representation of len(w)-p-1, followed by the last byte of w. Then len(A(words[i],p_i)) >= len(words[i]).
    Preconditions: words is a slice of byte vectors with 1 <= len(words) <= 400; for every i with 0 <= i < len(words), 2 <= len(words[i]) <= 400, every byte of words[i] is an ASCII lowercase letter a through z, and words[i] is distinct from words[j] for every j != i. -/
  theorem spec_13
      (words : Slice (alloc.vec.Vec Std.U8))
      (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
      (h_word_len : ∀ i, i < words.val.length →
        2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
      (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
      (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
        wordBytes words i ≠ wordBytes words j)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
      (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r) :
      ∀ i, i < words.val.length → 4 ≤ (wordBytes words i).length →
        outBytes r i = wordBytes words i →
        ∃ p, IsLeastFree words i p ∧
          (wordBytes words i).length ≤ (abbr (wordBytes words i) p).length := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8))
        (h_len_lo : 1 ≤ words.val.length) (h_len_hi : words.val.length ≤ 400)
        (h_word_len : ∀ i, i < words.val.length →
          2 ≤ (wordBytes words i).length ∧ (wordBytes words i).length ≤ 400)
        (h_word_lower : ∀ i, i < words.val.length → ∀ b, b ∈ wordBytes words i → IsLowerByte b)
        (h_distinct : ∀ i j, i < words.val.length → j < words.val.length → i ≠ j →
          wordBytes words i ≠ wordBytes words j)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
        (hr : Aegis.WordsAbbreviation.words_abbreviation words = ok r), ∀ i, i < words.val.length → 4 ≤ (wordBytes words i).length →
          outBytes r i = wordBytes words i →
          ∃ p, IsLeastFree words i p ∧
            (wordBytes words i).length ≤ (abbr (wordBytes words i) p).length) := by
    sorry

  end AegisSpec.WordsAbbreviation
