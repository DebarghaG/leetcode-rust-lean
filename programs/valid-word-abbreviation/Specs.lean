import Aegis.ValidWordAbbreviation.Code.Funs

/-!
# Specifications of `Aegis.ValidWordAbbreviation.valid_word_abbreviation`

LeetCode problem `valid-word-abbreviation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidWordAbbreviation

  open Aegis.ValidWordAbbreviation

  @[reducible] def isLower (c : U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

  @[reducible] def isDigit (c : U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

  def byteAt (l : List U8) (i : Nat) : Option Nat := (l[i]?).map (fun b => b.val)

  def SameBytes (l₁ l₂ : List U8) : Prop :=
    l₁.length = l₂.length ∧ ∀ (i : Nat), i < l₁.length → byteAt l₁ i = byteAt l₂ i

  def countLower (abbr : List U8) : Nat := (abbr.filter (fun c => decide (isLower c))).length

  inductive Token where

    | letter (c : U8)

    | num (first : U8) (value : Nat)

  namespace Token

  def expandedLength : Token → Nat
    | letter _ => 1
    | num _ n => n

  def value? : Token → Option Nat
    | letter _ => none
    | num _ n => some n

  end Token

  structure RunState where

    start : Nat

    first : U8

    value : Nat

  structure TState where

    pos : Nat

    acc : List (Nat × Token)

    run : Option RunState

  namespace TState

  def step (st : TState) (c : U8) : TState :=
    if isDigit c then
      match st.run with
      | none => { pos := st.pos + 1, acc := st.acc, run := some { start := st.pos, first := c, value := c.val - 48 } }
      | some r => { pos := st.pos + 1, acc := st.acc, run := some { start := r.start, first := r.first, value := 10 * r.value + (c.val - 48) } }
    else
      let acc :=
        match st.run with
        | none => st.acc
        | some r => st.acc ++ [(r.start, Token.num r.first r.value)]
      { pos := st.pos + 1, acc := acc ++ [(st.pos, Token.letter c)], run := none }

  def finish (st : TState) : List (Nat × Token) :=
    match st.run with
    | none => st.acc
    | some r => st.acc ++ [(r.start, Token.num r.first r.value)]

  end TState

  def indexedTokens (abbr : List U8) : List (Nat × Token) :=
    (abbr.foldl TState.step { pos := 0, acc := [], run := none }).finish

  def tokens (abbr : List U8) : List Token := (indexedTokens abbr).map (fun p => p.2)

  def digitRunValues (abbr : List U8) : List Nat := (tokens abbr).filterMap Token.value?

  def digitRunValueSum (abbr : List U8) : Nat := (digitRunValues abbr).sum

  def DigitRunsBounded (abbr : List U8) (B : Nat) : Prop :=
    ∀ t ∈ tokens abbr, ∀ (d0 : U8) (n : Nat), t = Token.num d0 n → n ≤ B

  def NoLeadingZeroDigitRun (abbr : List U8) : Prop :=
    ∀ t ∈ tokens abbr, ∀ (d0 : U8) (n : Nat), t = Token.num d0 n → d0.val ≠ 48

  def HasLeadingZeroDigitRun (abbr : List U8) : Prop :=
    ∃ t ∈ tokens abbr, ∃ (d0 : U8) (n : Nat), t = Token.num d0 n ∧ d0.val = 48

  def countLetters (ts : List Token) : Nat :=
    (ts.filter (fun t => match t with | Token.letter _ => true | Token.num _ _ => false)).length

  def sumDigitValues (ts : List Token) : Nat := (ts.filterMap Token.value?).sum

  def expandedLength (abbr : List U8) : Nat := countLower abbr + digitRunValueSum abbr

  def expandedAfterTokens (abbr : List U8) (m : Nat) : Nat :=
    countLetters ((tokens abbr).take m) + sumDigitValues ((tokens abbr).take m)

  def expandedBefore (abbr : List U8) (k : Nat) : Nat :=
    countLower (abbr.take k) +
      sumDigitValues (((indexedTokens abbr).takeWhile (fun p => decide (p.1 < k))).map (fun p => p.2))

  def AbbrMatchesFrom (word : List U8) : Nat → List Token → Prop
    | p, [] => p = word.length
    | p, Token.letter c :: ts =>
      p < word.length ∧ byteAt word p = some c.val ∧ AbbrMatchesFrom word (p + 1) ts
    | p, Token.num d0 n :: ts =>
      d0.val ≠ 48 ∧ 0 < n ∧ p + n ≤ word.length ∧ AbbrMatchesFrom word (p + n) ts

  def MatchesAbbr (word abbr : List U8) : Prop := AbbrMatchesFrom word 0 (tokens abbr)

  def LettersMatch (word abbr : List U8) : Prop :=
    ∀ (k : Nat) (c : U8), k < abbr.length → byteAt abbr k = some c.val → isLower c →
      expandedBefore abbr k < word.length ∧ byteAt word (expandedBefore abbr k) = some c.val

  def IsNumeralWithValue (abbr : List U8) (n : Nat) : Prop :=
    ∃ d0 : U8, tokens abbr = [Token.num d0 n] ∧ d0.val ≠ 48

  /-- Whenever the function returns a result r, r = true if and only if abbr matches word as follows. Decompose abbr left to right into tokens: each lowercase byte (97..122) is a one-byte letter token, and each maximal non-empty contiguous run of digit bytes is one number token whose value n is the decimal value of that run. Start at p = 0 and process the tokens in order. For a letter token c, require p < len(word) and word[p] = c, then set p := p + 1. For a number token whose first byte is d0 and whose value is n, require d0 != 48, n > 0, p + n <= len(word), then set p := p + n. After all tokens are processed, require p = len(word). If all these requirements hold, r = true; otherwise r = false.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous run of bytes in abbr that are between 48 and 57 inclusive, interpreted as a decimal numeral, has value at most 2^31 - 1. -/
  theorem spec_1 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      (r = true ↔ MatchesAbbr word.val abbr.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), (r = true ↔ MatchesAbbr word.val abbr.val)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous run of bytes in abbr that are between 48 and 57 inclusive, interpreted as a decimal numeral, has value at most 2^31 - 1. -/
  theorem spec_2 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1)) :
      ∃ r, Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1)), ∃ r, Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1; and abbr contains at least one maximal non-empty contiguous run of digit bytes whose first byte is 48. -/
  theorem spec_3 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (h_leading_zero : HasLeadingZeroDigitRun abbr.val)
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (h_leading_zero : HasLeadingZeroDigitRun abbr.val)
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), r = false) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if len(word) = len(abbr) and for every i with 0 <= i < len(word), word[i] = abbr[i].
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), 97 <= abbr[i] <= 122; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_4 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_lower : ∀ (i : Nat) (hi : i < abbr.val.length), isLower (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      (r = true ↔ SameBytes word.val abbr.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_lower : ∀ (i : Nat) (hi : i < abbr.val.length), isLower (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), (r = true ↔ SameBytes word.val abbr.val)) := by
    sorry

  /-- Whenever the function returns a result r, let n be the decimal value of abbr, which is its single maximal digit run. Then r = true if and only if abbr[0] != 48 and n = len(word).
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), 48 <= abbr[i] <= 57; and the decimal value of abbr is at most 2^31 - 1. -/
  theorem spec_5 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_digits : ∀ (i : Nat) (hi : i < abbr.val.length), isDigit (abbr.val[i]'hi))
      (h_value_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
      (d0 : U8) (n : Nat) (h_single_run : tokens abbr.val = [Token.num d0 n]) :
      (r = true ↔ (d0.val ≠ 48 ∧ n = word.val.length)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_digits : ∀ (i : Nat) (hi : i < abbr.val.length), isDigit (abbr.val[i]'hi))
        (h_value_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
        (d0 : U8) (n : Nat) (h_single_run : tokens abbr.val = [Token.num d0 n]), (r = true ↔ (d0.val ≠ 48 ∧ n = word.val.length))) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then len(word) = L + sum_{d in D} value(d), where L is the number of lowercase bytes in abbr, D is the set of all maximal non-empty contiguous digit runs of abbr, and value(d) is the decimal value of d.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_6 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
      (h_true : r = true) :
      word.val.length = countLower abbr.val + digitRunValueSum abbr.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
        (h_true : r = true), word.val.length = countLower abbr.val + digitRunValueSum abbr.val) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every byte c of abbr with 97 <= c <= 122, if p(c) is the number of lowercase bytes of abbr occurring before this c plus the sum of the decimal values of all maximal digit runs of abbr that end before this c, then p(c) < len(word) and word[p(c)] = c.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_7 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
      (h_true : r = true) :
      LettersMatch word.val abbr.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
        (h_true : r = true), LettersMatch word.val abbr.val) := by
    sorry

  /-- Whenever the function returns a result r, if there is a prefix of abbr ending exactly after a token (after a lowercase byte or after a complete maximal digit run) whose expanded length is strictly greater than len(word), then r = false. The expanded length of such a prefix is the number of lowercase bytes in it plus the sum of the decimal values of the complete digit runs in it.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1; and every maximal non-empty contiguous digit run of abbr has first byte not 48. -/
  theorem spec_8 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (h_no_leading_zero : NoLeadingZeroDigitRun abbr.val)
      (h_prefix_overflows : ∃ (m : Nat), 0 < m ∧ m ≤ (tokens abbr.val).length ∧
        word.val.length < expandedAfterTokens abbr.val m)
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      r = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (h_no_leading_zero : NoLeadingZeroDigitRun abbr.val)
        (h_prefix_overflows : ∃ (m : Nat), 0 < m ∧ m ≤ (tokens abbr.val).length ∧
          word.val.length < expandedAfterTokens abbr.val m)
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), r = false) := by
    sorry

  /-- Whenever the function returns a result r for (word, abbr) and r = true, the following holds. Let d be any maximal non-empty contiguous digit run of abbr with decimal value n, and let p be the expanded length of the prefix of abbr that ends just before d (the number of lowercase bytes before d plus the sum of values of digit runs before d). Then for every k with 0 <= k < n and every byte b with 97 <= b <= 122, if word' is obtained from word by replacing word[p+k] with b, then whenever the function returns a result r' for (word', abbr), r' = true.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_9 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
      (h_true : r = true)
      (start : Nat) (d0 : U8) (n : Nat)
      (h_run : (start, Token.num d0 n) ∈ indexedTokens abbr.val)
      (k : Nat) (hk : k < n) (b : U8) (hb : isLower b)
      (word' : Slice U8)
      (h_word' : word'.val = word.val.set (expandedBefore abbr.val start + k) b)
      (r' : Bool) (hr' : Aegis.ValidWordAbbreviation.valid_word_abbreviation word' abbr = ok r') :
      r' = true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r)
        (h_true : r = true)
        (start : Nat) (d0 : U8) (n : Nat)
        (h_run : (start, Token.num d0 n) ∈ indexedTokens abbr.val)
        (k : Nat) (hk : k < n) (b : U8) (hb : isLower b)
        (word' : Slice U8)
        (h_word' : word'.val = word.val.set (expandedBefore abbr.val start + k) b)
        (r' : Bool) (hr' : Aegis.ValidWordAbbreviation.valid_word_abbreviation word' abbr = ok r'), r' = true) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1; every maximal non-empty contiguous digit run of abbr has first byte not 48; if L is the number of lowercase bytes in abbr and D is the set of maximal digit runs of abbr, then len(word) = L + sum_{d in D} value(d); and for every lowercase byte c of abbr, p(c) < len(word) and word[p(c)] = c, where p(c) is the number of lowercase bytes of abbr before c plus the sum of the decimal values of all maximal digit runs of abbr that end before c. -/
  theorem spec_10 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (h_no_leading_zero : NoLeadingZeroDigitRun abbr.val)
      (h_total_length : word.val.length = countLower abbr.val + digitRunValueSum abbr.val)
      (h_letters_match : LettersMatch word.val abbr.val) :
      ∃ r, Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r ∧ r = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (h_no_leading_zero : NoLeadingZeroDigitRun abbr.val)
        (h_total_length : word.val.length = countLower abbr.val + digitRunValueSum abbr.val)
        (h_letters_match : LettersMatch word.val abbr.val), ∃ r, Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r ∧ r = true) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if either (a) len(abbr) = 1 and abbr[0] = word[0], or (b) abbr is a valid decimal numeral with no leading zero whose value is 1.
    Preconditions: len(word) = 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_11 (word abbr : Slice U8)
      (h_word_len_eq : word.val.length = 1)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      (r = true ↔
        ((abbr.val.length = 1 ∧ byteAt abbr.val 0 = byteAt word.val 0) ∨
          IsNumeralWithValue abbr.val 1)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_eq : word.val.length = 1)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), (r = true ↔
          ((abbr.val.length = 1 ∧ byteAt abbr.val 0 = byteAt word.val 0) ∨
            IsNumeralWithValue abbr.val 1))) := by
    sorry

  /-- Whenever the function returns a result r, if the number of lowercase bytes in abbr is strictly greater than len(word), then r = false.
    Preconditions: len(word) >= 1; len(word) <= 20; for every i with 0 <= i < len(word), 97 <= word[i] <= 122; len(abbr) >= 1; len(abbr) <= 10; for every i with 0 <= i < len(abbr), either 97 <= abbr[i] <= 122 or 48 <= abbr[i] <= 57; and every maximal non-empty contiguous digit run in abbr has value at most 2^31 - 1. -/
  theorem spec_12 (word abbr : Slice U8)
      (h_word_len_ge : 1 ≤ word.val.length)
      (h_word_len_le : word.val.length ≤ 20)
      (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
      (h_abbr_len_ge : 1 ≤ abbr.val.length)
      (h_abbr_len_le : abbr.val.length ≤ 10)
      (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
        isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
      (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
      (h_too_many_letters : word.val.length < countLower abbr.val)
      (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r) :
      r = false := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word abbr : Slice U8)
        (h_word_len_ge : 1 ≤ word.val.length)
        (h_word_len_le : word.val.length ≤ 20)
        (h_word_lower : ∀ (i : Nat) (hi : i < word.val.length), isLower (word.val[i]'hi))
        (h_abbr_len_ge : 1 ≤ abbr.val.length)
        (h_abbr_len_le : abbr.val.length ≤ 10)
        (h_abbr_bytes : ∀ (i : Nat) (hi : i < abbr.val.length),
          isLower (abbr.val[i]'hi) ∨ isDigit (abbr.val[i]'hi))
        (h_runs_bounded : DigitRunsBounded abbr.val (2 ^ 31 - 1))
        (h_too_many_letters : word.val.length < countLower abbr.val)
        (r : Bool) (hr : Aegis.ValidWordAbbreviation.valid_word_abbreviation word abbr = ok r), r = false) := by
    sorry

  end AegisSpec.ValidWordAbbreviation
