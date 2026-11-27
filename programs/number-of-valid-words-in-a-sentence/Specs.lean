import Aegis.CountValidWords.Code.Funs

/-!
# Specifications of `Aegis.CountValidWords.count_valid_words`

LeetCode problem `number-of-valid-words-in-a-sentence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountValidWords

namespace AegisSpec.CountValidWords

abbrev IsLower (c : ℕ) : Prop := 97 ≤ c ∧ c ≤ 122

abbrev IsDigit (c : ℕ) : Prop := 48 ≤ c ∧ c ≤ 57

abbrev IsHyphen (c : ℕ) : Prop := c = 45

abbrev IsPunct (c : ℕ) : Prop := c = 33 ∨ c = 44 ∨ c = 46

abbrev IsSpace (c : ℕ) : Prop := c = 32

abbrev InAlphabet (c : ℕ) : Prop := IsLower c ∨ IsDigit c ∨ IsSpace c ∨ IsHyphen c ∨ IsPunct c

def bytes (sentence : Slice Std.U8) : List ℕ := sentence.val.map (fun c => c.val)

def LengthOK (sentence : Slice Std.U8) : Prop :=
  1 ≤ (bytes sentence).length ∧ (bytes sentence).length ≤ 1000

def AlphabetOK (sentence : Slice Std.U8) : Prop := ∀ c ∈ bytes sentence, InAlphabet c

def HasToken (sentence : Slice Std.U8) : Prop := ∃ c ∈ bytes sentence, c ≠ 32

def NoSpaceByte (sentence : Slice Std.U8) : Prop := ∀ c ∈ bytes sentence, c ≠ 32

def SentenceOK (sentence : Slice Std.U8) : Prop :=
  LengthOK sentence ∧ AlphabetOK sentence ∧ HasToken sentence

def tokensAux : List ℕ → List ℕ → List (List ℕ)
  | cur, [] => if cur.isEmpty then [] else [cur.reverse]
  | cur, c :: rest =>
      if c = 32 then
        (if cur.isEmpty then [] else [cur.reverse]) ++ tokensAux [] rest
      else tokensAux (c :: cur) rest

def tokens (l : List ℕ) : List (List ℕ) := tokensAux [] l

def numTokens (l : List ℕ) : ℕ := (tokens l).length

def hyphenCount (t : List ℕ) : ℕ := List.countP (fun c => decide (c = 45)) t

def punctCount (t : List ℕ) : ℕ := List.countP (fun c => decide (c = 33 ∨ c = 44 ∨ c = 46)) t

abbrev OnlyWordBytes (t : List ℕ) : Prop :=
  ∀ (j : ℕ) (_hj : j < t.length), IsLower t[j] ∨ IsHyphen t[j] ∨ IsPunct t[j]

abbrev HyphenOK (t : List ℕ) : Prop :=
  hyphenCount t ≤ 1 ∧
    (∀ (j : ℕ) (_hj : j < t.length), t[j] = 45 → 0 < j ∧ j + 1 < t.length) ∧
    (∀ (j : ℕ) (_hj : j < t.length) (_hj1 : j + 1 < t.length), t[j] = 45 →
      IsLower t[j - 1] ∧ IsLower t[j + 1])

abbrev PunctOK (t : List ℕ) : Prop :=
  punctCount t ≤ 1 ∧
    (∀ (j : ℕ) (_hj : j < t.length), IsPunct t[j] → j = t.length - 1)

abbrev IsValidToken (t : List ℕ) : Prop := OnlyWordBytes t ∧ HyphenOK t ∧ PunctOK t

def numValidTokens (l : List ℕ) : ℕ := List.countP (fun t => decide (IsValidToken t)) (tokens l)

/-- Let a token of sentence be a maximal nonempty interval of indices [a,b) with 0 <= a < b <= len(sentence) such that sentence[a..b) contains no 32, and (a=0 or sentence[a-1]=32) and (b=len(sentence) or sentence[b]=32). For a token t = sentence[a..b), let m=b-a. Call t valid iff: (1) every byte t[j] (0 <= j < m) is a lowercase letter (97 <= t[j] <= 122), a hyphen (t[j]=45), or a punctuation mark (t[j] in {33,44,46}); under the input alphabet this is equivalent to containing no digit; (2) the set H={j | 0 <= j < m and t[j]=45} has size at most 1, and if H={j} then 0 < j < m-1 and both t[j-1] and t[j+1] are in 97..122; (3) the set P={j | 0 <= j < m and t[j] in {33,44,46}} has size at most 1, and if P={j} then j=m-1. The function returns a result r and r equals the number of valid tokens of sentence.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122 (lowercase letters), 48..57 (digits), 32 (space), 45 (hyphen), 33 ('!'), 44 (','), or 46 ('.'); and sentence contains at least one byte different from 32 (at least one token). -/
theorem spec_1 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence) :
    ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧ r.val = (numValidTokens (bytes sentence) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence), ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧ r.val = (numValidTokens (bytes sentence) : ℤ)) := by
  sorry

/-- The function returns a result r and does not fail (no overflow, panic, or out-of-bounds access) for every sentence satisfying the preconditions.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122, 48..57, 32, 45, 33, 44, 46; and sentence contains at least one non-space byte. -/
theorem spec_2 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence) :
    ∃ r : Std.I64, count_valid_words sentence = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence), ∃ r : Std.I64, count_valid_words sentence = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= N, where N is the number of tokens of sentence, i.e. the number of maximal nonempty non-space blocks defined as in spec_1.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122, 48..57, 32, 45, 33, 44, 46; and sentence contains at least one non-space byte. -/
theorem spec_3 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence) :
    ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (numTokens (bytes sentence) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence), ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (numTokens (bytes sentence) : ℤ)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if no token of sentence is valid, where a token is a maximal nonempty non-space block and is valid exactly when it contains no digit, has at most one hyphen with any hyphen between two lowercase letters, and has at most one punctuation mark from {33,44,46} with any such mark at the token's last byte.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122, 48..57, 32, 45, 33, 44, 46; and sentence contains at least one non-space byte. -/
theorem spec_4 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence) :
    ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (r.val = 0 ↔ ∀ t ∈ tokens (bytes sentence), ¬ IsValidToken t) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence), ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (r.val = 0 ↔ ∀ t ∈ tokens (bytes sentence), ¬ IsValidToken t)) := by
  sorry

/-- Let N be the number of tokens of sentence. The function returns a result r and r = N if and only if every token of sentence is valid, where validity is: no digit byte, at most one hyphen and any hyphen is surrounded by lowercase letters, at most one punctuation mark from {33,44,46} and any such mark is at the token's last byte.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122, 48..57, 32, 45, 33, 44, 46; and sentence contains at least one non-space byte. -/
theorem spec_5 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence) :
    ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (r.val = (numTokens (bytes sentence) : ℤ) ↔ ∀ t ∈ tokens (bytes sentence), IsValidToken t) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence), ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (r.val = (numTokens (bytes sentence) : ℤ) ↔ ∀ t ∈ tokens (bytes sentence), IsValidToken t)) := by
  sorry

/-- The function returns a result r and r = 1 exactly when the whole sentence, viewed as the unique token, is valid (no digit byte; at most one hyphen with lowercase neighbors; at most one punctuation mark from {33,44,46} at the last byte); otherwise r = 0.
  Preconditions: 1 <= len(sentence) <= 1000; each byte of sentence is one of the ASCII codes 97..122, 48..57, 32, 45, 33, 44, 46; sentence contains at least one non-space byte; and sentence contains no byte equal to 32. -/
theorem spec_6 (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence)
    (h_no_space : NoSpaceByte sentence) :
    ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (IsValidToken (bytes sentence) → r.val = 1) ∧
        (¬ IsValidToken (bytes sentence) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence)
    (h_no_space : NoSpaceByte sentence), ∃ r : Std.I64,
      count_valid_words sentence = ok r ∧
        (IsValidToken (bytes sentence) → r.val = 1) ∧
        (¬ IsValidToken (bytes sentence) → r.val = 0)) := by
  sorry

/-- The function returns a result r on sentence and a result r' on sentence'; then r = r'.
  Preconditions: sentence and sentence' are byte sequences each satisfying: 1 <= len <= 1000; every byte is one of 97..122, 48..57, 32, 45, 33, 44, 46; and each contains at least one byte different from 32. Further, sentence' has the same sequence of maximal nonempty non-space tokens as sentence, with consecutive tokens separated by nonempty runs of 32 and arbitrary (possibly empty) leading and trailing runs of 32. -/
theorem spec_7 (sentence sentence' : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence)
    (h_len' : LengthOK sentence') (h_alphabet' : AlphabetOK sentence')
    (h_token' : HasToken sentence')
    (h_same_tokens : tokens (bytes sentence') = tokens (bytes sentence)) :
    ∃ r r' : Std.I64, count_valid_words sentence = ok r ∧ count_valid_words sentence' = ok r' ∧
      r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence sentence' : Slice Std.U8)
    (h_len : LengthOK sentence) (h_alphabet : AlphabetOK sentence) (h_token : HasToken sentence)
    (h_len' : LengthOK sentence') (h_alphabet' : AlphabetOK sentence')
    (h_token' : HasToken sentence')
    (h_same_tokens : tokens (bytes sentence') = tokens (bytes sentence)), ∃ r r' : Std.I64, count_valid_words sentence = ok r ∧ count_valid_words sentence' = ok r' ∧
      r = r') := by
  sorry

/-- If the function returns r on sentence and r' on sentence', then r' = r + 1.
  Preconditions: sentence satisfies the global constraints of spec_1; t is a nonempty byte sequence with no 32 byte that is a valid token (no digit; at most one hyphen with lowercase neighbors; at most one punctuation mark from {33,44,46} at the last byte); sentence' is obtained by appending to sentence a 32 byte followed by t; and sentence' satisfies the global constraints of spec_1. -/
theorem spec_8 (sentence sentence' t : Slice Std.U8)
    (h_sentence : SentenceOK sentence)
    (h_t_nonempty : t.val ≠ [])
    (h_t_no_space : ∀ c ∈ t.val, c.val ≠ 32)
    (h_t_valid : IsValidToken (bytes t))
    (h_append : bytes sentence' = bytes sentence ++ 32 :: bytes t)
    (h_sentence' : SentenceOK sentence') :
    ∀ r r' : Std.I64,
      count_valid_words sentence = ok r → count_valid_words sentence' = ok r' → r'.val = r.val + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence sentence' t : Slice Std.U8)
    (h_sentence : SentenceOK sentence)
    (h_t_nonempty : t.val ≠ [])
    (h_t_no_space : ∀ c ∈ t.val, c.val ≠ 32)
    (h_t_valid : IsValidToken (bytes t))
    (h_append : bytes sentence' = bytes sentence ++ 32 :: bytes t)
    (h_sentence' : SentenceOK sentence'), ∀ r r' : Std.I64,
      count_valid_words sentence = ok r → count_valid_words sentence' = ok r' → r'.val = r.val + 1) := by
  sorry

/-- If the function returns r on sentence and r' on sentence', then r' = r.
  Preconditions: sentence satisfies the global constraints of spec_1; t is a nonempty byte sequence with no 32 byte that is not a valid token (it contains a digit, or has two or more hyphens, or has a hyphen not surrounded by lowercase letters, or has two or more punctuation marks from {33,44,46}, or has a punctuation mark not at the last byte); sentence' is obtained by appending to sentence a 32 byte followed by t; and sentence' satisfies the global constraints of spec_1. -/
theorem spec_9 (sentence sentence' t : Slice Std.U8)
    (h_sentence : SentenceOK sentence)
    (h_t_nonempty : t.val ≠ [])
    (h_t_no_space : ∀ c ∈ t.val, c.val ≠ 32)
    (h_t_invalid : ¬ IsValidToken (bytes t))
    (h_append : bytes sentence' = bytes sentence ++ 32 :: bytes t)
    (h_sentence' : SentenceOK sentence') :
    ∀ r r' : Std.I64,
      count_valid_words sentence = ok r → count_valid_words sentence' = ok r' → r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence sentence' t : Slice Std.U8)
    (h_sentence : SentenceOK sentence)
    (h_t_nonempty : t.val ≠ [])
    (h_t_no_space : ∀ c ∈ t.val, c.val ≠ 32)
    (h_t_invalid : ¬ IsValidToken (bytes t))
    (h_append : bytes sentence' = bytes sentence ++ 32 :: bytes t)
    (h_sentence' : SentenceOK sentence'), ∀ r r' : Std.I64,
      count_valid_words sentence = ok r → count_valid_words sentence' = ok r' → r'.val = r.val) := by
  sorry

end AegisSpec.CountValidWords
