import Aegis.IsPrefixOfWord.Code.Funs

/-!
# Specifications of `Aegis.IsPrefixOfWord.is_prefix_of_word`

LeetCode problem `check-if-a-word-occurs-as-a-prefix-of-any-word-in-a-sentence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsPrefixOfWord

def IsSpaceByte (b : Std.U8) : Prop := b.val = 32

def AllLower (s : List Std.U8) : Prop := ∀ b ∈ s, 97 ≤ b.val ∧ b.val ≤ 122

def AllLowerOrSpace (s : List Std.U8) : Prop :=
  ∀ b ∈ s, (97 ≤ b.val ∧ b.val ≤ 122) ∨ b.val = 32

def NoSpacingAnomalies (s : List Std.U8) : Prop :=
  (∀ b rest, s = b :: rest → ¬ IsSpaceByte b) ∧
  (∀ rest b, s = rest ++ [b] → ¬ IsSpaceByte b) ∧
  (∀ pre a b post, s = pre ++ a :: b :: post → ¬ (IsSpaceByte a ∧ IsSpaceByte b))

def wordsOfAux (cur : List Std.U8) : List Std.U8 → List (List Std.U8)
  | [] => [cur]
  | b :: bs =>
      if b.val = 32 then cur :: wordsOfAux [] bs else wordsOfAux (cur ++ [b]) bs

def wordsOf (s : List Std.U8) : List (List Std.U8) :=
  match s with
  | [] => []
  | _ :: _ => wordsOfAux [] s

def wordAt (ws : List (List Std.U8)) (j : Nat) : List Std.U8 := ws.getD (j - 1) []

def IsPrefix (searchWord w : List Std.U8) : Prop :=
  searchWord.length ≤ w.length ∧
    ∀ (t : Nat), t < searchWord.length → w[t]? = searchWord[t]?

def HasPrefixWord (ws : List (List Std.U8)) (searchWord : List Std.U8) : Prop :=
  ∃ j, 1 ≤ j ∧ j ≤ ws.length ∧ IsPrefix searchWord (wordAt ws j)

def IsSpaceAt (s : List Std.U8) (i : Nat) : Prop := ∃ b, s[i]? = some b ∧ IsSpaceByte b

/-- The function returns a result r and the following holds. If there exists an index j with 1 <= j <= m such that searchWord is a prefix of w_j, then r is the least such j, represented as an i64 (so 1 <= r <= m). If no such j exists, then r = -1.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_1
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∃ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r ∧
        ((∃ j, 1 ≤ j ∧ j ≤ (wordsOf sentence.val).length ∧
            IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) ∧
            r.val = (j : Int) ∧
            (∀ i, 1 ≤ i → i < j →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i))) ∨
          (r.val = -1 ∧
            (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∃ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r ∧
        ((∃ j, 1 ≤ j ∧ j ≤ (wordsOf sentence.val).length ∧
            IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) ∧
            r.val = (j : Int) ∧
            (∀ i, 1 ≤ i → i < j →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i))) ∨
          (r.val = -1 ∧
            (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j))))) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_2
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∃ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∃ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1, or 1 <= r <= m, where m is the number of words of sentence (equivalently m = 1 + the number of space bytes in sentence).
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_3
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((wordsOf sentence.val).length : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ ((wordsOf sentence.val).length : Int))) := by
  sorry

/-- Whenever the function returns a result r, r != -1 if and only if there exists j with 1 <= j <= m such that searchWord is a prefix of w_j.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_4
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        (r.val ≠ -1 ↔ HasPrefixWord (wordsOf sentence.val) searchWord.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        (r.val ≠ -1 ↔ HasPrefixWord (wordsOf sentence.val) searchWord.val)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, the word w_r exists (1 <= r <= m), len(searchWord) <= len(w_r), and for every t with 0 <= t < len(searchWord), w_r[t] = searchWord[t].
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_5
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val ≠ -1 →
        ∃ (j : Nat), r.val = (j : Int) ∧ 1 ≤ j ∧ j ≤ (wordsOf sentence.val).length ∧
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val ≠ -1 →
        ∃ (j : Nat), r.val = (j : Int) ∧ 1 ≤ j ∧ j ≤ (wordsOf sentence.val).length ∧
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every j with 1 <= j < r, searchWord is not a prefix of w_j.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_6
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val ≠ -1 →
        ∀ (j : Nat), 1 ≤ j → (j : Int) < r.val →
          ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val ≠ -1 →
        ∀ (j : Nat), 1 ≤ j → (j : Int) < r.val →
          ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j)) := by
  sorry

/-- Whenever the function returns r = -1, for every j with 1 <= j <= m, searchWord is not a prefix of w_j; equivalently, for every j with 1 <= j <= m, either len(searchWord) > len(w_j), or (len(searchWord) <= len(w_j) and there exists t with 0 <= t < len(searchWord) such that w_j[t] != searchWord[t]).
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_7
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val = -1 →
        ((∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j)) ∧
          (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            searchWord.val.length > (wordAt (wordsOf sentence.val) j).length ∨
              (searchWord.val.length ≤ (wordAt (wordsOf sentence.val) j).length ∧
                ∃ t, t < searchWord.val.length ∧
                  (wordAt (wordsOf sentence.val) j)[t]? ≠ searchWord.val[t]?))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r → r.val = -1 →
        ((∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j)) ∧
          (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            searchWord.val.length > (wordAt (wordsOf sentence.val) j).length ∨
              (searchWord.val.length ≤ (wordAt (wordsOf sentence.val) j).length ∧
                ∃ t, t < searchWord.val.length ∧
                  (wordAt (wordsOf sentence.val) j)[t]? ≠ searchWord.val[t]?)))) := by
  sorry

/-- Whenever the function returns a result r and searchWord is a prefix of w_1, then r = 1.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_8
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        IsPrefix searchWord.val (wordAt (wordsOf sentence.val) 1) → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        IsPrefix searchWord.val (wordAt (wordsOf sentence.val) 1) → r.val = 1) := by
  sorry

/-- Whenever the function returns a result r and len(searchWord) > len(w_j) for every j with 1 <= j <= m, then r = -1.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_9
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            searchWord.val.length > (wordAt (wordsOf sentence.val) j).length) →
          r.val = -1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        (∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
            searchWord.val.length > (wordAt (wordsOf sentence.val) j).length) →
          r.val = -1) := by
  sorry

/-- Whenever the function returns a result r and there is exactly one index j with 1 <= j <= m for which searchWord is a prefix of w_j, then r = j.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_10
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ (j : Nat), 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) →
            (∀ (i : Nat), 1 ≤ i → i ≤ (wordsOf sentence.val).length →
              IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i) → i = j) →
              r.val = (j : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ (j : Nat), 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) →
            (∀ (i : Nat), 1 ≤ i → i ≤ (wordsOf sentence.val).length →
              IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i) → i = j) →
              r.val = (j : Int)) := by
  sorry

/-- Whenever the function returns a result r, if there is an index j with 1 <= j <= m such that w_j = searchWord byte-for-byte and searchWord is not a prefix of any w_i with 1 <= i < j, then r = j.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_11
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          wordAt (wordsOf sentence.val) j = searchWord.val →
            (∀ i, 1 ≤ i → i < j →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i)) →
              r.val = (j : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          wordAt (wordsOf sentence.val) j = searchWord.val →
            (∀ i, 1 ≤ i → i < j →
              ¬ IsPrefix searchWord.val (wordAt (wordsOf sentence.val) i)) →
              r.val = (j : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 1 <= j <= m, if searchWord is a prefix of w_j, then r != -1 and r <= j.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_12
    (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length) :
    ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) →
            r.val ≠ -1 ∧ r.val ≤ (j : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sentence searchWord : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length), ∀ r : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
          IsPrefix searchWord.val (wordAt (wordsOf sentence.val) j) →
            r.val ≠ -1 ∧ r.val ≤ (j : Int)) := by
  sorry

/-- Let sentence' be any byte array that also satisfies the same preconditions with the same searchWord and has the same length and the same set of space positions as sentence; let v_1, ..., v_m be its words. Suppose that for every j with 1 <= j <= m and every t with 0 <= t < min(len(searchWord), len(w_j)), v_j[t] = w_j[t]. Then whenever is_prefix_of_word(sentence, searchWord) returns r and is_prefix_of_word(sentence', searchWord) returns r', we have r = r'.
  Preconditions: len(sentence) is between 1 and 100 inclusive; len(searchWord) is between 1 and 10 inclusive; every byte of searchWord is an ASCII lowercase letter (97..122); sentence has no leading space, no trailing space, and no two consecutive spaces, and every byte of sentence is either an ASCII lowercase letter (97..122) or a space (32). Splitting sentence at its spaces gives the nonempty list of nonempty words w_1, ..., w_m in order, with m >= 1. For a word w, say searchWord is a prefix of w when len(searchWord) <= len(w) and w[t] = searchWord[t] for every t with 0 <= t < len(searchWord). Byte positions inside words are 0-based; word indices are 1-based. -/
theorem spec_13
    (sentence searchWord sentence' : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length)
    (h_sentence'_len : 1 ≤ sentence'.val.length ∧ sentence'.val.length ≤ 100)
    (h_sentence'_lower_or_space : AllLowerOrSpace sentence'.val)
    (h_sentence'_spacing : NoSpacingAnomalies sentence'.val)
    (h_sentence'_words_nonempty : 1 ≤ (wordsOf sentence'.val).length)
    (h_same_length : sentence'.val.length = sentence.val.length)
    (h_same_spaces : ∀ i, i < sentence.val.length →
      (IsSpaceAt sentence.val i ↔ IsSpaceAt sentence'.val i))
    (h_same_word_prefixes :
      ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
        ∀ t, t < min searchWord.val.length (wordAt (wordsOf sentence.val) j).length →
          (wordAt (wordsOf sentence'.val) j)[t]? = (wordAt (wordsOf sentence.val) j)[t]?) :
    ∀ r r' : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        Aegis.IsPrefixOfWord.is_prefix_of_word sentence' searchWord = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (sentence searchWord sentence' : Slice Std.U8)
    (h_sentence_len : 1 ≤ sentence.val.length ∧ sentence.val.length ≤ 100)
    (h_searchWord_len : 1 ≤ searchWord.val.length ∧ searchWord.val.length ≤ 10)
    (h_searchWord_lower : AllLower searchWord.val)
    (h_sentence_lower_or_space : AllLowerOrSpace sentence.val)
    (h_sentence_spacing : NoSpacingAnomalies sentence.val)
    (h_words_nonempty : 1 ≤ (wordsOf sentence.val).length)
    (h_sentence'_len : 1 ≤ sentence'.val.length ∧ sentence'.val.length ≤ 100)
    (h_sentence'_lower_or_space : AllLowerOrSpace sentence'.val)
    (h_sentence'_spacing : NoSpacingAnomalies sentence'.val)
    (h_sentence'_words_nonempty : 1 ≤ (wordsOf sentence'.val).length)
    (h_same_length : sentence'.val.length = sentence.val.length)
    (h_same_spaces : ∀ i, i < sentence.val.length →
      (IsSpaceAt sentence.val i ↔ IsSpaceAt sentence'.val i))
    (h_same_word_prefixes :
      ∀ j, 1 ≤ j → j ≤ (wordsOf sentence.val).length →
        ∀ t, t < min searchWord.val.length (wordAt (wordsOf sentence.val) j).length →
          (wordAt (wordsOf sentence'.val) j)[t]? = (wordAt (wordsOf sentence.val) j)[t]?), ∀ r r' : Std.I64,
      Aegis.IsPrefixOfWord.is_prefix_of_word sentence searchWord = ok r →
        Aegis.IsPrefixOfWord.is_prefix_of_word sentence' searchWord = ok r' → r = r') := by
  sorry

end AegisSpec.IsPrefixOfWord
