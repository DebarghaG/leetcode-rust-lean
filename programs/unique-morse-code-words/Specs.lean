import Aegis.UniqueMorseRepresentations.Code.Funs

/-!
# Specifications of `Aegis.UniqueMorseRepresentations.unique_morse_representations`

LeetCode problem `unique-morse-code-words`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.UniqueMorseRepresentations

  def morseTable : List (List Char) :=
    [['.', '-'],
     ['-', '.', '.', '.'],
     ['-', '.', '-', '.'],
     ['-', '.', '.'],
     ['.'],
     ['.', '.', '-', '.'],
     ['-', '-', '.'],
     ['.', '.', '.', '.'],
     ['.', '.'],
     ['.', '-', '-', '-'],
     ['-', '.', '-'],
     ['.', '-', '.', '.'],
     ['-', '-'],
     ['-', '.'],
     ['-', '-', '-'],
     ['.', '-', '-', '.'],
     ['-', '-', '.', '-'],
     ['.', '-', '.'],
     ['.', '.', '.'],
     ['-'],
     ['.', '.', '-'],
     ['.', '.', '.', '-'],
     ['.', '-', '-'],
     ['-', '.', '.', '-'],
     ['-', '.', '-', '-'],
     ['-', '-', '.', '.']]

  def morseCode (b : U8) : List Char := morseTable.getD (b.val - 97) []

  def morseTransform (w : alloc.vec.Vec U8) : List Char := (w.val.map morseCode).flatten

  def morseSet (words : List (alloc.vec.Vec U8)) : Finset (List Char) :=
    (words.map morseTransform).toFinset

  /-- Whenever the function returns a result r, r equals the cardinality of the set { T(words[i]) | 0 <= i < len(words) }, where T(w) is the concatenation of the standard Morse codes of the letters of w (the 26-letter table: a='.-', b='-...', c='-.-.', d='-..', e='.', f='..-.', g='--.', h='....', i='..', j='.---', k='-.-', l='.-..', m='--', n='-.', o='---', p='.--.', q='--.-', r='.-.', s='...', t='-', u='..-', v='...-', w='.--', x='-..-', y='-.--', z='--..'). Equivalently, if M is the 26-element array ['.-','-...','-.-.','-..','.','..-.','--.','....','..','.---','-.-','.-..','--','-.','---','.--.','--.-','.-.','...','-','..-','...-','.--','-..-','-.--','--..'] indexed from 0 for 'a' to 25 for 'z', then T(w) = M[w[0]-97] concatenated with M[w[1]-97] concatenated ... with M[w[len(w)-1]-97].
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122 (the byte is an ASCII lowercase letter 'a'..'z'). -/
  theorem spec_1
      (words : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (r : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r) :
      r.val = ((morseSet words.val).card : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (r : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r), r.val = ((morseSet words.val).card : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access memory out of bounds.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_2
      (words : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122) :
      ∃ r : I64, Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122), ∃ r : I64, Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= len(words).
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_3
      (words : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (r : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r) :
      1 ≤ r.val ∧ r.val ≤ (words.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (r : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r), 1 ≤ r.val ∧ r.val ≤ (words.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i and j with 0 <= i < len(words) and 0 <= j < len(words), T(words[i]) = T(words[j]), where T is the standard Morse transformation (a='.-', b='-...', c='-.-.', d='-..', e='.', f='..-.', g='--.', h='....', i='..', j='.---', k='-.-', l='.-..', m='--', n='-.', o='---', p='.--.', q='--.-', r='.-.', s='...', t='-', u='..-', v='...-', w='.--', x='-..-', y='-.--', z='--..').
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_4
      (words : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (r : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r) :
      (r.val = 1 ↔ ∀ (i : Nat) (_hi : i < words.val.length) (j : Nat)
        (_hj : j < words.val.length),
        morseTransform (words.val[i]'_hi) = morseTransform (words.val[j]'_hj)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (r : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r), (r.val = 1 ↔ ∀ (i : Nat) (_hi : i < words.val.length) (j : Nat)
          (_hj : j < words.val.length),
          morseTransform (words.val[i]'_hi) = morseTransform (words.val[j]'_hj))) := by
    sorry

  /-- Whenever the function returns a result r, r = len(words) if and only if for every i and j with 0 <= i < len(words), 0 <= j < len(words), and i != j, T(words[i]) != T(words[j]), where T is the standard Morse transformation (a='.-', b='-...', c='-.-.', d='-..', e='.', f='..-.', g='--.', h='....', i='..', j='.---', k='-.-', l='.-..', m='--', n='-.', o='---', p='.--.', q='--.-', r='.-.', s='...', t='-', u='..-', v='...-', w='.--', x='-..-', y='-.--', z='--..').
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_5
      (words : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (r : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r) :
      (r.val = (words.val.length : Int) ↔
        ∀ (i : Nat) (_hi : i < words.val.length) (j : Nat) (_hj : j < words.val.length),
          i ≠ j → morseTransform (words.val[i]'_hi) ≠ morseTransform (words.val[j]'_hj)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (r : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r), (r.val = (words.val.length : Int) ↔
          ∀ (i : Nat) (_hi : i < words.val.length) (j : Nat) (_hj : j < words.val.length),
            i ≠ j → morseTransform (words.val[i]'_hi) ≠ morseTransform (words.val[j]'_hj))) := by
    sorry

  /-- For every list words' satisfying the preconditions that is obtained from words by inserting one extra word w at any position (so len(words') = len(words) + 1 and deleting that inserted entry recovers words), if T(w) != T(words[i]) for every i with 0 <= i < len(words), where T is the standard Morse transformation (a='.-', b='-...', c='-.-.', d='-..', e='.', f='..-.', g='--.', h='....', i='..', j='.---', k='-.-', l='.-..', m='--', n='-.', o='---', p='.--.', q='--.-', r='.-.', s='...', t='-', u='..-', v='...-', w='.--', x='-..-', y='-.--', z='--..'), then whenever the function returns r on words and r' on words', r' = r + 1.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_6
      (words words' : Slice (alloc.vec.Vec U8))
      (k : Nat) (w : alloc.vec.Vec U8)
      (hk : k ≤ words.val.length)
      (hins : words'.val = words.val.take k ++ [w] ++ words.val.drop k)
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (hlen'_ge : 1 ≤ words'.val.length)
      (hlen'_le : words'.val.length ≤ 100)
      (hword'_ge : ∀ (i : Nat) (hi : i < words'.val.length),
        1 ≤ (words'.val[i]'hi).val.length)
      (hword'_le : ∀ (i : Nat) (hi : i < words'.val.length),
        (words'.val[i]'hi).val.length ≤ 12)
      (hbyte'_lower : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
        (hj : j < (words'.val[i]'hi).val.length),
        97 ≤ ((words'.val[i]'hi).val[j]'hj).val)
      (hbyte'_upper : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
        (hj : j < (words'.val[i]'hi).val.length),
        ((words'.val[i]'hi).val[j]'hj).val ≤ 122)
      (hnew : ∀ (i : Nat) (hi : i < words.val.length),
        morseTransform w ≠ morseTransform (words.val[i]'hi))
      (r r' : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r)
      (hr' : Aegis.UniqueMorseRepresentations.unique_morse_representations words' = .ok r') :
      r'.val = r.val + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec U8))
        (k : Nat) (w : alloc.vec.Vec U8)
        (hk : k ≤ words.val.length)
        (hins : words'.val = words.val.take k ++ [w] ++ words.val.drop k)
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (hlen'_ge : 1 ≤ words'.val.length)
        (hlen'_le : words'.val.length ≤ 100)
        (hword'_ge : ∀ (i : Nat) (hi : i < words'.val.length),
          1 ≤ (words'.val[i]'hi).val.length)
        (hword'_le : ∀ (i : Nat) (hi : i < words'.val.length),
          (words'.val[i]'hi).val.length ≤ 12)
        (hbyte'_lower : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
          (hj : j < (words'.val[i]'hi).val.length),
          97 ≤ ((words'.val[i]'hi).val[j]'hj).val)
        (hbyte'_upper : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
          (hj : j < (words'.val[i]'hi).val.length),
          ((words'.val[i]'hi).val[j]'hj).val ≤ 122)
        (hnew : ∀ (i : Nat) (hi : i < words.val.length),
          morseTransform w ≠ morseTransform (words.val[i]'hi))
        (r r' : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r)
        (hr' : Aegis.UniqueMorseRepresentations.unique_morse_representations words' = Result.ok r'), r'.val = r.val + 1) := by
    sorry

  /-- For every pair of inputs words and words' both satisfying the preconditions, if { T(words[i]) | 0 <= i < len(words) } = { T(words'[j]) | 0 <= j < len(words') } as sets of byte strings, where T is the standard Morse transformation (a='.-', b='-...', c='-.-.', d='-..', e='.', f='..-.', g='--.', h='....', i='..', j='.---', k='-.-', l='.-..', m='--', n='-.', o='---', p='.--.', q='--.-', r='.-.', s='...', t='-', u='..-', v='...-', w='.--', x='-..-', y='-.--', z='--..'), then whenever the function returns r on words and r' on words', r = r'.
    Preconditions: len(words) >= 1 and len(words) <= 100; for every i with 0 <= i < len(words), 1 <= len(words[i]) <= 12; for every i with 0 <= i < len(words) and every j with 0 <= j < len(words[i]), 97 <= words[i][j] <= 122. -/
  theorem spec_7
      (words words' : Slice (alloc.vec.Vec U8))
      (hlen_ge : 1 ≤ words.val.length)
      (hlen_le : words.val.length ≤ 100)
      (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
        1 ≤ (words.val[i]'hi).val.length)
      (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
        (words.val[i]'hi).val.length ≤ 12)
      (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        97 ≤ ((words.val[i]'hi).val[j]'hj).val)
      (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
        (hj : j < (words.val[i]'hi).val.length),
        ((words.val[i]'hi).val[j]'hj).val ≤ 122)
      (hlen'_ge : 1 ≤ words'.val.length)
      (hlen'_le : words'.val.length ≤ 100)
      (hword'_ge : ∀ (i : Nat) (hi : i < words'.val.length),
        1 ≤ (words'.val[i]'hi).val.length)
      (hword'_le : ∀ (i : Nat) (hi : i < words'.val.length),
        (words'.val[i]'hi).val.length ≤ 12)
      (hbyte'_lower : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
        (hj : j < (words'.val[i]'hi).val.length),
        97 ≤ ((words'.val[i]'hi).val[j]'hj).val)
      (hbyte'_upper : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
        (hj : j < (words'.val[i]'hi).val.length),
        ((words'.val[i]'hi).val[j]'hj).val ≤ 122)
      (hsets : morseSet words.val = morseSet words'.val)
      (r r' : I64)
      (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = .ok r)
      (hr' : Aegis.UniqueMorseRepresentations.unique_morse_representations words' = .ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words words' : Slice (alloc.vec.Vec U8))
        (hlen_ge : 1 ≤ words.val.length)
        (hlen_le : words.val.length ≤ 100)
        (hword_ge : ∀ (i : Nat) (hi : i < words.val.length),
          1 ≤ (words.val[i]'hi).val.length)
        (hword_le : ∀ (i : Nat) (hi : i < words.val.length),
          (words.val[i]'hi).val.length ≤ 12)
        (hbyte_lower : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          97 ≤ ((words.val[i]'hi).val[j]'hj).val)
        (hbyte_upper : ∀ (i : Nat) (hi : i < words.val.length) (j : Nat)
          (hj : j < (words.val[i]'hi).val.length),
          ((words.val[i]'hi).val[j]'hj).val ≤ 122)
        (hlen'_ge : 1 ≤ words'.val.length)
        (hlen'_le : words'.val.length ≤ 100)
        (hword'_ge : ∀ (i : Nat) (hi : i < words'.val.length),
          1 ≤ (words'.val[i]'hi).val.length)
        (hword'_le : ∀ (i : Nat) (hi : i < words'.val.length),
          (words'.val[i]'hi).val.length ≤ 12)
        (hbyte'_lower : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
          (hj : j < (words'.val[i]'hi).val.length),
          97 ≤ ((words'.val[i]'hi).val[j]'hj).val)
        (hbyte'_upper : ∀ (i : Nat) (hi : i < words'.val.length) (j : Nat)
          (hj : j < (words'.val[i]'hi).val.length),
          ((words'.val[i]'hi).val[j]'hj).val ≤ 122)
        (hsets : morseSet words.val = morseSet words'.val)
        (r r' : I64)
        (hr : Aegis.UniqueMorseRepresentations.unique_morse_representations words = Result.ok r)
        (hr' : Aegis.UniqueMorseRepresentations.unique_morse_representations words' = Result.ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.UniqueMorseRepresentations
