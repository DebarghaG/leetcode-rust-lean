import Aegis.CountVowelSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountVowelSubstrings.count_vowel_substrings`

LeetCode problem `count-vowel-substrings-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountVowelSubstrings

def byteA : Nat := 97

def byteE : Nat := 101

def byteI : Nat := 105

def byteO : Nat := 111

def byteU : Nat := 117

def vowels : List Nat := [byteA, byteE, byteI, byteO, byteU]

abbrev IsVowelByte (b : Nat) : Prop :=
  b = byteA ∨ b = byteE ∨ b = byteI ∨ b = byteO ∨ b = byteU

abbrev IsLowercaseLetter (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

def bytesOf (word : Slice Std.U8) : List Nat := word.val.map (fun b => b.val)

def allVowelsB (l : List Nat) : Bool := l.all (fun b => decide (IsVowelByte b))

abbrev AllVowels (l : List Nat) : Prop := allVowelsB l = true

abbrev HasAllVowels (l : List Nat) : Prop :=
  byteA ∈ l ∧ byteE ∈ l ∧ byteI ∈ l ∧ byteO ∈ l ∧ byteU ∈ l

abbrev IsVowelPermutation (l : List Nat) : Prop := AllVowels l ∧ HasAllVowels l

def segment (l : List Nat) (i j : Nat) : List Nat := (l.drop i).take (j + 1 - i)

def byteAt (l : List Nat) (i : Nat) : Nat := l.getD i 0

abbrev IsVowelSegment (l : List Nat) (i j : Nat) : Prop :=
  AllVowels (segment l i j) ∧ HasAllVowels (segment l i j)

def indexPairs (lo hi : Nat) : List (Nat × Nat) :=
  ((List.range hi).filter (fun i => lo ≤ i)).flatMap
    (fun i => ((List.range hi).filter (fun j => i ≤ j)).map (fun j => (i, j)))

def countGoodPairsIn (l : List Nat) (lo hi : Nat) : Nat :=
  (indexPairs lo hi).countP (fun p : Nat × Nat => decide (IsVowelSegment l p.1 p.2))

def countGoodPairs (l : List Nat) : Nat := countGoodPairsIn l 0 l.length

abbrev IsMaxVowelBlock (l : List Nat) (lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi < l.length ∧ AllVowels (segment l lo hi) ∧
    (lo = 0 ∨ ¬ IsVowelByte (byteAt l (lo - 1))) ∧
    (hi + 1 = l.length ∨ ¬ IsVowelByte (byteAt l (hi + 1)))

def isMaxVowelBlockB (l : List Nat) (lo hi : Nat) : Bool :=
  decide (IsMaxVowelBlock l lo hi)

def maxVowelBlocks (l : List Nat) : List (Nat × Nat) :=
  (indexPairs 0 l.length).filter (fun p : Nat × Nat => isMaxVowelBlockB l p.1 p.2)

def sumOverBlocks (l : List Nat) : Nat :=
  (maxVowelBlocks l).foldr (fun p acc => countGoodPairsIn l p.1 (p.2 + 1) + acc) 0

def HasNoFullVowelBlock (l : List Nat) : Prop :=
  ∀ lo hi, IsMaxVowelBlock l lo hi → ¬ HasAllVowels (segment l lo hi)

/-- Whenever the function returns a result r, r is exactly the number of pairs of indices (i,j) such that 0 <= i <= j < len(word), every byte word[k] with i <= k <= j is one of the five vowel bytes 'a','e','i','o','u', and for each v in {'a','e','i','o','u'} there exists k with i <= k <= j and word[k] = v. Each index pair (i,j) is counted once, even if a different index pair gives the same substring text.
  Preconditions: 1 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_1 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (countGoodPairs (bytesOf word) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (countGoodPairs (bytesOf word) : Int)) := by
  sorry

/-- For every word satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_2 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b) :
    ∃ r : Std.I64, Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b), ∃ r : Std.I64, Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= ((len(word)-4)*(len(word)-3))/2.
  Preconditions: 5 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_3 (word : Slice Std.U8)
    (hlen_pos : 5 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val ≤ (((bytesOf word).length : Int) - 4) * (((bytesOf word).length : Int) - 3) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 5 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val ≤ (((bytesOf word).length : Int) - 4) * (((bytesOf word).length : Int) - 3) / 2) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(word) <= 4, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_4 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 4)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 4)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if the whole word consists of the five vowel bytes 'a','e','i','o','u' in some order (equivalently, every byte is a vowel and each of the five vowels occurs), and r = 0 otherwise.
  Preconditions: len(word) = 5 and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_5 (word : Slice Std.U8)
    (hlen : (bytesOf word).length = 5)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    (IsVowelPermutation (bytesOf word) → r.val = 1) ∧
      (¬ IsVowelPermutation (bytesOf word) → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen : (bytesOf word).length = 5)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), (IsVowelPermutation (bytesOf word) → r.val = 1) ∧
      (¬ IsVowelPermutation (bytesOf word) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = sum over all maximal contiguous vowel blocks [l,r] of the number of pairs (i,j) with l <= i <= j <= r such that the set {word[k] | i <= k <= j} contains all five vowels 'a','e','i','o','u'. A maximal contiguous vowel block is an interval [l,r] with 0 <= l <= r < len(word) such that every byte in it is a vowel, either l=0 or word[l-1] is not a vowel, and either r=len(word)-1 or word[r+1] is not a vowel.
  Preconditions: 1 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_6 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (sumOverBlocks (bytesOf word) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (sumOverBlocks (bytesOf word) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no maximal contiguous vowel block whose bytes include all five vowels 'a','e','i','o','u'. Here a maximal contiguous vowel block is an interval all of whose bytes are vowels and which is bordered by non-vowels or the ends of word.
  Preconditions: 1 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_7 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    (r.val = 0 ↔ HasNoFullVowelBlock (bytesOf word)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), (r.val = 0 ↔ HasNoFullVowelBlock (bytesOf word))) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: 1 <= len(word) <= 100, every byte of word is one of the five vowels 'a','e','i','o','u', and each of the five vowels occurs at least once in word. -/
theorem spec_8 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hvowels : IsVowelPermutation (bytesOf word))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hvowels : IsVowelPermutation (bytesOf word))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of pairs (i,j) with 0 <= i <= j < len(word)-1 such that every byte word[k] for i <= k <= j is a vowel and the set {word[k] | i <= k <= j} contains all five vowels 'a','e','i','o','u'. In other words, appending this final consonant does not change the count for the prefix word[0..len(word)-2].
  Preconditions: 1 <= len(word) <= 100, every byte of word is a lowercase English letter (ASCII 'a' through 'z'), and word[len(word)-1] is a consonant (a lowercase non-vowel letter). -/
theorem spec_9 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hlast : ¬ IsVowelByte (byteAt (bytesOf word) ((bytesOf word).length - 1)))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (countGoodPairsIn (bytesOf word) 0 ((bytesOf word).length - 1) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hlast : ¬ IsVowelByte (byteAt (bytesOf word) ((bytesOf word).length - 1)))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (countGoodPairsIn (bytesOf word) 0 ((bytesOf word).length - 1) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of pairs (i,j) with 1 <= i <= j < len(word) such that every byte word[k] for i <= k <= j is a vowel and the set {word[k] | i <= k <= j} contains all five vowels 'a','e','i','o','u'. In other words, prepending this first consonant does not change the count for the suffix word[1..len(word)-1], with indices shifted by one.
  Preconditions: 1 <= len(word) <= 100, every byte of word is a lowercase English letter (ASCII 'a' through 'z'), and word[0] is a consonant (a lowercase non-vowel letter). -/
theorem spec_10 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hfirst : ¬ IsVowelByte (byteAt (bytesOf word) 0))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (countGoodPairsIn (bytesOf word) 1 (bytesOf word).length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hfirst : ¬ IsVowelByte (byteAt (bytesOf word) 0))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (countGoodPairsIn (bytesOf word) 1 (bytesOf word).length : Int)) := by
  sorry

/-- Whenever the function returns a result r, if rev is the byte slice of length len(word) defined by rev[i] = word[len(word)-1-i] for every 0 <= i < len(word), then r equals the number of pairs (i,j) with 0 <= i <= j < len(word) such that every byte rev[k] for i <= k <= j is a vowel and the set {rev[k] | i <= k <= j} contains all five vowels 'a','e','i','o','u'.
  Preconditions: 1 <= len(word) <= 100, and every byte of word is a lowercase English letter (ASCII 'a' through 'z'). -/
theorem spec_11 (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (countGoodPairsIn (bytesOf word).reverse 0 (bytesOf word).length : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (countGoodPairsIn (bytesOf word).reverse 0 (bytesOf word).length : Int)) := by
  sorry

/-- Whenever the function returns a result r for word, the number of pairs (i,j) with 0 <= i <= j < len(word) such that every byte word2[k] for i <= k <= j is a vowel and the set {word2[k] | i <= k <= j} contains all five vowels 'a','e','i','o','u' is also r.
  Preconditions: 1 <= len(word) <= 100 and every byte of word is a lowercase English letter. Let word2 be any byte slice with len(word2)=len(word) such that for every i, if word[i] is a vowel ('a','e','i','o','u') then word2[i]=word[i], and if word[i] is not a vowel then word2[i] is a lowercase non-vowel English letter. -/
theorem spec_12 (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hlen2 : (bytesOf word2).length = (bytesOf word).length)
    (hvowel : ∀ i, i < (bytesOf word).length → IsVowelByte (byteAt (bytesOf word) i) →
      byteAt (bytesOf word2) i = byteAt (bytesOf word) i)
    (hnonvowel : ∀ i, i < (bytesOf word).length → ¬ IsVowelByte (byteAt (bytesOf word) i) →
      ¬ IsVowelByte (byteAt (bytesOf word2) i) ∧ IsLowercaseLetter (byteAt (bytesOf word2) i))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r) :
    r.val = (countGoodPairsIn (bytesOf word2) 0 (bytesOf word).length : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (word word2 : Slice Std.U8)
    (hlen_pos : 1 ≤ (bytesOf word).length)
    (hlen_le : (bytesOf word).length ≤ 100)
    (hlower : ∀ b ∈ bytesOf word, IsLowercaseLetter b)
    (hlen2 : (bytesOf word2).length = (bytesOf word).length)
    (hvowel : ∀ i, i < (bytesOf word).length → IsVowelByte (byteAt (bytesOf word) i) →
      byteAt (bytesOf word2) i = byteAt (bytesOf word) i)
    (hnonvowel : ∀ i, i < (bytesOf word).length → ¬ IsVowelByte (byteAt (bytesOf word) i) →
      ¬ IsVowelByte (byteAt (bytesOf word2) i) ∧ IsLowercaseLetter (byteAt (bytesOf word2) i))
    (r : Std.I64)
    (hres : Aegis.CountVowelSubstrings.count_vowel_substrings word = ok r), r.val = (countGoodPairsIn (bytesOf word2) 0 (bytesOf word).length : Int)) := by
  sorry

end AegisSpec.CountVowelSubstrings
