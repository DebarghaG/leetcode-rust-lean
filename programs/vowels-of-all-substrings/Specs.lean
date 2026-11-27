import Aegis.CountVowels.Code.Funs

/-!
# Specifications of `Aegis.CountVowels.count_vowels`

LeetCode problem `vowels-of-all-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountVowels

def IsLower (c : U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

def IsVowel (c : U8) : Prop :=
  c.val = 97 ∨ c.val = 101 ∨ c.val = 105 ∨ c.val = 111 ∨ c.val = 117

instance instDecidableIsVowel (c : U8) : Decidable (IsVowel c) := by
  unfold IsVowel
  infer_instance

def byteAt (l : List U8) (k : ℕ) : U8 := l.getD k default

def vowelAt (l : List U8) (k : ℕ) : ℕ := if IsVowel (byteAt l k) then 1 else 0

def substringVowelSum (l : List U8) : ℕ :=
  ∑ i ∈ Finset.range l.length,
    ∑ j ∈ (Finset.range l.length).filter (fun j => i ≤ j),
      ∑ k ∈ Finset.Icc i j, vowelAt l k

def weightedVowelSum (l : List U8) : ℕ :=
  ∑ k ∈ Finset.range l.length, vowelAt l k * (k + 1) * (l.length - k)

def totalVowelSumBound (n : ℕ) : ℕ := n * (n + 1) * (n + 2) / 6

/-- The function returns a result r, and the integer value represented by r is exactly Σ_{i=0}^{n-1} Σ_{j=i}^{n-1} Σ_{k=i}^{j} I(word[k] is a vowel), where I(P) = 1 if P holds and 0 otherwise. A byte is a vowel exactly when it is 97 ('a'), 101 ('e'), 105 ('i'), 111 ('o'), or 117 ('u'). Equivalently, this is the sum, over every non-empty contiguous substring word[i..j] with 0 <= i <= j < n, of the number of vowels in that substring.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= word[i] <= 122 (word[i] is a lowercase English letter). -/
theorem spec_1 (word : Slice U8)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c) :
    ∃ r : I64, Aegis.CountVowels.count_vowels word = ok r ∧
      r.val = (substringVowelSum word.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c), ∃ r : I64, Aegis.CountVowels.count_vowels word = ok r ∧
      r.val = (substringVowelSum word.val : ℤ)) := by
  sorry

/-- For every word satisfying the preconditions, count_vowels(word) returns a result r (it does not fail, panic, go out of bounds, or overflow the 64-bit result).
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter (97 <= word[i] <= 122 for 0 <= i < n). -/
theorem spec_2 (word : Slice U8)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c) :
    ∃ r : I64, Aegis.CountVowels.count_vowels word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c), ∃ r : I64, Aegis.CountVowels.count_vowels word = ok r) := by
  sorry

/-- Whenever count_vowels(word) returns a result r, the integer value represented by r is non-negative: 0 <= r.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. -/
theorem spec_3 (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever count_vowels(word) returns a result r, the integer value represented by r is at most n*(n+1)*(n+2)/6.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. -/
theorem spec_4 (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r) :
    r.val ≤ (totalVowelSumBound word.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r), r.val ≤ (totalVowelSumBound word.val.length : ℤ)) := by
  sorry

/-- Whenever count_vowels(word) returns a result r, the integer value represented by r equals Σ_{k=0}^{n-1} c_k*(k+1)*(n-k), where c_k = 1 if word[k] is a vowel ('a', 'e', 'i', 'o', or 'u'), and c_k = 0 otherwise.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. -/
theorem spec_5 (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r) :
    r.val = (weightedVowelSum word.val : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r), r.val = (weightedVowelSum word.val : ℤ)) := by
  sorry

/-- Whenever count_vowels(word) returns r and count_vowels(rev) returns r_rev, the integer values represented by r and r_rev are equal.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. Let rev be the byte array of length n defined by rev[i] = word[n-1-i] for 0 <= i < n. -/
theorem spec_6 (word rev : Slice U8) (r r_rev : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hrev : rev.val = word.val.reverse)
    (hres : Aegis.CountVowels.count_vowels word = ok r)
    (hres_rev : Aegis.CountVowels.count_vowels rev = ok r_rev) :
    r.val = r_rev.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word rev : Slice U8) (r r_rev : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hrev : rev.val = word.val.reverse)
    (hres : Aegis.CountVowels.count_vowels word = ok r)
    (hres_rev : Aegis.CountVowels.count_vowels rev = ok r_rev), r.val = r_rev.val) := by
  sorry

/-- Whenever count_vowels(word) returns r_word and count_vowels(v) returns r_v, the integer values represented by r_word and r_v are equal.
  Preconditions: Let n = len(word). 1 <= n <= 100000, and both word and v are byte slices of length n whose bytes are lowercase English letters. For every i with 0 <= i < n, word[i] is a vowel if and only if v[i] is a vowel. -/
theorem spec_7 (word v : Slice U8) (r_word r_v : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hlen : v.val.length = word.val.length)
    (hlower_v : ∀ c ∈ v.val, IsLower c)
    (hvowel : ∀ i, i < word.val.length → (IsVowel (byteAt word.val i) ↔ IsVowel (byteAt v.val i)))
    (hres_word : Aegis.CountVowels.count_vowels word = ok r_word)
    (hres_v : Aegis.CountVowels.count_vowels v = ok r_v) :
    r_word.val = r_v.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word v : Slice U8) (r_word r_v : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hlen : v.val.length = word.val.length)
    (hlower_v : ∀ c ∈ v.val, IsLower c)
    (hvowel : ∀ i, i < word.val.length → (IsVowel (byteAt word.val i) ↔ IsVowel (byteAt v.val i)))
    (hres_word : Aegis.CountVowels.count_vowels word = ok r_word)
    (hres_v : Aegis.CountVowels.count_vowels v = ok r_v), r_word.val = r_v.val) := by
  sorry

/-- Whenever count_vowels(word) returns r and count_vowels(word2) returns r2, the integer value represented by r2 equals the integer value represented by r plus (p+1)*(n-p).
  Preconditions: Let n = len(word). 1 <= n <= 100000, every byte of word is a lowercase English letter, and p is an index with 0 <= p < n such that word[p] is not a vowel. Let word2 be a byte slice of length n such that word2[p] is a vowel, word2[i] = word[i] for every i != p, and every byte of word2 is a lowercase English letter. -/
theorem spec_8 (word word2 : Slice U8) (p : ℕ) (r r2 : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hp : p < word.val.length)
    (hp_not_vowel : ¬ IsVowel (byteAt word.val p))
    (hlen2 : word2.val.length = word.val.length)
    (hlower2 : ∀ c ∈ word2.val, IsLower c)
    (hp2_vowel : IsVowel (byteAt word2.val p))
    (hagree : ∀ i, i < word.val.length → i ≠ p → byteAt word2.val i = byteAt word.val i)
    (hres : Aegis.CountVowels.count_vowels word = ok r)
    (hres2 : Aegis.CountVowels.count_vowels word2 = ok r2) :
    r2.val = r.val + ((p : ℤ) + 1) * ((word.val.length : ℤ) - (p : ℤ)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word word2 : Slice U8) (p : ℕ) (r r2 : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hp : p < word.val.length)
    (hp_not_vowel : ¬ IsVowel (byteAt word.val p))
    (hlen2 : word2.val.length = word.val.length)
    (hlower2 : ∀ c ∈ word2.val, IsLower c)
    (hp2_vowel : IsVowel (byteAt word2.val p))
    (hagree : ∀ i, i < word.val.length → i ≠ p → byteAt word2.val i = byteAt word.val i)
    (hres : Aegis.CountVowels.count_vowels word = ok r)
    (hres2 : Aegis.CountVowels.count_vowels word2 = ok r2), r2.val = r.val + ((p : ℤ) + 1) * ((word.val.length : ℤ) - (p : ℤ))) := by
  sorry

/-- Whenever count_vowels(word) returns a result r, the integer value represented by r equals n*(n+1)*(n+2)/6 if and only if every byte word[i] with 0 <= i < n is a vowel ('a', 'e', 'i', 'o', or 'u').
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. -/
theorem spec_9 (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r) :
    r.val = (totalVowelSumBound word.val.length : ℤ) ↔ ∀ c ∈ word.val, IsVowel c := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r), r.val = (totalVowelSumBound word.val.length : ℤ) ↔ ∀ c ∈ word.val, IsVowel c) := by
  sorry

/-- Whenever count_vowels(word) returns a result r, the integer value represented by r equals 0 if and only if every byte word[i] with 0 <= i < n is not a vowel ('a', 'e', 'i', 'o', or 'u').
  Preconditions: Let n = len(word). 1 <= n <= 100000, and every byte of word is a lowercase English letter. -/
theorem spec_10 (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r) :
    r.val = 0 ↔ ∀ c ∈ word.val, ¬ IsVowel c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice U8) (r : I64)
    (hne : 1 ≤ word.val.length) (hle : word.val.length ≤ 100000)
    (hlower : ∀ c ∈ word.val, IsLower c)
    (hres : Aegis.CountVowels.count_vowels word = ok r), r.val = 0 ↔ ∀ c ∈ word.val, ¬ IsVowel c) := by
  sorry

end AegisSpec.CountVowels
