import Aegis.CountOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountOfSubstrings.count_of_substrings`

LeetCode problem `count-of-substrings-containing-every-vowel-and-k-consonants-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountOfSubstrings

  namespace AegisSpec.CountOfSubstrings

  def vowelBytes : Finset ℕ := {97, 101, 105, 111, 117}

  def byteAt (word : Slice U8) (i : ℕ) : Option ℕ :=
    (word.val[i]?).map (fun b => b.val)

  def vowelAt (word : Slice U8) (i : ℕ) : Bool :=
    match byteAt word i with
    | some v => decide (v ∈ vowelBytes)
    | none => false

  def consonantAt (word : Slice U8) (i : ℕ) : Prop := vowelAt word i = false

  instance instDecidableConsonantAt (word : Slice U8) (i : ℕ) : Decidable (consonantAt word i) := by
    unfold consonantAt
    infer_instance

  def occursIn (word : Slice U8) (l t : ℕ) (v : ℕ) : Prop :=
    ∃ i, i ∈ Finset.Icc l t ∧ byteAt word i = some v

  def containsAllVowels (word : Slice U8) (l t : ℕ) : Prop :=
    ∀ v ∈ vowelBytes, occursIn word l t v

  def nonVowelCount (word : Slice U8) (l t : ℕ) : ℕ :=
    ((Finset.Icc l t).filter (fun i => consonantAt word i)).card

  def nonVowelCountAll (word : Slice U8) : ℕ :=
    ((Finset.range word.val.length).filter (fun i => consonantAt word i)).card

  def wordContainsAllVowels (word : Slice U8) : Prop :=
    ∀ v ∈ vowelBytes, ∃ i ∈ Finset.range word.val.length, byteAt word i = some v

  instance instDecidableOccursIn (word : Slice U8) (l t v : ℕ) : Decidable (occursIn word l t v) := by
    unfold occursIn
    infer_instance

  instance instDecidableContainsAllVowels (word : Slice U8) (l t : ℕ) :
      Decidable (containsAllVowels word l t) := by
    unfold containsAllVowels
    infer_instance

  instance instDecidableWordContainsAllVowels (word : Slice U8) :
      Decidable (wordContainsAllVowels word) := by
    unfold wordContainsAllVowels
    infer_instance

  def indexPairs (word : Slice U8) : Finset (ℕ × ℕ) :=
    (Finset.range word.val.length).product (Finset.range word.val.length)

  def goodPairCount (word : Slice U8) (k : ℤ) : ℕ :=
    ((indexPairs word).filter (fun p =>
      p.1 ≤ p.2 ∧ containsAllVowels word p.1 p.2 ∧ (nonVowelCount word p.1 p.2 : ℤ) = k)).card

  def kNonVowelPairCount (word : Slice U8) (k : ℤ) : ℕ :=
    ((indexPairs word).filter (fun p =>
      p.1 ≤ p.2 ∧ (nonVowelCount word p.1 p.2 : ℤ) = k)).card

  def allVowelPairCount (word : Slice U8) : ℕ :=
    ((indexPairs word).filter (fun p => p.1 ≤ p.2 ∧ containsAllVowels word p.1 p.2)).card

  def reverseSlice (word : Slice U8) : Slice U8 :=
    Slice.from word.val.reverse
      (by rw [List.length_reverse]; exact Slice.length_ineq word)

  /-- Whenever count_of_substrings(word, k) returns a result r, r equals the number of pairs (l, t) of integers such that 0 <= l <= t < len(word), the substring word[l..t] contains every byte in V at least once (for each v in V there exists i with l <= i <= t and word[i] = v), and the number of indices i with l <= i <= t and word[i] not in V is exactly k. Here word[l..t] denotes the nonempty contiguous substring from index l through index t inclusive.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}, the bytes for a,e,i,o,u. -/
  theorem spec_1
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r → r.val = (goodPairCount word k.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r → r.val = (goodPairCount word k.val : ℤ)) := by
    sorry

  /-- For every (word, k) satisfying the preconditions, count_of_substrings(word, k) returns a result r; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. -/
  theorem spec_2
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∃ r : I64, count_of_substrings word k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∃ r : I64, count_of_substrings word k = ok r) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, 0 <= r.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. -/
  theorem spec_3
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64, count_of_substrings word k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64, count_of_substrings word k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r <= len(word) * (len(word) + 1) / 2.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. -/
  theorem spec_4
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r →
          r.val ≤ (word.val.length : ℤ) * ((word.val.length : ℤ) + 1) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r →
            r.val ≤ (word.val.length : ℤ) * ((word.val.length : ℤ) + 1) / 2) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r = 0.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. There exists at least one byte v in V such that no index i with 0 <= i < len(word) has word[i] = v. -/
  theorem spec_5
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
      (hmissing : ∃ v ∈ vowelBytes, ∀ (i : ℕ) (b : U8), word.val[i]? = some b → b.val ≠ v) :
      ∀ r : I64, count_of_substrings word k = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
        (hmissing : ∃ v ∈ vowelBytes, ∀ (i : ℕ) (b : U8), word.val[i]? = some b → b.val ≠ v), ∀ r : I64, count_of_substrings word k = ok r → r.val = 0) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r >= 1.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. The whole word contains every byte in V at least once, and the number of indices i with 0 <= i < len(word) and word[i] not in V is exactly k. -/
  theorem spec_6
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
      (hwhole : wordContainsAllVowels word)
      (hk_count : (nonVowelCountAll word : ℤ) = k.val) :
      ∀ r : I64, count_of_substrings word k = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
        (hwhole : wordContainsAllVowels word)
        (hk_count : (nonVowelCountAll word : ℤ) = k.val), ∀ r : I64, count_of_substrings word k = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r = 1 if for every v in V there exists i with 0 <= i < 5 and word[i] = v, and r = 0 otherwise.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. Assume len(word) = 5 and k = 0. -/
  theorem spec_7
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
      (hlen : word.val.length = 5)
      (hk : k.val = 0) :
      ∀ r : I64,
        count_of_substrings word k = ok r →
          r.val = if containsAllVowels word 0 4 then (1 : ℤ) else 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
        (hlen : word.val.length = 5)
        (hk : k.val = 0), ∀ r : I64,
          count_of_substrings word k = ok r →
            r.val = if containsAllVowels word 0 4 then (1 : ℤ) else 0) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r = 1 if the whole word contains every byte in V at least once and the number of indices i with 0 <= i < len(word) and word[i] not in V is exactly k, and r = 0 otherwise.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. Assume k = len(word) - 5. -/
  theorem spec_8
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
      (hk : k.val = (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r →
          r.val = if wordContainsAllVowels word ∧ (nonVowelCountAll word : ℤ) = k.val
            then (1 : ℤ) else 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5)
        (hk : k.val = (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r →
            r.val = if wordContainsAllVowels word ∧ (nonVowelCountAll word : ℤ) = k.val
              then (1 : ℤ) else 0) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r <= (len(word) - (k + 5) + 1) * (len(word) - (k + 5) + 2) / 2.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. -/
  theorem spec_9
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r →
          r.val ≤ ((word.val.length : ℤ) - (k.val + 5) + 1)
            * ((word.val.length : ℤ) - (k.val + 5) + 2) / 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r →
            r.val ≤ ((word.val.length : ℤ) - (k.val + 5) + 1)
              * ((word.val.length : ℤ) - (k.val + 5) + 2) / 2) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r is at most the number of pairs (l, t) with 0 <= l <= t < len(word) for which the number of indices i with l <= i <= t and word[i] not in V is exactly k.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. -/
  theorem spec_10
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r → r.val ≤ (kNonVowelPairCount word k.val : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r → r.val ≤ (kNonVowelPairCount word k.val : ℤ)) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns a result r, r is at most the number of pairs (l, t) with 0 <= l <= t < len(word) for which word[l..t] contains every byte in V at least once.
    Preconditions: len(word) is an integer with 5 <= len(word) <= 200000; every byte word[i] for 0 <= i < len(word) is in the ASCII range 97..122 inclusive; k is an integer with 0 <= k <= len(word) - 5. Let V = {97,101,105,111,117}. -/
  theorem spec_11
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r : I64,
        count_of_substrings word k = ok r → r.val ≤ (allVowelPairCount word : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r : I64,
          count_of_substrings word k = ok r → r.val ≤ (allVowelPairCount word : ℤ)) := by
    sorry

  /-- Whenever count_of_substrings(word1, k) returns r1 and count_of_substrings(word2, k) returns r2, r1 = r2.
    Preconditions: For every pair of byte slices word1 and word2 and every integer k such that both (word1, k) and (word2, k) satisfy the problem constraints: 5 <= len(word1) <= 200000 and 5 <= len(word2) <= 200000; every byte word1[i] and word2[i] is in the ASCII range 97..122 inclusive; 0 <= k <= len(word1) - 5 and 0 <= k <= len(word2) - 5. Let V = {97,101,105,111,117}. Additionally, len(word1) = len(word2), and for every i with 0 <= i < len(word1), either word1[i] = word2[i] or both word1[i] and word2[i] are not in V. -/
  theorem spec_12
      (word1 word2 : Slice U8) (k : I64)
      (hlen1_lower : 5 ≤ word1.val.length)
      (hlen1_upper : word1.val.length ≤ 200000)
      (hlen2_lower : 5 ≤ word2.val.length)
      (hlen2_upper : word2.val.length ≤ 200000)
      (hbytes1 : ∀ (i : ℕ) (b : U8), word1.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hbytes2 : ∀ (i : ℕ) (b : U8), word2.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper1 : k.val ≤ (word1.val.length : ℤ) - 5)
      (hk_upper2 : k.val ≤ (word2.val.length : ℤ) - 5)
      (hlen_eq : word1.val.length = word2.val.length)
      (hsame : ∀ i, i < word1.val.length →
        word1.val[i]? = word2.val[i]? ∨ (consonantAt word1 i ∧ consonantAt word2 i)) :
      ∀ r1 r2 : I64,
        count_of_substrings word1 k = ok r1 →
        count_of_substrings word2 k = ok r2 → r1.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (word1 word2 : Slice U8) (k : I64)
        (hlen1_lower : 5 ≤ word1.val.length)
        (hlen1_upper : word1.val.length ≤ 200000)
        (hlen2_lower : 5 ≤ word2.val.length)
        (hlen2_upper : word2.val.length ≤ 200000)
        (hbytes1 : ∀ (i : ℕ) (b : U8), word1.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hbytes2 : ∀ (i : ℕ) (b : U8), word2.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper1 : k.val ≤ (word1.val.length : ℤ) - 5)
        (hk_upper2 : k.val ≤ (word2.val.length : ℤ) - 5)
        (hlen_eq : word1.val.length = word2.val.length)
        (hsame : ∀ i, i < word1.val.length →
          word1.val[i]? = word2.val[i]? ∨ (consonantAt word1 i ∧ consonantAt word2 i)), ∀ r1 r2 : I64,
          count_of_substrings word1 k = ok r1 →
          count_of_substrings word2 k = ok r2 → r1.val = r2.val) := by
    sorry

  /-- Whenever count_of_substrings(word, k) returns r and count_of_substrings(rev, k) returns r_rev, r = r_rev.
    Preconditions: For every word and k satisfying: 5 <= len(word) <= 200000; every byte word[i] is in the ASCII range 97..122 inclusive; 0 <= k <= len(word) - 5. Let n = len(word), and let rev be the byte slice of length n defined by rev[i] = word[n - 1 - i] for 0 <= i < n. -/
  theorem spec_13
      (word : Slice U8) (k : I64)
      (hlen_lower : 5 ≤ word.val.length)
      (hlen_upper : word.val.length ≤ 200000)
      (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
      (hk_lower : 0 ≤ k.val)
      (hk_upper : k.val ≤ (word.val.length : ℤ) - 5) :
      ∀ r r_rev : I64,
        count_of_substrings word k = ok r →
        count_of_substrings (reverseSlice word) k = ok r_rev → r.val = r_rev.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hlen_lower : 5 ≤ word.val.length)
        (hlen_upper : word.val.length ≤ 200000)
        (hbytes : ∀ (i : ℕ) (b : U8), word.val[i]? = some b → 97 ≤ b.val ∧ b.val ≤ 122)
        (hk_lower : 0 ≤ k.val)
        (hk_upper : k.val ≤ (word.val.length : ℤ) - 5), ∀ r r_rev : I64,
          count_of_substrings word k = ok r →
          count_of_substrings (reverseSlice word) k = ok r_rev → r.val = r_rev.val) := by
    sorry

  end AegisSpec.CountOfSubstrings
