import Aegis.CountOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountOfSubstrings.count_of_substrings`

LeetCode problem `count-of-substrings-containing-every-vowel-and-k-consonants-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountOfSubstrings

open Aegis.CountOfSubstrings

def letters (word : Slice U8) : List Nat := word.val.map (fun b => b.val)

def vowels : List Nat := [97, 101, 105, 111, 117]

def isVowelCode (c : Nat) : Bool :=
  c == 97 || c == 101 || c == 105 || c == 111 || c == 117

def IsVowel (c : Nat) : Prop := isVowelCode c = true

def IsLowerLetter (c : Nat) : Prop := 97 ≤ c ∧ c ≤ 122

def ContainsAllVowels (l : List Nat) : Prop := ∀ c ∈ vowels, c ∈ l

def EachVowelExactlyOnce (l : List Nat) : Prop := ∀ c ∈ vowels, l.count c = 1

def consonantCount (l : List Nat) : Nat := l.countP (fun c => !isVowelCode c)

def codeAt (word : Slice U8) (p : Nat) : Option Nat := (letters word)[p]?

def IsVowelAt (word : Slice U8) (p : Nat) : Prop :=
  ∃ c, codeAt word p = some c ∧ IsVowel c

def consonantAt (word : Slice U8) (p : Nat) : Bool :=
  match codeAt word p with
  | none => false
  | some c => !isVowelCode c

def intervalContent (word : Slice U8) (i j : Nat) : List Nat :=
  ((letters word).drop i).take (j + 1 - i)

def validIntervalB (word : Slice U8) (k : Nat) (i j : Nat) : Bool :=
  decide (i ≤ j) && decide (j < (letters word).length) &&
    (vowels.all fun c => (intervalContent word i j).contains c) &&
    (consonantCount (intervalContent word i j) == k)

def IsValidInterval (word : Slice U8) (k : Nat) (i j : Nat) : Prop :=
  validIntervalB word k i j = true

def allConsonantsIntervalB (word : Slice U8) (i j : Nat) : Bool :=
  decide (i ≤ j) && decide (j < (letters word).length) &&
    (vowels.all fun c => (intervalContent word i j).contains c) &&
    ((List.range (letters word).length).all fun p =>
      !consonantAt word p || (decide (i ≤ p) && decide (p ≤ j)))

def IsAllConsonantsInterval (word : Slice U8) (i j : Nat) : Prop :=
  allConsonantsIntervalB word i j = true

def countPairs (n : Nat) (test : Nat → Nat → Bool) : Nat :=
  ((List.range n).product (List.range n)).countP (fun q => test q.1 q.2)

def countValidIntervals (word : Slice U8) (k : Nat) : Nat :=
  countPairs (letters word).length fun i j => validIntervalB word k i j

def countAllConsonantsIntervals (word : Slice U8) : Nat :=
  countPairs (letters word).length fun i j => allConsonantsIntervalB word i j

def SameVowelPattern (word word2 : Slice U8) : Prop :=
  (letters word2).length = (letters word).length ∧
    ∀ i, i < (letters word).length → ∀ c, codeAt word i = some c →
      (IsVowel c → codeAt word2 i = some c) ∧
        (¬ IsVowel c → ∀ c2, codeAt word2 i = some c2 → ¬ IsVowel c2)

/-- Let V = {'a','e','i','o','u'}. For an interval [i,j] with 0 <= i <= j < n, call it valid when (1) for every v in V there exists p with i <= p <= j and word[p] = v, and (2) the number of p with i <= p <= j and word[p] not in V is exactly k. The function returns a result r such that r is the number of valid intervals [i,j]. Substrings are non-empty, contiguous, and identified by 0-based inclusive endpoints; the empty substring is not counted.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter (a byte with ASCII code between 'a' and 'z'). 0 <= k <= n - 5, treating the I64 parameter k as the mathematical integer it denotes. -/
theorem spec_1 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5) :
    ∃ r : I64,
      count_of_substrings word k = ok r ∧
        r.val = (countValidIntervals word k.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5), ∃ r : I64,
      count_of_substrings word k = ok r ∧
        r.val = (countValidIntervals word k.val.toNat : Int)) := by
  sorry

/-- For every word and k satisfying the preconditions, the function does not fail: it returns a result r and does not overflow, index out of bounds, or panic.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. -/
theorem spec_2 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5) :
    ∃ r : I64, count_of_substrings word k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5), ∃ r : I64, count_of_substrings word k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= ((n - k - 4) * (n - k - 3)) / 2, where n = len(word). The right-hand side is the number of substrings of length at least k+5.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. -/
theorem spec_3 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5) :
    ∀ r : I64,
      count_of_substrings word k = ok r →
        0 ≤ r.val ∧
          r.val ≤
            ((word.val.length : Int) - k.val - 4) * ((word.val.length : Int) - k.val - 3) /
              2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5), ∀ r : I64,
      count_of_substrings word k = ok r →
        0 ≤ r.val ∧
          r.val ≤
            ((word.val.length : Int) - k.val - 4) * ((word.val.length : Int) - k.val - 3) /
              2) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there are no indices i,j with 0 <= i <= j < n such that word[i..j] contains each of the five vowels 'a','e','i','o','u' at least once and contains exactly k consonant bytes (bytes not in {'a','e','i','o','u'}).
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. -/
theorem spec_4 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5) :
    ∀ r : I64,
      count_of_substrings word k = ok r →
        (r.val = 0 ↔ ¬ ∃ i j : Nat, IsValidInterval word k.val.toNat i j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5), ∀ r : I64,
      count_of_substrings word k = ok r →
        (r.val = 0 ↔ ¬ ∃ i j : Nat, IsValidInterval word k.val.toNat i j)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if the whole word contains each of the five vowels 'a','e','i','o','u' exactly once, and r = 0 otherwise. Equivalently, r = 1 iff word[0..n-1] has exactly n-5 consonant bytes and contains every vowel at least once.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. k = n - 5. -/
theorem spec_5 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk : k.val = (word.val.length : Int) - 5) :
    ∀ r : I64,
      count_of_substrings word k = ok r →
        (EachVowelExactlyOnce (letters word) → r.val = 1) ∧
          (¬ EachVowelExactlyOnce (letters word) → r.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk : k.val = (word.val.length : Int) - 5), ∀ r : I64,
      count_of_substrings word k = ok r →
        (EachVowelExactlyOnce (letters word) → r.val = 1) ∧
          (¬ EachVowelExactlyOnce (letters word) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. There exists v in {'a','e','i','o','u'} such that word[i] != v for every 0 <= i < n. -/
theorem spec_6 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hmiss : ∃ v ∈ vowels, ∀ b ∈ word.val, b.val ≠ v) :
    ∀ r : I64, count_of_substrings word k = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hmiss : ∃ v ∈ vowels, ∀ b ∈ word.val, b.val ≠ v), ∀ r : I64, count_of_substrings word k = ok r → r.val = 0) := by
  sorry

/-- Let rev be the slice of length n with rev[i] = word[n-1-i] for 0 <= i < n. If the function returns r for (word,k) and returns r_rev for (rev,k), then r = r_rev.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. -/
theorem spec_7 (word rev : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hrev : rev.val = word.val.reverse) :
    ∀ r rrev : I64,
      count_of_substrings word k = ok r →
        count_of_substrings rev k = ok rrev → r.val = rrev.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word rev : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hrev : rev.val = word.val.reverse), ∀ r rrev : I64,
      count_of_substrings word k = ok r →
        count_of_substrings rev k = ok rrev → r.val = rrev.val) := by
  sorry

/-- If the function returns r for (word,k) and returns r2 for (word2,k), then r = r2.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. Let V = {'a','e','i','o','u'}. Let word2 be any slice of length n of lowercase English letters such that for every i, if word[i] is in V then word2[i] = word[i], and if word[i] is not in V then word2[i] is not in V. -/
theorem spec_8 (word word2 : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hletter2 : ∀ b ∈ word2.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hpattern : SameVowelPattern word word2) :
    ∀ r r2 : I64,
      count_of_substrings word k = ok r →
        count_of_substrings word2 k = ok r2 → r.val = r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word word2 : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hletter2 : ∀ b ∈ word2.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hpattern : SameVowelPattern word word2), ∀ r r2 : I64,
      count_of_substrings word k = ok r →
        count_of_substrings word2 k = ok r2 → r.val = r2.val) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of intervals [i,j] with 0 <= i <= j < n such that (a) for every p with 0 <= p < n and word[p] not in V, i <= p <= j, and (b) for every v in V there exists q with i <= q <= j and word[q] = v.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. Let V = {'a','e','i','o','u'}. Let C = #{i | 0 <= i < n and word[i] not in V}. C = k. -/
theorem spec_9 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hC : consonantCount (letters word) = k.val.toNat) :
    ∀ r : I64,
      count_of_substrings word k = ok r →
        r.val = (countAllConsonantsIntervals word : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hC : consonantCount (letters word) = k.val.toNat), ∀ r : I64,
      count_of_substrings word k = ok r →
        r.val = (countAllConsonantsIntervals word : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let n = len(word). 5 <= n <= 250. For every i with 0 <= i < n, word[i] is a lowercase English letter. 0 <= k <= n - 5. The entire interval [0,n-1] contains each of the five vowels at least once and contains exactly k consonant bytes. -/
theorem spec_10 (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hvowels : ContainsAllVowels (letters word))
    (hcons : consonantCount (letters word) = k.val.toNat) :
    ∀ r : I64, count_of_substrings word k = ok r → 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice U8) (k : I64)
    (hn5 : 5 ≤ word.val.length) (hn250 : word.val.length ≤ 250)
    (hletter : ∀ b ∈ word.val, IsLowerLetter b.val)
    (hk0 : 0 ≤ k.val) (hk : k.val ≤ (word.val.length : Int) - 5)
    (hvowels : ContainsAllVowels (letters word))
    (hcons : consonantCount (letters word) = k.val.toNat), ∀ r : I64, count_of_substrings word k = ok r → 1 ≤ r.val) := by
  sorry

end AegisSpec.CountOfSubstrings
