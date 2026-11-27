import Aegis.EqualFrequency.Code.Funs

/-!
# Specifications of `Aegis.EqualFrequency.equal_frequency`

LeetCode problem `remove-letter-to-equalize-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.EqualFrequency (equal_frequency)

namespace AegisSpec.EqualFrequency

def isLower (c : U8) : Prop := 97 ≤ c.val ∧ c.val ≤ 122

def count (c : U8) (w : Slice U8) : ℕ := w.val.countP fun b => decide (b = c)

def countAfterDelete (c : U8) (w : Slice U8) (i : Fin w.val.length) : ℕ :=
  count c w - if c = w.val.get i then 1 else 0

def posFreqsAtMostTwo (w : Slice U8) : Prop :=
  ∃ f g : ℕ, ∀ c : U8, isLower c → 0 < count c w → count c w = f ∨ count c w = g

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Whenever equal_frequency(word) returns a result r, the following holds: r = true if and only if there exists an index i with 0 <= i < len(word) and there exists an integer f >= 1 such that, for every lowercase English letter c, if count(c,word) - (1 if c = word[i] else 0) > 0, then count(c,word) - (1 if c = word[i] else 0) = f. Equivalently, r = true if and only if deleting the single byte word[i] at some index i leaves a nonempty string in which every letter that still occurs has the same frequency f; otherwise r = false.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_1 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)) :
    ∀ r : Bool, equal_frequency word = ok r →
      (r = true ↔
        ∃ i : Fin word.val.length, ∃ f : ℕ, 1 ≤ f ∧
          ∀ c : U8, isLower c → 0 < countAfterDelete c word i →
            countAfterDelete c word i = f) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)), ∀ r : Bool, equal_frequency word = ok r →
      (r = true ↔
        ∃ i : Fin word.val.length, ∃ f : ℕ, 1 ≤ f ∧
          ∀ c : U8, isLower c → 0 < countAfterDelete c word i →
            countAfterDelete c word i = f)) := by
  sorry

/-- The call equal_frequency(word) does not fail: it returns a result, either true or false. In particular, no overflow, out-of-bounds access, or panic occurs for any input satisfying the preconditions.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_2 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)) :
    ∃ r : Bool, equal_frequency word = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)), ∃ r : Bool, equal_frequency word = ok r) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose that for every lowercase English letter c, count(c,word) = count(c,word'). Whenever equal_frequency(word) returns r and equal_frequency(word') returns r', we have r = r'.
  Preconditions: word and word' are slices of bytes, each with 2 <= len(word) <= 100 and 2 <= len(word') <= 100, every byte of each is an ASCII lowercase English letter (97..122), and len(word) = len(word'). -/
theorem spec_3 (word word' : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hlen2 : 2 ≤ word'.val.length) (hlen2' : word'.val.length ≤ 100)
    (hlower' : ∀ j : Fin word'.val.length, isLower (word'.val.get j))
    (hlenEq : word.val.length = word'.val.length)
    (hcount : ∀ c : U8, isLower c → count c word = count c word') :
    ∀ r r' : Bool,
      equal_frequency word = ok r → equal_frequency word' = ok r' → r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word word' : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hlen2 : 2 ≤ word'.val.length) (hlen2' : word'.val.length ≤ 100)
    (hlower' : ∀ j : Fin word'.val.length, isLower (word'.val.get j))
    (hlenEq : word.val.length = word'.val.length)
    (hcount : ∀ c : U8, isLower c → count c word = count c word'), ∀ r r' : Bool,
      equal_frequency word = ok r → equal_frequency word' = ok r' → r = r') := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose that for every lowercase English letter c, count(c,word) <= 1. Whenever equal_frequency(word) returns a result r, r = true.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_4 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hle : ∀ c : U8, isLower c → count c word ≤ 1) :
    ∀ r : Bool, equal_frequency word = ok r → r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hle : ∀ c : U8, isLower c → count c word ≤ 1), ∀ r : Bool, equal_frequency word = ok r → r = true) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose there exists a lowercase English letter c such that count(c,word) = len(word) (equivalently, every byte of word equals c). Whenever equal_frequency(word) returns a result r, r = true.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_5 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hconst : ∃ c : U8, isLower c ∧ count c word = word.val.length) :
    ∀ r : Bool, equal_frequency word = ok r → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hconst : ∃ c : U8, isLower c ∧ count c word = word.val.length), ∀ r : Bool, equal_frequency word = ok r → r = true) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose word contains exactly two distinct lowercase English letters; let a and b be their positive frequencies (so there are distinct letters c,d with count(c,word) = a, count(d,word) = b, a > 0, b > 0, and every other letter has count 0). Whenever equal_frequency(word) returns a result r, r = true if and only if a = 1 or b = 1 or |a-b| = 1.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_6 (word : Slice U8) (a b : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (ha : 0 < a) (hb : 0 < b)
    (hc : ∃ c : U8, isLower c ∧ count c word = a)
    (hd : ∃ d : U8, isLower d ∧ count d word = b)
    (htwo : ∀ e : U8, isLower e → count e word = a ∨ count e word = b ∨ count e word = 0)
    (hdisj : a ≠ b) :
    ∀ r : Bool, equal_frequency word = ok r →
      (r = true ↔ a = 1 ∨ b = 1 ∨ ((a : ℤ) - (b : ℤ)).natAbs = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice U8) (a b : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (ha : 0 < a) (hb : 0 < b)
    (hc : ∃ c : U8, isLower c ∧ count c word = a)
    (hd : ∃ d : U8, isLower d ∧ count d word = b)
    (htwo : ∀ e : U8, isLower e → count e word = a ∨ count e word = b ∨ count e word = 0)
    (hdisj : a ≠ b), ∀ r : Bool, equal_frequency word = ok r →
      (r = true ↔ a = 1 ∨ b = 1 ∨ ((a : ℤ) - (b : ℤ)).natAbs = 1)) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Whenever equal_frequency(word) returns a result r, if r = true then the set { count(c,word) | c is a lowercase English letter and count(c,word) > 0 } has at most two elements.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_7 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)) :
    ∀ r : Bool, equal_frequency word = ok r → r = true → posFreqsAtMostTwo word := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j)), ∀ r : Bool, equal_frequency word = ok r → r = true → posFreqsAtMostTwo word) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose word contains at least two distinct lowercase English letters and there is an integer f >= 2 such that exactly one lowercase English letter c has count(c,word) = 1, and every lowercase English letter d with count(d,word) > 0 and d != c has count(d,word) = f. Whenever equal_frequency(word) returns a result r, r = true.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_8 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (htwo : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ 0 < count c word ∧ 0 < count d word)
    (hshape : ∃ f : ℕ, 2 ≤ f ∧ ∃ c : U8, isLower c ∧ count c word = 1 ∧
      (∀ d : U8, isLower d → count d word = 1 → d = c) ∧
      ∀ d : U8, isLower d → 0 < count d word → d ≠ c → count d word = f) :
    ∀ r : Bool, equal_frequency word = ok r → r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (htwo : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ 0 < count c word ∧ 0 < count d word)
    (hshape : ∃ f : ℕ, 2 ≤ f ∧ ∃ c : U8, isLower c ∧ count c word = 1 ∧
      (∀ d : U8, isLower d → count d word = 1 → d = c) ∧
      ∀ d : U8, isLower d → 0 < count d word → d ≠ c → count d word = f), ∀ r : Bool, equal_frequency word = ok r → r = true) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose word contains at least two distinct lowercase English letters and there is an integer f >= 1 such that exactly one lowercase English letter c has count(c,word) = f+1, and every lowercase English letter d with count(d,word) > 0 and d != c has count(d,word) = f. Whenever equal_frequency(word) returns a result r, r = true.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_9 (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (htwo : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ 0 < count c word ∧ 0 < count d word)
    (hshape : ∃ f : ℕ, 1 ≤ f ∧ ∃ c : U8, isLower c ∧ count c word = f + 1 ∧
      (∀ d : U8, isLower d → count d word = f + 1 → d = c) ∧
      ∀ d : U8, isLower d → 0 < count d word → d ≠ c → count d word = f) :
    ∀ r : Bool, equal_frequency word = ok r → r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice U8)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (htwo : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ 0 < count c word ∧ 0 < count d word)
    (hshape : ∃ f : ℕ, 1 ≤ f ∧ ∃ c : U8, isLower c ∧ count c word = f + 1 ∧
      (∀ d : U8, isLower d → count d word = f + 1 → d = c) ∧
      ∀ d : U8, isLower d → 0 < count d word → d ≠ c → count d word = f), ∀ r : Bool, equal_frequency word = ok r → r = true) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose word contains at least three distinct lowercase English letters and there is an integer k >= 2 such that every lowercase English letter c with count(c,word) > 0 has count(c,word) = k. Whenever equal_frequency(word) returns a result r, r = false.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_10 (word : Slice U8) (k : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hk : 2 ≤ k)
    (hthree : ∃ c d e : U8, isLower c ∧ isLower d ∧ isLower e ∧
      0 < count c word ∧ 0 < count d word ∧ 0 < count e word ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e)
    (hcount : ∀ c : U8, isLower c → 0 < count c word → count c word = k) :
    ∀ r : Bool, equal_frequency word = ok r → r = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (word : Slice U8) (k : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (hk : 2 ≤ k)
    (hthree : ∃ c d e : U8, isLower c ∧ isLower d ∧ isLower e ∧
      0 < count c word ∧ 0 < count d word ∧ 0 < count e word ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e)
    (hcount : ∀ c : U8, isLower c → 0 < count c word → count c word = k), ∀ r : Bool, equal_frequency word = ok r → r = false) := by
  sorry

/-- For a byte c and a slice w, let count(c,w) be the number of indices j with 0 <= j < len(w) and w[j] = c. Suppose word has exactly two distinct positive frequencies a and b with a < b (so every present letter has count either a or b, and both values occur). Suppose also that at least two distinct lowercase English letters have frequency b, and either a > 1 or at least two distinct lowercase English letters have frequency a. Whenever equal_frequency(word) returns a result r, r = false.
  Preconditions: word is a slice of bytes with 2 <= len(word) <= 100, and every byte word[j] for 0 <= j < len(word) is an ASCII lowercase English letter (97 <= word[j] <= 122). -/
theorem spec_11 (word : Slice U8) (a b : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hpresent : ∀ c : U8, isLower c → 0 < count c word → count c word = a ∨ count c word = b)
    (hoccA : ∃ c : U8, isLower c ∧ count c word = a)
    (hoccB : ∃ c : U8, isLower c ∧ count c word = b)
    (hB2 : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ count c word = b ∧ count d word = b)
    (hcase : 1 < a ∨ ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧
      count c word = a ∧ count d word = a) :
    ∀ r : Bool, equal_frequency word = ok r → r = false := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (word : Slice U8) (a b : ℕ)
    (hlen : 2 ≤ word.val.length) (hlen' : word.val.length ≤ 100)
    (hlower : ∀ j : Fin word.val.length, isLower (word.val.get j))
    (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hpresent : ∀ c : U8, isLower c → 0 < count c word → count c word = a ∨ count c word = b)
    (hoccA : ∃ c : U8, isLower c ∧ count c word = a)
    (hoccB : ∃ c : U8, isLower c ∧ count c word = b)
    (hB2 : ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧ count c word = b ∧ count d word = b)
    (hcase : 1 < a ∨ ∃ c d : U8, isLower c ∧ isLower d ∧ c ≠ d ∧
      count c word = a ∧ count d word = a), ∀ r : Bool, equal_frequency word = ok r → r = false) := by
  sorry

end AegisSpec.EqualFrequency
