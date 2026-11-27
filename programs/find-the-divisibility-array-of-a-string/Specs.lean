import Aegis.DivisibilityArray.Code.Funs

/-!
# Specifications of `Aegis.DivisibilityArray.divisibility_array`

LeetCode problem `find-the-divisibility-array-of-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DivisibilityArray

def digit (c : Std.U8) : ℤ := (c.val : ℤ) - 48

def digits (word : Slice Std.U8) : List ℤ := word.val.map digit

def listVal : List ℤ → ℤ
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + listVal ds

def prefixVal (word : Slice Std.U8) (i : ℕ) : ℤ := listVal ((digits word).take (i + 1))

def byteIsDigit (c : Std.U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def isDigitWord (word : Slice Std.U8) : Prop :=
  ∀ j, j < word.val.length → byteIsDigit (word.val.getD j default)

def remSeq (ds : List ℤ) (m : ℤ) : ℕ → ℤ
  | 0 => ds.getD 0 0 % m
  | i + 1 => (10 * remSeq ds m i + ds.getD (i + 1) 0) % m

def remAt (word : Slice Std.U8) (m : ℤ) (i : ℕ) : ℤ := remSeq (digits word) m i

/-- Whenever the function returns a result r, len(r) = n and for every i with 0 <= i < n, if D_i = sum_{j=0}^{i} digit(word[j]) * 10^(i-j) is the mathematical numeric value of the decimal prefix word[0..i], then r[i] = 1 exactly when m divides D_i (equivalently D_i mod m = 0), and r[i] = 0 otherwise.
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, word[j] is an ASCII digit (48 <= word[j] <= 57). Write digit(word[j]) = word[j] - 48. -/
theorem spec_1 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    r.val.length = word.val.length ∧
      ∀ i, i < word.val.length →
        ((r.val.getD i 0#i64).val = 1 ↔ m.val ∣ prefixVal word i) ∧
          ((r.val.getD i 0#i64).val = 0 ↔ ¬ m.val ∣ prefixVal word i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), r.val.length = word.val.length ∧
      ∀ i, i < word.val.length →
        ((r.val.getD i 0#i64).val = 1 ↔ m.val ∣ prefixVal word i) ∧
          ((r.val.getD i 0#i64).val = 0 ↔ ¬ m.val ∣ prefixVal word i)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail by arithmetic overflow, panic, division by zero, or out-of-bounds access.
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. -/
theorem spec_2 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DivisibilityArray.divisibility_array word m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.DivisibilityArray.divisibility_array word m = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(word).
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. -/
theorem spec_3 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    r.val.length = word.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), r.val.length = word.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] is either 0 or 1 as an i64.
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. -/
theorem spec_4 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    ∀ i, i < r.val.length → (r.val.getD i 0#i64).val = 0 ∨ (r.val.getD i 0#i64).val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), ∀ i, i < r.val.length → (r.val.getD i 0#i64).val = 0 ∨ (r.val.getD i 0#i64).val = 1) := by
  sorry

/-- If word1[j] = word2[j] for every j with 0 <= j < k, then whenever the function returns r1 on (word1, m) and r2 on (word2, m), it holds that r1[i] = r2[i] for every i with 0 <= i < k.
  Preconditions: Let n1 = len(word1) and n2 = len(word2). Assume 1 <= n1 <= 100000, 1 <= n2 <= 100000, 1 <= m <= 1000000000, every byte of word1 and word2 is an ASCII digit (48 to 57), and k is an integer with 0 <= k <= n1 and 0 <= k <= n2. -/
theorem spec_5 (word1 word2 : Slice Std.U8) (m : Std.I64) (k : ℕ)
    (hn1 : 1 ≤ word1.val.length) (hn1' : word1.val.length ≤ 100000)
    (hn2 : 1 ≤ word2.val.length) (hn2' : word2.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig1 : isDigitWord word1) (hdig2 : isDigitWord word2)
    (hk1 : k ≤ word1.val.length) (hk2 : k ≤ word2.val.length)
    (hagree : ∀ j, j < k →
      (word1.val.getD j default).val = (word2.val.getD j default).val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hr1 : Aegis.DivisibilityArray.divisibility_array word1 m = ok r1)
    (hr2 : Aegis.DivisibilityArray.divisibility_array word2 m = ok r2) :
    ∀ i, i < k → (r1.val.getD i 0#i64).val = (r2.val.getD i 0#i64).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (word1 word2 : Slice Std.U8) (m : Std.I64) (k : ℕ)
    (hn1 : 1 ≤ word1.val.length) (hn1' : word1.val.length ≤ 100000)
    (hn2 : 1 ≤ word2.val.length) (hn2' : word2.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig1 : isDigitWord word1) (hdig2 : isDigitWord word2)
    (hk1 : k ≤ word1.val.length) (hk2 : k ≤ word2.val.length)
    (hagree : ∀ j, j < k →
      (word1.val.getD j default).val = (word2.val.getD j default).val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hr1 : Aegis.DivisibilityArray.divisibility_array word1 m = ok r1)
    (hr2 : Aegis.DivisibilityArray.divisibility_array word2 m = ok r2), ∀ i, i < k → (r1.val.getD i 0#i64).val = (r2.val.getD i 0#i64).val) := by
  sorry

/-- If the function returns r1 on (word, m1) and r2 on (word, m2), then for every i with 0 <= i < n, r2[i] = 1 implies r1[i] = 1. Equivalently, r1[i] >= r2[i] for every i.
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, every byte of word is an ASCII digit (48 to 57), and m1, m2 are positive integers with 1 <= m1 <= 1000000000, 1 <= m2 <= 1000000000, and m1 divides m2 (there exists a positive integer q with m2 = q * m1). -/
theorem spec_6 (word : Slice Std.U8) (m1 m2 : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hdig : isDigitWord word)
    (hm1 : 1 ≤ m1.val) (hm1' : m1.val ≤ 1000000000)
    (hm2 : 1 ≤ m2.val) (hm2' : m2.val ≤ 1000000000)
    (hdvd : ∃ q : ℤ, 1 ≤ q ∧ m2.val = q * m1.val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hr1 : Aegis.DivisibilityArray.divisibility_array word m1 = ok r1)
    (hr2 : Aegis.DivisibilityArray.divisibility_array word m2 = ok r2) :
    ∀ i, i < word.val.length →
      (r2.val.getD i 0#i64).val = 1 → (r1.val.getD i 0#i64).val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (word : Slice Std.U8) (m1 m2 : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hdig : isDigitWord word)
    (hm1 : 1 ≤ m1.val) (hm1' : m1.val ≤ 1000000000)
    (hm2 : 1 ≤ m2.val) (hm2' : m2.val ≤ 1000000000)
    (hdvd : ∃ q : ℤ, 1 ≤ q ∧ m2.val = q * m1.val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hr1 : Aegis.DivisibilityArray.divisibility_array word m1 = ok r1)
    (hr2 : Aegis.DivisibilityArray.divisibility_array word m2 = ok r2), ∀ i, i < word.val.length →
      (r2.val.getD i 0#i64).val = 1 → (r1.val.getD i 0#i64).val = 1) := by
  sorry

/-- Whenever the function returns a result r, let R_0 = digit(word[0]) mod m and, for 1 <= i < n, let R_i = (10 * R_{i-1} + digit(word[i])) mod m. Then for every i with 0 <= i < n, r[i] = 1 exactly when R_i = 0.
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. Write digit(word[j]) = word[j] - 48. -/
theorem spec_7 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    ∀ i, i < word.val.length →
      ((r.val.getD i 0#i64).val = 1 ↔ remAt word m.val i = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), ∀ i, i < word.val.length →
      ((r.val.getD i 0#i64).val = 1 ↔ remAt word m.val i = 0)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = 1 then there exists a nonnegative integer q such that D_i = q * m, where D_i = sum_{j=0}^{i} digit(word[j]) * 10^(i-j).
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. Write digit(word[j]) = word[j] - 48. -/
theorem spec_8 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    ∀ i, i < word.val.length → (r.val.getD i 0#i64).val = 1 →
      ∃ q : ℤ, 0 ≤ q ∧ prefixVal word i = q * m.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), ∀ i, i < word.val.length → (r.val.getD i 0#i64).val = 1 →
      ∃ q : ℤ, 0 ≤ q ∧ prefixVal word i = q * m.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = 0 then there exist integers q and a with q >= 0 and 1 <= a < m such that D_i = q * m + a, where D_i = sum_{j=0}^{i} digit(word[j]) * 10^(i-j).
  Preconditions: Let n = len(word). Assume 1 <= n <= 100000, 1 <= m <= 1000000000, and for every j with 0 <= j < n, 48 <= word[j] <= 57. Write digit(word[j]) = word[j] - 48. -/
theorem spec_9 (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r) :
    ∀ i, i < word.val.length → (r.val.getD i 0#i64).val = 0 →
      ∃ q a : ℤ, 0 ≤ q ∧ 1 ≤ a ∧ a < m.val ∧ prefixVal word i = q * m.val + a := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (word : Slice Std.U8) (m : Std.I64)
    (hn1 : 1 ≤ word.val.length) (hn2 : word.val.length ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000000000)
    (hdig : isDigitWord word)
    (r : alloc.vec.Vec Std.I64)
    (hr : Aegis.DivisibilityArray.divisibility_array word m = ok r), ∀ i, i < word.val.length → (r.val.getD i 0#i64).val = 0 →
      ∃ q a : ℤ, 0 ≤ q ∧ 1 ≤ a ∧ a < m.val ∧ prefixVal word i = q * m.val + a) := by
  sorry

end AegisSpec.DivisibilityArray
