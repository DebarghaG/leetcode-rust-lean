import Aegis.SequentialDigits.Code.Funs

/-!
# Specifications of `Aegis.SequentialDigits.sequential_digits`

LeetCode problem `sequential-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SequentialDigits

namespace AegisSpec.SequentialDigits

def IsSequential (n : ℤ) : Prop :=
  ∃ (k : ℕ) (d : ℕ → ℤ),
    2 ≤ k ∧
      1 ≤ d 0 ∧
      (∀ i : ℕ, i < k → 0 ≤ d i ∧ d i ≤ 9) ∧
      (∀ i : ℕ, i + 1 < k → d (i + 1) = d i + 1) ∧
      n = Finset.sum (Finset.range k) fun i => d i * 10 ^ (k - 1 - i)

def digitsRev : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n + 1 => (n + 1) % 10 :: digitsRev fuel ((n + 1) / 10)

def decimalDigits (n : ℕ) : List ℕ := (digitsRev (n + 1) n).reverse

def StepsIncr : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => b = a + 1 ∧ StepsIncr (b :: rest)

def HasSequentialDigits (n : ℤ) : Prop :=
  10 ≤ n ∧ StepsIncr (decimalDigits n.toNat)

noncomputable def sequentialCount (low high : ℤ) : ℕ :=
  Nat.card { n : ℤ // low ≤ n ∧ n ≤ high ∧ IsSequential n }

def firstOf {α : Type} (l : List α) (h : 0 < l.length) : α := l.get ⟨0, h⟩

def lastOf {α : Type} (l : List α) (h : 0 < l.length) : α :=
  l.get ⟨l.length - 1, Nat.sub_lt h Nat.zero_lt_one⟩

/-- The function returns a result r such that r is exactly the list of all integers n with low <= n <= high and sequential_digits(n), in strictly increasing order. Here sequential_digits(n) means there exist an integer k >= 2 and digits d_0, ..., d_{k-1} such that 1 <= d_0 <= 9, 0 <= d_i <= 9 for every i, d_{i+1} = d_i + 1 for every 0 <= i < k-1, and n = sum_{i=0}^{k-1} d_i * 10^{k-1-i}. Equivalently: (a) for every i with 0 <= i < len(r), low <= r[i] <= high and sequential_digits(r[i]); (b) for every n with low <= n <= high and sequential_digits(n), there is exactly one i with 0 <= i < len(r) and r[i] = n; (c) for every i,j with 0 <= i < j < len(r), r[i] < r[j].
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_1 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec Std.I64,
      sequential_digits low high = ok r ∧
        (∀ i : Fin r.val.length,
          low.val ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ high.val ∧
            IsSequential (r.val.get i).val) ∧
        (∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n →
          ∃! i : Fin r.val.length, (r.val.get i).val = n) ∧
        (∀ i j : Fin r.val.length, i < j → (r.val.get i).val < (r.val.get j).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec Std.I64,
      sequential_digits low high = ok r ∧
        (∀ i : Fin r.val.length,
          low.val ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ high.val ∧
            IsSequential (r.val.get i).val) ∧
        (∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n →
          ∃! i : Fin r.val.length, (r.val.get i).val = n) ∧
        (∀ i j : Fin r.val.length, i < j → (r.val.get i).val < (r.val.get j).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), low <= r[i] <= high.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_2 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i : Fin r.val.length,
        low.val ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ high.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i : Fin r.val.length,
        low.val ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ high.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] has sequential digits; that is, r[i] >= 10 and in the usual decimal notation of r[i] without leading zeros, every digit after the first is exactly one greater than the digit immediately before it.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_3 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i : Fin r.val.length, HasSequentialDigits (r.val.get i).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i : Fin r.val.length, HasSequentialDigits (r.val.get i).val) := by
  sorry

/-- Whenever the function returns a result r, for every integer n with low <= n <= high that has sequential digits, there exists an index i with 0 <= i < len(r) such that r[i] = n.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_4 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n →
        ∃ i : Fin r.val.length, (r.val.get i).val = n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n →
        ∃ i : Fin r.val.length, (r.val.get i).val = n) := by
  sorry

/-- Whenever the function returns a result r, r is strictly increasing: for every i,j with 0 <= i < j < len(r), r[i] < r[j].
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_5 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i j : Fin r.val.length, i < j → (r.val.get i).val < (r.val.get j).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i j : Fin r.val.length, i < j → (r.val.get i).val < (r.val.get j).val) := by
  sorry

/-- Whenever the function returns a result r, len(r) is the number of integers n such that low <= n <= high and n has sequential digits.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_6 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      r.val.length = sequentialCount low.val high.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      r.val.length = sequentialCount low.val high.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if there is no integer n with low <= n <= high that has sequential digits.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_7 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      (r.val.length = 0 ↔ ¬ ∃ n : ℤ, low.val ≤ n ∧ n ≤ high.val ∧ IsSequential n) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      (r.val.length = 0 ↔ ¬ ∃ n : ℤ, low.val ≤ n ∧ n ≤ high.val ∧ IsSequential n)) := by
  sorry

/-- Whenever the function returns a result r and len(r) > 0, r[0] is the least integer n satisfying low <= n <= high and n has sequential digits; that is, r[0] satisfies low <= r[0] <= high, has sequential digits, and for every integer n with low <= n <= high and sequential digits, r[0] <= n.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_8 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ hpos : 0 < r.val.length,
        let x := (firstOf r.val hpos).val
        low.val ≤ x ∧ x ≤ high.val ∧ IsSequential x ∧
          ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n → x ≤ n := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ hpos : 0 < r.val.length,
        let x := (firstOf r.val hpos).val
        low.val ≤ x ∧ x ≤ high.val ∧ IsSequential x ∧
          ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n → x ≤ n) := by
  sorry

/-- Whenever the function returns a result r and len(r) > 0, r[len(r)-1] is the greatest integer n satisfying low <= n <= high and n has sequential digits; that is, r[len(r)-1] satisfies low <= r[len(r)-1] <= high, has sequential digits, and for every integer n with low <= n <= high and sequential digits, n <= r[len(r)-1].
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_9 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ hpos : 0 < r.val.length,
        let x := (lastOf r.val hpos).val
        low.val ≤ x ∧ x ≤ high.val ∧ IsSequential x ∧
          ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n → n ≤ x := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ hpos : 0 < r.val.length,
        let x := (lastOf r.val hpos).val
        low.val ≤ x ∧ x ≤ high.val ∧ IsSequential x ∧
          ∀ n : ℤ, low.val ≤ n → n ≤ high.val → IsSequential n → n ≤ x) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, there is no integer n such that low <= n <= high, n has sequential digits, and r[i] < n < r[i+1].
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_10 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i j : Fin r.val.length, (i : ℕ) + 1 = (j : ℕ) →
        ¬ ∃ n : ℤ, low.val ≤ n ∧ n ≤ high.val ∧ IsSequential n ∧
          (r.val.get i).val < n ∧ n < (r.val.get j).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r →
      ∀ i j : Fin r.val.length, (i : ℕ) + 1 = (j : ℕ) →
        ¬ ∃ n : ℤ, low.val ≤ n ∧ n ≤ high.val ∧ IsSequential n ∧
          (r.val.get i).val < n ∧ n < (r.val.get j).val) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 36.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_11 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r → r.val.length ≤ 36 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∀ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r → r.val.length ≤ 36) := by
  sorry

/-- The function returns a result r; it does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs during the call.
  Preconditions: low and high are 64-bit integers with 10 <= low <= high <= 10^9. -/
theorem spec_12 (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9) :
    ∃ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (low high : Std.I64)
    (h_low : 10 ≤ low.val) (h_le : low.val ≤ high.val) (h_high : high.val ≤ 10 ^ 9), ∃ r : alloc.vec.Vec Std.I64, sequential_digits low high = ok r) := by
  sorry

end AegisSpec.SequentialDigits
