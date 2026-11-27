import Aegis.MaximumEvenSplit.Code.Funs

/-!
# Specifications of `Aegis.MaximumEvenSplit.maximum_even_split`

LeetCode problem `maximum-split-of-positive-even-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumEvenSplit

  def IsEvenInt (n : ℤ) : Prop := ∃ a : ℤ, n = 2 * a

  def IsOddInt (n : ℤ) : Prop := ∃ a : ℤ, n = 2 * a + 1

  def IsLargestTriangularIndex (n k : ℤ) : Prop :=
    0 ≤ k ∧ k * (k + 1) ≤ n ∧ ∀ k' : ℤ, 0 ≤ k' → k' * (k' + 1) ≤ n → k' ≤ k

  def vecSum (l : List Std.I64) : ℤ := (l.map fun x => x.val).sum

  def PairwiseDistinct (l : List Std.I64) : Prop :=
    ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length),
      i ≠ j → (l.get ⟨i, hi⟩).val ≠ (l.get ⟨j, hj⟩).val

  def AllPositiveEven (l : List Std.I64) : Prop :=
    ∀ (i : ℕ) (hi : i < l.length), 0 < (l.get ⟨i, hi⟩).val ∧ IsEvenInt (l.get ⟨i, hi⟩).val

  /-- The function returns a result r and does not fail. If finalSum is odd, then len(r) = 0. If finalSum is even, let k be the largest nonnegative integer such that k*(k+1) <= finalSum. Then: (a) len(r) = k; (b) for every i with 0 <= i < len(r), r[i] > 0 and r[i] is even; (c) for all i, j with 0 <= i < len(r) and 0 <= j < len(r), if i != j then r[i] != r[j]; and (d) sum_{i=0}^{len(r)-1} r[i] = finalSum. The order of the entries of r is not constrained.
    Preconditions: 1 <= finalSum <= 10000000000 (the problem constraint). -/
  theorem spec_1
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000) :
      (IsOddInt finalSum.val →
          ∃ r : alloc.vec.Vec Std.I64,
            Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r ∧
              r.val.length = 0) ∧
        (IsEvenInt finalSum.val →
          ∀ k : ℤ, IsLargestTriangularIndex finalSum.val k →
            ∃ r : alloc.vec.Vec Std.I64,
              Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r ∧
                r.val.length = k.toNat ∧
                AllPositiveEven r.val ∧
                PairwiseDistinct r.val ∧
                vecSum r.val = finalSum.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000), (IsOddInt finalSum.val →
            ∃ r : alloc.vec.Vec Std.I64,
              Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r ∧
                r.val.length = 0) ∧
          (IsEvenInt finalSum.val →
            ∀ k : ℤ, IsLargestTriangularIndex finalSum.val k →
              ∃ r : alloc.vec.Vec Std.I64,
                Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r ∧
                  r.val.length = k.toNat ∧
                  AllPositiveEven r.val ∧
                  PairwiseDistinct r.val ∧
                  vecSum r.val = finalSum.val)) := by
    sorry

  /-- The function returns a result r (not a failure) for every finalSum satisfying the precondition; in particular it does not overflow and does not index out of bounds.
    Preconditions: 1 <= finalSum <= 10000000000. -/
  theorem spec_2
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0; that is, r is the empty list.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is odd. -/
  theorem spec_3
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_odd : IsOddInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          r.val.length = 0 ∧ r.val = [] := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_odd : IsOddInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            r.val.length = 0 ∧ r.val = []) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= 1.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_4
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          1 ≤ r.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            1 ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), r[i] > 0.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_5
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ∀ (i : ℕ) (hi : i < r.val.length), 0 < (r.val.get ⟨i, hi⟩).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ∀ (i : ℕ) (hi : i < r.val.length), 0 < (r.val.get ⟨i, hi⟩).val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), r[i] is even (there exists an integer a with r[i] = 2*a).
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_6
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ∀ (i : ℕ) (hi : i < r.val.length),
            ∃ a : ℤ, (r.val.get ⟨i, hi⟩).val = 2 * a := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ∀ (i : ℕ) (hi : i < r.val.length),
              ∃ a : ℤ, (r.val.get ⟨i, hi⟩).val = 2 * a) := by
    sorry

  /-- Whenever the function returns a result r, its entries are pairwise distinct: for all i, j with 0 <= i < len(r), 0 <= j < len(r), and i != j, we have r[i] != r[j].
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_7
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          PairwiseDistinct r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            PairwiseDistinct r.val) := by
    sorry

  /-- Whenever the function returns a result r, the entries sum to finalSum: sum_{i=0}^{len(r)-1} r[i] = finalSum.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_8
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          vecSum r.val = finalSum.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            vecSum r.val = finalSum.val) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = k, where k is the largest nonnegative integer satisfying k*(k+1) <= finalSum (equivalently k*(k+1)/2 <= finalSum/2).
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_9
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ∀ k : ℤ, IsLargestTriangularIndex finalSum.val k → r.val.length = k.toNat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ∀ k : ℤ, IsLargestTriangularIndex finalSum.val k → r.val.length = k.toNat) := by
    sorry

  /-- Whenever the function returns a result r, there does not exist any integer m with m > len(r) and a list of m pairwise distinct positive even integers whose sum is finalSum. Equivalently, len(r) is the maximum cardinality of a set of pairwise distinct positive even integers summing to finalSum.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_10
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ¬ ∃ l : List ℤ,
              r.val.length < l.length ∧
                (∀ x ∈ l, 0 < x ∧ IsEvenInt x) ∧ l.Nodup ∧ l.sum = finalSum.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ¬ ∃ l : List ℤ,
                r.val.length < l.length ∧
                  (∀ x ∈ l, 0 < x ∧ IsEvenInt x) ∧ l.Nodup ∧ l.sum = finalSum.val) := by
    sorry

  /-- Whenever the function returns a result r, len(r)*(len(r)+1) <= finalSum.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_11
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          (r.val.length : ℤ) * ((r.val.length : ℤ) + 1) ≤ finalSum.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            (r.val.length : ℤ) * ((r.val.length : ℤ) + 1) ≤ finalSum.val) := by
    sorry

  /-- Whenever the function returns a result r, (len(r)+1)*(len(r)+2) > finalSum.
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_12
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ((r.val.length : ℤ) + 1) * ((r.val.length : ℤ) + 2) > finalSum.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ((r.val.length : ℤ) + 1) * ((r.val.length : ℤ) + 2) > finalSum.val) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), r[i] <= finalSum - len(r)*(len(r)-1).
    Preconditions: 1 <= finalSum <= 10000000000 and finalSum is even. -/
  theorem spec_13
    (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
    (h_even : IsEvenInt finalSum.val) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
          ∀ (i : ℕ) (hi : i < r.val.length),
            (r.val.get ⟨i, hi⟩).val ≤
              finalSum.val - (r.val.length : ℤ) * ((r.val.length : ℤ) - 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (finalSum : Std.I64) (h_lo : 1 ≤ finalSum.val) (h_hi : finalSum.val ≤ 10000000000)
      (h_even : IsEvenInt finalSum.val), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.MaximumEvenSplit.maximum_even_split finalSum = Result.ok r →
            ∀ (i : ℕ) (hi : i < r.val.length),
              (r.val.get ⟨i, hi⟩).val ≤
                finalSum.val - (r.val.length : ℤ) * ((r.val.length : ℤ) - 1)) := by
    sorry

  end AegisSpec.MaximumEvenSplit
