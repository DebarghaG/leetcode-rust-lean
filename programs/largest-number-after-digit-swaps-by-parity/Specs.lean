import Aegis.LargestInteger.Code.Funs

/-!
# Specifications of `Aegis.LargestInteger.largest_integer`

LeetCode problem `largest-number-after-digit-swaps-by-parity`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LargestInteger

namespace AegisSpec.LargestInteger

def decDigits (n : Nat) : List Nat :=
  if _h : n = 0 then [] else decDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by omega

def parityIndices (d : List Nat) (p : Nat) : List Nat :=
  (List.range d.length).filter (fun i => decide (d.getD i 0 % 2 = p))

def SortedNonIncreasing (l : List Nat) : Prop := l.Pairwise (fun a b => a ≥ b)

def ParityNonIncreasing (d : List Nat) : Prop :=
  ∀ i j : Nat, i < j → j < d.length →
    d.getD i 0 % 2 = d.getD j 0 % 2 → d.getD i 0 ≥ d.getD j 0

def AllSameParity (d : List Nat) : Prop :=
  (∀ x : Nat, x ∈ d → x % 2 = 0) ∨ (∀ x : Nat, x ∈ d → x % 2 = 1)

/-- Let d[0..n-1] be the decimal digits of num from most significant to least, where n = len(digits(num)) and d[0] != 0. Whenever largest_integer returns a result r, r has exactly n decimal digits; let e[0..n-1] be its decimal digits from most significant to least. For each parity p in {0,1}, let i_0 < i_1 < ... < i_{m-1} be all indices with d[i_j] mod 2 = p. Then e[i_0],...,e[i_{m-1}] is exactly the list of all digits d[k] with d[k] mod 2 = p, sorted in non-increasing order. Equivalently, e[i_0] >= e[i_1] >= ... >= e[i_{m-1}], and the multiset {e[i_0],...,e[i_{m-1}]} equals the multiset {d[k] | 0 <= k < n and d[k] mod 2 = p}. Equivalently, r is the largest integer obtainable from num by any sequence of swaps of two digits having the same parity.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_1 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ p : Nat, p < 2 →
        SortedNonIncreasing
          ((parityIndices (decDigits num.val.toNat) p).map
            (fun i => (decDigits r.val.toNat).getD i 0)) ∧
        List.Perm
          ((parityIndices (decDigits num.val.toNat) p).map
            (fun i => (decDigits r.val.toNat).getD i 0))
          ((decDigits num.val.toNat).filter (fun x => decide (x % 2 = p)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ p : Nat, p < 2 →
        SortedNonIncreasing
          ((parityIndices (decDigits num.val.toNat) p).map
            (fun i => (decDigits r.val.toNat).getD i 0)) ∧
        List.Perm
          ((parityIndices (decDigits num.val.toNat) p).map
            (fun i => (decDigits r.val.toNat).getD i 0))
          ((decDigits num.val.toNat).filter (fun x => decide (x % 2 = p))))) := by
  sorry

/-- For every num with 1 <= num <= 1,000,000,000, largest_integer num returns a result r (it does not fail, panic, or overflow).
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_2 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∃ r, largest_integer num = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∃ r, largest_integer num = ok r) := by
  sorry

/-- Whenever largest_integer returns a result r, r <= 1,000,000,000.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_3 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r → r.val ≤ 1000000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r → r.val ≤ 1000000000) := by
  sorry

/-- Whenever largest_integer returns a result r, r >= num.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_4 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r → num.val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r → num.val ≤ r.val) := by
  sorry

/-- Whenever largest_integer returns a result r, len(digits(r)) = len(digits(num)), where digits(x) denotes the decimal digits of a positive integer x, most significant first and with no leading zero. Equivalently, if n = len(digits(num)), then 10^(n-1) <= r < 10^n.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_5 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length) := by
  sorry

/-- Let d[0..n-1] be the decimal digits of num from most significant to least. Whenever largest_integer returns a result r, r has exactly n decimal digits; let e[0..n-1] be its decimal digits from most significant to least. Then for every i with 0 <= i < n, e[i] mod 2 = d[i] mod 2.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_6 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i : Nat, i < (decDigits num.val.toNat).length →
        (decDigits r.val.toNat).getD i 0 % 2 = (decDigits num.val.toNat).getD i 0 % 2) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i : Nat, i < (decDigits num.val.toNat).length →
        (decDigits r.val.toNat).getD i 0 % 2 = (decDigits num.val.toNat).getD i 0 % 2)) := by
  sorry

/-- Whenever largest_integer returns a result r, the multiset of decimal digits of r equals the multiset of decimal digits of num. Equivalently, for every digit v in {0,1,...,9}, the number of occurrences of v in the decimal representation of r equals the number of occurrences of v in the decimal representation of num.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_7 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      List.Perm (decDigits r.val.toNat) (decDigits num.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      List.Perm (decDigits r.val.toNat) (decDigits num.val.toNat)) := by
  sorry

/-- Let d[0..n-1] and e[0..n-1] be the decimal digits from most significant to least of num and of the returned r, respectively (r has exactly n digits). For every pair of indices i < j such that d[i] is odd and d[j] is odd, we have e[i] >= e[j].
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_8 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i j : Nat, i < j → j < (decDigits num.val.toNat).length →
        (decDigits num.val.toNat).getD i 0 % 2 = 1 →
        (decDigits num.val.toNat).getD j 0 % 2 = 1 →
        (decDigits r.val.toNat).getD i 0 ≥ (decDigits r.val.toNat).getD j 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i j : Nat, i < j → j < (decDigits num.val.toNat).length →
        (decDigits num.val.toNat).getD i 0 % 2 = 1 →
        (decDigits num.val.toNat).getD j 0 % 2 = 1 →
        (decDigits r.val.toNat).getD i 0 ≥ (decDigits r.val.toNat).getD j 0)) := by
  sorry

/-- Let d[0..n-1] and e[0..n-1] be the decimal digits from most significant to least of num and of the returned r, respectively (r has exactly n digits). For every pair of indices i < j such that d[i] is even and d[j] is even, we have e[i] >= e[j].
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_9 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i j : Nat, i < j → j < (decDigits num.val.toNat).length →
        (decDigits num.val.toNat).getD i 0 % 2 = 0 →
        (decDigits num.val.toNat).getD j 0 % 2 = 0 →
        (decDigits r.val.toNat).getD i 0 ≥ (decDigits r.val.toNat).getD j 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      (decDigits r.val.toNat).length = (decDigits num.val.toNat).length ∧
      (∀ i j : Nat, i < j → j < (decDigits num.val.toNat).length →
        (decDigits num.val.toNat).getD i 0 % 2 = 0 →
        (decDigits num.val.toNat).getD j 0 % 2 = 0 →
        (decDigits r.val.toNat).getD i 0 ≥ (decDigits r.val.toNat).getD j 0)) := by
  sorry

/-- If every decimal digit of num has the same parity (all are even or all are odd), then whenever largest_integer returns a result r, the decimal digits of r, read from most significant to least, are exactly the decimal digits of num sorted in non-increasing order.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_10 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000)
    (hpar : AllSameParity (decDigits num.val.toNat)) :
    ∀ r, largest_integer num = ok r →
      SortedNonIncreasing (decDigits r.val.toNat) ∧
      List.Perm (decDigits r.val.toNat) (decDigits num.val.toNat) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000)
    (hpar : AllSameParity (decDigits num.val.toNat)), ∀ r, largest_integer num = ok r →
      SortedNonIncreasing (decDigits r.val.toNat) ∧
      List.Perm (decDigits r.val.toNat) (decDigits num.val.toNat)) := by
  sorry

/-- Suppose the decimal digits d[0..n-1] of num already satisfy the condition that for every i < j with d[i] mod 2 = d[j] mod 2, d[i] >= d[j]. Then whenever largest_integer returns a result r, r = num.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_11 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000)
    (hsorted : ParityNonIncreasing (decDigits num.val.toNat)) :
    ∀ r, largest_integer num = ok r → r = num := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000)
    (hsorted : ParityNonIncreasing (decDigits num.val.toNat)), ∀ r, largest_integer num = ok r → r = num) := by
  sorry

/-- Whenever largest_integer num returns a result r, the value r satisfies 1 <= r <= 1,000,000,000, and largest_integer r returns the result r.
  Preconditions: 1 <= num <= 1,000,000,000. -/
theorem spec_12 (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000) :
    ∀ r, largest_integer num = ok r →
      1 ≤ r.val ∧ r.val ≤ 1000000000 ∧ largest_integer r = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num : Std.I64) (hnum : 1 ≤ num.val ∧ num.val ≤ 1000000000), ∀ r, largest_integer num = ok r →
      1 ≤ r.val ∧ r.val ≤ 1000000000 ∧ largest_integer r = ok r) := by
  sorry

end AegisSpec.LargestInteger
