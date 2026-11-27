import Aegis.MinimumPossibleSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumPossibleSum.minimum_possible_sum`

LeetCode problem `find-the-minimum-possible-sum-of-a-beautiful-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumPossibleSum

def mpsMod : ℤ := 1000000007

def NoPairSumsTo (target : ℤ) (A : List ℤ) : Prop :=
  ∀ (i j : ℕ), i < A.length → j < A.length → i ≠ j →
    ∀ a b : ℤ, A[i]? = some a → A[j]? = some b → a + b ≠ target

def IsBeautiful (n : ℕ) (target : ℤ) (A : List ℤ) : Prop :=
  A.length = n ∧ (∀ x ∈ A, 0 < x) ∧ A.Nodup ∧ NoPairSumsTo target A

def IsMinimumSum (n : ℕ) (target : ℤ) (s : ℤ) : Prop :=
  (∃ A : List ℤ, IsBeautiful n target A ∧ A.sum = s) ∧
    ∀ A : List ℤ, IsBeautiful n target A → s ≤ A.sum

def IsResidueOf (r s : ℤ) : Prop :=
  0 ≤ r ∧ r < mpsMod ∧ Int.ModEq mpsMod r s

/-- The function returns a result r, and r is the unique integer with 0 <= r < P that is congruent modulo P to the least possible value of sum_{i=0}^{n-1} A[i] over all beautiful arrays A of length n.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9; n and target denote their mathematical integer values. Let P = 1000000007. An array A of length n is beautiful when all its entries are pairwise distinct positive integers and, for every i and j with 0 <= i < n, 0 <= j < n, and i != j, A[i] + A[j] != target. -/
theorem spec_1 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9) :
    ∃ r : Aeneas.Std.I64,
      Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r ∧
        ∃ S : ℤ, IsMinimumSum n.val.toNat target.val S ∧ IsResidueOf r.val S := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9), ∃ r : Aeneas.Std.I64,
      Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r ∧
        ∃ S : ℤ, IsMinimumSum n.val.toNat target.val S ∧ IsResidueOf r.val S) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or produce an out-of-bounds access for any input satisfying the preconditions.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_2 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9) :
    ∃ r : Aeneas.Std.I64, Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9), ∃ r : Aeneas.Std.I64, Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) := by
  sorry

/-- Whenever the function returns a result r, it satisfies 0 <= r < 1000000007.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. -/
theorem spec_3 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Whenever the function returns a result r, r is the unique integer with 0 <= r < P and r congruent to n*(n+1)/2 modulo P.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Let m = floor(target/2) and P = 1000000007. Assume n <= m. -/
theorem spec_4 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hnm : n.val ≤ target.val / 2)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    IsResidueOf r.val (n.val * (n.val + 1) / 2) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hnm : n.val ≤ target.val / 2)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), IsResidueOf r.val (n.val * (n.val + 1) / 2)) := by
  sorry

/-- Whenever the function returns a result r, r is the unique integer with 0 <= r < P and r congruent modulo P to m*(m+1)/2 + d*target + d*(d-1)/2.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Let m = floor(target/2), d = n - m, and P = 1000000007. Assume n > m. -/
theorem spec_5 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hnm : target.val / 2 < n.val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    IsResidueOf r.val
      ((target.val / 2) * (target.val / 2 + 1) / 2
        + (n.val - target.val / 2) * target.val
        + (n.val - target.val / 2) * (n.val - target.val / 2 - 1) / 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hnm : target.val / 2 < n.val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), IsResidueOf r.val
      ((target.val / 2) * (target.val / 2 + 1) / 2
        + (n.val - target.val / 2) * target.val
        + (n.val - target.val / 2) * (n.val - target.val / 2 - 1) / 2)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Assume n = 1. -/
theorem spec_6 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hn : n.val = 1)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hn : n.val = 1)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r is the unique integer with 0 <= r < 1000000007 that is congruent to n*(n+1)/2 modulo 1000000007.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Assume target = 1. -/
theorem spec_7 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht : target.val = 1)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    IsResidueOf r.val (n.val * (n.val + 1) / 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht : target.val = 1)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), IsResidueOf r.val (n.val * (n.val + 1) / 2)) := by
  sorry

/-- Whenever the function returns a result r, r = 4 if target = 3, and r = 3 if target != 3.
  Preconditions: The parameters satisfy 1 <= target <= 10^9 and n = 2. -/
theorem spec_8 (n target : Aeneas.Std.I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hn : n.val = 2)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    if target.val = 3 then r.val = 4 else r.val = 3 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (hn : n.val = 2)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), if target.val = 3 then r.val = 4 else r.val = 3) := by
  sorry

/-- Whenever the function returns a result r, there exists a beautiful array A of length n such that r is the least non-negative residue modulo P of sum_{i=0}^{n-1} A[i].
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Let P = 1000000007. -/
theorem spec_9 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    ∃ A : List ℤ, IsBeautiful n.val.toNat target.val A ∧ IsResidueOf r.val A.sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), ∃ A : List ℤ, IsBeautiful n.val.toNat target.val A ∧ IsResidueOf r.val A.sum) := by
  sorry

/-- Let S be the least possible sum of a beautiful array of length n. Whenever the function returns a result r, r is the least non-negative residue of S modulo 1000000007, and S > n*(n+1)/2.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Let m = floor(target/2). Assume target >= 3 and n > m. -/
theorem spec_10 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht3 : 3 ≤ target.val)
    (hnm : target.val / 2 < n.val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    ∃ S : ℤ,
      IsMinimumSum n.val.toNat target.val S ∧
        IsResidueOf r.val S ∧ n.val * (n.val + 1) / 2 < S := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht3 : 3 ≤ target.val)
    (hnm : target.val / 2 < n.val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), ∃ S : ℤ,
      IsMinimumSum n.val.toNat target.val S ∧
        IsResidueOf r.val S ∧ n.val * (n.val + 1) / 2 < S) := by
  sorry

/-- Whenever the function returns a result r, r is the unique integer with 0 <= r < P and r congruent modulo P to (n*n + 3*n - 2)/2.
  Preconditions: The parameters satisfy 1 <= n <= 10^9 and 1 <= target <= 10^9. Assume target = 3. Let P = 1000000007. -/
theorem spec_11 (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht : target.val = 3)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r) :
    IsResidueOf r.val ((n.val * n.val + 3 * n.val - 2) / 2) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n target : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 9)
    (ht1 : 1 ≤ target.val) (ht2 : target.val ≤ 10 ^ 9)
    (ht : target.val = 3)
    (r : Aeneas.Std.I64)
    (hr : Aegis.MinimumPossibleSum.minimum_possible_sum n target = ok r), IsResidueOf r.val ((n.val * n.val + 3 * n.val - 2) / 2)) := by
  sorry

end AegisSpec.MinimumPossibleSum
