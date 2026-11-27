import Aegis.MinimumNumbers.Code.Funs

/-!
# Specifications of `Aegis.MinimumNumbers.minimum_numbers`

LeetCode problem `sum-of-numbers-with-units-digit-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumNumbers

def IsCandidateMultiset (num k : ℤ) (M : Multiset ℤ) : Prop :=
  (∀ x ∈ M, 0 < x) ∧ (∀ x ∈ M, x % 10 = k) ∧ M.sum = num

def IsCandidateCount (num k t : ℤ) : Prop :=
  0 < t ∧ t * k ≤ num ∧ (t * k) % 10 = num % 10

/-- The function returns a result r and r is the minimum possible size of a finite multiset M of positive integers such that every x in M satisfies x mod 10 = k and sum(M) = num, where the empty multiset is allowed and has size 0 and sum 0; if no such multiset exists, then r = -1.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_1 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      ((∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M) →
        (0 ≤ r.val ∧
          ∃ M : Multiset ℤ,
            IsCandidateMultiset num.val k.val M ∧ r.val = (M.card : ℤ) ∧
              ∀ M' : Multiset ℤ, IsCandidateMultiset num.val k.val M' →
                r.val ≤ (M'.card : ℤ))) ∧
      ((¬ ∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      ((∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M) →
        (0 ≤ r.val ∧
          ∃ M : Multiset ℤ,
            IsCandidateMultiset num.val k.val M ∧ r.val = (M.card : ℤ) ∧
              ∀ M' : Multiset ℤ, IsCandidateMultiset num.val k.val M' →
                r.val ≤ (M'.card : ℤ))) ∧
      ((¬ ∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M) → r.val = -1)) := by
  sorry

/-- The function returns a result r and r = 1 if and only if num > 0 and num mod 10 = k.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_2 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val = 1 ↔ 0 < num.val ∧ num.val % 10 = k.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val = 1 ↔ 0 < num.val ∧ num.val % 10 = k.val)) := by
  sorry

/-- The function returns a result r and, if k = 0 and num > 0, then r = 1 when num mod 10 = 0, and r = -1 otherwise.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_3 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (k.val = 0 → 0 < num.val →
        ((num.val % 10 = 0 → r.val = 1) ∧ (num.val % 10 ≠ 0 → r.val = -1))) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (k.val = 0 → 0 < num.val →
        ((num.val % 10 = 0 → r.val = 1) ∧ (num.val % 10 ≠ 0 → r.val = -1)))) := by
  sorry

/-- The function returns a result r and, if r >= 0 and num > 0, then 1 <= r <= 10.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_4 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → 0 < num.val → 1 ≤ r.val ∧ r.val ≤ 10) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → 0 < num.val → 1 ≤ r.val ∧ r.val ≤ 10)) := by
  sorry

/-- The function returns a result r and, if r >= 0, then (r * k) mod 10 = num mod 10.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_5 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → (r.val * k.val) % 10 = num.val % 10) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → (r.val * k.val) % 10 = num.val % 10)) := by
  sorry

/-- The function returns a result r and, if k > 0 and r > 0, then r * k <= num.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_6 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < k.val → 0 < r.val → r.val * k.val ≤ num.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < k.val → 0 < r.val → r.val * k.val ≤ num.val)) := by
  sorry

/-- The function returns a result r and, if k = 0 and r > 0, then 10 * r <= num.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_7 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (k.val = 0 → 0 < r.val → 10 * r.val ≤ num.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (k.val = 0 → 0 < r.val → 10 * r.val ≤ num.val)) := by
  sorry

/-- The function returns a result r and, if k > 0 and num > 0, then either (a) there is a positive integer t with t * k <= num and (t * k) mod 10 = num mod 10, and r is the least such t, or (b) no such positive integer t exists, and r = -1.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_8 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < k.val → 0 < num.val →
        ((∃ t : ℤ, IsCandidateCount num.val k.val t ∧ r.val = t ∧
            ∀ t' : ℤ, IsCandidateCount num.val k.val t' → t ≤ t') ∨
          ((¬ ∃ t : ℤ, IsCandidateCount num.val k.val t) ∧ r.val = -1))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < k.val → 0 < num.val →
        ((∃ t : ℤ, IsCandidateCount num.val k.val t ∧ r.val = t ∧
            ∀ t' : ℤ, IsCandidateCount num.val k.val t' → t ≤ t') ∨
          ((¬ ∃ t : ℤ, IsCandidateCount num.val k.val t) ∧ r.val = -1)))) := by
  sorry

/-- The function returns a result r and, if r > 0, then there exist positive integers x_1, ..., x_r such that x_i mod 10 = k for all i with 1 <= i <= r and x_1 + ... + x_r = num.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_9 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < r.val →
        ∃ xs : List ℤ, xs.length = r.val.toNat ∧ (∀ x ∈ xs, 0 < x) ∧
          (∀ x ∈ xs, x % 10 = k.val) ∧ xs.sum = num.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (0 < r.val →
        ∃ xs : List ℤ, xs.length = r.val.toNat ∧ (∀ x ∈ xs, 0 < x) ∧
          (∀ x ∈ xs, x % 10 = k.val) ∧ xs.sum = num.val)) := by
  sorry

/-- The function returns a result r and, if r >= 0, then every finite multiset M of positive integers with sum(M) = num and x mod 10 = k for every x in M satisfies |M| >= r.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_10 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → ∀ M : Multiset ℤ, IsCandidateMultiset num.val k.val M →
        r.val ≤ (M.card : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val ≥ 0 → ∀ M : Multiset ℤ, IsCandidateMultiset num.val k.val M →
        r.val ≤ (M.card : ℤ))) := by
  sorry

/-- The function returns a result r and, if r = -1, then there does not exist a finite multiset M of positive integers such that sum(M) = num and every x in M satisfies x mod 10 = k.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_11 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val = -1 → ¬ ∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r ∧
      (r.val = -1 → ¬ ∃ M : Multiset ℤ, IsCandidateMultiset num.val k.val M)) := by
  sorry

/-- For every num and k satisfying the preconditions, the function returns a result r and does not fail: no integer overflow, out-of-bounds access, or panic occurs.
  Preconditions: The integer values of num and k satisfy 0 <= num <= 3000 and 0 <= k <= 9. -/
theorem spec_12 (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9) :
    ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num k : Std.I64)
    (hnum0 : 0 ≤ num.val) (hnum3000 : num.val ≤ 3000)
    (hk0 : 0 ≤ k.val) (hk9 : k.val ≤ 9), ∃ r, Aegis.MinimumNumbers.minimum_numbers num k = ok r) := by
  sorry

  end AegisSpec.MinimumNumbers
