import Aegis.KItemsWithMaximumSum.Code.Funs

/-!
# Specifications of `Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum`

LeetCode problem `k-items-with-the-maximum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KItemsWithMaximumSum

  /-- The function returns Result.ok r, where r = min(k, numOnes) - max(0, k - numOnes - numZeros).
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_1
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∃ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r ∧
          r.val = min k.val numOnes.val - max 0 (k.val - numOnes.val - numZeros.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∃ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r ∧
            r.val = min k.val numOnes.val - max 0 (k.val - numOnes.val - numZeros.val)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns Result.ok r for some integer r; in particular, it does not overflow, panic, or fail.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_2
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∃ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
          = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∃ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r) := by
    sorry

  /-- Whenever the function returns Result.ok r, we have r <= numOnes.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_3
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          r.val ≤ numOnes.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            r.val ≤ numOnes.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, we have r <= k.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_4
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          r.val ≤ k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            r.val ≤ k.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, we have r >= -k.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_5
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          -k.val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            -k.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, we have r >= -min(k, numNegOnes).
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_6
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          -min k.val numNegOnes.val ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            -min k.val numNegOnes.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns Result.ok r, there exist integers a, b, c such that 0 <= a <= numOnes, 0 <= b <= numZeros, 0 <= c <= numNegOnes, a + b + c = k, and r = a - c.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_7
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          ∃ a b c : ℤ,
            0 ≤ a ∧ a ≤ numOnes.val ∧
              0 ≤ b ∧ b ≤ numZeros.val ∧
                0 ≤ c ∧ c ≤ numNegOnes.val ∧ a + b + c = k.val ∧ r.val = a - c := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            ∃ a b c : ℤ,
              0 ≤ a ∧ a ≤ numOnes.val ∧
                0 ≤ b ∧ b ≤ numZeros.val ∧
                  0 ≤ c ∧ c ≤ numNegOnes.val ∧ a + b + c = k.val ∧ r.val = a - c) := by
    sorry

  /-- Whenever the function returns Result.ok r, for every integers a, b, c with 0 <= a <= numOnes, 0 <= b <= numZeros, 0 <= c <= numNegOnes, and a + b + c = k, we have a - c <= r.
    Preconditions: numOnes, numZeros, numNegOnes, and k are integers with 0 <= numOnes <= 50, 0 <= numZeros <= 50, 0 <= numNegOnes <= 50, and 0 <= k <= numOnes + numZeros + numNegOnes. -/
  theorem spec_8
      (numOnes numZeros numNegOnes k : Std.I64)
      (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
      (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
      (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
      (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val) :
      ∀ r : Std.I64,
        Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
            = Result.ok r →
          ∀ a b c : ℤ,
            0 ≤ a → a ≤ numOnes.val →
              0 ≤ b → b ≤ numZeros.val →
                0 ≤ c → c ≤ numNegOnes.val → a + b + c = k.val → a - c ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (numOnes numZeros numNegOnes k : Std.I64)
        (hOnes : 0 ≤ numOnes.val ∧ numOnes.val ≤ 50)
        (hZeros : 0 ≤ numZeros.val ∧ numZeros.val ≤ 50)
        (hNegOnes : 0 ≤ numNegOnes.val ∧ numNegOnes.val ≤ 50)
        (hk : 0 ≤ k.val ∧ k.val ≤ numOnes.val + numZeros.val + numNegOnes.val), ∀ r : Std.I64,
          Aegis.KItemsWithMaximumSum.k_items_with_maximum_sum numOnes numZeros numNegOnes k
              = Result.ok r →
            ∀ a b c : ℤ,
              0 ≤ a → a ≤ numOnes.val →
                0 ≤ b → b ≤ numZeros.val →
                  0 ≤ c → c ≤ numNegOnes.val → a + b + c = k.val → a - c ≤ r.val) := by
    sorry

  end AegisSpec.KItemsWithMaximumSum
