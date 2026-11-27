import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `apply-operations-to-make-sum-of-array-greater-than-or-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinOperations

  def operations_values (k : ℤ) : Set ℤ :=
    { r | ∃ a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ k ≤ a * b ∧ a + b - 2 = r }

  def IsLeastSqrtCeil (k s : ℤ) : Prop :=
    0 < s ∧ k ≤ s * s ∧ ∀ t : ℤ, 0 < t → k ≤ t * t → s ≤ t

  def IsGreatestSqrtFloor (k s : ℤ) : Prop :=
    0 ≤ s ∧ s * s ≤ k ∧ ∀ t : ℤ, 0 ≤ t → t * t ≤ k → t ≤ s

  /-- The function returns a result r (it does not fail), and r = min { a + b - 2 | a and b are positive integers and a * b >= k }.
    Preconditions: 1 <= k <= 100000 (k is the value of the parameter k). -/
  theorem spec_1 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : Std.I64,
        Aegis.MinOperations.min_operations k = ok r ∧
          IsLeast (operations_values k.val) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64,
          Aegis.MinOperations.min_operations k = ok r ∧
            IsLeast (operations_values k.val) r.val) := by
    sorry

  /-- For every k with 1 <= k <= 100000, the function returns a result r; it does not fail (no overflow, out-of-bounds, panic, or other run-time failure).
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_2 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) :
      ∃ r : Std.I64, Aegis.MinOperations.min_operations k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000), ∃ r : Std.I64, Aegis.MinOperations.min_operations k = ok r) := by
    sorry

  /-- Whenever the function returns a result r on input k, 0 <= r.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_3 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r on input k, (r + 2) * (r + 2) >= 4 * k.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_4 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      (r.val + 2) * (r.val + 2) ≥ 4 * k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), (r.val + 2) * (r.val + 2) ≥ 4 * k.val) := by
    sorry

  /-- Whenever the function returns a result r on input k, if r > 0 then (r + 1) * (r + 1) < 4 * k.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_5 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) (hr0 : r.val > 0) :
      (r.val + 1) * (r.val + 1) < 4 * k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r) (hr0 : r.val > 0), (r.val + 1) * (r.val + 1) < 4 * k.val) := by
    sorry

  /-- Whenever the function returns a result r on input k, r = 0 if and only if k = 1.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_6 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      r.val = 0 ↔ k.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), r.val = 0 ↔ k.val = 1) := by
    sorry

  /-- Whenever the function returns a result r on input k, r <= k - 1.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_7 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      r.val ≤ k.val - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), r.val ≤ k.val - 1) := by
    sorry

  /-- Let s be the least positive integer such that s * s >= k. Whenever the function returns a result r on input k, r <= 2 * s - 2.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_8 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) (s : ℤ)
      (hs : IsLeastSqrtCeil k.val s) :
      r.val ≤ 2 * s - 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r) (s : ℤ)
        (hs : IsLeastSqrtCeil k.val s), r.val ≤ 2 * s - 2) := by
    sorry

  /-- Let s be the greatest integer such that 0 <= s and s * s <= k. Whenever the function returns a result r on input k, r >= 2 * s - 2.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_9 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) (s : ℤ)
      (hs : IsGreatestSqrtFloor k.val s) :
      r.val ≥ 2 * s - 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r) (s : ℤ)
        (hs : IsGreatestSqrtFloor k.val s), r.val ≥ 2 * s - 2) := by
    sorry

  /-- Whenever the function returns a result r on input k, there exist positive integers a and b such that a * b >= k and a + b - 2 = r.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_10 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      ∃ a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ k.val ≤ a * b ∧ a + b - 2 = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), ∃ a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ k.val ≤ a * b ∧ a + b - 2 = r.val) := by
    sorry

  /-- Whenever the function returns a result r on input k, for every pair of positive integers a and b with a * b >= k, we have r <= a + b - 2.
    Preconditions: 1 <= k <= 100000. -/
  theorem spec_11 (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r) :
      ∀ a b : ℤ, 1 ≤ a → 1 ≤ b → k.val ≤ a * b → r.val ≤ a + b - 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000) (r : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r), ∀ a b : ℤ, 1 ≤ a → 1 ≤ b → k.val ≤ a * b → r.val ≤ a + b - 2) := by
    sorry

  /-- If min_operations(k1) returns r1 and min_operations(k2) returns r2, then r1 <= r2.
    Preconditions: 1 <= k1 <= k2 <= 100000. -/
  theorem spec_12 (k1 k2 : Std.I64) (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2 : k2.val ≤ 100000) (r1 r2 : Std.I64)
      (hr1 : Aegis.MinOperations.min_operations k1 = ok r1)
      (hr2 : Aegis.MinOperations.min_operations k2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (k1 k2 : Std.I64) (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2 : k2.val ≤ 100000) (r1 r2 : Std.I64)
        (hr1 : Aegis.MinOperations.min_operations k1 = ok r1)
        (hr2 : Aegis.MinOperations.min_operations k2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If min_operations(k) returns r and min_operations(k + 1) returns r', then r <= r' <= r + 1.
    Preconditions: 1 <= k < 100000. -/
  theorem spec_13 (k k' : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val < 100000)
      (hsucc : k'.val = k.val + 1) (r r' : Std.I64)
      (hr : Aegis.MinOperations.min_operations k = ok r)
      (hr' : Aegis.MinOperations.min_operations k' = ok r') :
      r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (k k' : Std.I64) (hk1 : 1 ≤ k.val) (hk2 : k.val < 100000)
        (hsucc : k'.val = k.val + 1) (r r' : Std.I64)
        (hr : Aegis.MinOperations.min_operations k = ok r)
        (hr' : Aegis.MinOperations.min_operations k' = ok r'), r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
    sorry

  end AegisSpec.MinOperations
