import Aegis.ReachNumber.Code.Funs

/-!
# Specifications of `Aegis.ReachNumber.reach_number`

LeetCode problem `reach-a-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReachNumber

  def T (n : ℤ) : ℤ := n * (n + 1) / 2

  def IsLeastReach (a n : ℤ) : Prop :=
    0 ≤ n ∧ a ≤ T n ∧ Even (T n - a) ∧
      ∀ m : ℤ, 0 ≤ m → m < n → ¬ (a ≤ T m ∧ Even (T m - a))

  def IsLeastT (a n : ℤ) : Prop :=
    0 ≤ n ∧ a ≤ T n ∧ ∀ m : ℤ, 0 ≤ m → m < n → T m < a

  /-- Let a = |target| and T(n) = n(n+1)/2 for n >= 0. The function returns a result r, and r is the least integer n >= 0 such that T(n) >= a and T(n) - a is even.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_1 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∃ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r ∧ IsLeastReach |target.val| r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∃ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r ∧ IsLeastReach |target.val| r.val) := by
    sorry

  /-- For every target satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_2 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∃ r : Std.I64, Aegis.ReachNumber.reach_number target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∃ r : Std.I64, Aegis.ReachNumber.reach_number target = ok r) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, T(r) >= |target|, where T(n) = n(n+1)/2.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_3 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → |target.val| ≤ T r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → |target.val| ≤ T r.val) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, T(r) and |target| have the same parity (equivalently, T(r) - |target| is even), where T(n) = n(n+1)/2.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_4 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → Even (T r.val - |target.val|) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → Even (T r.val - |target.val|)) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, for every integer n with 0 <= n < r, either T(n) < |target| or T(n) - |target| is odd, where T(n) = n(n+1)/2.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_5 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r →
          ∀ n : ℤ, 0 ≤ n → n < r.val → T n < |target.val| ∨ Odd (T n - |target.val|) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r →
            ∀ n : ℤ, 0 ≤ n → n < r.val → T n < |target.val| ∨ Odd (T n - |target.val|)) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r <= |target| + 2.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_6 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → r.val ≤ |target.val| + 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → r.val ≤ |target.val| + 2) := by
    sorry

  /-- Let N be the least integer n >= 0 such that T(n) >= |target|, where T(n) = n(n+1)/2. Whenever the function returns a result r under the preconditions, r is equal to N, N+1, or N+2.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_7 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ (N : ℤ), IsLeastT |target.val| N →
        ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r →
            r.val = N ∨ r.val = N + 1 ∨ r.val = N + 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ (N : ℤ), IsLeastT |target.val| N →
          ∀ r : Std.I64,
            Aegis.ReachNumber.reach_number target = ok r →
              r.val = N ∨ r.val = N + 1 ∨ r.val = N + 2) := by
    sorry

  /-- If the function returns r on input target and returns r' on input -target, then r = r'.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_8 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ (target' : Std.I64), target'.val = -target.val →
        ∀ r r' : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r →
            Aegis.ReachNumber.reach_number target' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ (target' : Std.I64), target'.val = -target.val →
          ∀ r r' : Std.I64,
            Aegis.ReachNumber.reach_number target = ok r →
              Aegis.ReachNumber.reach_number target' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, there exist signs epsilon_1, ..., epsilon_r, each equal to -1 or +1, such that sum_{i=1}^r epsilon_i * i = target.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_9 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r →
          ∃ ε : List ℤ,
            ε.length = r.val.toNat ∧ (∀ e ∈ ε, e = 1 ∨ e = -1) ∧
              (ε.mapIdx fun i e => e * ((i : ℤ) + 1)).sum = target.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r →
            ∃ ε : List ℤ,
              ε.length = r.val.toNat ∧ (∀ e ∈ ε, e = 1 ∨ e = -1) ∧
                (ε.mapIdx fun i e => e * ((i : ℤ) + 1)).sum = target.val) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r = 1 if and only if |target| = 1.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_10 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → (r.val = 1 ↔ |target.val| = 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → (r.val = 1 ↔ |target.val| = 1)) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r = 2 if and only if |target| = 3.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_11 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → (r.val = 2 ↔ |target.val| = 3) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → (r.val = 2 ↔ |target.val| = 3)) := by
    sorry

  /-- Whenever the function returns a result r under the preconditions, r <= 44723.
    Preconditions: target is an integer with -1000000000 <= target <= 1000000000 and target != 0. -/
  theorem spec_12 (target : Std.I64)
      (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
      (hne : target.val ≠ 0) :
      ∀ r : Std.I64,
        Aegis.ReachNumber.reach_number target = ok r → r.val ≤ 44723 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (target : Std.I64)
        (hlo : -1000000000 ≤ target.val) (hhi : target.val ≤ 1000000000)
        (hne : target.val ≠ 0), ∀ r : Std.I64,
          Aegis.ReachNumber.reach_number target = ok r → r.val ≤ 44723) := by
    sorry

  end AegisSpec.ReachNumber
