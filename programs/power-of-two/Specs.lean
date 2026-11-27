import Aegis.IsPowerOfTwo.Code.Funs

/-!
# Specifications of `Aegis.IsPowerOfTwo.is_power_of_two`

LeetCode problem `power-of-two`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsPowerOfTwo

  def bitCount (x : ℕ) : ℕ := (Nat.bits x).count true

  /-- The function returns a result r and does not fail; moreover r = true if and only if there exists an integer k with 0 <= k <= 30 such that n = 2^k. In particular, r = false exactly when no such k exists (this includes n <= 0 and all positive non-powers of two).
    Preconditions: -2^31 <= n <= 2^31 - 1 (the constraint from the problem, interpreted as the mathematical value of the i64 n). -/
  theorem spec_1 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) :
      ∃ r : Bool, Aegis.IsPowerOfTwo.is_power_of_two n = ok r ∧
        (r = true ↔ ∃ k : ℕ, k ≤ 30 ∧ n.val = (2:ℤ)^k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1), ∃ r : Bool, Aegis.IsPowerOfTwo.is_power_of_two n = ok r ∧
          (r = true ↔ ∃ k : ℕ, k ≤ 30 ∧ n.val = (2:ℤ)^k)) := by
    sorry

  /-- For every 64-bit integer n, the function returns a result (it does not overflow, panic, or get stuck), whether or not n lies in the problem constraint interval.
    Preconditions: none (n is an arbitrary Std.I64 value). -/
  theorem spec_2 (n : Std.I64) :
      ∃ r : Bool, Aegis.IsPowerOfTwo.is_power_of_two n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64), ∃ r : Bool, Aegis.IsPowerOfTwo.is_power_of_two n = ok r) := by
    sorry

  /-- The function returns false.
    Preconditions: -2^31 <= n <= 2^31 - 1 and n <= 0. -/
  theorem spec_3 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) (hnp : n.val ≤ 0) :
      Aegis.IsPowerOfTwo.is_power_of_two n = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) (hnp : n.val ≤ 0), Aegis.IsPowerOfTwo.is_power_of_two n = ok false) := by
    sorry

  /-- For every integer k with 0 <= k <= 30, if n = 2^k (as mathematical integers), then the function returns true.
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_4 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
      (k : ℕ) (hk : k ≤ 30) (hnk : n.val = (2:ℤ)^k) :
      Aegis.IsPowerOfTwo.is_power_of_two n = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
        (k : ℕ) (hk : k ≤ 30) (hnk : n.val = (2:ℤ)^k), Aegis.IsPowerOfTwo.is_power_of_two n = ok true) := by
    sorry

  /-- Whenever the function returns r = true, the mathematical value of n satisfies 1 <= n <= 2^30.
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_5 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
      (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true) :
      1 ≤ n.val ∧ n.val ≤ (2:ℤ)^30 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
        (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true), 1 ≤ n.val ∧ n.val ≤ (2:ℤ)^30) := by
    sorry

  /-- Whenever the function returns r = true, there exists an integer k with 0 <= k <= 30 such that n = 2^k.
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_6 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
      (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true) :
      ∃ k : ℕ, k ≤ 30 ∧ n.val = (2:ℤ)^k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
        (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true), ∃ k : ℕ, k ≤ 30 ∧ n.val = (2:ℤ)^k) := by
    sorry

  /-- The function returns true for n if and only if n is even and the function returns true for n / 2, where / denotes integer division (floor division, which equals exact division when n is even).
    Preconditions: -2^31 <= n <= 2^31 - 1 and n > 1. -/
  theorem spec_7 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) (hgt : 1 < n.val) :
      (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
        (n.val % 2 = 0 ∧
          ∃ m : Std.I64, m.val = n.val.fdiv 2 ∧
            Aegis.IsPowerOfTwo.is_power_of_two m = ok true)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) (hgt : 1 < n.val), (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
          (n.val % 2 = 0 ∧
            ∃ m : Std.I64, m.val = n.val.fdiv 2 ∧
              Aegis.IsPowerOfTwo.is_power_of_two m = ok true))) := by
    sorry

  /-- The function returns true if and only if n > 0 and the binary representation of the mathematical value of n contains exactly one bit equal to 1; equivalently, n > 0 and n & (n - 1) = 0 using 64-bit bitwise AND.
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_8 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) :
      (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
          (0 < n.val ∧ bitCount n.val.toNat = 1)) ∧
        (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
          (0 < n.val ∧ n.bv &&& (n.bv - 1) = 0)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1), (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
            (0 < n.val ∧ bitCount n.val.toNat = 1)) ∧
          (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
            (0 < n.val ∧ n.bv &&& (n.bv - 1) = 0))) := by
    sorry

  /-- The function returns true if and only if n > 0 and every prime number p that divides the mathematical value of n satisfies p = 2. For n = 1 there are no such primes, so the condition is true.
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_9 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1) :
      (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
        (0 < n.val ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n.val → p = 2)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1), (Aegis.IsPowerOfTwo.is_power_of_two n = ok true ↔
          (0 < n.val ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n.val → p = 2))) := by
    sorry

  /-- Whenever the function returns r = true and n != 1, the mathematical value of n is even (n mod 2 = 0).
    Preconditions: -2^31 <= n <= 2^31 - 1. -/
  theorem spec_10 (n : Std.I64)
      (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
      (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true)
      (hne : n.val ≠ 1) :
      n.val % 2 = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64)
        (hlo : -(2:ℤ)^31 ≤ n.val) (hhi : n.val ≤ (2:ℤ)^31 - 1)
        (r : Bool) (hr : Aegis.IsPowerOfTwo.is_power_of_two n = ok r) (hrt : r = true)
        (hne : n.val ≠ 1), n.val % 2 = 0) := by
    sorry

  end AegisSpec.IsPowerOfTwo
