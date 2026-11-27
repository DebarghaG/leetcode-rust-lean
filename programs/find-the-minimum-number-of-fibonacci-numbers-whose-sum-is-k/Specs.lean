import Aegis.FindMinFibonacciNumbers.Code.Funs
import Mathlib.Data.Nat.Fib.Basic

/-!
# Specifications of `Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers`

LeetCode problem `find-the-minimum-number-of-fibonacci-numbers-whose-sum-is-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMinFibonacciNumbers

def IsPosFib (x : Int) : Prop := ∃ n : Nat, 1 ≤ n ∧ (Nat.fib n : Int) = x

def IsFibSum (t : Nat) (k : Int) : Prop :=
  ∃ a : List Int, a.length = t ∧ (∀ x ∈ a, IsPosFib x) ∧ a.sum = k

def IsLeastFibSumCount (k : Int) (t : Nat) : Prop :=
  IsFibSum t k ∧ ∀ s : Nat, IsFibSum s k → t ≤ s

noncomputable def C (x : Int) : Nat := sInf {t : Nat | IsFibSum t x}

theorem isPosFib_fib (n : Nat) (hn : 1 ≤ n) : IsPosFib (Nat.fib n) := ⟨n, hn, rfl⟩

theorem isPosFib_one : IsPosFib 1 := ⟨1, le_rfl, by simp [Nat.fib_one]⟩

theorem C_zero : C 0 = 0 := by
  unfold C
  refine Nat.le_antisymm (Nat.sInf_le ?_) (Nat.zero_le _)
  exact ⟨[], rfl, by simp, by simp⟩

/-- The function returns a result r, and r is the minimum t >= 0 such that there exist t (not necessarily distinct) positive Fibonacci numbers whose sum is k. A positive Fibonacci number is an integer F_n with n >= 1, where F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2. Repetitions among the t summands are allowed.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_1 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∃ t : Nat, r.val = (t : Int) ∧ IsLeastFibSumCount k.val t := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∃ t : Nat, r.val = (t : Int) ∧ IsLeastFibSumCount k.val t) := by
  sorry

/-- For every k satisfying the precondition, the function returns a result r and does not fail: in particular, it does not overflow, panic, or otherwise terminate with an error.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_2 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r) := by
  sorry

/-- The function returns a result r, and there are r (not necessarily distinct) positive Fibonacci numbers a_1, ..., a_r (where F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2) such that a_1 + ... + a_r = k.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_3 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∃ t : Nat, r.val = (t : Int) ∧ IsFibSum t k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∃ t : Nat, r.val = (t : Int) ∧ IsFibSum t k.val) := by
  sorry

/-- The function returns a result r, and for every integer m with 0 <= m < r there do not exist m (not necessarily distinct) positive Fibonacci numbers whose sum is k, using F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_4 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∀ m : Nat, (m : Int) < r.val → ¬ IsFibSum m k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∀ m : Nat, (m : Int) < r.val → ¬ IsFibSum m k.val) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_5 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= k.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_6 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val ≤ k.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val ≤ k.val) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: k is an integer with 1 <= k <= 10^9, and k is a positive Fibonacci number: k = F_n for some n >= 1, where F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2. -/
theorem spec_7 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9)
    (hk_fib : IsPosFib k.val) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9)
    (hk_fib : IsPosFib k.val), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r >= 2.
  Preconditions: k is an integer with 1 <= k <= 10^9, and k is not a positive Fibonacci number, where F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2. -/
theorem spec_8 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9)
    (hk_not_fib : ¬ IsPosFib k.val) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ 2 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9)
    (hk_not_fib : ¬ IsPosFib k.val), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ 2 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = 2 if and only if k is the sum of two (not necessarily distinct) positive Fibonacci numbers (F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2) and k is not itself a positive Fibonacci number.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_9 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (r.val = 2 ↔ IsFibSum 2 k.val ∧ ¬ IsPosFib k.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (r.val = 2 ↔ IsFibSum 2 k.val ∧ ¬ IsPosFib k.val)) := by
  sorry

/-- Let C(x), for every integer x >= 0, be the minimum number of (not necessarily distinct) positive Fibonacci numbers (F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2) whose sum is x, with C(0) = 0. The function returns a result r and r = min { 1 + C(k - f) : f is a positive Fibonacci number and f <= k }.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_10 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (∀ f : Int, IsPosFib f → f ≤ k.val → r.val ≤ 1 + (C (k.val - f) : Int)) ∧
        ∃ f : Int, IsPosFib f ∧ f ≤ k.val ∧ r.val = 1 + (C (k.val - f) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (∀ f : Int, IsPosFib f → f ≤ k.val → r.val ≤ 1 + (C (k.val - f) : Int)) ∧
        ∃ f : Int, IsPosFib f ∧ f ≤ k.val ∧ r.val = 1 + (C (k.val - f) : Int)) := by
  sorry

/-- For every integer t >= 0 such that k can be written as the sum of t (not necessarily distinct) positive Fibonacci numbers (F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2), the function returns a result r and r <= t.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_11 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∀ t : Nat, IsFibSum t k.val → r.val ≤ (t : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        ∀ t : Nat, IsFibSum t k.val → r.val ≤ (t : Int)) := by
  sorry

/-- The function returns a result r and r <= 22.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_12 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val ≤ 22 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧ r.val ≤ 22) := by
  sorry

/-- The function returns a result r, and r >= 3 if and only if k is not a positive Fibonacci number and k is not the sum of two (not necessarily distinct) positive Fibonacci numbers, using F_1 = F_2 = 1 and F_n = F_{n-1} + F_{n-2} for n > 2.
  Preconditions: k is an integer with 1 <= k <= 10^9. -/
theorem spec_13 (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (3 ≤ r.val ↔ ¬ IsPosFib k.val ∧ ¬ IsFibSum 2 k.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (k : Std.I64) (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindMinFibonacciNumbers.find_min_fibonacci_numbers k = ok r ∧
        (3 ≤ r.val ↔ ¬ IsPosFib k.val ∧ ¬ IsFibSum 2 k.val)) := by
  sorry

end AegisSpec.FindMinFibonacciNumbers
