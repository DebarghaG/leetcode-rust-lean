import Aegis.GetMaximumGenerated.Code.Funs

/-!
# Specifications of `Aegis.GetMaximumGenerated.get_maximum_generated`

LeetCode problem `get-maximum-in-generated-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetMaximumGenerated

def gen : Nat → Int
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 2 = 0 then gen ((n + 2) / 2)
      else gen ((n + 2) / 2) + gen ((n + 2) / 2 + 1)
termination_by n => n
decreasing_by
  all_goals
    simp_wf
    omega

def IsMaxUpTo (m : Nat) (r : Int) : Prop :=
  (∃ i : Nat, i ≤ m ∧ r = gen i) ∧ ∀ i : Nat, i ≤ m → gen i ≤ r

/-- Let f : Nat -> Int be the unique function with f(0)=0, f(1)=1, and for every integer k >= 1, f(2*k)=f(k) and f(2*k+1)=f(k)+f(k+1). The function returns a result r, and r = max_{0 <= i <= n} f(i); equivalently, there exists i0 with 0 <= i0 <= n and r = f(i0), and for every i with 0 <= i <= n, f(i) <= r.
  Preconditions: 0 <= n <= 100, with n regarded as a natural number. -/
theorem spec_1 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ IsMaxUpTo n.val.toNat r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ IsMaxUpTo n.val.toNat r.val) := by
  sorry

/-- The function returns a result r; it does not overflow, panic, or access an out-of-bounds index.
  Preconditions: 0 <= n <= 100. -/
theorem spec_2 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: 0 <= n <= 100. -/
theorem spec_3 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= n.
  Preconditions: 0 <= n <= 100. -/
theorem spec_4 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: 1 <= n <= 100. -/
theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: n = 0. -/
theorem spec_6 (n : Std.I64) (hn : n.val = 0) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 0), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: n = 1. -/
theorem spec_7 (n : Std.I64) (hn : n.val = 1) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r = 2.
  Preconditions: n = 3. -/
theorem spec_8 (n : Std.I64) (hn : n.val = 3) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 3), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 2) := by
  sorry

/-- The function returns a result r and r = 21.
  Preconditions: n = 100. -/
theorem spec_9 (n : Std.I64) (hn : n.val = 100) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 21 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 21) := by
  sorry

/-- Let f : Nat -> Int be the unique function with f(0)=0, f(1)=1, and for every integer k >= 1, f(2*k)=f(k) and f(2*k+1)=f(k)+f(k+1). The function returns a result r, and there exists an index i with 0 <= i <= n such that r = f(i).
  Preconditions: 0 <= n <= 100. -/
theorem spec_10 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧
        ∃ i : Nat, i ≤ n.val.toNat ∧ r.val = gen i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧
        ∃ i : Nat, i ≤ n.val.toNat ∧ r.val = gen i) := by
  sorry

/-- Let f : Nat -> Int be the unique function with f(0)=0, f(1)=1, and for every integer k >= 1, f(2*k)=f(k) and f(2*k+1)=f(k)+f(k+1). The function returns a result r, and for every i with 0 <= i <= n, f(i) <= r.
  Preconditions: 0 <= n <= 100. -/
theorem spec_11 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) :
    ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧
        ∀ i : Nat, i ≤ n.val.toNat → gen i ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100), ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧
        ∀ i : Nat, i ≤ n.val.toNat → gen i ≤ r.val) := by
  sorry

/-- Let f : Nat -> Int be the unique function with f(0)=0, f(1)=1, and for every integer k >= 1, f(2*k)=f(k) and f(2*k+1)=f(k)+f(k+1). The function returns a result r, and r = max_{0 <= i <= n-1} f(i).
  Preconditions: 0 <= n <= 100, n is even, and n >= 2. -/
theorem spec_12 (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) (hpar : n.val % 2 = 0)
    (hge : 2 ≤ n.val) :
    ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ IsMaxUpTo (n.val.toNat - 1) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn : 0 ≤ n.val) (hn' : n.val ≤ 100) (hpar : n.val % 2 = 0)
    (hge : 2 ≤ n.val), ∃ r : Std.I64,
      Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ IsMaxUpTo (n.val.toNat - 1) r.val) := by
  sorry

/-- The function returns a result r and r = 3.
  Preconditions: n = 7. -/
theorem spec_13 (n : Std.I64) (hn : n.val = 7) :
    ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 3 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 7), ∃ r : Std.I64, Aegis.GetMaximumGenerated.get_maximum_generated n = ok r ∧ r.val = 3) := by
  sorry

end AegisSpec.GetMaximumGenerated
