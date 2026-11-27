import Aegis.MinimumHealth.Code.Funs

/-!
# Specifications of `Aegis.MinimumHealth.minimum_health`

LeetCode problem `minimum-health-to-beat-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.MinimumHealth (minimum_health)

namespace AegisSpec.MinimumHealth

def vals (damage : Slice Std.I64) : List ℤ := damage.val.map (fun d => d.val)

def dmg (damage : Slice Std.I64) (i : ℕ) : ℤ := (vals damage).getD i 0

def sumDamage (damage : Slice Std.I64) : ℤ := (vals damage).sum

def maxDamage (damage : Slice Std.I64) : ℤ := (vals damage).foldr max 0

def bestProtection (damage : Slice Std.I64) (armor : ℤ) : ℤ :=
  (vals damage).foldr (fun d acc => max (min d armor) acc) 0

def healthAfter (damage : Slice Std.I64) (H : ℤ) (j : ℕ) (p : ℤ) : ℕ → ℤ
  | 0 => H
  | k + 1 => healthAfter damage H j p k - (dmg damage k - if k = j then p else 0)

inductive ArmorUsage where

  | none : ArmorUsage

  | one (j : ℕ) (p : ℤ) : ArmorUsage

def IsLegalUsage (damage : Slice Std.I64) (armor : ℤ) (n : ℕ) : ArmorUsage → Prop
  | .none => True
  | .one j p => j < n ∧ 0 ≤ p ∧ p ≤ min (dmg damage j) armor

def finalHealth (damage : Slice Std.I64) (H : ℤ) : ArmorUsage → ℤ
  | .none => H - sumDamage damage
  | .one _ p => H - sumDamage damage + p

def IsPermutationOf (damage damage' : Slice Std.I64) (n : ℕ) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ i : Fin n, dmg damage' (e i).val = dmg damage i.val

/-- Let S = sum_{i=0}^{n-1} damage[i] and P = max_{0 <= i < n} min(damage[i], armor). The function returns a result r and r = 1 + S - P.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_1 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + sumDamage damage - bestProtection damage armor.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + sumDamage damage - bestProtection damage armor.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_2 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_3 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} damage[i]. The function returns a result r and r <= 1 + S.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_4 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val ≤ 1 + sumDamage damage := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val ≤ 1 + sumDamage damage) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} damage[i]. The function returns a result r and for every i with 0 <= i < n, r <= 1 + S - min(damage[i], armor).
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_5 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∀ i, i < n → r.val ≤ 1 + sumDamage damage - min (dmg damage i) armor.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∀ i, i < n → r.val ≤ 1 + sumDamage damage - min (dmg damage i) armor.val) := by
  sorry

/-- Let S = sum_{i=0}^{n-1} damage[i]. The function returns a result r and there exists j with 0 <= j < n such that r = 1 + S - min(damage[j], armor).
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_6 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∃ j : ℕ, j < n ∧ r.val = 1 + sumDamage damage - min (dmg damage j) armor.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∃ j : ℕ, j < n ∧ r.val = 1 + sumDamage damage - min (dmg damage j) armor.val) := by
  sorry

/-- The function returns a result r and there exists j with 0 <= j < n such that, if the player starts with health r, uses the armor only on level j to block exactly min(damage[j], armor) damage, and uses no armor on all other levels, then after every level t with 0 <= t < n the player's health is greater than 0.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_7 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∃ j : ℕ, j < n ∧ ∀ t : ℕ, t < n →
        0 < healthAfter damage r.val j (min (dmg damage j) armor.val) (t + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∃ j : ℕ, j < n ∧ ∀ t : ℕ, t < n →
        0 < healthAfter damage r.val j (min (dmg damage j) armor.val) (t + 1)) := by
  sorry

/-- The function returns a result r and, for every integer H with H < r and every armor usage consisting either of no armor or of one choice of a level j with 0 <= j < n and a protected amount p with 0 <= p <= min(damage[j], armor), the health value obtained by starting at H and subtracting the net damage of all n levels is at most 0.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_8 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∀ H : ℤ, H < r.val → ∀ u : ArmorUsage,
        IsLegalUsage damage armor.val n u → finalHealth damage H u ≤ 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      ∀ H : ℤ, H < r.val → ∀ u : ArmorUsage,
        IsLegalUsage damage armor.val n u → finalHealth damage H u ≤ 0) := by
  sorry

/-- If armor = 0, then the function returns a result r and r = 1 + sum_{i=0}^{n-1} damage[i].
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_9 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (ha_zero : armor.val = 0) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧ r.val = 1 + sumDamage damage := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (ha_zero : armor.val = 0), ∃ r : Std.I64, minimum_health damage armor = ok r ∧ r.val = 1 + sumDamage damage) := by
  sorry

/-- If armor >= max_{0 <= i < n} damage[i], then the function returns a result r and r = 1 + sum_{i=0}^{n-1} damage[i] - max_{0 <= i < n} damage[i].
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_10 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (ha_big : ∀ i, i < n → dmg damage i ≤ armor.val) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + sumDamage damage - maxDamage damage := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (ha_big : ∀ i, i < n → dmg damage i ≤ armor.val), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + sumDamage damage - maxDamage damage) := by
  sorry

/-- If damage[i] = 0 for every i with 0 <= i < n, then the function returns a result r and r = 1.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_11 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hd_zero : ∀ i, i < n → dmg damage i = 0) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧ r.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hd_zero : ∀ i, i < n → dmg damage i = 0), ∃ r : Std.I64, minimum_health damage armor = ok r ∧ r.val = 1) := by
  sorry

/-- If n = 1, then the function returns a result r and r = 1 + max(0, damage[0] - armor).
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_12 (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hn_one : n = 1) :
    ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + max 0 (dmg damage 0 - armor.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (damage : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hn_one : n = 1), ∃ r : Std.I64, minimum_health damage armor = ok r ∧
      r.val = 1 + max 0 (dmg damage 0 - armor.val)) := by
  sorry

/-- If the function returns r1 on input (damage, a1) and returns r2 on input (damage, a2), then r1 >= r2.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; and 0 <= a1 <= a2 <= 100000. -/
theorem spec_13 (damage : Slice Std.I64) (a1 a2 : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha1_lo : 0 ≤ a1.val) (ha_le : a1.val ≤ a2.val) (ha2_hi : a2.val ≤ 100000) :
    ∀ r1 r2 : Std.I64,
      minimum_health damage a1 = ok r1 → minimum_health damage a2 = ok r2 →
        r2.val ≤ r1.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (damage : Slice Std.I64) (a1 a2 : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha1_lo : 0 ≤ a1.val) (ha_le : a1.val ≤ a2.val) (ha2_hi : a2.val ≤ 100000), ∀ r1 r2 : Std.I64,
      minimum_health damage a1 = ok r1 → minimum_health damage a2 = ok r2 →
        r2.val ≤ r1.val) := by
  sorry

/-- If the function returns r1 on input (d1, armor) and returns r2 on input (d2, armor), then r1 <= r2.
  Preconditions: n = len(d1) = len(d2); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= d1[i] <= d2[i] <= 100000; and 0 <= armor <= 100000. -/
theorem spec_14 (d1 d2 : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : d1.val.length = n) (hn2 : d2.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd1_lo : ∀ i, i < n → 0 ≤ dmg d1 i)
    (hd1_le : ∀ i, i < n → dmg d1 i ≤ dmg d2 i)
    (hd2_hi : ∀ i, i < n → dmg d2 i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000) :
    ∀ r1 r2 : Std.I64,
      minimum_health d1 armor = ok r1 → minimum_health d2 armor = ok r2 →
        r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (d1 d2 : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : d1.val.length = n) (hn2 : d2.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd1_lo : ∀ i, i < n → 0 ≤ dmg d1 i)
    (hd1_le : ∀ i, i < n → dmg d1 i ≤ dmg d2 i)
    (hd2_hi : ∀ i, i < n → dmg d2 i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000), ∀ r1 r2 : Std.I64,
      minimum_health d1 armor = ok r1 → minimum_health d2 armor = ok r2 →
        r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r on input (damage, armor) and returns r' on input (damage', armor), then r' = r.
  Preconditions: n = len(damage); 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= damage[i] <= 100000; 0 <= armor <= 100000; damage' is an array with len(damage') = n and is a permutation of damage, meaning there is a bijection f from {0,...,n-1} to itself with damage'[f(i)] = damage[i] for every i. -/
theorem spec_15 (damage damage' : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn' : damage'.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hperm : IsPermutationOf damage damage' n) :
    ∀ r r' : Std.I64,
      minimum_health damage armor = ok r → minimum_health damage' armor = ok r' →
        r'.val = r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (damage damage' : Slice Std.I64) (armor : Std.I64) (n : ℕ)
    (hn : damage.val.length = n) (hn' : damage'.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hd_lo : ∀ i, i < n → 0 ≤ dmg damage i)
    (hd_hi : ∀ i, i < n → dmg damage i ≤ 100000)
    (ha_lo : 0 ≤ armor.val) (ha_hi : armor.val ≤ 100000)
    (hperm : IsPermutationOf damage damage' n), ∀ r r' : Std.I64,
      minimum_health damage armor = ok r → minimum_health damage' armor = ok r' →
        r'.val = r.val) := by
  sorry

end AegisSpec.MinimumHealth
