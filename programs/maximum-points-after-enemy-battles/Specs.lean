import Aegis.MaximumPoints.Code.Funs

/-!
# Specifications of `Aegis.MaximumPoints.maximum_points`

LeetCode problem `maximum-points-after-enemy-battles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumPoints

def energies (enemyEnergies : Slice Std.I64) : List Int :=
  enemyEnergies.val.map (fun x => x.val)

def minEnergy (enemyEnergies : Slice Std.I64) : Int :=
  match energies enemyEnergies with
  | [] => 0
  | a :: l => l.foldr min a

def sumEnergy (enemyEnergies : Slice Std.I64) : Int :=
  (energies enemyEnergies).sum

structure GameState where

  points : Int

  energy : Int

  marked : Nat → Bool

def enemyEnergy (enemies : List Int) (i : Nat) : Int :=
  enemies.getD i 0

def initialState (currentEnergy : Int) : GameState :=
  { points := 0, energy := currentEnergy, marked := fun _ => false }

def DefeatStep (enemies : List Int) (s t : GameState) : Prop :=
  ∃ i, s.marked i = false ∧ i < enemies.length ∧ enemyEnergy enemies i ≤ s.energy ∧
    t = { points := s.points + 1
          energy := s.energy - enemyEnergy enemies i
          marked := fun j => if j = i then true else s.marked j }

def RechargeStep (enemies : List Int) (s t : GameState) : Prop :=
  ∃ i, 1 ≤ s.points ∧ s.marked i = true ∧ i < enemies.length ∧
    t = { points := s.points - 1
          energy := s.energy + enemyEnergy enemies i
          marked := s.marked }

def Step (enemies : List Int) (s t : GameState) : Prop :=
  DefeatStep enemies s t ∨ RechargeStep enemies s t

def Run (enemies : List Int) (s t : GameState) : Prop :=
  Relation.ReflTransGen (Step enemies) s t

/-- Let n = len(enemyEnergies), m = min_{0 <= i < n} enemyEnergies[i], and S = sum_{i=0}^{n-1} enemyEnergies[i]. The function returns a result r, and: (a) if currentEnergy < m then r = 0; (b) if currentEnergy >= m then r = (currentEnergy + S - m) / m, where / is integer division (floor; the numerator is nonnegative).
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_1 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        (currentEnergy.val < minEnergy enemyEnergies → r.val = 0) ∧
        (minEnergy enemyEnergies ≤ currentEnergy.val →
          r.val = (currentEnergy.val + sumEnergy enemyEnergies - minEnergy enemyEnergies) /
            minEnergy enemyEnergies) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        (currentEnergy.val < minEnergy enemyEnergies → r.val = 0) ∧
        (minEnergy enemyEnergies ≤ currentEnergy.val →
          r.val = (currentEnergy.val + sumEnergy enemyEnergies - minEnergy enemyEnergies) /
            minEnergy enemyEnergies)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail by panic, arithmetic overflow, out-of-bounds access, or any other error.
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_2 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r) := by
  sorry

/-- Let m = min_{0 <= i < len(enemyEnergies)} enemyEnergies[i]. The function returns a result r, and r = 0 if and only if currentEnergy < m.
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_3 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        (r.val = 0 ↔ currentEnergy.val < minEnergy enemyEnergies) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        (r.val = 0 ↔ currentEnergy.val < minEnergy enemyEnergies)) := by
  sorry

/-- Let m = min_{0 <= i < len(enemyEnergies)} enemyEnergies[i] and S = sum_{i=0}^{len(enemyEnergies)-1} enemyEnergies[i]. The function returns a result r and r <= (currentEnergy + S) / m, where / is integer division (floor).
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_4 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        r.val ≤ (currentEnergy.val + sumEnergy enemyEnergies) / minEnergy enemyEnergies := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        r.val ≤ (currentEnergy.val + sumEnergy enemyEnergies) / minEnergy enemyEnergies) := by
  sorry

/-- Let m = min_{0 <= i < len(enemyEnergies)} enemyEnergies[i] and S = sum_{i=0}^{len(enemyEnergies)-1} enemyEnergies[i]. The function returns a result r and r >= S / m, where / is integer division (floor).
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9; currentEnergy >= m, where m = min_{0 <= i < len(enemyEnergies)} enemyEnergies[i]. -/
theorem spec_5 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9)
    (h_energy_ge_min : minEnergy enemyEnergies ≤ currentEnergy.val) :
    ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        sumEnergy enemyEnergies / minEnergy enemyEnergies ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9)
    (h_energy_ge_min : minEnergy enemyEnergies ≤ currentEnergy.val), ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        sumEnergy enemyEnergies / minEnergy enemyEnergies ≤ r.val) := by
  sorry

/-- Let r be the value returned by the function. There exists a finite sequence of the allowed operations (possibly the empty sequence when r = 0) that starts from the initial state (0 points, all enemies unmarked, energy currentEnergy) and ends with exactly r points.
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_6 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        ∃ t : GameState,
          Run (energies enemyEnergies) (initialState currentEnergy.val) t ∧ t.points = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r ∧
        ∃ t : GameState,
          Run (energies enemyEnergies) (initialState currentEnergy.val) t ∧ t.points = r.val) := by
  sorry

/-- Let r be the value returned by the function. For every finite sequence of the allowed operations starting from the initial state (0 points, all enemies unmarked, energy currentEnergy), the total points at the end of the sequence is at most r.
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_7 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r →
        ∀ t : GameState,
          Run (energies enemyEnergies) (initialState currentEnergy.val) t → t.points ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r →
        ∀ t : GameState,
          Run (energies enemyEnergies) (initialState currentEnergy.val) t → t.points ≤ r.val) := by
  sorry

/-- Let r be the value returned on the given input, and let n = len(enemyEnergies). For every permutation π of {0,1,...,n-1}, if the function is called with the slice A defined by A[j] = enemyEnergies[π(j)] for 0 <= j < n and with the same currentEnergy, it returns r.
  Preconditions: 1 <= len(enemyEnergies) <= 10^5; for every i with 0 <= i < len(enemyEnergies), 1 <= enemyEnergies[i] <= 10^9; 0 <= currentEnergy <= 10^9. -/
theorem spec_8 (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r →
        ∀ A : Slice Std.I64,
          List.Perm (energies A) (energies enemyEnergies) →
            ∃ r' : Std.I64,
              Aegis.MaximumPoints.maximum_points A currentEnergy = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (enemyEnergies : Slice Std.I64) (currentEnergy : Std.I64)
    (hlen_pos : 1 ≤ enemyEnergies.val.length)
    (hlen_le : enemyEnergies.val.length ≤ 10 ^ 5)
    (h_enemies : ∀ x ∈ enemyEnergies.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9)
    (h_energy_pos : 0 ≤ currentEnergy.val)
    (h_energy_le : currentEnergy.val ≤ 10 ^ 9), ∀ r : Std.I64,
      Aegis.MaximumPoints.maximum_points enemyEnergies currentEnergy = ok r →
        ∀ A : Slice Std.I64,
          List.Perm (energies A) (energies enemyEnergies) →
            ∃ r' : Std.I64,
              Aegis.MaximumPoints.maximum_points A currentEnergy = ok r' ∧ r'.val = r.val) := by
  sorry

end AegisSpec.MaximumPoints
