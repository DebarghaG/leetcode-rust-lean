import Aegis.MaxEnergyBoost.Code.Funs

/-!
# Specifications of `Aegis.MaxEnergyBoost.max_energy_boost`

LeetCode problem `maximum-energy-boost-from-two-drinks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.MaxEnergyBoost

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def entry (s : Slice Std.I64) (i : ℕ) : ℤ := (vals s)[i]?.getD 0

lemma entry_eq_get (s : Slice Std.I64) (i : ℕ) (h : i < s.val.length) :
    entry s i = s.val[i].val := by
  simp [entry, vals, List.getElem?_eq_getElem h]

def revEntry (s : Slice Std.I64) (n i : ℕ) : ℤ := entry s (n - 1 - i)

def sumRange (f : ℕ → ℤ) (n : ℕ) : ℤ := (Finset.range n).sum f

inductive Sched where
  | A
  | B
  | cleanse
  deriving DecidableEq, Repr

abbrev Schedule (n : ℕ) := Fin n → Sched

def Valid {n : ℕ} (s : Schedule n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n),
    ¬ (s i = Sched.A ∧ s ⟨i.val + 1, h⟩ = Sched.B) ∧
      ¬ (s i = Sched.B ∧ s ⟨i.val + 1, h⟩ = Sched.A)

def NoDoubleCleanse {n : ℕ} (s : Schedule n) : Prop :=
  ∀ (i : Fin n) (h : i.val + 1 < n),
    ¬ (s i = Sched.cleanse ∧ s ⟨i.val + 1, h⟩ = Sched.cleanse)

def score (a b : ℕ → ℤ) {n : ℕ} (s : Schedule n) : ℤ :=
  ∑ i : Fin n, match s i with
    | Sched.A => a i.val
    | Sched.B => b i.val
    | Sched.cleanse => 0

def IsMaxScore (a b : ℕ → ℤ) (n : ℕ) (r : ℤ) : Prop :=
  ∃ s : Schedule n,
    Valid s ∧ score a b s = r ∧ ∀ t : Schedule n, Valid t → score a b t ≤ r

structure DpState where
  a2 : ℤ
  b2 : ℤ
  a1 : ℤ
  b1 : ℤ

def dpStep (a b : ℕ → ℤ) (st : DpState) (i : ℕ) : DpState :=
  { a2 := st.a1
    b2 := st.b1
    a1 := a i + max st.a1 st.b2
    b1 := b i + max st.b1 st.a2 }

def dpState (a b : ℕ → ℤ) : ℕ → DpState
  | 0 => { a2 := 0, b2 := 0, a1 := a 0, b1 := b 0 }
  | 1 => { a2 := a 0, b2 := b 0, a1 := a 0 + a 1, b1 := b 0 + b 1 }
  | i + 2 => dpStep a b (dpState a b (i + 1)) (i + 2)
  termination_by i => i

def dpA (a b : ℕ → ℤ) (i : ℕ) : ℤ := (dpState a b i).a1

def dpB (a b : ℕ → ℤ) (i : ℕ) : ℤ := (dpState a b i).b1

lemma dpA_zero (a b : ℕ → ℤ) : dpA a b 0 = a 0 := by
  simp [dpA, dpState]

lemma dpA_one (a b : ℕ → ℤ) : dpA a b 1 = a 0 + a 1 := by
  simp [dpA, dpState]

lemma dpB_zero (a b : ℕ → ℤ) : dpB a b 0 = b 0 := by
  simp [dpB, dpState]

lemma dpB_one (a b : ℕ → ℤ) : dpB a b 1 = b 0 + b 1 := by
  simp [dpB, dpState]

lemma dpA_succ_succ (a b : ℕ → ℤ) (i : ℕ) :
    dpA a b (i + 2) = a (i + 2) + max (dpA a b (i + 1)) (dpB a b i) := by
  rcases i with _ | k <;> simp [dpA, dpB, dpState, dpStep]

lemma dpB_succ_succ (a b : ℕ → ℤ) (i : ℕ) :
    dpB a b (i + 2) = b (i + 2) + max (dpB a b (i + 1)) (dpA a b i) := by
  rcases i with _ | k <;> simp [dpA, dpB, dpState, dpStep]

/-- A schedule assigns to each hour i with 0 <= i < n exactly one of A, B, or cleanse. It is valid if for every i with 0 <= i < n-1, a direct switch is forbidden: it is not the case that hour i is A and hour i+1 is B, nor that hour i is B and hour i+1 is A. Its score is the sum of energyDrinkA[i] over hours assigned A, plus the sum of energyDrinkB[i] over hours assigned B, plus 0 over cleanse hours. The function returns a result r, and r is the maximum score over all valid schedules.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_1 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val) := by
  sorry

/-- The function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_2 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r) := by
  sorry

/-- The function returns a result r, and r >= max(sum over i from 0 to n-1 of energyDrinkA[i], sum over i from 0 to n-1 of energyDrinkB[i]).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_3 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        max (sumRange (entry energyDrinkA) n) (sumRange (entry energyDrinkB) n) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        max (sumRange (entry energyDrinkA) n) (sumRange (entry energyDrinkB) n) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r <= sum over i from 0 to n-1 of max(energyDrinkA[i], energyDrinkB[i]).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_4 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val ≤ sumRange (fun i => max (entry energyDrinkA i) (entry energyDrinkB i)) n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val ≤ sumRange (fun i => max (entry energyDrinkA i) (entry energyDrinkB i)) n) := by
  sorry

/-- The function returns a result r, and r = sum over i from 0 to n-1 of energyDrinkA[i].
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. Additionally, for every i with 0 <= i < n, energyDrinkA[i] >= energyDrinkB[i]. -/
theorem spec_5 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hge : ∀ i, i < n → entry energyDrinkB i ≤ entry energyDrinkA i) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = sumRange (entry energyDrinkA) n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hge : ∀ i, i < n → entry energyDrinkB i ≤ entry energyDrinkA i), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = sumRange (entry energyDrinkA) n) := by
  sorry

/-- The function returns a result r, and r = sum over i from 0 to n-1 of energyDrinkB[i].
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. Additionally, for every i with 0 <= i < n, energyDrinkB[i] >= energyDrinkA[i]. -/
theorem spec_6 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hge : ∀ i, i < n → entry energyDrinkA i ≤ entry energyDrinkB i) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = sumRange (entry energyDrinkB) n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hge : ∀ i, i < n → entry energyDrinkA i ≤ entry energyDrinkB i), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = sumRange (entry energyDrinkB) n) := by
  sorry

/-- The function returns a result r, and r = max(sum over i from 0 to 2 of energyDrinkA[i], sum over i from 0 to 2 of energyDrinkB[i], energyDrinkA[0] + energyDrinkB[2], energyDrinkB[0] + energyDrinkA[2]).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. Additionally, n = 3. -/
theorem spec_7 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (h3 : n = 3) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = max (max (entry energyDrinkA 0 + entry energyDrinkA 1 + entry energyDrinkA 2)
                          (entry energyDrinkB 0 + entry energyDrinkB 1 + entry energyDrinkB 2))
                    (max (entry energyDrinkA 0 + entry energyDrinkB 2)
                         (entry energyDrinkB 0 + entry energyDrinkA 2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (h3 : n = 3), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = max (max (entry energyDrinkA 0 + entry energyDrinkA 1 + entry energyDrinkA 2)
                          (entry energyDrinkB 0 + entry energyDrinkB 1 + entry energyDrinkB 2))
                    (max (entry energyDrinkA 0 + entry energyDrinkB 2)
                         (entry energyDrinkB 0 + entry energyDrinkA 2))) := by
  sorry

/-- For an ordered pair of arrays (X,Y), define a valid schedule exactly as in the main specification with X in place of energyDrinkA and Y in place of energyDrinkB, and define its score analogously. The function returns a result r, and r is also the maximum score over all valid schedules for the pair (energyDrinkB, energyDrinkA).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_8 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val ∧
          IsMaxScore (entry energyDrinkB) (entry energyDrinkA) n r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val ∧
          IsMaxScore (entry energyDrinkB) (entry energyDrinkA) n r.val) := by
  sorry

/-- Define A_rev[i] = energyDrinkA[n-1-i] and B_rev[i] = energyDrinkB[n-1-i] for 0 <= i < n. For an ordered pair of arrays (X,Y), define a valid schedule and its score exactly as in the main specification. The function returns a result r, and r is also the maximum score over all valid schedules for the pair (A_rev, B_rev).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_9 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val ∧
          IsMaxScore (revEntry energyDrinkA n) (revEntry energyDrinkB n) n r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        IsMaxScore (entry energyDrinkA) (entry energyDrinkB) n r.val ∧
          IsMaxScore (revEntry energyDrinkA n) (revEntry energyDrinkB n) n r.val) := by
  sorry

/-- The function returns a result r, and for every i with i + 2 < n, both r >= energyDrinkA[i] + energyDrinkB[i+2] and r >= energyDrinkB[i] + energyDrinkA[i+2] hold.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_10 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∀ i, i + 2 < n →
          r.val ≥ entry energyDrinkA i + entry energyDrinkB (i + 2) ∧
            r.val ≥ entry energyDrinkB i + entry energyDrinkA (i + 2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∀ i, i + 2 < n →
          r.val ≥ entry energyDrinkA i + entry energyDrinkB (i + 2) ∧
            r.val ≥ entry energyDrinkB i + entry energyDrinkA (i + 2)) := by
  sorry

/-- Define valid schedules and their scores as in the main specification. The function returns a result r, and there exists a valid schedule s with score r such that for no i with 0 <= i < n-1 are both hour i and hour i+1 assigned cleanse.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_11 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∃ s : Schedule n,
          Valid s ∧ score (entry energyDrinkA) (entry energyDrinkB) s = r.val ∧
            NoDoubleCleanse s := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∃ s : Schedule n,
          Valid s ∧ score (entry energyDrinkA) (entry energyDrinkB) s = r.val ∧
            NoDoubleCleanse s) := by
  sorry

/-- Define valid schedules and their scores as in the main specification. The function returns a result r, and if r > max(sum over i from 0 to n-1 of energyDrinkA[i], sum over i from 0 to n-1 of energyDrinkB[i]), then every valid schedule attaining score r assigns A at least once and assigns B at least once.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_12 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        (max (sumRange (entry energyDrinkA) n) (sumRange (entry energyDrinkB) n) < r.val →
          ∀ s : Schedule n,
            Valid s → score (entry energyDrinkA) (entry energyDrinkB) s = r.val →
              (∃ i : Fin n, s i = Sched.A) ∧ (∃ i : Fin n, s i = Sched.B)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        (max (sumRange (entry energyDrinkA) n) (sumRange (entry energyDrinkB) n) < r.val →
          ∀ s : Schedule n,
            Valid s → score (entry energyDrinkA) (entry energyDrinkB) s = r.val →
              (∃ i : Fin n, s i = Sched.A) ∧ (∃ i : Fin n, s i = Sched.B))) := by
  sorry

/-- Let dpA and dpB be arrays of length n with dpA[0] = energyDrinkA[0] and dpB[0] = energyDrinkB[0]; dpA[1] = energyDrinkA[0] + energyDrinkA[1] and dpB[1] = energyDrinkB[0] + energyDrinkB[1]; and for 2 <= i < n, dpA[i] = energyDrinkA[i] + max(dpA[i-1], dpB[i-2]) and dpB[i] = energyDrinkB[i] + max(dpB[i-1], dpA[i-2]). The function returns a result r, and r = max(dpA[n-1], dpB[n-1]).
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_13 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = max (dpA (entry energyDrinkA) (entry energyDrinkB) (n - 1))
                    (dpB (entry energyDrinkA) (entry energyDrinkB) (n - 1)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        r.val = max (dpA (entry energyDrinkA) (entry energyDrinkB) (n - 1))
                    (dpB (entry energyDrinkA) (entry energyDrinkB) (n - 1))) := by
  sorry

/-- Define valid schedules and scores as in the main specification. The function returns a result r, and there exists a valid schedule s with score r such that hour 0 and hour n-1 are not assigned cleanse, and for every i with 0 < i < n-1, if hour i is assigned cleanse then one of hours i-1 and i+1 is assigned A and the other is assigned B.
  Preconditions: Let n = len(energyDrinkA). The inputs satisfy len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and for every i with 0 <= i < n, 1 <= energyDrinkA[i] <= 100000 and 1 <= energyDrinkB[i] <= 100000. -/
theorem spec_14 (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∃ s : Schedule n,
          Valid s ∧ score (entry energyDrinkA) (entry energyDrinkB) s = r.val ∧
            s ⟨0, by omega⟩ ≠ Sched.cleanse ∧
            s ⟨n - 1, by omega⟩ ≠ Sched.cleanse ∧
            ∀ (i : ℕ) (h0 : 0 < i) (h1 : i < n - 1),
              s ⟨i, by omega⟩ = Sched.cleanse →
                (s ⟨i - 1, by omega⟩ = Sched.A ∧ s ⟨i + 1, by omega⟩ = Sched.B) ∨
                  (s ⟨i - 1, by omega⟩ = Sched.B ∧ s ⟨i + 1, by omega⟩ = Sched.A) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (energyDrinkA energyDrinkB : Slice Std.I64) (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000), ∃ r : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r ∧
        ∃ s : Schedule n,
          Valid s ∧ score (entry energyDrinkA) (entry energyDrinkB) s = r.val ∧
            s ⟨0, by omega⟩ ≠ Sched.cleanse ∧
            s ⟨n - 1, by omega⟩ ≠ Sched.cleanse ∧
            ∀ (i : ℕ) (h0 : 0 < i) (h1 : i < n - 1),
              s ⟨i, by omega⟩ = Sched.cleanse →
                (s ⟨i - 1, by omega⟩ = Sched.A ∧ s ⟨i + 1, by omega⟩ = Sched.B) ∨
                  (s ⟨i - 1, by omega⟩ = Sched.B ∧ s ⟨i + 1, by omega⟩ = Sched.A)) := by
  sorry

/-- If the function returns r for (energyDrinkA, energyDrinkB) and r' for (energyDrinkA', energyDrinkB'), then r <= r'.
  Preconditions: Let n = len(energyDrinkA) = len(energyDrinkA'). The first pair satisfies len(energyDrinkA) = len(energyDrinkB) = n, 3 <= n <= 100000, and 1 <= energyDrinkA[i], energyDrinkB[i] <= 100000 for all i. The second pair satisfies len(energyDrinkA') = len(energyDrinkB') = n, 3 <= n <= 100000, and 1 <= energyDrinkA'[i], energyDrinkB'[i] <= 100000 for all i. Additionally, for every i with 0 <= i < n, energyDrinkA[i] <= energyDrinkA'[i] and energyDrinkB[i] <= energyDrinkB'[i]. -/
theorem spec_15 (energyDrinkA energyDrinkB energyDrinkA' energyDrinkB' : Slice Std.I64)
    (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hA' : energyDrinkA'.val.length = n) (hB' : energyDrinkB'.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hAb' : ∀ i, i < n → 1 ≤ entry energyDrinkA' i ∧ entry energyDrinkA' i ≤ 100000)
    (hBb' : ∀ i, i < n → 1 ≤ entry energyDrinkB' i ∧ entry energyDrinkB' i ≤ 100000)
    (hmono : ∀ i, i < n →
      entry energyDrinkA i ≤ entry energyDrinkA' i ∧ entry energyDrinkB i ≤ entry energyDrinkB' i) :
    ∀ r r' : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r →
        Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA' energyDrinkB' = ok r' →
          r.val ≤ r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (energyDrinkA energyDrinkB energyDrinkA' energyDrinkB' : Slice Std.I64)
    (n : ℕ)
    (hA : energyDrinkA.val.length = n) (hB : energyDrinkB.val.length = n)
    (hA' : energyDrinkA'.val.length = n) (hB' : energyDrinkB'.val.length = n)
    (hn3 : 3 ≤ n) (hn100 : n ≤ 100000)
    (hAb : ∀ i, i < n → 1 ≤ entry energyDrinkA i ∧ entry energyDrinkA i ≤ 100000)
    (hBb : ∀ i, i < n → 1 ≤ entry energyDrinkB i ∧ entry energyDrinkB i ≤ 100000)
    (hAb' : ∀ i, i < n → 1 ≤ entry energyDrinkA' i ∧ entry energyDrinkA' i ≤ 100000)
    (hBb' : ∀ i, i < n → 1 ≤ entry energyDrinkB' i ∧ entry energyDrinkB' i ≤ 100000)
    (hmono : ∀ i, i < n →
      entry energyDrinkA i ≤ entry energyDrinkA' i ∧ entry energyDrinkB i ≤ entry energyDrinkB' i), ∀ r r' : Std.I64,
      Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA energyDrinkB = ok r →
        Aegis.MaxEnergyBoost.max_energy_boost energyDrinkA' energyDrinkB' = ok r' →
          r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxEnergyBoost
