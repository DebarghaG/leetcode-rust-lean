import Aegis.MinTime.Code.Funs
import Mathlib.Basic.Real.Basic

/-!
# Specifications of `Aegis.MinTime.min_time`

LeetCode problem `find-the-minimum-amount-of-time-to-brew-potions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinTime

  def i64vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def sumFirst (v : List ℤ) (k : ℕ) : ℤ := (v.take k).sum

  def maxRange (f : ℕ → ℤ) (n : ℕ) : ℤ :=
    (List.range n).foldr (fun i acc => max (f i) acc) (f 0)

  def Starts (sv mv : List ℤ) (n m : ℕ) (t : ℕ → ℝ) : Prop :=
    (∀ j, j < m → 0 ≤ t j) ∧
      ∀ j, j + 1 < m → ∀ i, i < n →
        t j + ((sumFirst sv (i + 1) : ℤ) : ℝ) * ((mv.getD j 0 : ℤ) : ℝ) ≤
          t (j + 1) + ((sumFirst sv i : ℤ) : ℝ) * ((mv.getD (j + 1) 0 : ℤ) : ℝ)

  def Cost (sv mv : List ℤ) (n m : ℕ) (t : ℕ → ℝ) : ℝ :=
    t (m - 1) + ((sumFirst sv n : ℤ) : ℝ) * ((mv.getD (m - 1) 0 : ℤ) : ℝ)

  def stepGain (sv mv : List ℤ) (n j : ℕ) : ℤ :=
    maxRange
      (fun i => sumFirst sv (i + 1) * mv.getD j 0 - sumFirst sv i * mv.getD (j + 1) 0) n

  def greedyStarts (sv mv : List ℤ) (n : ℕ) : ℕ → ℤ
    | 0 => 0
    | j + 1 => greedyStarts sv mv n j + stepGain sv mv n j

  /-- Whenever min_time(skill, mana) returns a result r, r equals the minimum over all nonnegative real start times t_0,...,t_{m-1} of t_{m-1} + (sum_{k=0}^{n-1} skill[k])*mana[m-1], subject to the condition that for every j with 0≤j<m-1 and every i with 0≤i<n: t_{j+1} + (sum_{k=0}^{i-1} skill[k])*mana[j+1] ≥ t_j + (sum_{k=0}^{i} skill[k])*mana[j], with an empty sum equal to 0.
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_1
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      IsLeast
        { v : ℝ | ∃ t : ℕ → ℝ,
            Starts (i64vals skill) (i64vals mana) n m t ∧
              Cost (i64vals skill) (i64vals mana) n m t = v }
        ((r.val : ℤ) : ℝ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), IsLeast
          { v : ℝ | ∃ t : ℕ → ℝ,
              Starts (i64vals skill) (i64vals mana) n m t ∧
                Cost (i64vals skill) (i64vals mana) n m t = v }
          ((r.val : ℤ) : ℝ)) := by
    sorry

  /-- For every skill and mana satisfying the preconditions, min_time(skill, mana) returns a result (Result.ok r for some 64-bit integer r); it does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_2
      (skill mana : Slice Std.I64) (n m : ℕ)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000) :
      ∃ r : Std.I64, Aegis.MinTime.min_time skill mana = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000), ∃ r : Std.I64, Aegis.MinTime.min_time skill mana = Result.ok r) := by
    sorry

  /-- Let P_i = sum_{k=0}^{i} skill[k] for 0≤i<n, and Q_i = sum_{k=0}^{i-1} skill[k] for 0≤i<n (so Q_0=0). Define S_0=0 and, for each j with 0≤j<m-1, S_{j+1} = S_j + max_{0≤i<n} (P_i*mana[j] - Q_i*mana[j+1]). Whenever min_time(skill, mana) returns r, r = S_{m-1} + P_{n-1}*mana[m-1]. Moreover, the start times t_j = S_j are feasible for the problem and attain this value.
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_3
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      r.val = greedyStarts (i64vals skill) (i64vals mana) n (m - 1) +
          sumFirst (i64vals skill) n * (i64vals mana).getD (m - 1) 0 ∧
        Starts (i64vals skill) (i64vals mana) n m
          (fun j => ((greedyStarts (i64vals skill) (i64vals mana) n j : ℤ) : ℝ)) ∧
        Cost (i64vals skill) (i64vals mana) n m
            (fun j => ((greedyStarts (i64vals skill) (i64vals mana) n j : ℤ) : ℝ)) =
          ((r.val : ℤ) : ℝ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), r.val = greedyStarts (i64vals skill) (i64vals mana) n (m - 1) +
            sumFirst (i64vals skill) n * (i64vals mana).getD (m - 1) 0 ∧
          Starts (i64vals skill) (i64vals mana) n m
            (fun j => ((greedyStarts (i64vals skill) (i64vals mana) n j : ℤ) : ℝ)) ∧
          Cost (i64vals skill) (i64vals mana) n m
              (fun j => ((greedyStarts (i64vals skill) (i64vals mana) n j : ℤ) : ℝ)) =
            ((r.val : ℤ) : ℝ)) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r, r ≥ (sum_{i=0}^{n-1} skill[i]) * (max_{0≤j<m} mana[j]).
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_4
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      sumFirst (i64vals skill) n * maxRange (fun j => (i64vals mana).getD j 0) m ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), sumFirst (i64vals skill) n * maxRange (fun j => (i64vals mana).getD j 0) m ≤ r.val) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r, r ≥ (max_{0≤i<n} skill[i]) * (sum_{j=0}^{m-1} mana[j]).
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_5
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      maxRange (fun i => (i64vals skill).getD i 0) n * sumFirst (i64vals mana) m ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), maxRange (fun i => (i64vals skill).getD i 0) n * sumFirst (i64vals mana) m ≤ r.val) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r, r ≤ (sum_{i=0}^{n-1} skill[i]) * (sum_{j=0}^{m-1} mana[j]).
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_6
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      r.val ≤ sumFirst (i64vals skill) n * sumFirst (i64vals mana) m := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), r.val ≤ sumFirst (i64vals skill) n * sumFirst (i64vals mana) m) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r, r = skill[0] * (sum_{j=0}^{m-1} mana[j]).
    Preconditions: len(skill)=n=1, len(mana)=m, 1≤m≤5000, and 1≤skill[0]≤5000; for every j with 0≤j<m, 1≤mana[j]≤5000. -/
  theorem spec_7
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : n = 1) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : 1 ≤ (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val ∧
        (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      r.val = (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val *
        sumFirst (i64vals mana) m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : n = 1) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : 1 ≤ (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val ∧
          (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), r.val = (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val *
          sumFirst (i64vals mana) m) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r, r = d * ((sum_{i=0}^{n-1} skill[i]) + (m-1) * (max_{0≤i<n} skill[i])).
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m≤5000, and for every i with 0≤i<n, 1≤skill[i]≤5000; there exists an integer d with 1≤d≤5000 such that mana[j]=d for every 0≤j<m. -/
  theorem spec_8
      (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64) (d : ℤ)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
      (hmana_const : ∀ (j : ℕ) (hj : j < m),
        (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val = d)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r) :
      r.val = d * (sumFirst (i64vals skill) n +
        (((m : ℤ) - 1) * maxRange (fun i => (i64vals skill).getD i 0) n)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (skill mana : Slice Std.I64) (n m : ℕ) (r : Std.I64) (d : ℤ)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
        (hmana_const : ∀ (j : ℕ) (hj : j < m),
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val = d)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r), r.val = d * (sumFirst (i64vals skill) n +
          (((m : ℤ) - 1) * maxRange (fun i => (i64vals skill).getD i 0) n))) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r and min_time(skill2, mana) returns r2, r ≤ r2.
    Preconditions: skill and skill2 have length n with 1≤n≤5000 and entries in [1,5000], and skill[i] ≤ skill2[i] for every 0≤i<n. mana has length m with 1≤m≤5000 and entries in [1,5000]. -/
  theorem spec_9
      (skill skill2 mana : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64)
      (hskill_len : skill.val.length = n) (hskill2_len : skill2.val.length = n)
      (hmana_len : mana.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hskill2_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val ∧
          (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hle : ∀ (i : ℕ) (hi : i < n),
        (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤
          (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
      (hres2 : Aegis.MinTime.min_time skill2 mana = Result.ok r2) :
      r.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (skill skill2 mana : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64)
        (hskill_len : skill.val.length = n) (hskill2_len : skill2.val.length = n)
        (hmana_len : mana.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hskill2_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val ∧
            (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hle : ∀ (i : ℕ) (hi : i < n),
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤
            (skill2.val[i]'(Nat.lt_of_lt_of_eq hi hskill2_len.symm)).val)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
        (hres2 : Aegis.MinTime.min_time skill2 mana = Result.ok r2), r.val ≤ r2.val) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r and min_time(skill, mana2) returns r2, r2 ≥ r + skill[n-1]*d.
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m<5000, and all skill and mana entries are in [1,5000]. Also d is an integer with 1≤d≤5000, and mana2 has length m+1 with mana2[j]=mana[j] for 0≤j<m and mana2[m]=d. -/
  theorem spec_10
      (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64) (d : ℤ)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hmana2_len : mana2.val.length = m + 1)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_lt : m < 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
      (hmana2_agree : ∀ (j : ℕ) (hj : j < m),
        (mana2.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val =
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val)
      (hmana2_last : (mana2.val[m]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val = d)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
      (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2) :
      r.val + (skill.val[n - 1]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val * d ≤
        r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64) (d : ℤ)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hmana2_len : mana2.val.length = m + 1)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_lt : m < 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
        (hmana2_agree : ∀ (j : ℕ) (hj : j < m),
          (mana2.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val =
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val)
        (hmana2_last : (mana2.val[m]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val = d)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
        (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2), r.val + (skill.val[n - 1]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val * d ≤
          r2.val) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r and min_time(skill, mana2) returns r2, r2 ≥ r + skill[0]*d.
    Preconditions: len(skill)=n, len(mana)=m, 1≤n≤5000, 1≤m<5000, and all skill and mana entries are in [1,5000]. Also d is an integer with 1≤d≤5000, and mana2 has length m+1 with mana2[0]=d and mana2[j+1]=mana[j] for 0≤j<m. -/
  theorem spec_11
      (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64) (d : ℤ)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hmana2_len : mana2.val.length = m + 1)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_lt : m < 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
      (hmana2_first : (mana2.val[0]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val = d)
      (hmana2_agree : ∀ (j : ℕ) (hj : j < m),
        (mana2.val[j + 1]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val =
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
      (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2) :
      r.val + (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val * d ≤
        r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64) (d : ℤ)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hmana2_len : mana2.val.length = m + 1)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_lt : m < 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hd_lb : 1 ≤ d) (hd_ub : d ≤ 5000)
        (hmana2_first : (mana2.val[0]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val = d)
        (hmana2_agree : ∀ (j : ℕ) (hj : j < m),
          (mana2.val[j + 1]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val =
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
        (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2), r.val + (skill.val[0]'(Nat.lt_of_lt_of_eq (by omega) hskill_len.symm)).val * d ≤
          r2.val) := by
    sorry

  /-- Whenever min_time(skill, mana) returns r and min_time(skill, mana2) returns r2, r <= r2.
    Preconditions: skill has length n with 1<=n<=5000 and 1<=skill[i]<=5000 for all i. Both mana and mana2 have length m with 1<=m<=5000 and entries in [1,5000]. For every 0<=j<m-1, mana[j]=mana2[j], and mana[m-1]<=mana2[m-1]. -/
  theorem spec_12
      (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64)
      (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
      (hmana2_len : mana2.val.length = m)
      (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
      (hskill_bd : ∀ (i : ℕ) (hi : i < n),
        1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
          (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
      (hmana_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
          (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
      (hmana2_bd : ∀ (j : ℕ) (hj : j < m),
        1 ≤ (mana2.val[j]'(Nat.lt_of_lt_of_eq hj hmana2_len.symm)).val ∧
          (mana2.val[j]'(Nat.lt_of_lt_of_eq hj hmana2_len.symm)).val ≤ 5000)
      (hmana_agree : ∀ (j : ℕ) (hj : j + 1 < m),
        (mana.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana_len.symm)).val =
          (mana2.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val)
      (hmana_last : (mana.val[m - 1]'(Nat.lt_of_lt_of_eq (by omega) hmana_len.symm)).val ≤
        (mana2.val[m - 1]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val)
      (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
      (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2) :
      r.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (skill mana mana2 : Slice Std.I64) (n m : ℕ) (r r2 : Std.I64)
        (hskill_len : skill.val.length = n) (hmana_len : mana.val.length = m)
        (hmana2_len : mana2.val.length = m)
        (hn : 1 ≤ n) (hn_le : n ≤ 5000) (hm : 1 ≤ m) (hm_le : m ≤ 5000)
        (hskill_bd : ∀ (i : ℕ) (hi : i < n),
          1 ≤ (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ∧
            (skill.val[i]'(Nat.lt_of_lt_of_eq hi hskill_len.symm)).val ≤ 5000)
        (hmana_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ∧
            (mana.val[j]'(Nat.lt_of_lt_of_eq hj hmana_len.symm)).val ≤ 5000)
        (hmana2_bd : ∀ (j : ℕ) (hj : j < m),
          1 ≤ (mana2.val[j]'(Nat.lt_of_lt_of_eq hj hmana2_len.symm)).val ∧
            (mana2.val[j]'(Nat.lt_of_lt_of_eq hj hmana2_len.symm)).val ≤ 5000)
        (hmana_agree : ∀ (j : ℕ) (hj : j + 1 < m),
          (mana.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana_len.symm)).val =
            (mana2.val[j]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val)
        (hmana_last : (mana.val[m - 1]'(Nat.lt_of_lt_of_eq (by omega) hmana_len.symm)).val ≤
          (mana2.val[m - 1]'(Nat.lt_of_lt_of_eq (by omega) hmana2_len.symm)).val)
        (hres : Aegis.MinTime.min_time skill mana = Result.ok r)
        (hres2 : Aegis.MinTime.min_time skill mana2 = Result.ok r2), r.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinTime
