import Aegis.MaximumPopulation.Code.Funs

/-!
# Specifications of `Aegis.MaximumPopulation.maximum_population`

LeetCode problem `maximum-population-year`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumPopulation

abbrev Logs : Type := Slice (alloc.vec.Vec I64)

def birth (logs : Logs) (i : ℕ) : ℤ :=
  match logs.val[i]? with
  | some row =>
    match row.val[0]? with
    | some b => b.val
    | none => 0
  | none => 0

def death (logs : Logs) (i : ℕ) : ℤ :=
  match logs.val[i]? with
  | some row =>
    match row.val[1]? with
    | some d => d.val
    | none => 0
  | none => 0

def entry (logs : Logs) (i : ℕ) : ℤ × ℤ :=
  (birth logs i, death logs i)

def entries (logs : Logs) : List (ℤ × ℤ) :=
  (List.range logs.val.length).map (entry logs)

def pop (logs : Logs) (x : ℤ) : ℕ :=
  ((List.range logs.val.length).filter
    (fun i => decide (birth logs i ≤ x ∧ x < death logs i))).length

def birthYears (logs : Logs) : List ℤ :=
  (List.range logs.val.length).map (birth logs)

def deathYears (logs : Logs) : List ℤ :=
  (List.range logs.val.length).map (death logs)

def maxBirth (logs : Logs) : ℤ :=
  (birthYears logs).max?.getD 0

def minBirth (logs : Logs) : ℤ :=
  (birthYears logs).min?.getD 0

def minDeath (logs : Logs) : ℤ :=
  (deathYears logs).min?.getD 0

def ValidLogs (logs : Logs) : Prop :=
  1 ≤ logs.val.length ∧
  logs.val.length ≤ 100 ∧
  (∀ row ∈ logs.val, row.val.length = 2) ∧
  (∀ i : ℕ, i < logs.val.length →
    1950 ≤ birth logs i ∧ birth logs i < death logs i ∧ death logs i ≤ 2050)

/-- Let pop(x) be the number of indices i with 0 <= i < len(logs) such that logs[i][0] <= x < logs[i][1], for any integer x. Whenever maximum_population(logs) returns a result r, r is an integer year such that (a) for every integer x, pop(x) <= pop(r), and (b) for every integer y with y < r, pop(y) < pop(r). Equivalently, r is the earliest year whose population equals the maximum population over all years.
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_1 (logs : Logs) (hlogs : ValidLogs logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      (∀ x : ℤ, pop logs x ≤ pop logs r.val) ∧
      (∀ y : ℤ, y < r.val → pop logs y < pop logs r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      (∀ x : ℤ, pop logs x ≤ pop logs r.val) ∧
      (∀ y : ℤ, y < r.val → pop logs y < pop logs r.val)) := by
  sorry

/-- For every logs satisfying the preconditions, the call maximum_population(logs) returns a result r; that is, it does not fail.
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_2 (logs : Logs) (hlogs : ValidLogs logs) :
    ∃ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∃ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r) := by
  sorry

/-- Whenever maximum_population(logs) returns r, 1950 <= r <= 2049.
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_3 (logs : Logs) (hlogs : ValidLogs logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      1950 ≤ r.val ∧ r.val ≤ 2049 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      1950 ≤ r.val ∧ r.val ≤ 2049) := by
  sorry

/-- Whenever maximum_population(logs) returns r, there exists an index i with 0 <= i < len(logs) such that r = logs[i][0].
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_4 (logs : Logs) (hlogs : ValidLogs logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      ∃ i : ℕ, i < logs.val.length ∧ r.val = birth logs i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      ∃ i : ℕ, i < logs.val.length ∧ r.val = birth logs i) := by
  sorry

/-- Whenever maximum_population(logs) returns r, letting pop(x) be the number of indices i with 0 <= i < len(logs) and logs[i][0] <= x < logs[i][1], one has 1 <= pop(r) <= len(logs).
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_5 (logs : Logs) (hlogs : ValidLogs logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      1 ≤ pop logs r.val ∧ pop logs r.val ≤ logs.val.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      1 ≤ pop logs r.val ∧ pop logs r.val ≤ logs.val.length) := by
  sorry

/-- Whenever maximum_population(logs) returns r, minBirth <= r <= maxBirth, where minBirth = min over 0 <= i < len(logs) of logs[i][0], and maxBirth = max over 0 <= i < len(logs) of logs[i][0].
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050. -/
theorem spec_6 (logs : Logs) (hlogs : ValidLogs logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      minBirth logs ≤ r.val ∧ r.val ≤ maxBirth logs := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      minBirth logs ≤ r.val ∧ r.val ≤ maxBirth logs) := by
  sorry

/-- Whenever maximum_population(logs) returns r, r = maxBirth, where maxBirth = max over 0 <= i < len(logs) of logs[i][0].
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050; additionally, writing maxBirth = max over 0 <= i < len(logs) of b_i and minDeath = min over 0 <= i < len(logs) of d_i, we have maxBirth < minDeath. -/
theorem spec_7 (logs : Logs) (hlogs : ValidLogs logs)
    (hoverlap : maxBirth logs < minDeath logs) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      r.val = maxBirth logs := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs)
    (hoverlap : maxBirth logs < minDeath logs), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      r.val = maxBirth logs) := by
  sorry

/-- Whenever maximum_population(logs) returns r, r = min over 0 <= i < len(logs) of logs[i][0].
  Preconditions: 1 <= len(logs) <= 100; for every i with 0 <= i < len(logs), len(logs[i]) = 2, and, writing b_i = logs[i][0] and d_i = logs[i][1], 1950 <= b_i < d_i <= 2050; additionally, for all i and j with 0 <= i < j < len(logs), either logs[i][1] <= logs[j][0] or logs[j][1] <= logs[i][0]. -/
theorem spec_8 (logs : Logs) (hlogs : ValidLogs logs)
    (hdisj : ∀ i j : ℕ, i < j → j < logs.val.length →
      death logs i ≤ birth logs j ∨ death logs j ≤ birth logs i) :
    ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      r.val = minBirth logs := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (logs : Logs) (hlogs : ValidLogs logs)
    (hdisj : ∀ i j : ℕ, i < j → j < logs.val.length →
      death logs i ≤ birth logs j ∨ death logs j ≤ birth logs i), ∀ r : I64, Aegis.MaximumPopulation.maximum_population logs = ok r →
      r.val = minBirth logs) := by
  sorry

/-- Whenever maximum_population(logs1) returns r1 and maximum_population(logs2) returns r2, r1 = r2.
  Preconditions: Both logs1 and logs2 satisfy: 1 <= len <= 100; each inner vector has length 2; and for each i, 1950 <= logs[i][0] < logs[i][1] <= 2050. Also, the multiset of ordered pairs (logs1[i][0], logs1[i][1]) equals the multiset of ordered pairs (logs2[j][0], logs2[j][1]). -/
theorem spec_9 (logs1 logs2 : Logs) (hlogs1 : ValidLogs logs1) (hlogs2 : ValidLogs logs2)
    (hperm : (entries logs1).Perm (entries logs2)) :
    ∀ r1 r2 : I64,
      Aegis.MaximumPopulation.maximum_population logs1 = ok r1 →
      Aegis.MaximumPopulation.maximum_population logs2 = ok r2 →
      r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (logs1 logs2 : Logs) (hlogs1 : ValidLogs logs1) (hlogs2 : ValidLogs logs2)
    (hperm : (entries logs1).Perm (entries logs2)), ∀ r1 r2 : I64,
      Aegis.MaximumPopulation.maximum_population logs1 = ok r1 →
      Aegis.MaximumPopulation.maximum_population logs2 = ok r2 →
      r1 = r2) := by
  sorry

/-- Whenever maximum_population(logs) returns r and maximum_population(logs') returns r', we have r' = r + k.
  Preconditions: Both logs and logs' satisfy: 1 <= len <= 100; each inner vector has length 2; and for each i, 1950 <= logs[i][0] < logs[i][1] <= 2050. Also, len(logs') = len(logs) and there is an integer k such that for every i with 0 <= i < len(logs), logs'[i][0] = logs[i][0] + k and logs'[i][1] = logs[i][1] + k. -/
theorem spec_10 (logs logs' : Logs) (hlogs : ValidLogs logs) (hlogs' : ValidLogs logs')
    (hlen : logs'.val.length = logs.val.length) (k : ℤ)
    (hshift : ∀ i : ℕ, i < logs.val.length →
      birth logs' i = birth logs i + k ∧ death logs' i = death logs i + k) :
    ∀ r r' : I64,
      Aegis.MaximumPopulation.maximum_population logs = ok r →
      Aegis.MaximumPopulation.maximum_population logs' = ok r' →
      r'.val = r.val + k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (logs logs' : Logs) (hlogs : ValidLogs logs) (hlogs' : ValidLogs logs')
    (hlen : logs'.val.length = logs.val.length) (k : ℤ)
    (hshift : ∀ i : ℕ, i < logs.val.length →
      birth logs' i = birth logs i + k ∧ death logs' i = death logs i + k), ∀ r r' : I64,
      Aegis.MaximumPopulation.maximum_population logs = ok r →
      Aegis.MaximumPopulation.maximum_population logs' = ok r' →
      r'.val = r.val + k) := by
  sorry

end AegisSpec.MaximumPopulation
