import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-eat-all-grains`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTime

  open Aeneas.Std

  def henVals (hens : Slice Std.I64) : List ℤ := hens.val.map (fun h => h.val)

  def grainVals (grains : Slice Std.I64) : List ℤ := grains.val.map (fun g => g.val)

  def henAt (H : List ℤ) (i : ℕ) : ℤ := H.getD i 0

  def grainAt (G : List ℤ) (j : ℕ) : ℤ := G.getD j 0

  def listMin : List ℤ → Option ℤ
    | [] => none
    | a :: l => some (l.foldr min a)

  def listMax : List ℤ → Option ℤ
    | [] => none
    | a :: l => some (l.foldr max a)

  def grainLo (G : List ℤ) : ℤ := (listMin G).getD 0

  def grainHi (G : List ℤ) : ℤ := (listMax G).getD 0

  def minOver (n : ℕ) (f : ℕ → ℤ) : ℤ := (listMin ((List.range n).map f)).getD 0

  def maxOver (n : ℕ) (f : ℕ → ℤ) : ℤ := (listMax ((List.range n).map f)).getD 0

  def IsAssign (n m : ℕ) (A : ℕ → ℕ) : Prop := ∀ j : ℕ, j < m → A j < n

  def assignedGrains (G : List ℤ) (A : ℕ → ℕ) (i : ℕ) : List ℤ :=
    (List.range G.length).filterMap (fun j => if A j = i then G[j]? else none)

  def grazeTime (S : List ℤ) (h : ℤ) : ℤ :=
    match listMin S, listMax S with
    | some a, some b => (b - a) + min |h - a| |h - b|
    | _, _ => 0

  def henTime (H G : List ℤ) (A : ℕ → ℕ) (i : ℕ) : ℤ :=
    grazeTime (assignedGrains G A i) (henAt H i)

  def makespan (H G : List ℤ) (A : ℕ → ℕ) : ℤ :=
    maxOver H.length (fun i => henTime H G A i)

  def Achievable (H G : List ℤ) (t : ℤ) : Prop :=
    ∃ A : ℕ → ℕ, IsAssign H.length G.length A ∧
      ∀ i : ℕ, i < H.length → henTime H G A i ≤ t

  /-- Whenever the function returns a result r, r is the least nonnegative integer t for which there exists an assignment A from grain indices to hen indices such that, for every hen index i, the time needed by hen i to eat exactly the grains assigned to it is at most t. For a hen i, let S_i = { grains[j] | 0 <= j < len(grains) and A(j) = i }; if S_i is empty its time is 0, otherwise its time is (max S_i - min S_i) + min(|hens[i] - min S_i|, |hens[i] - max S_i|). Equivalently, r = min over all such assignments A of the maximum, over all hen indices i, of these hen times.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_1 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      Achievable (henVals hens) (grainVals grains) r.val ∧
        ∀ t : ℤ, 0 ≤ t → Achievable (henVals hens) (grainVals grains) t → r.val ≤ t := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), Achievable (henVals hens) (grainVals grains) r.val ∧
          ∀ t : ℤ, 0 ≤ t → Achievable (henVals hens) (grainVals grains) t → r.val ≤ t) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, index out of bounds, or overflow.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_2 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.MinimumTime.minimum_time hens grains = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000), ∃ r : Std.I64, Aegis.MinimumTime.minimum_time hens grains = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 1500000000.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_3 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      0 ≤ r.val ∧ r.val ≤ 1500000000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), 0 ≤ r.val ∧ r.val ≤ 1500000000) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every grain index j with 0 <= j < len(grains) there exists a hen index i with 0 <= i < len(hens) such that hens[i] = grains[j].
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_4 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      (r.val = 0 ↔
        ∀ j : ℕ, j < (grainVals grains).length →
          ∃ i : ℕ, i < (henVals hens).length ∧ henAt (henVals hens) i = grainAt (grainVals grains) j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), (r.val = 0 ↔
          ∀ j : ℕ, j < (grainVals grains).length →
            ∃ i : ℕ, i < (henVals hens).length ∧ henAt (henVals hens) i = grainAt (grainVals grains) j)) := by
    sorry

  /-- Assume len(hens) = 1. Let h = hens[0], a = min_{0 <= j < len(grains)} grains[j], and b = max_{0 <= j < len(grains)} grains[j]. Whenever the function returns a result r, r = (b - a) + min(|h - a|, |h - b|).
    Preconditions: 1 <= len(hens), len(grains) <= 20000; len(hens) = 1; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_5 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_single : (henVals hens).length = 1)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      r.val = (grainHi (grainVals grains) - grainLo (grainVals grains)) +
        min |henAt (henVals hens) 0 - grainLo (grainVals grains)|
          |henAt (henVals hens) 0 - grainHi (grainVals grains)| := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_single : (henVals hens).length = 1)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), r.val = (grainHi (grainVals grains) - grainLo (grainVals grains)) +
          min |henAt (henVals hens) 0 - grainLo (grainVals grains)|
            |henAt (henVals hens) 0 - grainHi (grainVals grains)|) := by
    sorry

  /-- Assume all grains are at the same position p. Whenever the function returns a result r, r = min_{0 <= i < len(hens)} |hens[i] - p|.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; there exists an integer p such that grains[j] = p for every j with 0 <= j < len(grains); for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; 0 <= p <= 1000000000. -/
  theorem spec_6 (hens grains : Slice Std.I64) (p : ℤ)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_const : ∀ j : ℕ, j < (grainVals grains).length → grainAt (grainVals grains) j = p)
      (hp_lo : 0 ≤ p) (hp_hi : p ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      r.val = minOver (henVals hens).length (fun i => |henAt (henVals hens) i - p|) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (hens grains : Slice Std.I64) (p : ℤ)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_const : ∀ j : ℕ, j < (grainVals grains).length → grainAt (grainVals grains) j = p)
        (hp_lo : 0 ≤ p) (hp_hi : p ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), r.val = minOver (henVals hens).length (fun i => |henAt (henVals hens) i - p|)) := by
    sorry

  /-- Whenever the function returns a result r, for every grain index j with 0 <= j < len(grains), r >= min_{0 <= i < len(hens)} |hens[i] - grains[j]|.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_7 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      ∀ j : ℕ, j < (grainVals grains).length →
        r.val ≥ minOver (henVals hens).length
          (fun i => |henAt (henVals hens) i - grainAt (grainVals grains) j|) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), ∀ j : ℕ, j < (grainVals grains).length →
          r.val ≥ minOver (henVals hens).length
            (fun i => |henAt (henVals hens) i - grainAt (grainVals grains) j|)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an assignment A from grain indices to hen indices such that the maximum over hen indices i of the time for hen i to eat the grains assigned to it equals r. The time for hen i is 0 if no grain is assigned to i; otherwise it is (max S_i - min S_i) + min(|hens[i] - min S_i|, |hens[i] - max S_i|), where S_i = { grains[j] | A(j) = i }.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_8 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      ∃ A : ℕ → ℕ, IsAssign (henVals hens).length (grainVals grains).length A ∧
        makespan (henVals hens) (grainVals grains) A = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), ∃ A : ℕ → ℕ, IsAssign (henVals hens).length (grainVals grains).length A ∧
          makespan (henVals hens) (grainVals grains) A = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every assignment A from grain indices to hen indices, the maximum over hen indices i of the time for hen i to eat the grains assigned to it is at least r. The time for hen i is 0 if no grain is assigned to i; otherwise it is (max S_i - min S_i) + min(|hens[i] - min S_i|, |hens[i] - max S_i|), where S_i = { grains[j] | A(j) = i }.
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_9 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      ∀ A : ℕ → ℕ, IsAssign (henVals hens).length (grainVals grains).length A →
        r.val ≤ makespan (henVals hens) (grainVals grains) A := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), ∀ A : ℕ → ℕ, IsAssign (henVals hens).length (grainVals grains).length A →
          r.val ≤ makespan (henVals hens) (grainVals grains) A) := by
    sorry

  /-- Whenever the function returns a result r, let a = min_{0 <= j < len(grains)} grains[j] and b = max_{0 <= j < len(grains)} grains[j]. Then r <= min_{0 <= i < len(hens)} ((b - a) + min(|hens[i] - a|, |hens[i] - b|)).
    Preconditions: 1 <= len(hens), len(grains) <= 20000; for every i with 0 <= i < len(hens), 0 <= hens[i] <= 1000000000; for every j with 0 <= j < len(grains), 0 <= grains[j] <= 1000000000. -/
  theorem spec_10 (hens grains : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r) :
      r.val ≤ minOver (henVals hens).length (fun i =>
        (grainHi (grainVals grains) - grainLo (grainVals grains)) +
          min |henAt (henVals hens) i - grainLo (grainVals grains)|
            |henAt (henVals hens) i - grainHi (grainVals grains)|) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (hens grains : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (r : Std.I64) (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r), r.val ≤ minOver (henVals hens).length (fun i =>
          (grainHi (grainVals grains) - grainLo (grainVals grains)) +
            min |henAt (henVals hens) i - grainLo (grainVals grains)|
              |henAt (henVals hens) i - grainHi (grainVals grains)|)) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens', grains'), and there are bijections pi on {0,...,len(hens)-1} and sigma on {0,...,len(grains)-1} such that len(hens') = len(hens), len(grains') = len(grains), hens'[k] = hens[pi(k)] for all k, and grains'[k] = grains[sigma(k)] for all k, then r = r'.
    Preconditions: Both (hens, grains) and (hens', grains') satisfy the common constraints: 1 <= len(hens), len(grains), len(hens'), len(grains') <= 20000; all positions are in [0,1000000000]. -/
  theorem spec_11 (hens grains hens' grains' : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
      (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
      (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
        0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
      (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
        0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
      (hH_perm : (henVals hens').Perm (henVals hens))
      (hG_perm : (grainVals grains').Perm (grainVals grains))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens' grains' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (hens grains hens' grains' : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
        (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
        (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
          0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
        (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
          0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
        (hH_perm : (henVals hens').Perm (henVals hens))
        (hG_perm : (grainVals grains').Perm (grainVals grains))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens' grains' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens'', grains'') with hens''[i] = hens[i] + c for all i and grains''[j] = grains[j] + c for all j, then r = r'.
    Preconditions: Both original and shifted inputs satisfy the common constraints: positions remain in [0,1000000000]. There is an integer c such that 0 <= hens[i] + c <= 1000000000 for all i and 0 <= grains[j] + c <= 1000000000 for all j. -/
  theorem spec_12 (hens grains hens'' grains'' : Slice Std.I64) (c : ℤ)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hH_len'' : 1 ≤ (henVals hens'').length) (hH_len_le'' : (henVals hens'').length ≤ 20000)
      (hG_len'' : 1 ≤ (grainVals grains'').length) (hG_len_le'' : (grainVals grains'').length ≤ 20000)
      (hH_bd'' : ∀ i : ℕ, i < (henVals hens'').length →
        0 ≤ henAt (henVals hens'') i ∧ henAt (henVals hens'') i ≤ 1000000000)
      (hG_bd'' : ∀ j : ℕ, j < (grainVals grains'').length →
        0 ≤ grainAt (grainVals grains'') j ∧ grainAt (grainVals grains'') j ≤ 1000000000)
      (hH_shift : henVals hens'' = (henVals hens).map (fun x => x + c))
      (hG_shift : grainVals grains'' = (grainVals grains).map (fun x => x + c))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens'' grains'' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (hens grains hens'' grains'' : Slice Std.I64) (c : ℤ)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hH_len'' : 1 ≤ (henVals hens'').length) (hH_len_le'' : (henVals hens'').length ≤ 20000)
        (hG_len'' : 1 ≤ (grainVals grains'').length) (hG_len_le'' : (grainVals grains'').length ≤ 20000)
        (hH_bd'' : ∀ i : ℕ, i < (henVals hens'').length →
          0 ≤ henAt (henVals hens'') i ∧ henAt (henVals hens'') i ≤ 1000000000)
        (hG_bd'' : ∀ j : ℕ, j < (grainVals grains'').length →
          0 ≤ grainAt (grainVals grains'') j ∧ grainAt (grainVals grains'') j ≤ 1000000000)
        (hH_shift : henVals hens'' = (henVals hens).map (fun x => x + c))
        (hG_shift : grainVals grains'' = (grainVals grains).map (fun x => x + c))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens'' grains'' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens'', grains'') with hens''[i] = k * hens[i] for all i and grains''[j] = k * grains[j] for all j, then r' = k * r.
    Preconditions: Both original and scaled inputs satisfy the common constraints: positions remain in [0,1000000000]. There is a positive integer k such that 0 <= k * hens[i] <= 1000000000 for all i and 0 <= k * grains[j] <= 1000000000 for all j. -/
  theorem spec_13 (hens grains hens'' grains'' : Slice Std.I64) (k : ℤ)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hH_len'' : 1 ≤ (henVals hens'').length) (hH_len_le'' : (henVals hens'').length ≤ 20000)
      (hG_len'' : 1 ≤ (grainVals grains'').length) (hG_len_le'' : (grainVals grains'').length ≤ 20000)
      (hH_bd'' : ∀ i : ℕ, i < (henVals hens'').length →
        0 ≤ henAt (henVals hens'') i ∧ henAt (henVals hens'') i ≤ 1000000000)
      (hG_bd'' : ∀ j : ℕ, j < (grainVals grains'').length →
        0 ≤ grainAt (grainVals grains'') j ∧ grainAt (grainVals grains'') j ≤ 1000000000)
      (hk_pos : 0 < k)
      (hH_scale : henVals hens'' = (henVals hens).map (fun x => k * x))
      (hG_scale : grainVals grains'' = (grainVals grains).map (fun x => k * x))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens'' grains'' = ok r') :
      r'.val = k * r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (hens grains hens'' grains'' : Slice Std.I64) (k : ℤ)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hH_len'' : 1 ≤ (henVals hens'').length) (hH_len_le'' : (henVals hens'').length ≤ 20000)
        (hG_len'' : 1 ≤ (grainVals grains'').length) (hG_len_le'' : (grainVals grains'').length ≤ 20000)
        (hH_bd'' : ∀ i : ℕ, i < (henVals hens'').length →
          0 ≤ henAt (henVals hens'') i ∧ henAt (henVals hens'') i ≤ 1000000000)
        (hG_bd'' : ∀ j : ℕ, j < (grainVals grains'').length →
          0 ≤ grainAt (grainVals grains'') j ∧ grainAt (grainVals grains'') j ≤ 1000000000)
        (hk_pos : 0 < k)
        (hH_scale : henVals hens'' = (henVals hens).map (fun x => k * x))
        (hG_scale : grainVals grains'' = (grainVals grains).map (fun x => k * x))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens'' grains'' = ok r'), r'.val = k * r.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens', grains), then r' <= r.
    Preconditions: Both (hens, grains) and (hens', grains) satisfy the common constraints. The multiset of positions in hens' contains the multiset of positions in hens: len(hens') >= len(hens) and there is an injective map from hen indices to indices of hens' preserving positions. -/
  theorem spec_14 (hens grains hens' : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
      (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
        0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
      (hH_subperm : (henVals hens).Subperm (henVals hens'))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens' grains = ok r') :
      r'.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (hens grains hens' : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
        (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
          0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
        (hH_subperm : (henVals hens).Subperm (henVals hens'))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens' grains = ok r'), r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens, grains'), then r' >= r.
    Preconditions: Both (hens, grains) and (hens, grains') satisfy the common constraints. The multiset of positions in grains' contains the multiset of positions in grains: len(grains') >= len(grains) and there is an injective map from grain indices to indices of grains' preserving positions. -/
  theorem spec_15 (hens grains grains' : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
      (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
        0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
      (hG_subperm : (grainVals grains).Subperm (grainVals grains'))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens grains' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (hens grains grains' : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
        (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
          0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
        (hG_subperm : (grainVals grains).Subperm (grainVals grains'))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens grains' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens, grains'), then r = r'.
    Preconditions: Both (hens, grains) and (hens, grains') satisfy the common constraints. len(grains) >= 2, and there are indices j0, i0 with 0 <= j0 < len(grains), 0 <= i0 < len(hens), and grains[j0] = hens[i0]. grains' is obtained from grains by deleting index j0. -/
  theorem spec_16 (hens grains grains' : Slice Std.I64) (j0 i0 : ℕ)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
      (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
        0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
      (hG_two : 2 ≤ (grainVals grains).length)
      (hj0 : j0 < (grainVals grains).length)
      (hi0 : i0 < (henVals hens).length)
      (h_coincide : grainAt (grainVals grains) j0 = henAt (henVals hens) i0)
      (hG_del : grainVals grains' = (grainVals grains).eraseIdx j0)
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens grains' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (hens grains grains' : Slice Std.I64) (j0 i0 : ℕ)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
        (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
          0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
        (hG_two : 2 ≤ (grainVals grains).length)
        (hj0 : j0 < (grainVals grains).length)
        (hi0 : i0 < (henVals hens).length)
        (h_coincide : grainAt (grainVals grains) j0 = henAt (henVals hens) i0)
        (hG_del : grainVals grains' = (grainVals grains).eraseIdx j0)
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens grains' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (hens, grains) and returns r' on (hens', grains'), then r = r'.
    Preconditions: Both (hens, grains) and (hens', grains') satisfy the common constraints: 1 <= len(hens), len(grains), len(hens'), len(grains') <= 20000; all positions in [0,1000000000]. Either len(hens') = len(hens) - 1 and there exist indices i0, i1 with i0 != i1, hens[i0] = hens[i1], and hens' is obtained from hens by deleting index i0; or len(grains') = len(grains) - 1 and there exist indices j0, j1 with j0 != j1, grains[j0] = grains[j1], and grains' is obtained from grains by deleting index j0. -/
  theorem spec_17 (hens grains hens' grains' : Slice Std.I64)
      (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
      (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
      (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
        0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
      (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
        0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
      (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
      (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
      (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
        0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
      (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
        0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
      (h_case :
        (∃ i0 i1 : ℕ, i0 < (henVals hens).length ∧ i1 < (henVals hens).length ∧ i0 ≠ i1 ∧
            henAt (henVals hens) i0 = henAt (henVals hens) i1 ∧
            henVals hens' = (henVals hens).eraseIdx i0 ∧
            grainVals grains' = grainVals grains) ∨
        (∃ j0 j1 : ℕ, j0 < (grainVals grains).length ∧ j1 < (grainVals grains).length ∧ j0 ≠ j1 ∧
            grainAt (grainVals grains) j0 = grainAt (grainVals grains) j1 ∧
            grainVals grains' = (grainVals grains).eraseIdx j0 ∧
            henVals hens' = henVals hens))
      (r r' : Std.I64)
      (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
      (h_r' : Aegis.MinimumTime.minimum_time hens' grains' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (hens grains hens' grains' : Slice Std.I64)
        (hH_len : 1 ≤ (henVals hens).length) (hH_len_le : (henVals hens).length ≤ 20000)
        (hG_len : 1 ≤ (grainVals grains).length) (hG_len_le : (grainVals grains).length ≤ 20000)
        (hH_bd : ∀ i : ℕ, i < (henVals hens).length →
          0 ≤ henAt (henVals hens) i ∧ henAt (henVals hens) i ≤ 1000000000)
        (hG_bd : ∀ j : ℕ, j < (grainVals grains).length →
          0 ≤ grainAt (grainVals grains) j ∧ grainAt (grainVals grains) j ≤ 1000000000)
        (hH_len' : 1 ≤ (henVals hens').length) (hH_len_le' : (henVals hens').length ≤ 20000)
        (hG_len' : 1 ≤ (grainVals grains').length) (hG_len_le' : (grainVals grains').length ≤ 20000)
        (hH_bd' : ∀ i : ℕ, i < (henVals hens').length →
          0 ≤ henAt (henVals hens') i ∧ henAt (henVals hens') i ≤ 1000000000)
        (hG_bd' : ∀ j : ℕ, j < (grainVals grains').length →
          0 ≤ grainAt (grainVals grains') j ∧ grainAt (grainVals grains') j ≤ 1000000000)
        (h_case :
          (∃ i0 i1 : ℕ, i0 < (henVals hens).length ∧ i1 < (henVals hens).length ∧ i0 ≠ i1 ∧
              henAt (henVals hens) i0 = henAt (henVals hens) i1 ∧
              henVals hens' = (henVals hens).eraseIdx i0 ∧
              grainVals grains' = grainVals grains) ∨
          (∃ j0 j1 : ℕ, j0 < (grainVals grains).length ∧ j1 < (grainVals grains).length ∧ j0 ≠ j1 ∧
              grainAt (grainVals grains) j0 = grainAt (grainVals grains) j1 ∧
              grainVals grains' = (grainVals grains).eraseIdx j0 ∧
              henVals hens' = henVals hens))
        (r r' : Std.I64)
        (h_r : Aegis.MinimumTime.minimum_time hens grains = ok r)
        (h_r' : Aegis.MinimumTime.minimum_time hens' grains' = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.MinimumTime
