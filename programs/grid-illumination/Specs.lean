import Aegis.GridIllumination.Code.Funs

/-!
# Specifications of `Aegis.GridIllumination.grid_illumination`

LeetCode problem `grid-illumination`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.GridIllumination (grid_illumination)

  namespace AegisSpec.GridIllumination

  abbrev Cell := ℤ × ℤ

  def coord (v : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ :=
    ((v.val[k]?).map (fun x => x.val)).getD 0

  def cell (v : alloc.vec.Vec Std.I64) : Cell := (coord v 0, coord v 1)

  def entry (r : alloc.vec.Vec Std.I64) (j : ℕ) : ℤ := coord r j

  def Aligned (p q : Cell) : Prop :=
    p.1 = q.1 ∨ p.2 = q.2 ∨ p.1 - p.2 = q.1 - q.2 ∨ p.1 + p.2 = q.1 + q.2

  def Near (p q : Cell) : Prop := |q.1 - p.1| ≤ 1 ∧ |q.2 - p.2| ≤ 1

  def Occurs (lamps : Slice (alloc.vec.Vec Std.I64)) (p : Cell) : Prop :=
    ∃ (i : ℕ) (v : alloc.vec.Vec Std.I64), lamps.val[i]? = some v ∧ cell v = p

  def DimmedBefore (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) (p : Cell) : Prop :=
    ∃ (k : ℕ) (q : alloc.vec.Vec Std.I64), k < j ∧ queries.val[k]? = some q ∧ Near p (cell q)

  def Witness (queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ)
      (lamp q : alloc.vec.Vec Std.I64) : Prop :=
    Aligned (cell lamp) (cell q) ∧ ¬ DimmedBefore queries j (cell lamp)

  def HasWitness (lamps queries : Slice (alloc.vec.Vec Std.I64)) (j : ℕ) : Prop :=
    ∃ (q : alloc.vec.Vec Std.I64) (i : ℕ) (lamp : alloc.vec.Vec Std.I64),
      queries.val[j]? = some q ∧ i < lamps.val.length ∧ lamps.val[i]? = some lamp ∧
        Witness queries j lamp q

  def LampAligned (lamps : Slice (alloc.vec.Vec Std.I64)) (q : Cell) : Prop :=
    ∃ (i : ℕ) (lamp : alloc.vec.Vec Std.I64),
      i < lamps.val.length ∧ lamps.val[i]? = some lamp ∧ Aligned (cell lamp) q

  def NRange (n : Std.I64) : Prop := 1 ≤ n.val ∧ n.val ≤ 1000000000

  def CellsOK (n : Std.I64) (l : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    l.val.length ≤ 20000 ∧
      ∀ (i : ℕ) (v : alloc.vec.Vec Std.I64), l.val[i]? = some v →
        v.val.length = 2 ∧ 0 ≤ coord v 0 ∧ coord v 0 < n.val ∧
          0 ≤ coord v 1 ∧ coord v 1 < n.val

  /-- Whenever the function returns a result r, len(r) = len(queries), and for every j with 0 <= j < len(queries), letting q_r = queries[j][0] and q_c = queries[j][1], r[j] = 1 if and only if there exists i with 0 <= i < len(lamps) such that, writing p_r = lamps[i][0] and p_c = lamps[i][1], (p_r = q_r or p_c = q_c or p_r - p_c = q_r - q_c or p_r + p_c = q_r + q_c) and for every k with 0 <= k < j, not (|queries[k][0] - p_r| <= 1 and |queries[k][1] - p_c| <= 1); if no such i exists then r[j] = 0.
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; for every i with 0 <= i < len(lamps), len(lamps[i]) = 2 and 0 <= lamps[i][0] < n and 0 <= lamps[i][1] < n; for every j with 0 <= j < len(queries), len(queries[j]) = 2 and 0 <= queries[j][0] < n and 0 <= queries[j][1] < n. -/
  theorem spec_1 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      r.val.length = queries.val.length ∧
        ∀ j : ℕ, j < queries.val.length →
          (entry r j = 1 ↔ HasWitness lamps queries j) ∧
            (¬ HasWitness lamps queries j → entry r j = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), r.val.length = queries.val.length ∧
          ∀ j : ℕ, j < queries.val.length →
            (entry r j = 1 ↔ HasWitness lamps queries j) ∧
              (¬ HasWitness lamps queries j → entry r j = 0)) := by
    sorry

  /-- The function returns a result r (it does not fail by panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_2 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries) :
      ∃ r : alloc.vec.Vec Std.I64, grid_illumination n lamps queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries), ∃ r : alloc.vec.Vec Std.I64, grid_illumination n lamps queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries).
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_3 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      r.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), r.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), r[j] = 0 or r[j] = 1.
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_4 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      ∀ j : ℕ, j < r.val.length → entry r j = 0 ∨ entry r j = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), ∀ j : ℕ, j < r.val.length → entry r j = 0 ∨ entry r j = 1) := by
    sorry

  /-- Whenever the calls grid_illumination n lamps queries and grid_illumination n lamps2 queries return results r and r2, len(r) = len(r2) = len(queries) and for every j with 0 <= j < len(queries), r[j] = r2[j].
    Preconditions: n and queries satisfy the query constraints from spec_1; lamps and lamps2 both satisfy the lamp constraints (len <= 20000, each inner vector has length 2, all coordinates in [0,n)); for every cell (a,b) with 0 <= a < n and 0 <= b < n, (a,b) occurs at least once in lamps if and only if it occurs at least once in lamps2. -/
  theorem spec_5 (n : Std.I64) (lamps lamps2 queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hlamps2 : CellsOK n lamps2)
      (hqueries : CellsOK n queries)
      (hsame : ∀ p : Cell, Occurs lamps p ↔ Occurs lamps2 p)
      (r r2 : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r)
      (hr2 : grid_illumination n lamps2 queries = ok r2) :
      r.val.length = queries.val.length ∧ r2.val.length = queries.val.length ∧
        ∀ j : ℕ, j < queries.val.length → entry r j = entry r2 j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (lamps lamps2 queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hlamps2 : CellsOK n lamps2)
        (hqueries : CellsOK n queries)
        (hsame : ∀ p : Cell, Occurs lamps p ↔ Occurs lamps2 p)
        (r r2 : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r)
        (hr2 : grid_illumination n lamps2 queries = ok r2), r.val.length = queries.val.length ∧ r2.val.length = queries.val.length ∧
          ∀ j : ℕ, j < queries.val.length → entry r j = entry r2 j) := by
    sorry

  /-- Whenever the calls grid_illumination n lamps1 queries and grid_illumination n lamps2 queries return results r1 and r2, for every j with 0 <= j < len(queries), r1[j] <= r2[j].
    Preconditions: n and queries satisfy the constraints from spec_1; lamps1 and lamps2 satisfy the lamp constraints; for every i with 0 <= i < len(lamps1), the cell (lamps1[i][0], lamps1[i][1]) occurs at least once in lamps2. -/
  theorem spec_6 (n : Std.I64) (lamps1 lamps2 queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps1 : CellsOK n lamps1) (hlamps2 : CellsOK n lamps2)
      (hqueries : CellsOK n queries)
      (hsub : ∀ (i : ℕ) (v : alloc.vec.Vec Std.I64),
        lamps1.val[i]? = some v → Occurs lamps2 (cell v))
      (r1 r2 : alloc.vec.Vec Std.I64)
      (hr1 : grid_illumination n lamps1 queries = ok r1)
      (hr2 : grid_illumination n lamps2 queries = ok r2) :
      ∀ j : ℕ, j < queries.val.length → entry r1 j ≤ entry r2 j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (lamps1 lamps2 queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps1 : CellsOK n lamps1) (hlamps2 : CellsOK n lamps2)
        (hqueries : CellsOK n queries)
        (hsub : ∀ (i : ℕ) (v : alloc.vec.Vec Std.I64),
          lamps1.val[i]? = some v → Occurs lamps2 (cell v))
        (r1 r2 : alloc.vec.Vec Std.I64)
        (hr1 : grid_illumination n lamps1 queries = ok r1)
        (hr2 : grid_illumination n lamps2 queries = ok r2), ∀ j : ℕ, j < queries.val.length → entry r1 j ≤ entry r2 j) := by
    sorry

  /-- Whenever the calls grid_illumination n lamps queries and grid_illumination n lamps2 queries return results r and r2, r and r2 have the same length and r[j] = r2[j] for every j with 0 <= j < len(queries).
    Preconditions: n and queries satisfy the query constraints from spec_1; lamps and lamps2 satisfy the lamp constraints; let L be the set of cells occurring in lamps and L2 the set occurring in lamps2; for every cell p = (a,b) in the symmetric difference of L and L2 (present in exactly one of the two sets), and for every j with 0 <= j < len(queries), a != queries[j][0], b != queries[j][1], a - b != queries[j][0] - queries[j][1], and a + b != queries[j][0] + queries[j][1]. -/
  theorem spec_7 (n : Std.I64) (lamps lamps2 queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hlamps2 : CellsOK n lamps2)
      (hqueries : CellsOK n queries)
      (hsymm : ∀ p : Cell,
        (Occurs lamps p ∧ ¬ Occurs lamps2 p) ∨ (¬ Occurs lamps p ∧ Occurs lamps2 p) →
          ∀ (j : ℕ) (q : alloc.vec.Vec Std.I64),
            queries.val[j]? = some q → ¬ Aligned p (cell q))
      (r r2 : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r)
      (hr2 : grid_illumination n lamps2 queries = ok r2) :
      r.val.length = r2.val.length ∧
        ∀ j : ℕ, j < queries.val.length → entry r j = entry r2 j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (lamps lamps2 queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hlamps2 : CellsOK n lamps2)
        (hqueries : CellsOK n queries)
        (hsymm : ∀ p : Cell,
          (Occurs lamps p ∧ ¬ Occurs lamps2 p) ∨ (¬ Occurs lamps p ∧ Occurs lamps2 p) →
            ∀ (j : ℕ) (q : alloc.vec.Vec Std.I64),
              queries.val[j]? = some q → ¬ Aligned p (cell q))
        (r r2 : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r)
        (hr2 : grid_illumination n lamps2 queries = ok r2), r.val.length = r2.val.length ∧
          ∀ j : ℕ, j < queries.val.length → entry r j = entry r2 j) := by
    sorry

  /-- Whenever the function returns a result r, for all j and k with 0 <= j < k < len(queries) and queries[j][0] = queries[k][0] and queries[j][1] = queries[k][1], if r[j] = 0 then r[k] = 0.
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_8 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      ∀ (j k : ℕ) (qj qk : alloc.vec.Vec Std.I64),
        j < k → k < queries.val.length →
          queries.val[j]? = some qj → queries.val[k]? = some qk → cell qj = cell qk →
            entry r j = 0 → entry r k = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), ∀ (j k : ℕ) (qj qk : alloc.vec.Vec Std.I64),
          j < k → k < queries.val.length →
            queries.val[j]? = some qj → queries.val[k]? = some qk → cell qj = cell qk →
              entry r j = 0 → entry r k = 0) := by
    sorry

  /-- Whenever the calls grid_illumination n lamps queries and grid_illumination n lamps queries2 return results r and r2, for every j with 0 <= j < len(queries) and 0 <= j < len(queries2), if for every i with 0 <= i <= j, queries[i][0] = queries2[i][0] and queries[i][1] = queries2[i][1], then r[j] = r2[j].
    Preconditions: n, lamps, queries, and queries2 satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; len(queries2) <= 20000; every lamps[i], queries[j], and queries2[j] has length 2; all their coordinates are in [0, n). -/
  theorem spec_9 (n : Std.I64) (lamps queries queries2 : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (hqueries2 : CellsOK n queries2)
      (r r2 : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r)
      (hr2 : grid_illumination n lamps queries2 = ok r2) :
      ∀ j : ℕ, j < queries.val.length → j < queries2.val.length →
        (∀ (i : ℕ) (a b : alloc.vec.Vec Std.I64), i ≤ j →
          queries.val[i]? = some a → queries2.val[i]? = some b → cell a = cell b) →
        entry r j = entry r2 j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (lamps queries queries2 : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (hqueries2 : CellsOK n queries2)
        (r r2 : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r)
        (hr2 : grid_illumination n lamps queries2 = ok r2), ∀ j : ℕ, j < queries.val.length → j < queries2.val.length →
          (∀ (i : ℕ) (a b : alloc.vec.Vec Std.I64), i ≤ j →
            queries.val[i]? = some a → queries2.val[i]? = some b → cell a = cell b) →
          entry r j = entry r2 j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries) and every i with 0 <= i < len(lamps), if, writing p_r = lamps[i][0], p_c = lamps[i][1], q_r = queries[j][0], q_c = queries[j][1], we have (p_r = q_r or p_c = q_c or p_r - p_c = q_r - q_c or p_r + p_c = q_r + q_c) and for every k with 0 <= k < j, not (|queries[k][0] - p_r| <= 1 and |queries[k][1] - p_c| <= 1), then r[j] = 1.
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_10 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      ∀ (j : ℕ) (q : alloc.vec.Vec Std.I64) (i : ℕ) (lamp : alloc.vec.Vec Std.I64),
        j < queries.val.length → queries.val[j]? = some q →
          i < lamps.val.length → lamps.val[i]? = some lamp →
            Witness queries j lamp q → entry r j = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), ∀ (j : ℕ) (q : alloc.vec.Vec Std.I64) (i : ℕ) (lamp : alloc.vec.Vec Std.I64),
          j < queries.val.length → queries.val[j]? = some q →
            i < lamps.val.length → lamps.val[i]? = some lamp →
              Witness queries j lamp q → entry r j = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if r[j] = 1 then there exists i with 0 <= i < len(lamps) such that, writing p_r = lamps[i][0], p_c = lamps[i][1], q_r = queries[j][0], q_c = queries[j][1], we have (p_r = q_r or p_c = q_c or p_r - p_c = q_r - q_c or p_r + p_c = q_r + q_c) and for every k with 0 <= k < j, not (|queries[k][0] - p_r| <= 1 and |queries[k][1] - p_c| <= 1).
    Preconditions: n, lamps, queries satisfy the problem constraints: 1 <= n <= 10^9; len(lamps) <= 20000; len(queries) <= 20000; every lamps[i] and queries[j] has length 2; all coordinates are in [0, n). -/
  theorem spec_11 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      ∀ j : ℕ, j < queries.val.length → entry r j = 1 → HasWitness lamps queries j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), ∀ j : ℕ, j < queries.val.length → entry r j = 1 → HasWitness lamps queries j) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries) and for every j with 0 <= j < len(queries), r[j] = 0.
    Preconditions: n and queries satisfy the query constraints from spec_1; len(lamps) = 0. -/
  theorem spec_12 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hqueries : CellsOK n queries) (hlamps : lamps.val.length = 0)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      r.val.length = queries.val.length ∧
        ∀ j : ℕ, j < queries.val.length → entry r j = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hqueries : CellsOK n queries) (hlamps : lamps.val.length = 0)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), r.val.length = queries.val.length ∧
          ∀ j : ℕ, j < queries.val.length → entry r j = 0) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 1 and r[0] = 1 if and only if there exists i with 0 <= i < len(lamps) such that, writing p_r = lamps[i][0], p_c = lamps[i][1], q_r = queries[0][0], q_c = queries[0][1], we have (p_r = q_r or p_c = q_c or p_r - p_c = q_r - q_c or p_r + p_c = q_r + q_c); otherwise r[0] = 0.
    Preconditions: n and lamps satisfy the constraints from spec_1; len(queries) = 1; queries[0] has length 2 and 0 <= queries[0][0] < n and 0 <= queries[0][1] < n. -/
  theorem spec_13 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : NRange n) (hlamps : CellsOK n lamps) (hlen : queries.val.length = 1)
      (hquery : ∀ q : alloc.vec.Vec Std.I64, queries.val[0]? = some q →
        q.val.length = 2 ∧ 0 ≤ coord q 0 ∧ coord q 0 < n.val ∧
          0 ≤ coord q 1 ∧ coord q 1 < n.val)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      r.val.length = 1 ∧
        ∀ q : alloc.vec.Vec Std.I64, queries.val[0]? = some q →
          (entry r 0 = 1 ↔ LampAligned lamps (cell q)) ∧
            (¬ LampAligned lamps (cell q) → entry r 0 = 0) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : NRange n) (hlamps : CellsOK n lamps) (hlen : queries.val.length = 1)
        (hquery : ∀ q : alloc.vec.Vec Std.I64, queries.val[0]? = some q →
          q.val.length = 2 ∧ 0 ≤ coord q 0 ∧ coord q 0 < n.val ∧
            0 ≤ coord q 1 ∧ coord q 1 < n.val)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), r.val.length = 1 ∧
          ∀ q : alloc.vec.Vec Std.I64, queries.val[0]? = some q →
            (entry r 0 = 1 ↔ LampAligned lamps (cell q)) ∧
              (¬ LampAligned lamps (cell q) → entry r 0 = 0)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries). If len(queries) > 0, then r[0] = 1 if and only if len(lamps) > 0, and for every j with 1 <= j < len(queries), r[j] = 0.
    Preconditions: n = 1; lamps and queries satisfy the problem constraints (so every coordinate in lamps and queries is 0); len(lamps) <= 20000; len(queries) <= 20000. -/
  theorem spec_14 (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn : n.val = 1) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
      (r : alloc.vec.Vec Std.I64)
      (hr : grid_illumination n lamps queries = ok r) :
      r.val.length = queries.val.length ∧
        (0 < queries.val.length →
          (entry r 0 = 1 ↔ 0 < lamps.val.length) ∧
            ∀ j : ℕ, 1 ≤ j → j < queries.val.length → entry r j = 0) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn : n.val = 1) (hlamps : CellsOK n lamps) (hqueries : CellsOK n queries)
        (r : alloc.vec.Vec Std.I64)
        (hr : grid_illumination n lamps queries = ok r), r.val.length = queries.val.length ∧
          (0 < queries.val.length →
            (entry r 0 = 1 ↔ 0 < lamps.val.length) ∧
              ∀ j : ℕ, 1 ≤ j → j < queries.val.length → entry r j = 0)) := by
    sorry

  /-- Whenever the calls grid_illumination n1 lamps queries and grid_illumination n2 lamps queries return results r1 and r2, len(r1) = len(r2) = len(queries) and r1[j] = r2[j] for every j with 0 <= j < len(queries).
    Preconditions: n1 and n2 satisfy 1 <= n1 <= 10^9 and 1 <= n2 <= 10^9; lamps and queries satisfy the problem constraints for both n1 and n2, meaning len(lamps) <= 20000, len(queries) <= 20000, every lamps[i] and queries[j] has length 2, and every coordinate is at least 0 and less than both n1 and n2. -/
  theorem spec_15 (n1 n2 : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
      (hn1 : NRange n1) (hn2 : NRange n2)
      (hlamps1 : CellsOK n1 lamps) (hlamps2 : CellsOK n2 lamps)
      (hqueries1 : CellsOK n1 queries) (hqueries2 : CellsOK n2 queries)
      (r1 r2 : alloc.vec.Vec Std.I64)
      (hr1 : grid_illumination n1 lamps queries = ok r1)
      (hr2 : grid_illumination n2 lamps queries = ok r2) :
      r1.val.length = queries.val.length ∧ r2.val.length = queries.val.length ∧
        ∀ j : ℕ, j < queries.val.length → entry r1 j = entry r2 j := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n1 n2 : Std.I64) (lamps queries : Slice (alloc.vec.Vec Std.I64))
        (hn1 : NRange n1) (hn2 : NRange n2)
        (hlamps1 : CellsOK n1 lamps) (hlamps2 : CellsOK n2 lamps)
        (hqueries1 : CellsOK n1 queries) (hqueries2 : CellsOK n2 queries)
        (r1 r2 : alloc.vec.Vec Std.I64)
        (hr1 : grid_illumination n1 lamps queries = ok r1)
        (hr2 : grid_illumination n2 lamps queries = ok r2), r1.val.length = queries.val.length ∧ r2.val.length = queries.val.length ∧
          ∀ j : ℕ, j < queries.val.length → entry r1 j = entry r2 j) := by
    sorry

  end AegisSpec.GridIllumination
