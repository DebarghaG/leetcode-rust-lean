import Aegis.GetResults.Code.Funs
import Mathlib.Data.Real.Basic

/-!
# Specifications of `Aegis.GetResults.get_results`

LeetCode problem `block-placement-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetResults

def row (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun i => i.val)

def IsType1 (v : alloc.vec.Vec Std.I64) : Prop := ∃ y : ℤ, row v = [1, y]

def IsType2 (v : alloc.vec.Vec Std.I64) : Prop := ∃ x sz : ℤ, row v = [2, x, sz]

def isType1Row (v : alloc.vec.Vec Std.I64) : Bool :=
  match row v with
  | [1, _] => true
  | _ => false

def isType2Row (v : alloc.vec.Vec Std.I64) : Bool :=
  match row v with
  | [2, _, _] => true
  | _ => false

def firstIsTwo (v : alloc.vec.Vec Std.I64) : Bool :=
  match row v with
  | 2 :: _ => true
  | _ => false

def type1Positions (qs : List (alloc.vec.Vec Std.I64)) : List ℤ :=
  qs.filterMap fun v =>
    match row v with
    | [1, y] => some y
    | _ => none

def obstaclesBefore (qs : List (alloc.vec.Vec Std.I64)) (j : Nat) : List ℤ :=
  type1Positions (qs.take j)

def countType2Before (qs : List (alloc.vec.Vec Std.I64)) (j : Nat) : Nat :=
  ((qs.take j).filter isType2Row).length

def numType2 (qs : List (alloc.vec.Vec Std.I64)) : Nat :=
  (qs.filter isType2Row).length

def numFirstIsTwo (qs : List (alloc.vec.Vec Std.I64)) : Nat :=
  (qs.filter firstIsTwo).length

def IsKthType2Row (qs : List (alloc.vec.Vec Std.I64)) (k j : Nat) (x sz : ℤ) : Prop :=
  ∃ v : alloc.vec.Vec Std.I64, qs[j]? = some v ∧ row v = [2, x, sz] ∧ countType2Before qs j = k

def Placeable (O : List ℤ) (x sz : ℤ) : Prop :=
  ∃ a : ℝ,
    0 ≤ a ∧ a + (sz : ℝ) ≤ (x : ℝ) ∧
      ∀ y ∈ O, ¬ (a < (y : ℝ) ∧ (y : ℝ) < a + (sz : ℝ))

def coordBound (n : Nat) : ℤ := min 50000 (3 * (n : ℤ))

def WellFormed (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ queries.val.length ∧
    queries.val.length ≤ 150000 ∧
    (∀ v ∈ queries.val, IsType1 v ∨ IsType2 v) ∧
    (∀ v ∈ queries.val, ∀ y : ℤ, row v = [1, y] →
      1 ≤ y ∧ y ≤ coordBound queries.val.length) ∧
    (∀ v ∈ queries.val, ∀ x sz : ℤ, row v = [2, x, sz] →
      1 ≤ x ∧ x ≤ coordBound queries.val.length ∧
        1 ≤ sz ∧ sz ≤ coordBound queries.val.length) ∧
    (type1Positions queries.val).Nodup ∧
    (∃ v ∈ queries.val, IsType2 v)

def keepFar (x : ℤ) (v : alloc.vec.Vec Std.I64) : Bool :=
  match row v with
  | [1, y] => decide (y ≤ x)
  | _ => true

def keepNotAt (p : ℤ) (v : alloc.vec.Vec Std.I64) : Bool :=
  match row v with
  | [1, y] => decide (y ≠ p)
  | _ => true

def deleteFarObstacles (qs : List (alloc.vec.Vec Std.I64)) (j : Nat) (x : ℤ) :
    List (alloc.vec.Vec Std.I64) :=
  (qs.take j).filter (keepFar x) ++ qs.drop j

def deleteObstaclesAt (qs : List (alloc.vec.Vec Std.I64)) (j : Nat) (p : ℤ) :
    List (alloc.vec.Vec Std.I64) :=
  (qs.take j).filter (keepNotAt p) ++ qs.drop j

/-- The function returns a result r (it does not fail) such that: (1) r has exactly one boolean entry for each type-2 row of queries, in the order in which those type-2 rows occur; (2) for every 0-based k, if the k-th type-2 row is queries[j] = [2,x,sz] and O = { y | there is t < j with queries[t] = [1,y] }, then r[k] = true if and only if there exists a real number a with 0 <= a, a+sz <= x, and for all y in O, not (a < y < a+sz). Equivalently, the closed interval [a,a+sz] lies in [0,x] and has no obstacle in its strict interior; touching an obstacle or an endpoint is allowed.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_1 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries) :
    ∃ r : alloc.vec.Vec Bool,
      Aegis.GetResults.get_results queries = ok r ∧
        r.val.length = numType2 queries.val ∧
        ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
          (r.val[k]? = some true ↔ Placeable (obstaclesBefore queries.val j) x sz) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries), ∃ r : alloc.vec.Vec Bool,
      Aegis.GetResults.get_results queries = ok r ∧
        r.val.length = numType2 queries.val ∧
        ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
          (r.val[k]? = some true ↔ Placeable (obstaclesBefore queries.val j) x sz)) := by
  sorry

/-- Whenever the function returns a result r, len(r) is exactly the number of indices i with queries[i][0] = 2, i.e. the number of type-2 rows in queries.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_2 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    r.val.length = numFirstIsTwo queries.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), r.val.length = numFirstIsTwo queries.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, go out of bounds, or overflow.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_3 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries) :
    ∃ r : alloc.vec.Vec Bool, Aegis.GetResults.get_results queries = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries), ∃ r : alloc.vec.Vec Bool, Aegis.GetResults.get_results queries = ok r) := by
  sorry

/-- Whenever the function returns r, for every 0-based k whose type-2 row is [2,x,sz] with prior obstacle set O, if r[k] = true then there exist real numbers a and b such that b-a = sz, 0 <= a, b <= x, and no y in O satisfies a < y < b.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_4 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      r.val[k]? = some true →
        ∃ a b : ℝ,
          b - a = (sz : ℝ) ∧ 0 ≤ a ∧ b ≤ (x : ℝ) ∧
            ∀ y ∈ obstaclesBefore queries.val j, ¬ (a < (y : ℝ) ∧ (y : ℝ) < b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      r.val[k]? = some true →
        ∃ a b : ℝ,
          b - a = (sz : ℝ) ∧ 0 ≤ a ∧ b ≤ (x : ℝ) ∧
            ∀ y ∈ obstaclesBefore queries.val j, ¬ (a < (y : ℝ) ∧ (y : ℝ) < b)) := by
  sorry

/-- Whenever the function returns r, for every 0-based k whose type-2 row is [2,x,sz] with prior obstacle set O, if r[k] = false then for every real a with 0 <= a and a+sz <= x there exists y in O such that a < y < a+sz.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_5 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      r.val[k]? = some false →
        ∀ a : ℝ, 0 ≤ a → a + (sz : ℝ) ≤ (x : ℝ) →
          ∃ y ∈ obstaclesBefore queries.val j, a < (y : ℝ) ∧ (y : ℝ) < a + (sz : ℝ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      r.val[k]? = some false →
        ∀ a : ℝ, 0 ≤ a → a + (sz : ℝ) ≤ (x : ℝ) →
          ∃ y ∈ obstaclesBefore queries.val j, a < (y : ℝ) ∧ (y : ℝ) < a + (sz : ℝ)) := by
  sorry

/-- Whenever the function returns r, let k < l be two type-2 occurrences such that the k-th type-2 row is [2,x,sz1], the l-th type-2 row is [2,x,sz2], no type-1 row occurs strictly between these two rows, and sz1 <= sz2. Then r[l] = true implies r[k] = true.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_6 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k l jk jl : Nat) (x sz1 sz2 : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x sz1 →
          IsKthType2Row queries.val l jl x sz2 →
            (∀ t : Nat, jk < t → t < jl → ∀ v : alloc.vec.Vec Std.I64,
              queries.val[t]? = some v → ¬ IsType1 v) →
              sz1 ≤ sz2 →
                r.val[l]? = some true → r.val[k]? = some true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k l jk jl : Nat) (x sz1 sz2 : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x sz1 →
          IsKthType2Row queries.val l jl x sz2 →
            (∀ t : Nat, jk < t → t < jl → ∀ v : alloc.vec.Vec Std.I64,
              queries.val[t]? = some v → ¬ IsType1 v) →
              sz1 ≤ sz2 →
                r.val[l]? = some true → r.val[k]? = some true) := by
  sorry

/-- Whenever the function returns r, let k < l be two type-2 occurrences such that the k-th row is [2,x1,sz], the l-th row is [2,x2,sz], no type-1 row occurs strictly between these two rows, and x1 <= x2. Then r[k] = true implies r[l] = true.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_7 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k l jk jl : Nat) (x1 x2 sz : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x1 sz →
          IsKthType2Row queries.val l jl x2 sz →
            (∀ t : Nat, jk < t → t < jl → ∀ v : alloc.vec.Vec Std.I64,
              queries.val[t]? = some v → ¬ IsType1 v) →
              x1 ≤ x2 →
                r.val[k]? = some true → r.val[l]? = some true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k l jk jl : Nat) (x1 x2 sz : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x1 sz →
          IsKthType2Row queries.val l jl x2 sz →
            (∀ t : Nat, jk < t → t < jl → ∀ v : alloc.vec.Vec Std.I64,
              queries.val[t]? = some v → ¬ IsType1 v) →
              x1 ≤ x2 →
                r.val[k]? = some true → r.val[l]? = some true) := by
  sorry

/-- Whenever the function returns r, let k < l be two type-2 occurrences whose rows are [2,x,sz] and [2,x,sz] respectively, with the same x and the same sz. Then r[l] = true implies r[k] = true.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_8 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k l jk jl : Nat) (x sz : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x sz →
          IsKthType2Row queries.val l jl x sz →
            r.val[l]? = some true → r.val[k]? = some true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k l jk jl : Nat) (x sz : ℤ),
      k < l →
        IsKthType2Row queries.val k jk x sz →
          IsKthType2Row queries.val l jl x sz →
            r.val[l]? = some true → r.val[k]? = some true) := by
  sorry

/-- Let k be a 0-based type-2 occurrence at row j of queries, and let r be the result returned for queries. For every well-formed input queries2 that agrees with queries on all rows t with 0 <= t <= j and in which the k-th type-2 occurrence is also at row j, the k-th entry of the result returned for queries2 equals r[k].
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. Additionally, any second input queries2 mentioned in the statement is well-formed in the same sense. -/
theorem spec_9 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ),
      IsKthType2Row queries.val k j x sz →
        ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
          (∀ t : Nat, t ≤ j → queries2.val[t]? = queries.val[t]?) →
            IsKthType2Row queries2.val k j x sz →
              ∀ r2 : alloc.vec.Vec Bool,
                Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]? := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ),
      IsKthType2Row queries.val k j x sz →
        ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
          (∀ t : Nat, t ≤ j → queries2.val[t]? = queries.val[t]?) →
            IsKthType2Row queries2.val k j x sz →
              ∀ r2 : alloc.vec.Vec Bool,
                Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]?) := by
  sorry

/-- Let k be a 0-based type-2 occurrence of queries with row [2,x,sz], and let O be the set of type-1 positions occurring before it. For every well-formed input queries2 and every 0-based type-2 occurrence k2 of queries2 with row [2,x,sz] such that the set of type-1 positions occurring before k2 in queries2 is also O, the k2-th boolean result for queries2 equals the k-th boolean result for queries.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. Additionally, any second input queries2 mentioned in the statement is well-formed in the same sense. -/
theorem spec_10 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        ∀ (k2 j2 : Nat), IsKthType2Row queries2.val k2 j2 x sz →
          (∀ y : ℤ,
            y ∈ obstaclesBefore queries2.val j2 ↔ y ∈ obstaclesBefore queries.val j) →
            ∀ r2 : alloc.vec.Vec Bool,
              Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k2]? = r.val[k]? := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        ∀ (k2 j2 : Nat), IsKthType2Row queries2.val k2 j2 x sz →
          (∀ y : ℤ,
            y ∈ obstaclesBefore queries2.val j2 ↔ y ∈ obstaclesBefore queries.val j) →
            ∀ r2 : alloc.vec.Vec Bool,
              Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k2]? = r.val[k]?) := by
  sorry

/-- Whenever the function returns r, for every 0-based k whose type-2 row is [2,x,sz], prior obstacles at positions y with y > x have no effect on r[k]: r[k] is unchanged if all such prior type-1 rows are deleted before that query, keeping all other rows and the same type-2 occurrence k.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_11 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        queries2.val = deleteFarObstacles queries.val j x →
          ∀ r2 : alloc.vec.Vec Bool,
            Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]? := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        queries2.val = deleteFarObstacles queries.val j x →
          ∀ r2 : alloc.vec.Vec Bool,
            Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]?) := by
  sorry

/-- Whenever the function returns r, for every 0-based k whose type-2 row is [2,x,sz], a prior obstacle exactly at position x has no effect on r[k]: r[k] is unchanged if all prior type-1 rows at position x are deleted before that query, keeping all other rows and the same type-2 occurrence k.
  Preconditions: queries is a well-formed block-placement input: 1 <= len(queries) <= 150000; every row is either [1,y] with exactly two entries or [2,x,sz] with exactly three entries; every y, x, and sz is an integer satisfying 1 <= value <= min(50000, 3*len(queries)); all type-1 positions y are pairwise distinct; and at least one type-2 row exists. -/
theorem spec_12 (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r) :
    ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        queries2.val = deleteObstaclesAt queries.val j x →
          ∀ r2 : alloc.vec.Vec Bool,
            Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]? := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (queries : Slice (alloc.vec.Vec Std.I64)) (h : WellFormed queries)
    (r : alloc.vec.Vec Bool) (hr : Aegis.GetResults.get_results queries = ok r), ∀ (k j : Nat) (x sz : ℤ), IsKthType2Row queries.val k j x sz →
      ∀ (queries2 : Slice (alloc.vec.Vec Std.I64)), WellFormed queries2 →
        queries2.val = deleteObstaclesAt queries.val j x →
          ∀ r2 : alloc.vec.Vec Bool,
            Aegis.GetResults.get_results queries2 = ok r2 → r2.val[k]? = r.val[k]?) := by
  sorry

end AegisSpec.GetResults
