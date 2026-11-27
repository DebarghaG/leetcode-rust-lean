import Aegis.LeftmostBuildingQueries.Code.Funs

/-!
# Specifications of `Aegis.LeftmostBuildingQueries.leftmost_building_queries`

LeetCode problem `find-building-where-alice-and-bob-can-meet`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LeftmostBuildingQueries

namespace AegisSpec.LeftmostBuildingQueries

def sliceVals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def vecVals (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

def queryVals (queries : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  queries.val.map vecVals

def queryAt (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : List ℤ :=
  (queryVals queries).getD i []

def qA (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : ℤ := (queryAt queries i).getD 0 (-1)

def qB (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : ℤ := (queryAt queries i).getD 1 (-1)

def rAt (r : alloc.vec.Vec I64) (i : Nat) : ℤ := (vecVals r).getD i (-1)

def hAt (heights : Slice I64) (x : ℤ) : ℤ :=
  if 0 ≤ x ∧ x < ((sliceVals heights).length : ℤ) then
    (sliceVals heights).getD x.toNat (-1)
  else -1

def inR (heights : Slice I64) (x m : ℤ) : Prop :=
  m = x ∨ (x < m ∧ m < ((sliceVals heights).length : ℤ) ∧ hAt heights m > hAt heights x)

def meets (heights : Slice I64) (a b : ℤ) : Prop :=
  ∃ m : ℤ, inR heights a m ∧ inR heights b m

/-- Let n = len(heights). Whenever the function returns a result r (and it does not fail under the preconditions), len(r) = len(queries), and for every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1] and defining R(x) = {x} union {m | x < m < n and heights[m] > heights[x]} for each index x with 0 <= x < n, the following holds: if R(a) intersection R(b) is nonempty, then r[i] = min(R(a) intersection R(b)); otherwise r[i] = -1.
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_1 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)) :
    ∃ r : alloc.vec.Vec I64,
      leftmost_building_queries heights queries = ok r ∧
        (vecVals r).length = (queryVals queries).length ∧
          ∀ (i : Nat), i < (queryVals queries).length →
            let a := qA queries i
            let b := qB queries i
            (meets heights a b →
                inR heights a (rAt r i) ∧ inR heights b (rAt r i) ∧
                  ∀ m : ℤ, inR heights a m → inR heights b m → rAt r i ≤ m) ∧
              (¬ meets heights a b → rAt r i = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)), ∃ r : alloc.vec.Vec I64,
      leftmost_building_queries heights queries = ok r ∧
        (vecVals r).length = (queryVals queries).length ∧
          ∀ (i : Nat), i < (queryVals queries).length →
            let a := qA queries i
            let b := qB queries i
            (meets heights a b →
                inR heights a (rAt r i) ∧ inR heights b (rAt r i) ∧
                  ∀ m : ℤ, inR heights a m → inR heights b m → rAt r i ≤ m) ∧
              (¬ meets heights a b → rAt r i = -1)) := by
  sorry

/-- Let n = len(heights). The function returns a result r with len(r) = len(queries).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_2 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)) :
    ∃ r : alloc.vec.Vec I64,
      leftmost_building_queries heights queries = ok r ∧
        (vecVals r).length = (queryVals queries).length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)), ∃ r : alloc.vec.Vec I64,
      leftmost_building_queries heights queries = ok r ∧
        (vecVals r).length = (queryVals queries).length) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), r[i] = -1 or (0 <= r[i] < n).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_3 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      rAt r i = -1 ∨ (0 ≤ rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      rAt r i = -1 ∨ (0 ≤ rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ))) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), if queries[i][0] = queries[i][1] = a, then r[i] = a.
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_4 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      qB queries i = a → rAt r i = a := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      qB queries i = a → rAt r i = a) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if a != b and heights[min(a,b)] < heights[max(a,b)], then r[i] = max(a,b).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_5 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) < hAt heights (max a b) → rAt r i = max a b := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) < hAt heights (max a b) → rAt r i = max a b) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if a != b and heights[min(a,b)] >= heights[max(a,b)], then r[i] = -1 or r[i] > max(a,b).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_6 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) ≥ hAt heights (max a b) →
        rAt r i = -1 ∨ rAt r i > max a b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) ≥ hAt heights (max a b) →
        rAt r i = -1 ∨ rAt r i > max a b) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if r[i] != -1, then r[i] = a or (a < r[i] < n and heights[r[i]] > heights[a]).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_7 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      rAt r i ≠ -1 →
        rAt r i = a ∨
          (a < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
            hAt heights (rAt r i) > hAt heights a) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      rAt r i ≠ -1 →
        rAt r i = a ∨
          (a < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
            hAt heights (rAt r i) > hAt heights a)) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if r[i] != -1, then r[i] = b or (b < r[i] < n and heights[r[i]] > heights[b]).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_8 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let b := qB queries i
      rAt r i ≠ -1 →
        rAt r i = b ∨
          (b < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
            hAt heights (rAt r i) > hAt heights b) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let b := qB queries i
      rAt r i ≠ -1 →
        rAt r i = b ∨
          (b < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
            hAt heights (rAt r i) > hAt heights b)) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if r[i] != -1, then for every m with 0 <= m < r[i], it is not the case that ( (m = a or (a < m < n and heights[m] > heights[a])) and (m = b or (b < m < n and heights[m] > heights[b])) ).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_9 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i ≠ -1 →
        ∀ m : ℤ, 0 ≤ m → m < rAt r i → ¬ (inR heights a m ∧ inR heights b m) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i ≠ -1 →
        ∀ m : ℤ, 0 ≤ m → m < rAt r i → ¬ (inR heights a m ∧ inR heights b m)) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if r[i] = -1, then for every m with 0 <= m < n, it is not the case that ( (m = a or (a < m < n and heights[m] > heights[a])) and (m = b or (b < m < n and heights[m] > heights[b])) ).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_10 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i = -1 →
        ∀ m : ℤ, 0 ≤ m → m < ((sliceVals heights).length : ℤ) →
          ¬ (inR heights a m ∧ inR heights b m) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i = -1 →
        ∀ m : ℤ, 0 ≤ m → m < ((sliceVals heights).length : ℤ) →
          ¬ (inR heights a m ∧ inR heights b m)) := by
  sorry

/-- Let n = len(heights). The function returns a result (does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_11 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)) :
    ∃ r : alloc.vec.Vec I64, leftmost_building_queries heights queries = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ)), ∃ r : alloc.vec.Vec I64, leftmost_building_queries heights queries = ok r) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if r[i] != -1 then r[i] >= a and r[i] >= b.
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_12 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i ≠ -1 → rAt r i ≥ a ∧ rAt r i ≥ b := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      rAt r i ≠ -1 → rAt r i ≥ a ∧ rAt r i ≥ b) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], if a != b and heights[min(a,b)] >= heights[max(a,b)] and r[i] != -1, then r[i] is the minimum index k such that max(a,b) < k < n and heights[k] > heights[a] and heights[k] > heights[b].
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_13 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) ≥ hAt heights (max a b) → rAt r i ≠ -1 →
        max a b < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
          hAt heights (rAt r i) > hAt heights a ∧ hAt heights (rAt r i) > hAt heights b ∧
            ∀ k : ℤ, max a b < k → k < ((sliceVals heights).length : ℤ) →
              hAt heights k > hAt heights a → hAt heights k > hAt heights b → rAt r i ≤ k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      a ≠ b → hAt heights (min a b) ≥ hAt heights (max a b) → rAt r i ≠ -1 →
        max a b < rAt r i ∧ rAt r i < ((sliceVals heights).length : ℤ) ∧
          hAt heights (rAt r i) > hAt heights a ∧ hAt heights (rAt r i) > hAt heights b ∧
            ∀ k : ℤ, max a b < k → k < ((sliceVals heights).length : ℤ) →
              hAt heights k > hAt heights a → hAt heights k > hAt heights b → rAt r i ≤ k) := by
  sorry

/-- Let n = len(heights). For every i with 0 <= i < len(queries), writing a = queries[i][0] and b = queries[i][1], r[i] = -1 if and only if: a != b, and heights[min(a,b)] >= heights[max(a,b)], and for every k with max(a,b) < k < n, it is not the case that (heights[k] > heights[a] and heights[k] > heights[b]).
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_14 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      (rAt r i = -1 ↔
        a ≠ b ∧ hAt heights (min a b) ≥ hAt heights (max a b) ∧
          ∀ k : ℤ, max a b < k → k < ((sliceVals heights).length : ℤ) →
            ¬ (hAt heights k > hAt heights a ∧ hAt heights k > hAt heights b)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i : Nat), i < (queryVals queries).length →
      let a := qA queries i
      let b := qB queries i
      (rAt r i = -1 ↔
        a ≠ b ∧ hAt heights (min a b) ≥ hAt heights (max a b) ∧
          ∀ k : ℤ, max a b < k → k < ((sliceVals heights).length : ℤ) →
            ¬ (hAt heights k > hAt heights a ∧ hAt heights k > hAt heights b))) := by
  sorry

/-- Let n = len(heights). For every i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i][0] = queries[j][0] and queries[i][1] = queries[j][1], then r[i] = r[j].
  Preconditions: Let n = len(heights). The inputs satisfy: 1 <= n <= 50000; for every j with 0 <= j < n, 1 <= heights[j] <= 1000000000; 1 <= len(queries) <= 50000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 0 <= queries[i][0] < n, and 0 <= queries[i][1] < n. -/
theorem spec_15 (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r) :
    ∀ (i j : Nat), i < (queryVals queries).length → j < (queryVals queries).length →
      qA queries i = qA queries j → qB queries i = qB queries j → rAt r i = rAt r j := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (heights : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn_pos : 1 ≤ (sliceVals heights).length)
    (hn_le : (sliceVals heights).length ≤ 50000)
    (hh : ∀ (j : Nat) (hj : j < (sliceVals heights).length),
      1 ≤ (sliceVals heights).get ⟨j, hj⟩ ∧ (sliceVals heights).get ⟨j, hj⟩ ≤ 1000000000)
    (hq_pos : 1 ≤ (queryVals queries).length)
    (hq_le : (queryVals queries).length ≤ 50000)
    (hq : ∀ (i : Nat) (_hi : i < (queryVals queries).length),
      (queryAt queries i).length = 2 ∧
        0 ≤ qA queries i ∧ qA queries i < ((sliceVals heights).length : ℤ) ∧
        0 ≤ qB queries i ∧ qB queries i < ((sliceVals heights).length : ℤ))
    (r : alloc.vec.Vec I64)
    (hres : leftmost_building_queries heights queries = ok r), ∀ (i j : Nat), i < (queryVals queries).length → j < (queryVals queries).length →
      qA queries i = qA queries j → qB queries i = qB queries j → rAt r i = rAt r j) := by
  sorry

end AegisSpec.LeftmostBuildingQueries
