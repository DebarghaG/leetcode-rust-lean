import Aegis.AssignBikes.Code.Funs

/-!
# Specifications of `Aegis.AssignBikes.assign_bikes`

LeetCode problem `campus-bikes-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Data.ListN
open Aegis.AssignBikes

namespace AegisSpec.AssignBikes

abbrev Pt := alloc.vec.Vec Std.I64

def coord (p : Pt) (i : Nat) : ℤ := (p.val.getD i 0#i64).val

def mkPt (x y : ℤ) : Pt :=
  ⟨Slice.mk 2 (ListN.cons ⟨BitVec.ofInt 64 x⟩ (ListN.cons ⟨BitVec.ofInt 64 y⟩ ListN.nil))
    (by
      rcases System.Platform.numBits_eq with h | h <;>
        simp [Usize.max, Usize.numBits, h])⟩

def pt (s : Slice Pt) (i : Nat) : Pt := s.val.getD i (mkPt 0 0)

def manhattan (p q : Pt) : ℤ := |coord p 0 - coord q 0| + |coord p 1 - coord q 1|

def IsInjectiveOn (n m : Nat) (f : Nat → Nat) : Prop :=
  (∀ i, i < n → f i < m) ∧ ∀ i, i < n → ∀ j, j < n → f i = f j → i = j

def cost (workers bikes : Slice Pt) (f : Nat → Nat) : ℤ :=
  ∑ i ∈ Finset.range workers.val.length, manhattan (pt workers i) (pt bikes (f i))

def minDist (w : Pt) : List Pt → ℤ
  | [] => 0
  | b :: bs => bs.foldr (fun b' acc => min (manhattan w b') acc) (manhattan w b)

def flipXPt (p : Pt) : Pt := mkPt (999 - coord p 0) (coord p 1)

def flipYPt (p : Pt) : Pt := mkPt (coord p 0) (999 - coord p 1)

def swapPt (p : Pt) : Pt := mkPt (coord p 1) (coord p 0)

def translatePt (p : Pt) (dx dy : ℤ) : Pt := mkPt (coord p 0 + dx) (coord p 1 + dy)

def scalePt (p : Pt) (k : ℤ) : Pt := mkPt (k * coord p 0) (k * coord p 1)

def mkSlice (l : List Pt) (h : l.length ≤ Usize.max) : Slice Pt :=
  { leng := l.length, list := ListN.fromList l, bound := h }

theorem fromList_toList (l : List Pt) : (ListN.fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ListN.fromList, ListN.toList, ih]

@[simp] theorem val_mkSlice (l : List Pt) (h : l.length ≤ Usize.max) :
    (mkSlice l h).val = l := by
  simp [mkSlice, Slice.val, fromList_toList]

def mapPts (s : Slice Pt) (g : Pt → Pt) : Slice Pt := mkSlice (s.val.map g) (by simp)

@[simp] theorem val_mapPts (s : Slice Pt) (g : Pt → Pt) : (mapPts s g).val = s.val.map g := by
  simp [mapPts]

def permutePts (s : Slice Pt) (π : Equiv.Perm (Fin s.val.length)) : Slice Pt :=
  mkSlice (List.ofFn (fun i : Fin s.val.length => s.val.getD (π i).val (mkPt 0 0))) (by simp)

@[simp] theorem val_permutePts (s : Slice Pt) (π : Equiv.Perm (Fin s.val.length)) :
    (permutePts s π).val =
      List.ofFn (fun i : Fin s.val.length => s.val.getD (π i).val (mkPt 0 0)) := by
  simp [permutePts]

def appendPt (s : Slice Pt) (q : Pt) (hb : s.val.length + 1 ≤ Usize.max) : Slice Pt :=
  mkSlice (s.val ++ [q]) (by simpa using hb)

@[simp] theorem val_appendPt (s : Slice Pt) (q : Pt) (hb : s.val.length + 1 ≤ Usize.max) :
    (appendPt s q hb).val = s.val ++ [q] := by
  simp [appendPt]

def translatePts (s : Slice Pt) (dx dy : ℤ) : Slice Pt := mapPts s (fun p => translatePt p dx dy)

def flipXPts (s : Slice Pt) : Slice Pt := mapPts s flipXPt

def flipYPts (s : Slice Pt) : Slice Pt := mapPts s flipYPt

def swapPts (s : Slice Pt) : Slice Pt := mapPts s swapPt

def scalePts (s : Slice Pt) (k : ℤ) : Slice Pt := mapPts s (fun p => scalePt p k)

theorem le_usize_max {n : ℕ} (h : n ≤ 1000) : n ≤ Usize.max := by
  rcases System.Platform.numBits_eq with h' | h' <;>
    simp [Usize.max, Usize.numBits, h'] <;> omega

/-- The function returns a result r, and r is the minimum possible total Manhattan distance: defining C(f) = sum_{i=0}^{n-1} (|workers[i][0] - bikes[f(i)][0]| + |workers[i][1] - bikes[f(i)][1]|) for an injective function f : {0,...,n-1} -> {0,...,m-1}, there exists an injective f with C(f) = r, and for every injective g : {0,...,n-1} -> {0,...,m-1}, C(g) >= r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_1 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (∃ f : Nat → Nat,
          IsInjectiveOn workers.val.length bikes.val.length f ∧ cost workers bikes f = r.val) ∧
        (∀ g : Nat → Nat,
          IsInjectiveOn workers.val.length bikes.val.length g → r.val ≤ cost workers bikes g) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (∃ f : Nat → Nat,
          IsInjectiveOn workers.val.length bikes.val.length f ∧ cost workers bikes f = r.val) ∧
        (∀ g : Nat → Nat,
          IsInjectiveOn workers.val.length bikes.val.length g → r.val ≤ cost workers bikes g)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_2 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64, assign_bikes workers bikes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64, assign_bikes workers bikes = ok r) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_3 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64, assign_bikes workers bikes = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64, assign_bikes workers bikes = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r >= sum_{i=0}^{n-1} min_{0 <= j < m} (|workers[i][0] - bikes[j][0]| + |workers[i][1] - bikes[j][1]|).
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_4 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (∑ i ∈ Finset.range workers.val.length, minDist (pt workers i) bikes.val) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (∑ i ∈ Finset.range workers.val.length, minDist (pt workers i) bikes.val) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} (|workers[i][0] - bikes[i][0]| + |workers[i][1] - bikes[i][1]|).
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_5 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        r.val ≤ ∑ i ∈ Finset.range workers.val.length,
          manhattan (pt workers i) (pt bikes i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        r.val ≤ ∑ i ∈ Finset.range workers.val.length,
          manhattan (pt workers i) (pt bikes i)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if there exists an injective function f : {0,...,n-1} -> {0,...,m-1} such that for every i with 0 <= i < n, workers[i][0] = bikes[f(i)][0] and workers[i][1] = bikes[f(i)][1] (equivalently, the Manhattan distance between workers[i] and bikes[f(i)] is 0).
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_6 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (r.val = 0 ↔
          ∃ f : Nat → Nat,
            IsInjectiveOn workers.val.length bikes.val.length f ∧
              ∀ i, i < workers.val.length →
                coord (pt workers i) 0 = coord (pt bikes (f i)) 0 ∧
                  coord (pt workers i) 1 = coord (pt bikes (f i)) 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        (r.val = 0 ↔
          ∃ f : Nat → Nat,
            IsInjectiveOn workers.val.length bikes.val.length f ∧
              ∀ i, i < workers.val.length →
                coord (pt workers i) 0 = coord (pt bikes (f i)) 0 ∧
                  coord (pt workers i) 1 = coord (pt bikes (f i)) 1)) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and for every permutation π of {0,...,n-1}, letting workers'[i] = workers[π(i)] for 0 <= i < n, the function on (workers', bikes) also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_7 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∀ π : Equiv.Perm (Fin workers.val.length),
          assign_bikes (permutePts workers π) bikes = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∀ π : Equiv.Perm (Fin workers.val.length),
          assign_bikes (permutePts workers π) bikes = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and for every permutation σ of {0,...,m-1}, letting bikes'[j] = bikes[σ(j)] for 0 <= j < m, the function on (workers, bikes') also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_8 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∀ σ : Equiv.Perm (Fin bikes.val.length),
          assign_bikes workers (permutePts bikes σ) = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∀ σ : Equiv.Perm (Fin bikes.val.length),
          assign_bikes workers (permutePts bikes σ) = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and for every pair of integers (dx, dy) with 0 <= workers[i][0]+dx < 1000 and 0 <= workers[i][1]+dy < 1000 for all i, and 0 <= bikes[j][0]+dx < 1000 and 0 <= bikes[j][1]+dy < 1000 for all j, letting workers'[i] = [workers[i][0]+dx, workers[i][1]+dy] and bikes'[j] = [bikes[j][0]+dx, bikes[j][1]+dy], the function on (workers', bikes') also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_9 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (dx dy : ℤ)
    (hwdx : ∀ i, i < workers.val.length →
      0 ≤ coord (pt workers i) 0 + dx ∧ coord (pt workers i) 0 + dx < 1000)
    (hwdy : ∀ i, i < workers.val.length →
      0 ≤ coord (pt workers i) 1 + dy ∧ coord (pt workers i) 1 + dy < 1000)
    (hbdx : ∀ j, j < bikes.val.length →
      0 ≤ coord (pt bikes j) 0 + dx ∧ coord (pt bikes j) 0 + dx < 1000)
    (hbdy : ∀ j, j < bikes.val.length →
      0 ≤ coord (pt bikes j) 1 + dy ∧ coord (pt bikes j) 1 + dy < 1000) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (translatePts workers dx dy) (translatePts bikes dx dy) = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (dx dy : ℤ)
    (hwdx : ∀ i, i < workers.val.length →
      0 ≤ coord (pt workers i) 0 + dx ∧ coord (pt workers i) 0 + dx < 1000)
    (hwdy : ∀ i, i < workers.val.length →
      0 ≤ coord (pt workers i) 1 + dy ∧ coord (pt workers i) 1 + dy < 1000)
    (hbdx : ∀ j, j < bikes.val.length →
      0 ≤ coord (pt bikes j) 0 + dx ∧ coord (pt bikes j) 0 + dx < 1000)
    (hbdy : ∀ j, j < bikes.val.length →
      0 ≤ coord (pt bikes j) 1 + dy ∧ coord (pt bikes j) 1 + dy < 1000), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (translatePts workers dx dy) (translatePts bikes dx dy) = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and letting workers'[i] = [999 - workers[i][0], workers[i][1]] and bikes'[j] = [999 - bikes[j][0], bikes[j][1]], the function on (workers', bikes') also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_10 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (flipXPts workers) (flipXPts bikes) = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (flipXPts workers) (flipXPts bikes) = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and letting workers'[i] = [workers[i][0], 999 - workers[i][1]] and bikes'[j] = [bikes[j][0], 999 - bikes[j][1]], the function on (workers', bikes') also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_11 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (flipYPts workers) (flipYPts bikes) = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (flipYPts workers) (flipYPts bikes) = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and letting workers'[i] = [workers[i][1], workers[i][0]] and bikes'[j] = [bikes[j][1], bikes[j][0]], the function on (workers', bikes') also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_12 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (swapPts workers) (swapPts bikes) = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        assign_bikes (swapPts workers) (swapPts bikes) = ok r) := by
  sorry

/-- The function on (workers, bikes) returns a result r. If m < 10, then for every coordinate [x, y] with 0 <= x < 1000, 0 <= y < 1000 not equal to any bikes[j], letting bikes' be the list obtained by appending [x, y] to bikes, the function on (workers, bikes') returns a result r' with r' <= r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_13 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hm10 : bikes.val.length < 10)
    (x y : ℤ) (hx : 0 ≤ x ∧ x < 1000) (hy : 0 ≤ y ∧ y < 1000)
    (hfresh : mkPt x y ∉ bikes.val) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes workers
              (appendPt bikes (mkPt x y) (by
                have h : bikes.val.length + 1 ≤ 1000 := by omega
                exact le_usize_max h)) = ok r' ∧
            r'.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hm10 : bikes.val.length < 10)
    (x y : ℤ) (hx : 0 ≤ x ∧ x < 1000) (hy : 0 ≤ y ∧ y < 1000)
    (hfresh : mkPt x y ∉ bikes.val), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes workers
              (appendPt bikes (mkPt x y) (by
                have h : bikes.val.length + 1 ≤ 1000 := by omega
                exact le_usize_max h)) = ok r' ∧
            r'.val ≤ r.val) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and assuming n < m, for every coordinate [x, y] with 0 <= x < 1000, 0 <= y < 1000 not equal to any workers[i], letting workers' be the list obtained by appending [x, y] to workers, the function on (workers', bikes) returns a result r' with r' >= r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_14 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hnm : workers.val.length < bikes.val.length)
    (x y : ℤ) (hx : 0 ≤ x ∧ x < 1000) (hy : 0 ≤ y ∧ y < 1000)
    (hfresh : mkPt x y ∉ workers.val) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes
              (appendPt workers (mkPt x y) (by
                have h : workers.val.length + 1 ≤ 1000 := by omega
                exact le_usize_max h)) bikes = ok r' ∧
            r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hnm : workers.val.length < bikes.val.length)
    (x y : ℤ) (hx : 0 ≤ x ∧ x < 1000) (hy : 0 ≤ y ∧ y < 1000)
    (hfresh : mkPt x y ∉ workers.val), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes
              (appendPt workers (mkPt x y) (by
                have h : workers.val.length + 1 ≤ 1000 := by omega
                exact le_usize_max h)) bikes = ok r' ∧
            r.val ≤ r'.val) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and for every positive integer k such that k * c < 1000 for every coordinate c appearing in workers or bikes, letting workers'[i] = [k * workers[i][0], k * workers[i][1]] and bikes'[j] = [k * bikes[j][0], k * bikes[j][1]], the function on (workers', bikes') returns a result r' with r' = k * r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume 1 <= n <= m <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_15 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (k : ℕ) (hk : 0 < k)
    (hwk : ∀ p ∈ workers.val, ∀ c ∈ p.val, (k : ℤ) * c.val < 1000)
    (hbk : ∀ p ∈ bikes.val, ∀ c ∈ p.val, (k : ℤ) * c.val < 1000) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes (scalePts workers (k : ℤ)) (scalePts bikes (k : ℤ)) = ok r' ∧
            r'.val = (k : ℤ) * r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (k : ℕ) (hk : 0 < k)
    (hwk : ∀ p ∈ workers.val, ∀ c ∈ p.val, (k : ℤ) * c.val < 1000)
    (hbk : ∀ p ∈ bikes.val, ∀ c ∈ p.val, (k : ℤ) * c.val < 1000), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧
        ∃ r' : Std.I64,
          assign_bikes (scalePts workers (k : ℤ)) (scalePts bikes (k : ℤ)) = ok r' ∧
            r'.val = (k : ℤ) * r.val) := by
  sorry

/-- The function on (workers, bikes) returns a result r, and the function on (bikes, workers) also returns r.
  Preconditions: Let n = len(workers) and m = len(bikes). Assume n = m and 1 <= n <= 10; every workers[i] and bikes[j] has length 2; all coordinates are integers in [0, 1000); all workers are pairwise distinct; all bikes are pairwise distinct. -/
theorem spec_16 (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hnm : workers.val.length = bikes.val.length) :
    ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧ assign_bikes bikes workers = ok r := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (workers bikes : Slice Pt)
    (hn : 1 ≤ workers.val.length) (hmn : workers.val.length ≤ bikes.val.length)
    (hm : bikes.val.length ≤ 10)
    (hwlen : ∀ p ∈ workers.val, p.val.length = 2)
    (hblen : ∀ p ∈ bikes.val, p.val.length = 2)
    (hwcoord : ∀ p ∈ workers.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hbcoord : ∀ p ∈ bikes.val, ∀ c ∈ p.val, 0 ≤ c.val ∧ c.val < 1000)
    (hwnodup : workers.val.Nodup) (hbnodup : bikes.val.Nodup)
    (hnm : workers.val.length = bikes.val.length), ∃ r : Std.I64,
      assign_bikes workers bikes = ok r ∧ assign_bikes bikes workers = ok r) := by
  sorry

end AegisSpec.AssignBikes
