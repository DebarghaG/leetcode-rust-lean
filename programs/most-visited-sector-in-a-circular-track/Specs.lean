import Aegis.MostVisited.Code.Funs
import Mathlib

/-!
# Specifications of `Aegis.MostVisited.most_visited`

LeetCode problem `most-visited-sector-in-a-circular-track`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MostVisited

namespace AegisSpec.MostVisited

def roundVals (rounds : Slice Std.I64) : List ℤ := rounds.val.map (fun x => x.val)

def outVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

def D (n a b : ℤ) : ℤ := if a < b then b - a else n - a + b

def step (n a k : ℤ) : ℤ := ((a - 1 + k) % n) + 1

def visitCount (n : ℤ) (l : List ℤ) (s : ℤ) : ℤ :=
  (if l.getD 0 0 = s then 1 else 0) +
    (Finset.range (l.length - 1)).sum (fun i =>
      (Finset.Icc (1 : ℤ) (D n (l.getD i 0) (l.getD (i + 1) 0))).sum (fun k =>
        if step n (l.getD i 0) k = s then 1 else 0))

def maxVisitCount (n : ℤ) (l : List ℤ) (hn : 1 ≤ n) : ℤ :=
  (Finset.Icc (1 : ℤ) n).sup' (Finset.nonempty_Icc.mpr hn) (visitCount n l)

def topSectors (n : ℤ) (l : List ℤ) (hn : 1 ≤ n) : List ℤ :=
  ((Finset.Icc (1 : ℤ) n).filter (fun s => visitCount n l s = maxVisitCount n l hn)).sort
    (· ≤ ·)

def totalMoves (n : ℤ) (l : List ℤ) : ℤ :=
  (Finset.range (l.length - 1)).sum (fun i => D n (l.getD i 0) (l.getD (i + 1) 0))

def arcSectors (n start T : ℤ) : Finset ℤ :=
  (Finset.Icc (0 : ℤ) T).image (fun t => step n start t)

def rot (n c s : ℤ) : ℤ := ((s - 1 + c) % n) + 1

def occurs (x : ℤ) (l : List ℤ) : Prop := x ∈ l

/-- Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. For 1 ≤ s ≤ n, let V(s) = (1 if s = rounds[0] else 0) + Σ_{i=0}^{L-2} Σ_{k=1}^{D(rounds[i],rounds[i+1])} [((rounds[i]-1+k) mod n)+1 = s], where [P] is 1 if P holds and 0 otherwise. Let M = max_{1 ≤ s ≤ n} V(s). Whenever the function returns a result r, r is exactly the strictly ascending list of all sectors s with 1 ≤ s ≤ n and V(s) = M: len(r) = |{s : 1 ≤ s ≤ n and V(s) = M}|, and for every j with 0 ≤ j < len(r), r[j] is the (j+1)-th smallest sector s with 1 ≤ s ≤ n and V(s) = M.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_1 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    outVals r = topSectors n.val (roundVals rounds) (by omega) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), outVals r = topSectors n.val (roundVals rounds) (by omega)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, access out of bounds, panic, or otherwise raise a runtime error.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_2 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1]) :
    ∃ r : alloc.vec.Vec Std.I64, most_visited n rounds = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1]), ∃ r : alloc.vec.Vec Std.I64, most_visited n rounds = ok r) := by
  sorry

/-- Whenever the function returns a result r, every element of r is a valid sector label: for every j with 0 ≤ j < len(r), 1 ≤ r[j] ≤ n.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_3 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    ∀ (j : ℕ) (hj : j < (outVals r).length), 1 ≤ (outVals r)[j] ∧ (outVals r)[j] ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), ∀ (j : ℕ) (hj : j < (outVals r).length), 1 ≤ (outVals r)[j] ∧ (outVals r)[j] ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, r is sorted in strictly ascending order: for every j with 0 ≤ j+1 < len(r), r[j] < r[j+1].
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_4 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    ∀ (j : ℕ) (hj : j + 1 < (outVals r).length), (outVals r)[j] < (outVals r)[j + 1] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), ∀ (j : ℕ) (hj : j + 1 < (outVals r).length), (outVals r)[j] < (outVals r)[j + 1]) := by
  sorry

/-- Whenever the function returns a result r, r is non-empty: len(r) ≥ 1.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_5 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    1 ≤ (outVals r).length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), 1 ≤ (outVals r).length) := by
  sorry

/-- Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. For 1 ≤ s ≤ n, let V(s) = (1 if s = rounds[0] else 0) + Σ_{i=0}^{L-2} Σ_{k=1}^{D(rounds[i],rounds[i+1])} [((rounds[i]-1+k) mod n)+1 = s], and let M = max_{1 ≤ s ≤ n} V(s). Whenever the function returns a result r, every returned element is a most-visited sector: for every j with 0 ≤ j < len(r), 1 ≤ r[j] ≤ n and V(r[j]) = M.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_6 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    ∀ (j : ℕ) (hj : j < (outVals r).length),
      1 ≤ (outVals r)[j] ∧ (outVals r)[j] ≤ n.val ∧
        visitCount n.val (roundVals rounds) (outVals r)[j] =
          maxVisitCount n.val (roundVals rounds) (by omega) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), ∀ (j : ℕ) (hj : j < (outVals r).length),
      1 ≤ (outVals r)[j] ∧ (outVals r)[j] ≤ n.val ∧
        visitCount n.val (roundVals rounds) (outVals r)[j] =
          maxVisitCount n.val (roundVals rounds) (by omega)) := by
  sorry

/-- Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. For 1 ≤ s ≤ n, let V(s) = (1 if s = rounds[0] else 0) + Σ_{i=0}^{L-2} Σ_{k=1}^{D(rounds[i],rounds[i+1])} [((rounds[i]-1+k) mod n)+1 = s], and let M = max_{1 ≤ s ≤ n} V(s). Whenever the function returns a result r, every most-visited sector occurs in r: for every s with 1 ≤ s ≤ n, if V(s) = M then there exists j with 0 ≤ j < len(r) and r[j] = s.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_7 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    ∀ s : ℤ, 1 ≤ s → s ≤ n.val →
      visitCount n.val (roundVals rounds) s = maxVisitCount n.val (roundVals rounds) (by omega) →
        ∃ (j : ℕ) (hj : j < (outVals r).length), (outVals r)[j] = s := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), ∀ s : ℤ, 1 ≤ s → s ≤ n.val →
      visitCount n.val (roundVals rounds) s = maxVisitCount n.val (roundVals rounds) (by omega) →
        ∃ (j : ℕ) (hj : j < (outVals r).length), (outVals r)[j] = s) := by
  sorry

/-- Whenever the function returns a result r, r is the strictly ascending list of the sectors visited by the whole marathon, which is the circular arc starting at rounds[0] and taking T one-step moves: r is the sorted list of the distinct values {((rounds[0]-1+t) mod n)+1 : 0 ≤ t ≤ T}.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. Let T = Σ_{i=0}^{L-2} D(rounds[i],rounds[i+1]). Assume T ≤ n-1. -/
theorem spec_8 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hT : totalMoves n.val (roundVals rounds) ≤ n.val - 1)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    outVals r =
      (arcSectors n.val ((roundVals rounds).getD 0 0) (totalMoves n.val (roundVals rounds))).sort
        (· ≤ ·) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hT : totalMoves n.val (roundVals rounds) ≤ n.val - 1)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), outVals r =
      (arcSectors n.val ((roundVals rounds).getD 0 0) (totalMoves n.val (roundVals rounds))).sort
        (· ≤ ·)) := by
  sorry

/-- Whenever the function returns a result r, r is the list of all sectors in ascending order: r = [1, 2, ..., n].
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. Let T = Σ_{i=0}^{L-2} D(rounds[i],rounds[i+1]). Assume T mod n = n-1. -/
theorem spec_9 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hT : totalMoves n.val (roundVals rounds) % n.val = n.val - 1)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    outVals r = (List.range n.val.toNat).map (fun k => (k : ℤ) + 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hT : totalMoves n.val (roundVals rounds) % n.val = n.val - 1)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), outVals r = (List.range n.val.toNat).map (fun k => (k : ℤ) + 1)) := by
  sorry

/-- Whenever the function returns a result r: if T is even, then r is the one-element list [rounds[0]]; if T is odd, then r is the two-element list [1, 2].
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. Let T = Σ_{i=0}^{L-2} D(rounds[i],rounds[i+1]). Assume n = 2. -/
theorem spec_10 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hn : n.val = 2)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    (Even (totalMoves n.val (roundVals rounds)) → outVals r = [(roundVals rounds).getD 0 0]) ∧
      (Odd (totalMoves n.val (roundVals rounds)) → outVals r = ([1, 2] : List ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (hn : n.val = 2)
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), (Even (totalMoves n.val (roundVals rounds)) → outVals r = [(roundVals rounds).getD 0 0]) ∧
      (Odd (totalMoves n.val (roundVals rounds)) → outVals r = ([1, 2] : List ℤ))) := by
  sorry

/-- Whenever the function returns result r on (n,rounds) and result r' on (n,rounds_c), r' is exactly the strictly ascending list of the sector labels ρ_c(x) for x occurring in r.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. Let c be an integer with 0 ≤ c < n, define ρ_c(s) = ((s-1+c) mod n)+1 for 1 ≤ s ≤ n, and let rounds_c be the length-L array with rounds_c[i] = ρ_c(rounds[i]). -/
theorem spec_11 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (c : ℤ) (hc_lo : 0 ≤ c) (hc_hi : c < n.val)
    (rounds_c : Slice Std.I64)
    (hrot : roundVals rounds_c = (roundVals rounds).map (fun s => rot n.val c s))
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r)
    (r' : alloc.vec.Vec Std.I64) (hres' : most_visited n rounds_c = ok r') :
    outVals r' = ((outVals r).toFinset.image (fun x => rot n.val c x)).sort (· ≤ ·) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (c : ℤ) (hc_lo : 0 ≤ c) (hc_hi : c < n.val)
    (rounds_c : Slice Std.I64)
    (hrot : roundVals rounds_c = (roundVals rounds).map (fun s => rot n.val c s))
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r)
    (r' : alloc.vec.Vec Std.I64) (hres' : most_visited n rounds_c = ok r'), outVals r' = ((outVals r).toFinset.image (fun x => rot n.val c x)).sort (· ≤ ·)) := by
  sorry

/-- Let D(a,b) = b-a if a < b, and n-a+b if a > b, for 1 ≤ a,b ≤ n with a ≠ b. For 1 ≤ s ≤ n, let V(s) = (1 if s = rounds[0] else 0) + Σ_{i=0}^{L-2} Σ_{k=1}^{D(rounds[i],rounds[i+1])} [((rounds[i]-1+k) mod n)+1 = s]. Whenever the function returns a result r, equal visit counts are treated equally: for every s,t with 1 ≤ s ≤ n and 1 ≤ t ≤ n, if V(s) = V(t), then s occurs in r if and only if t occurs in r.
  Preconditions: 2 ≤ n ≤ 100; let L = len(rounds); 2 ≤ L ≤ 101; for every i with 0 ≤ i < L, 1 ≤ rounds[i] ≤ n; for every i with 0 ≤ i < L-1, rounds[i] ≠ rounds[i+1]. -/
theorem spec_12 (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r) :
    ∀ s t : ℤ, 1 ≤ s → s ≤ n.val → 1 ≤ t → t ≤ n.val →
      visitCount n.val (roundVals rounds) s = visitCount n.val (roundVals rounds) t →
        (occurs s (outVals r) ↔ occurs t (outVals r)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (rounds : Slice Std.I64)
    (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hL_lo : 2 ≤ (roundVals rounds).length) (hL_hi : (roundVals rounds).length ≤ 101)
    (hbound : ∀ (i : ℕ) (hi : i < (roundVals rounds).length),
      1 ≤ (roundVals rounds)[i] ∧ (roundVals rounds)[i] ≤ n.val)
    (hadj : ∀ (i : ℕ) (hi : i + 1 < (roundVals rounds).length),
      (roundVals rounds)[i] ≠ (roundVals rounds)[i + 1])
    (r : alloc.vec.Vec Std.I64) (hres : most_visited n rounds = ok r), ∀ s t : ℤ, 1 ≤ s → s ≤ n.val → 1 ≤ t → t ≤ n.val →
      visitCount n.val (roundVals rounds) s = visitCount n.val (roundVals rounds) t →
        (occurs s (outVals r) ↔ occurs t (outVals r))) := by
  sorry

end AegisSpec.MostVisited
