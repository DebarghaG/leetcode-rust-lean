import Aegis.MinWastedSpace.Code.Funs

/-!
# Specifications of `Aegis.MinWastedSpace.min_wasted_space`

LeetCode problem `minimum-space-wasted-from-packaging`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinWastedSpace

namespace AegisSpec.MinWastedSpace

noncomputable section

def packagesList (packages : Slice I64) : List Int := packages.val.map (fun x => x.val)

def row (boxes : Slice (alloc.vec.Vec I64)) (j : Fin boxes.val.length) : List Int :=
  (boxes.val.get j).val.map (fun x => x.val)

def allBoxValues (boxes : Slice (alloc.vec.Vec I64)) : List Int :=
  (boxes.val.map (fun r => r.val.map (fun x => x.val))).flatten

def headPackage (packages : Slice I64) (h : packages.val.length = 1) : Int :=
  (packages.val.get ⟨0, by omega⟩).val

structure Precond (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64)) : Prop where

  len_packages_pos : 1 ≤ packages.val.length

  len_boxes_pos : 1 ≤ boxes.val.length

  row_nonempty : ∀ j : Fin boxes.val.length, 1 ≤ (boxes.val.get j).val.length

  packages_bounds : ∀ i : Fin packages.val.length,
    1 ≤ (packages.val.get i).val ∧ (packages.val.get i).val ≤ 100000

  boxes_bounds : ∀ (j : Fin boxes.val.length) (k : Fin (boxes.val.get j).val.length),
    1 ≤ ((boxes.val.get j).val.get k).val ∧ ((boxes.val.get j).val.get k).val ≤ 100000

  rows_nodup : ∀ j : Fin boxes.val.length, ((boxes.val.get j).val.map (fun x => x.val)).Nodup

  len_packages_le : packages.val.length ≤ 100000

  len_boxes_le : boxes.val.length ≤ 100000

  row_len_le : ∀ j : Fin boxes.val.length, (boxes.val.get j).val.length ≤ 100000

  sum_rows_len_le : (boxes.val.map (fun r => r.val.length)).sum ≤ 100000

def FeasibleRow (packages : List Int) (r : List Int) : Prop :=
  ∀ i : Fin packages.length, ∃ k : Fin r.length, packages.get i ≤ r.get k

def assignmentWaste (packages r : List Int) (a : Fin packages.length → Fin r.length) : Int :=
  ∑ i : Fin packages.length, (r.get (a i) - packages.get i)

def Waste (packages r : List Int) : Int :=
  let S : Finset (Fin packages.length → Fin r.length) :=
    Finset.univ.filter (fun a => ∀ i : Fin packages.length, packages.get i ≤ r.get (a i))
  if h : S.Nonempty then S.inf' h (fun a => assignmentWaste packages r a) else 0

def FeasibleSupplier (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (j : Fin boxes.val.length) : Prop :=
  FeasibleRow (packagesList packages) (row boxes j)

def NoFeasibleSupplier (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ j : Fin boxes.val.length, ¬ FeasibleSupplier packages boxes j

def MinWaste (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64)) : Int :=
  by
    classical
    exact
      let S : Finset (Fin boxes.val.length) :=
        Finset.univ.filter (fun j => FeasibleSupplier packages boxes j)
      if h : S.Nonempty then
        S.inf' h (fun j => Waste (packagesList packages) (row boxes j))
      else 0

def minBoxGE (r : List Int) (p : Int) : Int :=
  let S : Finset Int :=
    ((Finset.univ : Finset (Fin r.length)).image (fun k => r.get k)).filter (fun x => p ≤ x)
  if h : S.Nonempty then S.min' h else 0

def minBoxAtLeast (boxes : Slice (alloc.vec.Vec I64)) (p : Int) : Int :=
  minBoxGE (allBoxValues boxes) p

def maxBoxValue (boxes : Slice (alloc.vec.Vec I64)) : Int :=
  let vals := allBoxValues boxes
  let S : Finset Int := (Finset.univ : Finset (Fin vals.length)).image (fun k => vals.get k)
  if h : S.Nonempty then S.max' h else 0

def independentWaste (packages : List Int) (r : List Int) : Int :=
  ∑ i : Fin packages.length, (minBoxGE r (packages.get i) - packages.get i)

def MinIndependentWaste (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64)) : Int :=
  by
    classical
    exact
      let S : Finset (Fin boxes.val.length) :=
        Finset.univ.filter (fun j => FeasibleSupplier packages boxes j)
      if h : S.Nonempty then
        S.inf' h (fun j => independentWaste (packagesList packages) (row boxes j))
      else 0

def RowsPerm (bs bs' : List (alloc.vec.Vec I64)) : Prop :=
  List.Forall₂ (fun a b => List.Perm a.val b.val) bs bs'

def RowExtends (b b' : alloc.vec.Vec I64) : Prop :=
  ∃ (pre : List I64) (x : I64) (post : List I64), b'.val = pre ++ x :: post ∧ b.val = pre ++ post

def InsertsOneValue : List (alloc.vec.Vec I64) → List (alloc.vec.Vec I64) → Prop
  | [], [] => False
  | b :: bs, b' :: bs' => (RowExtends b b' ∧ bs = bs') ∨ InsertsOneValue bs bs'
  | _, _ => False

def InsertsNonemptyRow (bs bs' : List (alloc.vec.Vec I64)) : Prop :=
  bs'.length = bs.length + 1 ∧
    ∃ (pre : List (alloc.vec.Vec I64)) (r : alloc.vec.Vec I64)
      (post : List (alloc.vec.Vec I64)),
      bs' = (pre ++ r :: post) ∧ bs = (pre ++ post) ∧ r.val ≠ []

/-- Let M = 1000000007. For a supplier j < len(boxes), call j feasible if for every i < len(packages) there is k < len(boxes[j]) with packages[i] <= boxes[j][k]. For a feasible j, let Waste(j) be the minimum, over all functions a from {0,...,len(packages)-1} to {0,...,len(boxes[j])-1} satisfying packages[i] <= boxes[j][a(i)] for every i, of sum_{i=0}^{len(packages)-1} (boxes[j][a(i)] - packages[i]); the same box size may be reused any number of times. Whenever the function returns a result r, if no supplier is feasible then r = -1; otherwise, letting W = min{ Waste(j) | j < len(boxes) and j is feasible }, we have 0 <= r < M and r is congruent to W modulo M.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_1 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r →
      (NoFeasibleSupplier packages boxes → r.val = -1) ∧
      (¬ NoFeasibleSupplier packages boxes →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val (MinWaste packages boxes)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r →
      (NoFeasibleSupplier packages boxes → r.val = -1) ∧
      (¬ NoFeasibleSupplier packages boxes →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val (MinWaste packages boxes))) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_2 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∃ r : I64, min_wasted_space packages boxes = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∃ r : I64, min_wasted_space packages boxes = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r < 1000000007.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_3 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < 1000000007)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every supplier j < len(boxes) there exists a package index i < len(packages) such that packages[i] > boxes[j][k] for all k < len(boxes[j]).
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_4 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r →
      (r.val = -1 ↔
        ∀ j : Fin boxes.val.length, ∃ i : Fin (packagesList packages).length,
          ∀ k : Fin (row boxes j).length,
            (row boxes j).get k < (packagesList packages).get i) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r →
      (r.val = -1 ↔
        ∀ j : Fin boxes.val.length, ∃ i : Fin (packagesList packages).length,
          ∀ k : Fin (row boxes j).length,
            (row boxes j).get k < (packagesList packages).get i)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, let W be the exact minimum total waste over all feasible suppliers, where a supplier is feasible if every package fits some box of that supplier, and waste for a supplier is minimized using only that supplier's box sizes with unlimited reuse. Then W = 0 if and only if there exists a supplier j < len(boxes) such that for every package i < len(packages) there is an index k < len(boxes[j]) with boxes[j][k] = packages[i]. In particular, if such a supplier exists then r = 0.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_5 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      ((MinWaste packages boxes = 0 ↔
          ∃ j : Fin boxes.val.length, ∀ i : Fin (packagesList packages).length,
            ∃ k : Fin (row boxes j).length, (row boxes j).get k = (packagesList packages).get i) ∧
        ((∃ j : Fin boxes.val.length, ∀ i : Fin (packagesList packages).length,
            ∃ k : Fin (row boxes j).length, (row boxes j).get k = (packagesList packages).get i) →
          r.val = 0)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      ((MinWaste packages boxes = 0 ↔
          ∃ j : Fin boxes.val.length, ∀ i : Fin (packagesList packages).length,
            ∃ k : Fin (row boxes j).length, (row boxes j).get k = (packagesList packages).get i) ∧
        ((∃ j : Fin boxes.val.length, ∀ i : Fin (packagesList packages).length,
            ∃ k : Fin (row boxes j).length, (row boxes j).get k = (packagesList packages).get i) →
          r.val = 0))) := by
  sorry

/-- Whenever the function returns a result r, let p = packages[0]. If there is no pair (j,k) with j < len(boxes), k < len(boxes[j]), and boxes[j][k] >= p, then r = -1. Otherwise let B = min{ boxes[j][k] | j < len(boxes), k < len(boxes[j]), and boxes[j][k] >= p }. Then r = B - p.
  Preconditions: len(packages) = 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_6 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (h1 : packages.val.length = 1) :
    ∀ r : I64, min_wasted_space packages boxes = ok r →
      ((¬ ∃ (j : Fin boxes.val.length) (k : Fin (row boxes j).length),
            headPackage packages h1 ≤ (row boxes j).get k) → r.val = -1) ∧
      ((∃ (j : Fin boxes.val.length) (k : Fin (row boxes j).length),
            headPackage packages h1 ≤ (row boxes j).get k) →
          r.val = minBoxAtLeast boxes (headPackage packages h1) - headPackage packages h1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (h1 : packages.val.length = 1), ∀ r : I64, min_wasted_space packages boxes = ok r →
      ((¬ ∃ (j : Fin boxes.val.length) (k : Fin (row boxes j).length),
            headPackage packages h1 ≤ (row boxes j).get k) → r.val = -1) ∧
      ((∃ (j : Fin boxes.val.length) (k : Fin (row boxes j).length),
            headPackage packages h1 ≤ (row boxes j).get k) →
          r.val = minBoxAtLeast boxes (headPackage packages h1) - headPackage packages h1)) := by
  sorry

/-- Whenever the function returns r on (packages, boxes) and r' on (packages', boxes), where packages' is any permutation of the slice packages with len(packages') = len(packages), and (packages', boxes) also satisfies the preconditions, then r = r'.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_7 (packages packages' : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : List.Perm packages'.val packages.val)
    (hpre' : Precond packages' boxes) :
    ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages' boxes = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (packages packages' : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : List.Perm packages'.val packages.val)
    (hpre' : Precond packages' boxes), ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages' boxes = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on (packages, boxes) and r' on (packages, boxes'), where boxes' is any permutation of the outer slice boxes with len(boxes') = len(boxes) and each row of boxes' is one of the rows of boxes, and (packages, boxes') also satisfies the preconditions, then r = r'.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_8 (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : List.Perm boxes'.val boxes.val)
    (hpre' : Precond packages boxes') :
    ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages boxes' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : List.Perm boxes'.val boxes.val)
    (hpre' : Precond packages boxes'), ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages boxes' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on (packages, boxes) and r' on (packages, boxes'), where for every j < len(boxes) the row boxes'[j] has the same length as boxes[j] and is a permutation of boxes[j], and (packages, boxes') also satisfies the preconditions, then r = r'.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_9 (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : RowsPerm boxes.val boxes'.val)
    (hpre' : Precond packages boxes') :
    ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages boxes' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hperm : RowsPerm boxes.val boxes'.val)
    (hpre' : Precond packages boxes'), ∀ r r' : I64, min_wasted_space packages boxes = ok r →
      min_wasted_space packages boxes' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a supplier j0 < len(boxes) such that j0 is feasible, Waste(j0) = min{ Waste(j) | j < len(boxes) and j is feasible }, and r is congruent to Waste(j0) modulo 1000000007. Here feasible means every package fits some box of that supplier, and Waste(j) is the minimum total waste using only supplier j's box sizes with unlimited reuse.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_10 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      ∃ j0 : Fin boxes.val.length,
        FeasibleSupplier packages boxes j0 ∧
          Waste (packagesList packages) (row boxes j0) = MinWaste packages boxes ∧
            Int.ModEq 1000000007 r.val (Waste (packagesList packages) (row boxes j0)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      ∃ j0 : Fin boxes.val.length,
        FeasibleSupplier packages boxes j0 ∧
          Waste (packagesList packages) (row boxes j0) = MinWaste packages boxes ∧
            Int.ModEq 1000000007 r.val (Waste (packagesList packages) (row boxes j0))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, let W be the exact minimum total waste over all feasible suppliers, where feasible and waste are defined as in the main specification, and let B = max{ boxes[j][k] | j < len(boxes), k < len(boxes[j]) }. Then W <= sum_{i=0}^{len(packages)-1} (B - packages[i]).
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_11 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      MinWaste packages boxes ≤
        ∑ i : Fin (packagesList packages).length,
          (maxBoxValue boxes - (packagesList packages).get i) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      MinWaste packages boxes ≤
        ∑ i : Fin (packagesList packages).length,
          (maxBoxValue boxes - (packagesList packages).get i)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, let W be the exact minimum total waste over all feasible suppliers. If W < 1000000007, then r = W.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_12 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      MinWaste packages boxes < 1000000007 → r.val = MinWaste packages boxes := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      MinWaste packages boxes < 1000000007 → r.val = MinWaste packages boxes) := by
  sorry

/-- Let boxes' be any slice of vectors obtained from boxes by inserting one additional nonempty supplier row, so len(boxes') = len(boxes)+1 and the old rows appear in the same order with one new row somewhere, and suppose (packages, boxes') satisfies the preconditions. Whenever the function returns r on (packages, boxes) with r != -1 and returns r' on (packages, boxes'), let W and W' be the exact minimum total wastes for boxes and boxes' respectively. Then W' <= W.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_13 (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hins : InsertsNonemptyRow boxes.val boxes'.val)
    (hpre' : Precond packages boxes') :
    ∀ r r' : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      min_wasted_space packages boxes' = ok r' →
        MinWaste packages boxes' ≤ MinWaste packages boxes := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hins : InsertsNonemptyRow boxes.val boxes'.val)
    (hpre' : Precond packages boxes'), ∀ r r' : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      min_wasted_space packages boxes' = ok r' →
        MinWaste packages boxes' ≤ MinWaste packages boxes) := by
  sorry

/-- For every feasible supplier j < len(boxes), Waste(j) = sum_{i=0}^{len(packages)-1} (min{ boxes[j][k] | k < len(boxes[j]) and boxes[j][k] >= packages[i] } - packages[i]). Consequently, if some supplier is feasible, W = min{ sum_{i=0}^{len(packages)-1} (min{ boxes[j][k] | k < len(boxes[j]) and boxes[j][k] >= packages[i] } - packages[i]) | j < len(boxes) and j is feasible }, and r = W mod 1000000007. For a fixed supplier, the minimum is attained by assigning each package independently to the smallest box size of that supplier that is at least the package; unlimited supply makes the choices independent.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_14 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r →
      (∀ j : Fin boxes.val.length, FeasibleSupplier packages boxes j →
          Waste (packagesList packages) (row boxes j) =
            independentWaste (packagesList packages) (row boxes j)) ∧
        (¬ NoFeasibleSupplier packages boxes →
          MinWaste packages boxes = MinIndependentWaste packages boxes) ∧
          (¬ NoFeasibleSupplier packages boxes →
            r.val = MinWaste packages boxes % 1000000007) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r →
      (∀ j : Fin boxes.val.length, FeasibleSupplier packages boxes j →
          Waste (packagesList packages) (row boxes j) =
            independentWaste (packagesList packages) (row boxes j)) ∧
        (¬ NoFeasibleSupplier packages boxes →
          MinWaste packages boxes = MinIndependentWaste packages boxes) ∧
          (¬ NoFeasibleSupplier packages boxes →
            r.val = MinWaste packages boxes % 1000000007)) := by
  sorry

/-- Whenever the function returns r on (packages, boxes) with r != -1 and returns r' on (packages, boxes'), let W and W' be the exact minimum total wastes for boxes and boxes' respectively, as in the main specification. Then W' <= W.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000; boxes' is obtained from boxes by choosing one supplier j0 < len(boxes) and inserting one additional value into boxes'[j0], with len(boxes') = len(boxes), boxes'[j] = boxes[j] for j != j0, all entries of each boxes'[j] distinct, and (packages, boxes') satisfying the same size and sum constraints. -/
theorem spec_15 (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hins : InsertsOneValue boxes.val boxes'.val)
    (hpre' : Precond packages boxes') :
    ∀ r r' : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      min_wasted_space packages boxes' = ok r' →
        MinWaste packages boxes' ≤ MinWaste packages boxes := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (packages : Slice I64) (boxes boxes' : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) (hins : InsertsOneValue boxes.val boxes'.val)
    (hpre' : Precond packages boxes'), ∀ r r' : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      min_wasted_space packages boxes' = ok r' →
        MinWaste packages boxes' ≤ MinWaste packages boxes) := by
  sorry

/-- Whenever the function returns a result r with r != -1, let W be the exact minimum total waste over all feasible suppliers, as in the main specification. Then r = 0 if and only if W is a multiple of 1000000007. In particular, a returned value 0 can arise either from W = 0 or from a positive exact waste W divisible by 1000000007.
  Preconditions: len(packages) >= 1; len(boxes) >= 1; for every j < len(boxes), len(boxes[j]) >= 1; for every i < len(packages), 1 <= packages[i] <= 100000; for every j < len(boxes) and k < len(boxes[j]), 1 <= boxes[j][k] <= 100000; all entries of each boxes[j] are distinct; len(packages) <= 100000; len(boxes) <= 100000; for every j, len(boxes[j]) <= 100000; sum over j of len(boxes[j]) <= 100000. -/
theorem spec_16 (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes) :
    ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      (r.val = 0 ↔ (1000000007 : Int) ∣ MinWaste packages boxes) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (packages : Slice I64) (boxes : Slice (alloc.vec.Vec I64))
    (hpre : Precond packages boxes), ∀ r : I64, min_wasted_space packages boxes = ok r → r.val ≠ -1 →
      (r.val = 0 ↔ (1000000007 : Int) ∣ MinWaste packages boxes)) := by
  sorry

end

end AegisSpec.MinWastedSpace
