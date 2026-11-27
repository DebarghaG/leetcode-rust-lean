import Aegis.MergeTriplets.Code.Funs

/-!
# Specifications of `Aegis.MergeTriplets.merge_triplets`

LeetCode problem `merge-triplets-to-form-target-triplet`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MergeTriplets

def nth (l : List Int) (j : Nat) : Int := l.getD j 0

def vecInts (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

def rows (triplets : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  triplets.val.map vecInts

def tgts (target : Slice Std.I64) : List Int := target.val.map (fun x => x.val)

def cell (triplets : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  nth ((rows triplets).getD i []) j

def tcell (target : Slice Std.I64) (j : Nat) : Int := nth (tgts target) j

def vcell (u : alloc.vec.Vec Std.I64) (j : Nat) : Int := nth (vecInts u) j

lemma nth_of_lt (l : List Int) (j : Nat) (h : j < l.length) : nth l j = l[j] := by
  simp [nth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma rows_length (triplets : Slice (alloc.vec.Vec Std.I64)) :
    (rows triplets).length = triplets.val.length := by
  simp [rows]

lemma tgts_length (target : Slice Std.I64) : (tgts target).length = target.val.length := by
  simp [tgts]

def sliceOfList {α : Type} (l : List α) (h : l.length ≤ Usize.max) : Slice α where
  leng := l.length
  list := Aeneas.Data.ListN.ListN.fromList l
  bound := h

lemma slice_list_length_le {α : Type} (s : Slice α) : s.val.length ≤ Usize.max := by
  have h : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
  rw [h]
  exact s.bound

def setRow (triplets : Slice (alloc.vec.Vec Std.I64)) (i : Nat)
    (u : alloc.vec.Vec Std.I64) : Slice (alloc.vec.Vec Std.I64) :=
  sliceOfList (triplets.val.set i u) (by
    rw [List.length_set]
    exact slice_list_length_le triplets)

def delRow (triplets : Slice (alloc.vec.Vec Std.I64)) (i : Nat) :
    Slice (alloc.vec.Vec Std.I64) :=
  sliceOfList (triplets.val.eraseIdx i) (by
    exact Nat.le_trans (List.length_eraseIdx_le triplets.val i) (slice_list_length_le triplets))

def IsMaxOf (s : Set Int) (x : Int) : Prop := x ∈ s ∧ ∀ y ∈ s, y ≤ x

def Admissible (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (i : Nat) : Prop :=
  ∀ j, j < 3 → cell triplets i j ≤ tcell target j

def admissibleValues (triplets : Slice (alloc.vec.Vec Std.I64))
    (target : Slice Std.I64) (k : Nat) : Set Int :=
  { v : Int | ∃ i, i < triplets.val.length ∧ Admissible triplets target i ∧
      cell triplets i k = v }

def VecOK (u : alloc.vec.Vec Std.I64) : Prop :=
  (vecInts u).length = 3 ∧ ∀ j, j < 3 → 1 ≤ vcell u j ∧ vcell u j ≤ 1000

def InputOK (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64) : Prop :=
  1 ≤ triplets.val.length ∧
  triplets.val.length ≤ 100000 ∧
  target.val.length = 3 ∧
  (∀ i, i < triplets.val.length → ((rows triplets).getD i []).length = 3) ∧
  (∀ i, i < triplets.val.length → ∀ j, j < 3 →
    1 ≤ cell triplets i j ∧ cell triplets i j ≤ 1000) ∧
  (∀ j, j < 3 → 1 ≤ tcell target j ∧ tcell target j ≤ 1000)

def maxTriple (r s : List Int) : List Int := r.zipWith (fun a b => max a b) s

def step (t : List (List Int)) (i j : Nat) : List (List Int) :=
  t.set j (maxTriple (t.getD i []) (t.getD j []))

def runOps (t : List (List Int)) : List (Nat × Nat) → List (List Int)
  | [] => t
  | (i, j) :: rest => runOps (step t i j) rest

def Occurs (t : List (List Int)) (target : Slice Std.I64) : Prop :=
  ∃ i, i < t.length ∧ ∀ j, j < 3 → nth (t.getD i []) j = tcell target j

/-- Under the preconditions, the function returns a result r (a Boolean) and r = true if and only if for every coordinate k in {0,1,2} there exists an index i with 0 <= i < len(triplets) such that (for every j in {0,1,2}, triplets[i][j] <= target[j]) and triplets[i][k] = target[k]. Equivalently, r = false if and only if there is a coordinate k in {0,1,2} for which no index i with all coordinates <= target has triplets[i][k] = target[k].
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_1 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target) :
    ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ↔ ∀ k, k < 3 → ∃ i, i < triplets.val.length ∧
        (∀ j, j < 3 → cell triplets i j ≤ tcell target j) ∧
        cell triplets i k = tcell target k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target), ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ↔ ∀ k, k < 3 → ∃ i, i < triplets.val.length ∧
        (∀ j, j < 3 → cell triplets i j ≤ tcell target j) ∧
        cell triplets i k = tcell target k)) := by
  sorry

/-- Under the preconditions, the function returns a result (it does not fail, panic, or perform an out-of-bounds access or arithmetic overflow); the result is either true or false.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_2 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target) :
    ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ∨ r = false) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target), ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ∨ r = false)) := by
  sorry

/-- Under the preconditions, whenever the function returns r = true, there exists a nonempty finite set S of indices, each with 0 <= i < len(triplets), such that for every coordinate k in {0,1,2}, target[k] = max{ triplets[i][k] | i in S }.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_3 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok true) :
    ∃ S : Finset Nat, S.Nonempty ∧ (∀ i ∈ S, i < triplets.val.length) ∧
      ∀ k, k < 3 → IsMaxOf { v : Int | ∃ i ∈ S, cell triplets i k = v } (tcell target k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok true), ∃ S : Finset Nat, S.Nonempty ∧ (∀ i ∈ S, i < triplets.val.length) ∧
      ∀ k, k < 3 → IsMaxOf { v : Int | ∃ i ∈ S, cell triplets i k = v } (tcell target k)) := by
  sorry

/-- Under the preconditions, if there exists a nonempty finite set S of indices, each with 0 <= i < len(triplets), such that for every coordinate k in {0,1,2}, target[k] = max{ triplets[i][k] | i in S }, then the function returns r = true.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_4 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hwit : ∃ S : Finset Nat, S.Nonempty ∧ (∀ i ∈ S, i < triplets.val.length) ∧
      ∀ k, k < 3 → IsMaxOf { v : Int | ∃ i ∈ S, cell triplets i k = v } (tcell target k)) :
    ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧ r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hwit : ∃ S : Finset Nat, S.Nonempty ∧ (∀ i ∈ S, i < triplets.val.length) ∧
      ∀ k, k < 3 → IsMaxOf { v : Int | ∃ i ∈ S, cell triplets i k = v } (tcell target k)), ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧ r = true) := by
  sorry

/-- Under the preconditions, whenever the function returns r = true, for every coordinate k in {0,1,2}, the set V_k = { triplets[i][k] | 0 <= i < len(triplets) and for every j in {0,1,2}, triplets[i][j] <= target[j] } is nonempty and its maximum is exactly target[k].
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_5 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok true) :
    ∀ k, k < 3 → IsMaxOf (admissibleValues triplets target k) (tcell target k) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok true), ∀ k, k < 3 → IsMaxOf (admissibleValues triplets target k) (tcell target k)) := by
  sorry

/-- Under the preconditions, whenever the function returns r = false, there exists a coordinate k in {0,1,2} such that for every index i with 0 <= i < len(triplets), either triplets[i][k] != target[k] or there exists j in {0,1,2} with triplets[i][j] > target[j].
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_6 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok false) :
    ∃ k, k < 3 ∧ ∀ i, i < triplets.val.length →
      cell triplets i k ≠ tcell target k ∨
        ∃ j, j < 3 ∧ cell triplets i j > tcell target j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hres : Aegis.MergeTriplets.merge_triplets triplets target = ok false), ∃ k, k < 3 ∧ ∀ i, i < triplets.val.length →
      cell triplets i k ≠ tcell target k ∨
        ∃ j, j < 3 ∧ cell triplets i j > tcell target j) := by
  sorry

/-- Under the preconditions, suppose u and v are both inadmissible for target: there exist coordinates p and q in {0,1,2} with u[p] > target[p] and v[q] > target[q]. Let A be the triplet array obtained from triplets by replacing its i-th entry by u, and let B be the triplet array obtained from triplets by replacing its i-th entry by v, leaving all other entries and target unchanged. Then the function returns the same Boolean on A and target as on B and target.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. Additionally, i is an index with 0 <= i < len(triplets), and u and v are length-3 integer vectors with all entries in 1..1000. -/
theorem spec_7 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (i : Nat) (hi : i < triplets.val.length)
    (u v : alloc.vec.Vec Std.I64) (hu : VecOK u) (hv : VecOK v)
    (hu_inadm : ∃ p, p < 3 ∧ vcell u p > tcell target p)
    (hv_inadm : ∃ q, q < 3 ∧ vcell v q > tcell target q) :
    ∃ r : Bool,
      Aegis.MergeTriplets.merge_triplets (setRow triplets i u) target = ok r ∧
      Aegis.MergeTriplets.merge_triplets (setRow triplets i v) target = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (i : Nat) (hi : i < triplets.val.length)
    (u v : alloc.vec.Vec Std.I64) (hu : VecOK u) (hv : VecOK v)
    (hu_inadm : ∃ p, p < 3 ∧ vcell u p > tcell target p)
    (hv_inadm : ∃ q, q < 3 ∧ vcell v q > tcell target q), ∃ r : Bool,
      Aegis.MergeTriplets.merge_triplets (setRow triplets i u) target = ok r ∧
      Aegis.MergeTriplets.merge_triplets (setRow triplets i v) target = ok r) := by
  sorry

/-- Under these preconditions, let A be the array obtained from triplets by deleting the i-th entry and preserving the order of all other entries. Then the function returns the same Boolean on A and target as on triplets and target.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. Additionally, len(triplets) > 1, and there is an index i with 0 <= i < len(triplets) such that for some j in {0,1,2}, triplets[i][j] > target[j]. -/
theorem spec_8 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hlen : 1 < triplets.val.length)
    (i : Nat) (hi : i < triplets.val.length)
    (hinadm : ∃ j, j < 3 ∧ cell triplets i j > tcell target j) :
    ∃ r : Bool,
      Aegis.MergeTriplets.merge_triplets (delRow triplets i) target = ok r ∧
      Aegis.MergeTriplets.merge_triplets triplets target = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target)
    (hlen : 1 < triplets.val.length)
    (i : Nat) (hi : i < triplets.val.length)
    (hinadm : ∃ j, j < 3 ∧ cell triplets i j > tcell target j), ∃ r : Bool,
      Aegis.MergeTriplets.merge_triplets (delRow triplets i) target = ok r ∧
      Aegis.MergeTriplets.merge_triplets triplets target = ok r) := by
  sorry

/-- Under the preconditions, the function returns r = true if and only if there exists a finite sequence of operations, each choosing distinct indices i and j with 0 <= i,j < len(triplets) and replacing the j-th triplet by the componentwise maximum of the i-th and j-th triplets, after which the target triplet occurs as an element of the resulting triplets array; otherwise r = false.
  Preconditions: len(triplets) is an integer with 1 <= len(triplets) <= 100000; len(target) = 3; for every i with 0 <= i < len(triplets), len(triplets[i]) = 3; and for every i with 0 <= i < len(triplets) and every j in {0,1,2}, both triplets[i][j] and target[j] are integers in the inclusive range 1..1000. -/
theorem spec_9 (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target) :
    ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ↔ ∃ ops : List (Nat × Nat),
        (∀ p ∈ ops, p.1 < triplets.val.length ∧ p.2 < triplets.val.length ∧
          p.1 ≠ p.2) ∧
        Occurs (runOps (rows triplets) ops) target) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (triplets : Slice (alloc.vec.Vec Std.I64)) (target : Slice Std.I64)
    (hpre : InputOK triplets target), ∃ r : Bool, Aegis.MergeTriplets.merge_triplets triplets target = ok r ∧
      (r = true ↔ ∃ ops : List (Nat × Nat),
        (∀ p ∈ ops, p.1 < triplets.val.length ∧ p.2 < triplets.val.length ∧
          p.1 ≠ p.2) ∧
        Occurs (runOps (rows triplets) ops) target)) := by
  sorry

end AegisSpec.MergeTriplets
