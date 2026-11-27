import Aegis.MinAvailableDuration.Code.Funs

/-!
# Specifications of `Aegis.MinAvailableDuration.min_available_duration`

LeetCode problem `meeting-scheduler`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinAvailableDuration

namespace AegisSpec.MinAvailableDuration

def ints (v : alloc.vec.Vec Std.I64) : List ℤ :=
  v.val.map (fun x => x.val)

def slotStart (slots : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ :=
  match slots.val[i]? with
  | some v => (ints v).headD 0
  | none => 0

def slotEnd (slots : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ :=
  match slots.val[i]? with
  | some v => ((ints v).drop 1).headD 0
  | none => 0

def vecGet (v : alloc.vec.Vec Std.I64) (i : Nat) : ℤ :=
  (ints v).getD i 0

def IsWellFormedSlot (v : alloc.vec.Vec Std.I64) : Prop :=
  ∃ s e : ℤ, ints v = [s, e] ∧ 0 ≤ s ∧ s < e ∧ e ≤ 1000000000

def SlotsWellFormed (slots : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ v ∈ slots.val, IsWellFormedSlot v

def PairwiseNonIntersecting (slots : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i, i < slots.val.length → ∀ j, j < slots.val.length → i ≠ j →
    slotStart slots i > slotEnd slots j ∨ slotStart slots j > slotEnd slots i

structure ValidInputs (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64) :
    Prop where

  slots1_len_ge_one : 1 ≤ slots1.val.length

  slots1_len_le : slots1.val.length ≤ 10000

  slots2_len_ge_one : 1 ≤ slots2.val.length

  slots2_len_le : slots2.val.length ≤ 10000

  slots1_well_formed : SlotsWellFormed slots1

  slots2_well_formed : SlotsWellFormed slots2

  duration_ge_one : 1 ≤ duration.val

  duration_le : duration.val ≤ 1000000

  slots1_pairwise : PairwiseNonIntersecting slots1

  slots2_pairwise : PairwiseNonIntersecting slots2

def Feasible (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : ℤ) (s : ℤ) : Prop :=
  ∃ i j : Nat, i < slots1.val.length ∧ j < slots2.val.length ∧
    slotStart slots1 i ≤ s ∧ s + duration ≤ slotEnd slots1 i ∧
    slotStart slots2 j ≤ s ∧ s + duration ≤ slotEnd slots2 j

/-- Whenever the function returns a result r, let a time s be feasible if there exist indices i and j with 0 <= i < len(slots1), 0 <= j < len(slots2), slots1[i][0] <= s, s + duration <= slots1[i][1], slots2[j][0] <= s, and s + duration <= slots2[j][1]. If some integer s is feasible, then len(r) = 2, r[0] is the least feasible integer, and r[1] = r[0] + duration. If no integer s is feasible, then len(r) = 0.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_1 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        ((∃ s : ℤ, Feasible slots1 slots2 duration.val s) →
            r.val.length = 2 ∧
            Feasible slots1 slots2 duration.val (vecGet r 0) ∧
            (∀ s : ℤ, Feasible slots1 slots2 duration.val s → vecGet r 0 ≤ s) ∧
            vecGet r 1 = vecGet r 0 + duration.val) ∧
        ((¬ ∃ s : ℤ, Feasible slots1 slots2 duration.val s) → r.val.length = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        ((∃ s : ℤ, Feasible slots1 slots2 duration.val s) →
            r.val.length = 2 ∧
            Feasible slots1 slots2 duration.val (vecGet r 0) ∧
            (∀ s : ℤ, Feasible slots1 slots2 duration.val s → vecGet r 0 ≤ s) ∧
            vecGet r 1 = vecGet r 0 + duration.val) ∧
        ((¬ ∃ s : ℤ, Feasible slots1 slots2 duration.val s) → r.val.length = 0)) := by
  sorry

/-- Whenever the function returns a result r, either len(r) = 0 or len(r) = 2.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_2 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 0 ∨ r.val.length = 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 0 ∨ r.val.length = 2) := by
  sorry

/-- The function returns some result r; it does not fail, overflow, or panic on any input satisfying the preconditions.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_3 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∃ r : alloc.vec.Vec Std.I64, min_available_duration slots1 slots2 duration = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∃ r : alloc.vec.Vec Std.I64, min_available_duration slots1 slots2 duration = ok r) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, r[1] = r[0] + duration.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_4 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        vecGet r 1 = vecGet r 0 + duration.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        vecGet r 1 = vecGet r 0 + duration.val) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, there exist indices i and j with 0 <= i < len(slots1) and 0 <= j < len(slots2) such that slots1[i][0] <= r[0], r[0] + duration <= slots1[i][1], slots2[j][0] <= r[0], and r[0] + duration <= slots2[j][1].
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_5 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∃ i j : Nat, i < slots1.val.length ∧ j < slots2.val.length ∧
          slotStart slots1 i ≤ vecGet r 0 ∧ vecGet r 0 + duration.val ≤ slotEnd slots1 i ∧
          slotStart slots2 j ≤ vecGet r 0 ∧ vecGet r 0 + duration.val ≤ slotEnd slots2 j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∃ i j : Nat, i < slots1.val.length ∧ j < slots2.val.length ∧
          slotStart slots1 i ≤ vecGet r 0 ∧ vecGet r 0 + duration.val ≤ slotEnd slots1 i ∧
          slotStart slots2 j ≤ vecGet r 0 ∧ vecGet r 0 + duration.val ≤ slotEnd slots2 j) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every integer s and every pair of indices i,j with 0 <= i < len(slots1), 0 <= j < len(slots2), slots1[i][0] <= s, s + duration <= slots1[i][1], slots2[j][0] <= s, and s + duration <= slots2[j][1], it holds that r[0] <= s.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_6 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∀ (s : ℤ) (i j : Nat), i < slots1.val.length → j < slots2.val.length →
          slotStart slots1 i ≤ s → s + duration.val ≤ slotEnd slots1 i →
          slotStart slots2 j ≤ s → s + duration.val ≤ slotEnd slots2 j →
          vecGet r 0 ≤ s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∀ (s : ℤ) (i j : Nat), i < slots1.val.length → j < slots2.val.length →
          slotStart slots1 i ≤ s → s + duration.val ≤ slotEnd slots1 i →
          slotStart slots2 j ≤ s → s + duration.val ≤ slotEnd slots2 j →
          vecGet r 0 ≤ s) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if for every i,j with 0 <= i < len(slots1) and 0 <= j < len(slots2), max(slots1[i][0], slots2[j][0]) + duration > min(slots1[i][1], slots2[j][1]).
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_7 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        (r.val.length = 0 ↔
          ∀ (i j : Nat), i < slots1.val.length → j < slots2.val.length →
            max (slotStart slots1 i) (slotStart slots2 j) + duration.val >
              min (slotEnd slots1 i) (slotEnd slots2 j)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        (r.val.length = 0 ↔
          ∀ (i j : Nat), i < slots1.val.length → j < slots2.val.length →
            max (slotStart slots1 i) (slotStart slots2 j) + duration.val >
              min (slotEnd slots1 i) (slotEnd slots2 j))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, 0 <= r[0] and r[1] <= 1000000000.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_8 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        0 ≤ vecGet r 0 ∧ vecGet r 1 ≤ 1000000000 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        0 ≤ vecGet r 0 ∧ vecGet r 1 ≤ 1000000000) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, r[0] < r[1].
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_9 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        vecGet r 0 < vecGet r 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        vecGet r 0 < vecGet r 1) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, there exist indices i,j with 0 <= i < len(slots1) and 0 <= j < len(slots2) such that max(slots1[i][0], slots2[j][0]) + duration <= min(slots1[i][1], slots2[j][1]) and r[0] = max(slots1[i][0], slots2[j][0]).
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_10 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∃ i j : Nat, i < slots1.val.length ∧ j < slots2.val.length ∧
          max (slotStart slots1 i) (slotStart slots2 j) + duration.val ≤
            min (slotEnd slots1 i) (slotEnd slots2 j) ∧
          vecGet r 0 = max (slotStart slots1 i) (slotStart slots2 j) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ r : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r → r.val.length = 2 →
        ∃ i j : Nat, i < slots1.val.length ∧ j < slots2.val.length ∧
          max (slotStart slots1 i) (slotStart slots2 j) + duration.val ≤
            min (slotEnd slots1 i) (slotEnd slots2 j) ∧
          vecGet r 0 = max (slotStart slots1 i) (slotStart slots2 j)) := by
  sorry

/-- For any slices slots1' and slots2' that are permutations of slots1 and slots2 respectively (same lengths and same multiset of slot vectors), if the call on slots1', slots2', duration returns r' and the call on slots1, slots2, duration returns r, then r = r'.
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_11 (slots1 slots2 slots1' slots2' : Slice (alloc.vec.Vec Std.I64))
    (duration : Std.I64) (h : ValidInputs slots1 slots2 duration)
    (h1 : slots1'.val.Perm slots1.val) (h2 : slots2'.val.Perm slots2.val) :
    ∀ r r' : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        min_available_duration slots1' slots2' duration = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (slots1 slots2 slots1' slots2' : Slice (alloc.vec.Vec Std.I64))
    (duration : Std.I64) (h : ValidInputs slots1 slots2 duration)
    (h1 : slots1'.val.Perm slots1.val) (h2 : slots2'.val.Perm slots2.val), ∀ r r' : alloc.vec.Vec Std.I64,
      min_available_duration slots1 slots2 duration = ok r →
        min_available_duration slots1' slots2' duration = ok r' → r = r') := by
  sorry

/-- For every integer d2 with duration <= d2 <= 1000000, if the call on slots1, slots2, d2 returns a result r2 with len(r2) = 2, then the call on slots1, slots2, duration returns a result r with len(r) = 2 and r[0] <= r2[0].
  Preconditions: slots1 and slots2 are slices of vectors; 1 <= len(slots1) <= 10000; 1 <= len(slots2) <= 10000; every slot vector has length 2; for every i with 0 <= i < len(slots1), 0 <= slots1[i][0] < slots1[i][1] <= 1000000000; for every j with 0 <= j < len(slots2), 0 <= slots2[j][0] < slots2[j][1] <= 1000000000; 1 <= duration <= 1000000; the slots in slots1 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots1), 0 <= j < len(slots1), i != j, either slots1[i][0] > slots1[j][1] or slots1[j][0] > slots1[i][1]; and the slots in slots2 are pairwise non-intersecting: for all i,j with 0 <= i < len(slots2), 0 <= j < len(slots2), i != j, either slots2[i][0] > slots2[j][1] or slots2[j][0] > slots2[i][1]. -/
theorem spec_12 (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration) :
    ∀ (d2 : Std.I64) (r2 : alloc.vec.Vec Std.I64),
      duration.val ≤ d2.val → d2.val ≤ 1000000 →
        min_available_duration slots1 slots2 d2 = ok r2 → r2.val.length = 2 →
          ∃ r : alloc.vec.Vec Std.I64,
            min_available_duration slots1 slots2 duration = ok r ∧ r.val.length = 2 ∧
              vecGet r 0 ≤ vecGet r2 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (slots1 slots2 : Slice (alloc.vec.Vec Std.I64)) (duration : Std.I64)
    (h : ValidInputs slots1 slots2 duration), ∀ (d2 : Std.I64) (r2 : alloc.vec.Vec Std.I64),
      duration.val ≤ d2.val → d2.val ≤ 1000000 →
        min_available_duration slots1 slots2 d2 = ok r2 → r2.val.length = 2 →
          ∃ r : alloc.vec.Vec Std.I64,
            min_available_duration slots1 slots2 duration = ok r ∧ r.val.length = 2 ∧
              vecGet r 0 ≤ vecGet r2 0) := by
  sorry

end AegisSpec.MinAvailableDuration
