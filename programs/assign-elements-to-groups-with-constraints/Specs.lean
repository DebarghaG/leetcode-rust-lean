import Aegis.AssignElements.Code.Funs

/-!
# Specifications of `Aegis.AssignElements.assign_elements`

LeetCode problem `assign-elements-to-groups-with-constraints`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.AssignElements

namespace AegisSpec.AssignElements

def valAt (l : List Std.I64) (j : ℕ) : ℤ :=
  match l[j]? with
  | some x => x.val
  | none => 0

def elemAt (elements : List Std.I64) (j : ℤ) : ℤ := valAt elements j.toNat

theorem valAt_coe {l : List Std.I64} {j : ℕ} (h : j < l.length) :
    valAt l j = (l[j]).val := by
  simp only [valAt, List.getElem?_eq_getElem h]

theorem elemAt_coe {elements : List Std.I64} {k : ℕ} (h : k < elements.length) :
    elemAt elements (k : ℤ) = (elements[k]).val := by
  simp only [elemAt, Int.toNat_natCast, valAt_coe h]

def Divides (g e : ℤ) : Prop := g % e = 0

def IsWitness (g : ℤ) (elements : List Std.I64) (j : ℕ) : Prop :=
  j < elements.length ∧ Divides g (valAt elements j)

def HasWitness (g : ℤ) (elements : List Std.I64) : Prop :=
  ∃ j, IsWitness g elements j

def IsLeastWitness (g : ℤ) (elements : List Std.I64) (j : ℕ) : Prop :=
  IsWitness g elements j ∧ ∀ k, k < j → ¬ IsWitness g elements k

def Occurs (v : ℤ) (l : List Std.I64) : Prop := ∃ x, x ∈ l ∧ x.val = v

/-- Whenever assign_elements groups elements returns a result r, len(r) = len(groups), and for every i with 0 <= i < len(groups), if S_i = { j | 0 <= j < len(elements) and groups[i] mod elements[j] = 0 } is nonempty then r[i] equals the least element of S_i, and if S_i is empty then r[i] = -1.
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_1
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    r.val.length = groups.val.length ∧
      (∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
        (HasWitness (groups.val[i]).val elements.val →
            ∃ j, IsLeastWitness (groups.val[i]).val elements.val j ∧
              (r.val[i]).val = (j : ℤ)) ∧
        (¬ HasWitness (groups.val[i]).val elements.val →
            (r.val[i]).val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), r.val.length = groups.val.length ∧
      (∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
        (HasWitness (groups.val[i]).val elements.val →
            ∃ j, IsLeastWitness (groups.val[i]).val elements.val j ∧
              (r.val[i]).val = (j : ℤ)) ∧
        (¬ HasWitness (groups.val[i]).val elements.val →
            (r.val[i]).val = -1))) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, len(r) = len(groups).
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_2
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    r.val.length = groups.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), r.val.length = groups.val.length) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups), either r[i] = -1 or 0 <= r[i] < len(elements).
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_3
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (r.val[i]).val = -1 ∨
        (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (r.val[i]).val = -1 ∨
        (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ))) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups), if r[i] != -1 then 0 <= r[i] < len(elements) and groups[i] mod elements[r[i]] = 0.
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_4
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (r.val[i]).val ≠ -1 →
        (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) ∧
          Divides (groups.val[i]).val (elemAt elements.val (r.val[i]).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (r.val[i]).val ≠ -1 →
        (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) ∧
          Divides (groups.val[i]).val (elemAt elements.val (r.val[i]).val)) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups), if 0 <= r[i] < len(elements), then for every k with 0 <= k < r[i], groups[i] mod elements[k] != 0.
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_5
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) →
        ∀ (k : ℕ), (k : ℤ) < (r.val[i]).val →
          ¬ IsWitness (groups.val[i]).val elements.val k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) →
        ∀ (k : ℕ), (k : ℤ) < (r.val[i]).val →
          ¬ IsWitness (groups.val[i]).val elements.val k) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups), r[i] = -1 if and only if for every j with 0 <= j < len(elements), groups[i] mod elements[j] != 0.
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_6
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      ((r.val[i]).val = -1 ↔
        ∀ (j : ℕ) (hj : j < elements.val.length),
          ¬ Divides (groups.val[i]).val (elements.val[j]).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      ((r.val[i]).val = -1 ↔
        ∀ (j : ℕ) (hj : j < elements.val.length),
          ¬ Divides (groups.val[i]).val (elements.val[j]).val)) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i and k with 0 <= i < len(groups) and 0 <= k < len(groups), if groups[i] = groups[k] then r[i] = r[k].
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_7
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (k : ℕ) (hk : k < groups.val.length) (hkr : k < r.val.length),
      (groups.val[i]).val = (groups.val[k]).val → (r.val[i]).val = (r.val[k]).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (k : ℕ) (hk : k < groups.val.length) (hkr : k < r.val.length),
      (groups.val[i]).val = (groups.val[k]).val → (r.val[i]).val = (r.val[k]).val) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups), if 0 <= r[i] < len(elements), then elements[r[i]] <= groups[i].
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_8
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) →
        elemAt elements.val (r.val[i]).val ≤ (groups.val[i]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length),
      (0 ≤ (r.val[i]).val ∧ (r.val[i]).val < (elements.val.length : ℤ)) →
        elemAt elements.val (r.val[i]).val ≤ (groups.val[i]).val) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups) and every j with 0 <= j < len(elements), if r[i] = j then for every k with 0 <= k < j, elements[k] != elements[j].
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_9
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (j : ℕ) (hj : j < elements.val.length),
      (r.val[i]).val = (j : ℤ) → ¬ Occurs (elements.val[j]).val (elements.val.take j) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (j : ℕ) (hj : j < elements.val.length),
      (r.val[i]).val = (j : ℤ) → ¬ Occurs (elements.val[j]).val (elements.val.take j)) := by
  sorry

/-- Whenever assign_elements groups elements returns a result r, for every i with 0 <= i < len(groups) and every j with 0 <= j < len(elements), if groups[i] mod elements[j] = 0 and for every k with 0 <= k < j, groups[i] mod elements[k] != 0, then r[i] = j.
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_10
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r) :
    ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (j : ℕ) (hj : j < elements.val.length),
      Divides (groups.val[i]).val (elements.val[j]).val →
        (∀ k, k < j → ¬ IsWitness (groups.val[i]).val elements.val k) →
          (r.val[i]).val = (j : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000)
    (r : alloc.vec.Vec Std.I64)
    (hres : assign_elements groups elements = ok r), ∀ (i : ℕ) (hi : i < groups.val.length) (hir : i < r.val.length)
      (j : ℕ) (hj : j < elements.val.length),
      Divides (groups.val[i]).val (elements.val[j]).val →
        (∀ k, k < j → ¬ IsWitness (groups.val[i]).val elements.val k) →
          (r.val[i]).val = (j : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, assign_elements groups elements returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= len(groups) <= 100000; 1 <= len(elements) <= 100000; for every i with 0 <= i < len(groups), 1 <= groups[i] <= 100000; for every j with 0 <= j < len(elements), 1 <= elements[j] <= 100000. All indices are 0-based. -/
theorem spec_11
    (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000) :
    ∃ r, assign_elements groups elements = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (groups elements : Slice Std.I64)
    (hglen_lo : 1 ≤ groups.val.length) (hglen_hi : groups.val.length ≤ 100000)
    (helen_lo : 1 ≤ elements.val.length) (helen_hi : elements.val.length ≤ 100000)
    (hgval : ∀ (i : ℕ) (hi : i < groups.val.length),
      1 ≤ (groups.val[i]).val ∧ (groups.val[i]).val ≤ 100000)
    (heval : ∀ (j : ℕ) (hj : j < elements.val.length),
      1 ≤ (elements.val[j]).val ∧ (elements.val[j]).val ≤ 100000), ∃ r, assign_elements groups elements = ok r) := by
  sorry

end AegisSpec.AssignElements
