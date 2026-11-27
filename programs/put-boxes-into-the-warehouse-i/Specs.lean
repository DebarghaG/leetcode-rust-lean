import Aegis.MaxBoxesInWarehouse.Code.Funs

/-!
# Specifications of `Aegis.MaxBoxesInWarehouse.max_boxes_in_warehouse`

LeetCode problem `put-boxes-into-the-warehouse-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxBoxesInWarehouse

namespace AegisSpec.MaxBoxesInWarehouse

def vals (s : Slice I64) : List Int := s.val.map (fun x => x.val)

def getI (l : List Int) (i : Nat) : Int := ((l[i]?).getD 0)

def elem (s : Slice I64) (i : Nat) : Int := getI (vals s) i

def capsFrom (m : Int) : List Int → List Int
  | [] => []
  | y :: ys => min m y :: capsFrom (min m y) ys

def caps : List Int → List Int
  | [] => []
  | x :: xs => x :: capsFrom x xs

def cap (w : Slice I64) (j : Nat) : Int := getI (caps (vals w)) j

def ofInts (l : List Int) : List I64 := l.map (fun x => (⟨BitVec.ofInt 64 x⟩ : I64))

def insertSorted (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortVals : List Int → List Int
  | [] => []
  | x :: xs => insertSorted x (sortVals xs)

def InjUpTo (f : Nat → Nat) (R : Int) : Prop :=
  ∀ t t' : Nat, (t : Int) < R → (t' : Int) < R → f t = f t' → t = t'

def PermOn (n : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i, i < n → σ i < n) ∧
    (∀ i j, i < n → j < n → σ i = σ j → i = j) ∧
      (∀ j, j < n → ∃ i, i < n ∧ σ i = j)

def Placement (boxes warehouse : Slice I64) (K : Finset Nat) (p : Nat → Nat) : Prop :=
  (∀ b ∈ K, b < boxes.val.length) ∧
    (∀ b ∈ K, p b < warehouse.val.length) ∧
      (∀ b ∈ K, ∀ b' ∈ K, p b = p b' → b = b') ∧
        (∀ b ∈ K, elem boxes b ≤ cap warehouse (p b))

def IsMaxPlacementCard (boxes warehouse : Slice I64) (r : Int) : Prop :=
  (∃ K p, Placement boxes warehouse K p ∧ (K.card : Int) = r) ∧
    ∀ K p, Placement boxes warehouse K p → (K.card : Int) ≤ r

def C2Match (s t : List Int) (k : Nat) : Prop :=
  ∀ i, i < k → getI s i ≤ getI t (t.length - k + i)

def IsLargestC2Card (s t : List Int) (r : Int) : Prop :=
  ∃ k : Nat, r = (k : Int) ∧ k ≤ min s.length t.length ∧ C2Match s t k ∧
    ∀ k' : Nat, k' ≤ min s.length t.length → C2Match s t k' → k' ≤ k

/-- Let cap(j) = min{ warehouse[i] | 0 <= i <= j } for each 0 <= j < len(warehouse). Whenever the function returns a result r, r is the maximum cardinality |K| over sets K subset {0, 1, ..., len(boxes)-1} for which there exists an injective map p from K to {0, 1, ..., len(warehouse)-1} satisfying boxes[b] <= cap(p(b)) for every b in K. Equivalently, r is the largest number of distinct boxes that can be placed simultaneously into distinct rooms, where a box b can use room j exactly when boxes[b] <= cap(j).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_1
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    IsMaxPlacementCard boxes warehouse r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), IsMaxPlacementCard boxes warehouse r.val) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail with overflow, panic, or out-of-bounds error.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_2
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000) :
    ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000), ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= min(len(boxes), len(warehouse)).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_3
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), 0 ≤ r.val ∧ r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= count{ b | 0 <= b < len(boxes) and boxes[b] <= warehouse[0] }.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_4
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    r.val ≤ (((Finset.range boxes.val.length).filter
      (fun b => elem boxes b ≤ elem warehouse 0)).card : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), r.val ≤ (((Finset.range boxes.val.length).filter
      (fun b => elem boxes b ≤ elem warehouse 0)).card : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if boxes[b] > warehouse[0] for every b with 0 <= b < len(boxes).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_5
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    (r.val = 0 ↔ ∀ b, b < boxes.val.length → elem warehouse 0 < elem boxes b) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), (r.val = 0 ↔ ∀ b, b < boxes.val.length → elem warehouse 0 < elem boxes b)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if boxes[0] <= warehouse[0], and r = 0 otherwise.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; len(boxes) = 1. -/
theorem spec_6
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hm : boxes.val.length = 1)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    (elem boxes 0 ≤ elem warehouse 0 → r.val = 1) ∧
      (elem warehouse 0 < elem boxes 0 → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hm : boxes.val.length = 1)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), (elem boxes 0 ≤ elem warehouse 0 → r.val = 1) ∧
      (elem warehouse 0 < elem boxes 0 → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if there exists b with 0 <= b < len(boxes) and boxes[b] <= warehouse[0], and r = 0 otherwise.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; len(warehouse) = 1. -/
theorem spec_7
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hn : warehouse.val.length = 1)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    ((∃ b, b < boxes.val.length ∧ elem boxes b ≤ elem warehouse 0) → r.val = 1) ∧
      (¬ (∃ b, b < boxes.val.length ∧ elem boxes b ≤ elem warehouse 0) → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hn : warehouse.val.length = 1)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), ((∃ b, b < boxes.val.length ∧ elem boxes b ≤ elem warehouse 0) → r.val = 1) ∧
      (¬ (∃ b, b < boxes.val.length ∧ elem boxes b ≤ elem warehouse 0) → r.val = 0)) := by
  sorry

/-- Let cap(j) = min{ warehouse[i] | 0 <= i <= j } for 0 <= j < len(warehouse). Whenever the function returns a result r, r = min(len(boxes), count{ j | 0 <= j < len(warehouse) and cap(j) >= h }).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; there is an integer h such that boxes[i] = h for every i with 0 <= i < len(boxes). -/
theorem spec_8
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (h : Int) (hboxes : ∀ i, i < boxes.val.length → elem boxes i = h)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    r.val = ((min boxes.val.length ((Finset.range warehouse.val.length).filter
      (fun j => h ≤ cap warehouse j)).card : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (h : Int) (hboxes : ∀ i, i < boxes.val.length → elem boxes i = h)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), r.val = ((min boxes.val.length ((Finset.range warehouse.val.length).filter
      (fun j => h ≤ cap warehouse j)).card : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = min(len(warehouse), count{ b | 0 <= b < len(boxes) and boxes[b] <= w }).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; there is an integer w such that warehouse[j] = w for every j with 0 <= j < len(warehouse). -/
theorem spec_9
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (w : Int) (hwarehouse : ∀ j, j < warehouse.val.length → elem warehouse j = w)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    r.val = ((min warehouse.val.length ((Finset.range boxes.val.length).filter
      (fun b => elem boxes b ≤ w)).card : Nat) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (w : Int) (hwarehouse : ∀ j, j < warehouse.val.length → elem warehouse j = w)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), r.val = ((min warehouse.val.length ((Finset.range boxes.val.length).filter
      (fun b => elem boxes b ≤ w)).card : Nat) : Int)) := by
  sorry

/-- Let warehouse' be the slice of length len(warehouse) defined by warehouse'[j] = min{ warehouse[i] | 0 <= i <= j } for every 0 <= j < len(warehouse). If the call on (boxes, warehouse) returns r and the call on (boxes, warehouse') returns r', then r = r'.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_10
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (warehouse' : Slice I64)
    (hwarehouse' : warehouse'.val = ofInts (caps (vals warehouse)))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes warehouse' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (warehouse' : Slice I64)
    (hwarehouse' : warehouse'.val = ofInts (caps (vals warehouse)))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes warehouse' = ok r'), r.val = r'.val) := by
  sorry

/-- If the call on (boxes, warehouse) returns r and the call on (boxes', warehouse) returns r', then r = r'.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; boxes' is a slice with len(boxes') = len(boxes), every element of boxes' is in 1..1000000000, and there exists a bijection pi on {0, 1, ..., len(boxes)-1} such that boxes'[i] = boxes[pi(i)] for every i. -/
theorem spec_11
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (boxes' : Slice I64)
    (hboxes'len : boxes'.val.length = boxes.val.length)
    (hboxes'val : ∀ i, i < boxes'.val.length →
      1 ≤ elem boxes' i ∧ elem boxes' i ≤ 1000000000)
    (hboxes'perm : ∃ σ : Nat → Nat,
      PermOn boxes.val.length σ ∧ ∀ i, i < boxes.val.length → elem boxes' i = elem boxes (σ i))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes' warehouse = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (boxes' : Slice I64)
    (hboxes'len : boxes'.val.length = boxes.val.length)
    (hboxes'val : ∀ i, i < boxes'.val.length →
      1 ≤ elem boxes' i ∧ elem boxes' i ≤ 1000000000)
    (hboxes'perm : ∃ σ : Nat → Nat,
      PermOn boxes.val.length σ ∧ ∀ i, i < boxes.val.length → elem boxes' i = elem boxes (σ i))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes' warehouse = ok r'), r.val = r'.val) := by
  sorry

/-- If the call on (boxes, warehouse1) returns r1 and the call on (boxes, warehouse2) returns r2, then r1 <= r2.
  Preconditions: 1 <= len(boxes) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; warehouse1 and warehouse2 are slices of the same length n with 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= warehouse1[j] <= warehouse2[j] <= 1000000000. -/
theorem spec_12
    (boxes : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (warehouse1 warehouse2 : Slice I64)
    (hw1len : warehouse1.val.length = n) (hw2len : warehouse2.val.length = n)
    (hw1val : ∀ j, j < n → 1 ≤ elem warehouse1 j ∧ elem warehouse1 j ≤ elem warehouse2 j)
    (hw2val : ∀ j, j < n → elem warehouse2 j ≤ 1000000000)
    (r1 r2 : I64)
    (hr1 : max_boxes_in_warehouse boxes warehouse1 = ok r1)
    (hr2 : max_boxes_in_warehouse boxes warehouse2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (boxes : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (n : Nat) (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (warehouse1 warehouse2 : Slice I64)
    (hw1len : warehouse1.val.length = n) (hw2len : warehouse2.val.length = n)
    (hw1val : ∀ j, j < n → 1 ≤ elem warehouse1 j ∧ elem warehouse1 j ≤ elem warehouse2 j)
    (hw2val : ∀ j, j < n → elem warehouse2 j ≤ 1000000000)
    (r1 r2 : I64)
    (hr1 : max_boxes_in_warehouse boxes warehouse1 = ok r1)
    (hr2 : max_boxes_in_warehouse boxes warehouse2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If the call on (boxes1, warehouse) returns r1 and the call on (boxes2, warehouse) returns r2, then r2 >= r1.
  Preconditions: boxes1 and boxes2 are slices of the same length m with 1 <= m <= 100000; every element of boxes1 and boxes2 is in 1..1000000000; let b1_0 <= ... <= b1_(m-1) be the values of boxes1 sorted nondecreasing and b2_0 <= ... <= b2_(m-1) the values of boxes2 sorted nondecreasing; suppose b2_i <= b1_i for every 0 <= i < m; 1 <= len(warehouse) <= 100000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_13
    (m : Nat) (hm : 1 ≤ m) (hm' : m ≤ 100000)
    (boxes1 boxes2 : Slice I64)
    (hb1len : boxes1.val.length = m) (hb2len : boxes2.val.length = m)
    (hb1val : ∀ i, i < m → 1 ≤ elem boxes1 i ∧ elem boxes1 i ≤ 1000000000)
    (hb2val : ∀ i, i < m → 1 ≤ elem boxes2 i ∧ elem boxes2 i ≤ 1000000000)
    (hsorted : ∀ i, i < m →
      getI (sortVals (vals boxes2)) i ≤ getI (sortVals (vals boxes1)) i)
    (warehouse : Slice I64)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r1 r2 : I64)
    (hr1 : max_boxes_in_warehouse boxes1 warehouse = ok r1)
    (hr2 : max_boxes_in_warehouse boxes2 warehouse = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (m : Nat) (hm : 1 ≤ m) (hm' : m ≤ 100000)
    (boxes1 boxes2 : Slice I64)
    (hb1len : boxes1.val.length = m) (hb2len : boxes2.val.length = m)
    (hb1val : ∀ i, i < m → 1 ≤ elem boxes1 i ∧ elem boxes1 i ≤ 1000000000)
    (hb2val : ∀ i, i < m → 1 ≤ elem boxes2 i ∧ elem boxes2 i ≤ 1000000000)
    (hsorted : ∀ i, i < m →
      getI (sortVals (vals boxes2)) i ≤ getI (sortVals (vals boxes1)) i)
    (warehouse : Slice I64)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r1 r2 : I64)
    (hr1 : max_boxes_in_warehouse boxes1 warehouse = ok r1)
    (hr2 : max_boxes_in_warehouse boxes2 warehouse = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Let cap(j) = min{ warehouse[i] | 0 <= i <= j } for 0 <= j < len(warehouse). Whenever the function returns a result r, there exist r distinct indices b_0, ..., b_(r-1) with 0 <= b_t < len(boxes) and r distinct indices j_0, ..., j_(r-1) with 0 <= j_t < len(warehouse) such that boxes[b_t] <= cap(j_t) for every 0 <= t < r. For r = 0 this condition is vacuous.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_14
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    ∃ (b j : Nat → Nat),
      InjUpTo b r.val ∧ InjUpTo j r.val ∧
        ∀ t : Nat, (t : Int) < r.val →
          b t < boxes.val.length ∧ j t < warehouse.val.length ∧
            elem boxes (b t) ≤ cap warehouse (j t) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), ∃ (b j : Nat → Nat),
      InjUpTo b r.val ∧ InjUpTo j r.val ∧
        ∀ t : Nat, (t : Int) < r.val →
          b t < boxes.val.length ∧ j t < warehouse.val.length ∧
            elem boxes (b t) ≤ cap warehouse (j t)) := by
  sorry

/-- Whenever the function returns a result r, r = min(len(boxes), len(warehouse)).
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; max{ boxes[i] | 0 <= i < len(boxes) } <= min{ warehouse[j] | 0 <= j < len(warehouse) }. -/
theorem spec_15
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hfit : ∀ i j, i < boxes.val.length → j < warehouse.val.length →
      elem boxes i ≤ elem warehouse j)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    r.val = ((min boxes.val.length warehouse.val.length : Nat) : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (hfit : ∀ i j, i < boxes.val.length → j < warehouse.val.length →
      elem boxes i ≤ elem warehouse j)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), r.val = ((min boxes.val.length warehouse.val.length : Nat) : Int)) := by
  sorry

/-- If the call on (boxes, warehouse) returns r and the call on (boxes', warehouse) returns r', then r <= r' <= r + 1.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; boxes' is a slice with len(boxes') = len(boxes) + 1, every element of boxes' is in 1..1000000000, and the multiset of boxes' is the multiset of boxes plus one additional element h with 1 <= h <= 1000000000. -/
theorem spec_16
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (boxes' : Slice I64)
    (hboxes'len : boxes'.val.length = boxes.val.length + 1)
    (hboxes'val : ∀ i, i < boxes'.val.length →
      1 ≤ elem boxes' i ∧ elem boxes' i ≤ 1000000000)
    (h : Int) (hh : 1 ≤ h) (hh' : h ≤ 1000000000)
    (hboxes'perm : List.Perm (vals boxes') (h :: vals boxes))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes' warehouse = ok r') :
    r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (boxes' : Slice I64)
    (hboxes'len : boxes'.val.length = boxes.val.length + 1)
    (hboxes'val : ∀ i, i < boxes'.val.length →
      1 ≤ elem boxes' i ∧ elem boxes' i ≤ 1000000000)
    (h : Int) (hh : 1 ≤ h) (hh' : h ≤ 1000000000)
    (hboxes'perm : List.Perm (vals boxes') (h :: vals boxes))
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes' warehouse = ok r'), r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- Let cap(j) = min{ warehouse[i] | 0 <= i <= j } for 0 <= j < len(warehouse). Let t_1 <= ... <= t_n be cap(0),...,cap(n-1) sorted nondecreasing, and s_1 <= ... <= s_m be boxes sorted nondecreasing. Whenever the function returns r, r is the largest integer k with 0 <= k <= min(m,n) such that s_i <= t_{n-k+i} for every 1 <= i <= k.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000. -/
theorem spec_17
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r) :
    IsLargestC2Card (sortVals (vals boxes)) (sortVals (caps (vals warehouse))) r.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (r : I64) (hr : max_boxes_in_warehouse boxes warehouse = ok r), IsLargestC2Card (sortVals (vals boxes)) (sortVals (caps (vals warehouse))) r.val) := by
  sorry

/-- If the call on (boxes, warehouse) returns r and the call on (boxes, warehouse') returns r', then r <= r' <= r + 1.
  Preconditions: 1 <= len(boxes) <= 100000; 1 <= len(warehouse) <= 100000; for every i with 0 <= i < len(boxes), 1 <= boxes[i] <= 1000000000; for every j with 0 <= j < len(warehouse), 1 <= warehouse[j] <= 1000000000; warehouse' is a slice with len(warehouse') = len(warehouse) + 1, every element of warehouse' is in 1..1000000000, and warehouse'[j] = warehouse[j] for every 0 <= j < len(warehouse). -/
theorem spec_18
    (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (warehouse' : Slice I64)
    (hwarehouse'len : warehouse'.val.length = warehouse.val.length + 1)
    (hwarehouse'val : ∀ j, j < warehouse'.val.length →
      1 ≤ elem warehouse' j ∧ elem warehouse' j ≤ 1000000000)
    (hwarehouse'ext : ∀ j, j < warehouse.val.length → elem warehouse' j = elem warehouse j)
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes warehouse' = ok r') :
    r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_18_neg :
    ¬ (∀ (boxes warehouse : Slice I64)
    (hbm : 1 ≤ boxes.val.length) (hbm' : boxes.val.length ≤ 100000)
    (hwn : 1 ≤ warehouse.val.length) (hwn' : warehouse.val.length ≤ 100000)
    (hbox : ∀ i, i < boxes.val.length → 1 ≤ elem boxes i ∧ elem boxes i ≤ 1000000000)
    (hware : ∀ j, j < warehouse.val.length →
      1 ≤ elem warehouse j ∧ elem warehouse j ≤ 1000000000)
    (warehouse' : Slice I64)
    (hwarehouse'len : warehouse'.val.length = warehouse.val.length + 1)
    (hwarehouse'val : ∀ j, j < warehouse'.val.length →
      1 ≤ elem warehouse' j ∧ elem warehouse' j ≤ 1000000000)
    (hwarehouse'ext : ∀ j, j < warehouse.val.length → elem warehouse' j = elem warehouse j)
    (r r' : I64)
    (hr : max_boxes_in_warehouse boxes warehouse = ok r)
    (hr' : max_boxes_in_warehouse boxes warehouse' = ok r'), r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

end AegisSpec.MaxBoxesInWarehouse
