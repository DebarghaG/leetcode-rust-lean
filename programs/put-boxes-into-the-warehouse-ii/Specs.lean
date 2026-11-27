import Aegis.MaxBoxesInWarehouse.Code.Funs

/-!
# Specifications of `Aegis.MaxBoxesInWarehouse.max_boxes_in_warehouse`

LeetCode problem `put-boxes-into-the-warehouse-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxBoxesInWarehouse

  namespace AegisSpec.MaxBoxesInWarehouse

  def vals (s : Slice I64) : List Int := s.val.map (fun x => x.val)

  def nthVal : List Int → Nat → Int
    | [], _ => 0
    | x :: _, 0 => x
    | _ :: xs, i + 1 => nthVal xs i

  def boxAt (boxes : Slice I64) (b : Nat) : Int := nthVal (vals boxes) b

  def roomHeight (warehouse : Slice I64) (i : Nat) : Int := nthVal (vals warehouse) i

  def listMin? : List Int → Option Int
    | [] => none
    | x :: xs => some (xs.foldr min x)

  def prefixMin (l : List Int) (i : Nat) : Int := (listMin? (l.take (i + 1))).getD 0

  def suffixMin (l : List Int) (i : Nat) : Int := (listMin? (l.drop i)).getD 0

  def capOf (l : List Int) (i : Nat) : Int := max (prefixMin l i) (suffixMin l i)

  def cap (warehouse : Slice I64) (i : Nat) : Int := capOf (vals warehouse) i

  def capsOf (l : List Int) : List Int := (List.range l.length).map (capOf l)

  def caps (warehouse : Slice I64) : List Int := capsOf (vals warehouse)

  def capsMax (warehouse : Slice I64) : Int := (caps warehouse).foldr max 0

  def warehouseMin (warehouse : Slice I64) : Int := (listMin? (vals warehouse)).getD 0

  def countGE (l : List Int) (h : Int) : Nat := l.countP (fun x => decide (h ≤ x))

  def countLE (l : List Int) (h : Int) : Nat := l.countP (fun x => decide (x ≤ h))

  def countEq (l : List Int) (h : Int) : Nat := l.countP (fun x => decide (x = h))

  def Feasible (boxes warehouse : Slice I64) (k : Nat) : Prop :=
    ∃ b q : Fin k → Nat,
      (∀ t, b t < boxes.val.length) ∧ (∀ t, q t < warehouse.val.length) ∧
        Function.Injective b ∧ Function.Injective q ∧
          (∀ t, boxAt boxes (b t) ≤ cap warehouse (q t))

  def SortedUp (l : List Int) : Prop := l.Pairwise (fun a b => a ≤ b)

  def insertSorted (x : Int) : List Int → List Int
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

  def sortUp : List Int → List Int
    | [] => []
    | x :: xs => insertSorted x (sortUp xs)

  def fits (b c : List Int) (k : Nat) : Prop :=
    k ≤ min b.length c.length ∧ ∀ t, t < k → nthVal b t ≤ nthVal c (c.length - k + t)

  noncomputable def bestFit (b c : List Int) : Nat :=
    by classical exact Nat.findGreatest (fun k => fits b c k) (min b.length c.length)

  /-- Let m = len(boxes) and n = len(warehouse). For each room index i with 0 <= i < n define cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < n } ). The function returns a result r, and r is the largest integer k with 0 <= k <= min(m,n) for which there exist k distinct box indices b_1,...,b_k in [0,m) and k distinct room indices q_1,...,q_k in [0,n) such that boxes[b_t] <= cap(q_t) for every t = 1..k. For k=0 no indices are needed.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_1 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int) ∧
        Feasible boxes warehouse r.val.toNat ∧
        (∀ k : Nat, k ≤ min boxes.val.length warehouse.val.length →
          Feasible boxes warehouse k → (k : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int) ∧
          Feasible boxes warehouse r.val.toNat ∧
          (∀ k : Nat, k ≤ min boxes.val.length warehouse.val.length →
            Feasible boxes warehouse k → (k : Int) ≤ r.val)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result; it does not fail, panic, or overflow.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_2 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∃ r : I64, max_boxes_in_warehouse boxes warehouse = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= min(len(boxes), len(warehouse)).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_3 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        0 ≤ r.val ∧ r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          0 ≤ r.val ∧ r.val ≤ ((min boxes.val.length warehouse.val.length : Nat) : Int)) := by
    sorry

  /-- For each room index i with 0 <= i < len(warehouse), define cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < len(warehouse) } ). Whenever the function returns a result r, r = 0 if and only if for every box index b with 0 <= b < len(boxes) and every room index i with 0 <= i < len(warehouse), boxes[b] > cap(i).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_4 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        (r.val = 0 ↔ ∀ b i, b < boxes.val.length → i < warehouse.val.length →
          boxAt boxes b > cap warehouse i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          (r.val = 0 ↔ ∀ b i, b < boxes.val.length → i < warehouse.val.length →
            boxAt boxes b > cap warehouse i)) := by
    sorry

  /-- Whenever the function returns a result r, r = min(len(boxes), len(warehouse)).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. Also, for every box index b and every room index j, boxes[b] <= warehouse[j]. -/
  theorem spec_5 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hall : ∀ b i, b < boxes.val.length → i < warehouse.val.length →
        boxAt boxes b ≤ roomHeight warehouse i) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        r.val = ((min boxes.val.length warehouse.val.length : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hall : ∀ b i, b < boxes.val.length → i < warehouse.val.length →
          boxAt boxes b ≤ roomHeight warehouse i), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          r.val = ((min boxes.val.length warehouse.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if there exists a box index b with 0 <= b < len(boxes) and boxes[b] <= warehouse[0], and r = 0 otherwise.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. Also len(warehouse) = 1. -/
  theorem spec_6 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hwarehouse_len1 : warehouse.val.length = 1) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        ((∃ b, b < boxes.val.length ∧ boxAt boxes b ≤ roomHeight warehouse 0) → r.val = 1) ∧
        (¬ (∃ b, b < boxes.val.length ∧ boxAt boxes b ≤ roomHeight warehouse 0) → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hwarehouse_len1 : warehouse.val.length = 1), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          ((∃ b, b < boxes.val.length ∧ boxAt boxes b ≤ roomHeight warehouse 0) → r.val = 1) ∧
          (¬ (∃ b, b < boxes.val.length ∧ boxAt boxes b ≤ roomHeight warehouse 0) → r.val = 0)) := by
    sorry

  /-- For each room index i, define cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < len(warehouse) } ). Whenever the function returns a result r, r = 1 if boxes[0] <= max_{0 <= i < len(warehouse)} cap(i), and r = 0 otherwise.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. Also len(boxes) = 1. -/
  theorem spec_7 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hboxes_len1 : boxes.val.length = 1) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        (boxAt boxes 0 ≤ capsMax warehouse → r.val = 1) ∧
        (capsMax warehouse < boxAt boxes 0 → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hboxes_len1 : boxes.val.length = 1), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          (boxAt boxes 0 ≤ capsMax warehouse → r.val = 1) ∧
          (capsMax warehouse < boxAt boxes 0 → r.val = 0)) := by
    sorry

  /-- Let r be the result of the function on (boxes, warehouse) and r' the result on (boxes', warehouse). Whenever both calls return, r = r'.
    Preconditions: boxes, boxes', and warehouse are nonempty slices of 64-bit integers satisfying the problem constraints. len(boxes') = len(boxes), warehouse is the same, and for every integer h in [1, 10^9], the number of occurrences of h in boxes equals the number of occurrences of h in boxes'. -/
  theorem spec_8 (boxes boxes' warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
      (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
      (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hboxes'_range : ∀ b, b < boxes'.val.length →
        1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hlen : boxes'.val.length = boxes.val.length)
      (hcount : ∀ h : Int, 1 ≤ h → h ≤ 1000000000 →
        countEq (vals boxes) h = countEq (vals boxes') h) :
      ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        max_boxes_in_warehouse boxes' warehouse = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (boxes boxes' warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
        (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
        (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hboxes'_range : ∀ b, b < boxes'.val.length →
          1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hlen : boxes'.val.length = boxes.val.length)
        (hcount : ∀ h : Int, 1 ≤ h → h ≤ 1000000000 →
          countEq (vals boxes) h = countEq (vals boxes') h), ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          max_boxes_in_warehouse boxes' warehouse = ok r' → r = r') := by
    sorry

  /-- Let r be the result of the function on (boxes, warehouse) and r' the result on (boxes, warehouse'). Whenever both calls return, r = r'.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers satisfying the problem constraints. Let warehouse' be defined by warehouse'[i] = warehouse[len(warehouse)-1-i] for every 0 <= i < len(warehouse). -/
  theorem spec_9 (boxes warehouse warehouse' : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hwarehouse'_ne : 0 < warehouse'.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hwarehouse'_len : warehouse'.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hwarehouse'_range : ∀ i, i < warehouse'.val.length →
        1 ≤ roomHeight warehouse' i ∧ roomHeight warehouse' i ≤ 1000000000)
      (hlen : warehouse'.val.length = warehouse.val.length)
      (hrev : ∀ i, i < warehouse.val.length →
        roomHeight warehouse' i = roomHeight warehouse (warehouse.val.length - 1 - i)) :
      ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        max_boxes_in_warehouse boxes warehouse' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (boxes warehouse warehouse' : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hwarehouse'_ne : 0 < warehouse'.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hwarehouse'_len : warehouse'.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hwarehouse'_range : ∀ i, i < warehouse'.val.length →
          1 ≤ roomHeight warehouse' i ∧ roomHeight warehouse' i ≤ 1000000000)
        (hlen : warehouse'.val.length = warehouse.val.length)
        (hrev : ∀ i, i < warehouse.val.length →
          roomHeight warehouse' i = roomHeight warehouse (warehouse.val.length - 1 - i)), ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          max_boxes_in_warehouse boxes warehouse' = ok r' → r = r') := by
    sorry

  /-- Let r be the result of the function on (boxes, warehouse) and r' the result on (boxes', warehouse). Whenever both calls return, r' >= r.
    Preconditions: boxes and boxes' are nonempty slices of 64-bit integers satisfying the problem constraints, and warehouse is a nonempty slice satisfying the problem constraints. len(boxes') = len(boxes) + 1, len(boxes') <= 100000, and boxes' is obtained from boxes by adding one additional value v with 1 <= v <= 10^9, up to permutation of the resulting multiset. -/
  theorem spec_10 (boxes boxes' warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
      (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
      (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hboxes'_range : ∀ b, b < boxes'.val.length →
        1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hlen : boxes'.val.length = boxes.val.length + 1)
      (hext : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000000000 ∧
        List.Perm (vals boxes') (vals boxes ++ [v])) :
      ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        max_boxes_in_warehouse boxes' warehouse = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (boxes boxes' warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
        (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
        (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hboxes'_range : ∀ b, b < boxes'.val.length →
          1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hlen : boxes'.val.length = boxes.val.length + 1)
        (hext : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000000000 ∧
          List.Perm (vals boxes') (vals boxes ++ [v])), ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          max_boxes_in_warehouse boxes' warehouse = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Let r be the result of the function on (boxes, warehouse) and r' the result on (boxes', warehouse). Whenever both calls return, r' <= r + 1.
    Preconditions: boxes and boxes' are nonempty slices of 64-bit integers satisfying the problem constraints, and warehouse is a nonempty slice satisfying the problem constraints. len(boxes') = len(boxes) + 1, len(boxes') <= 100000, and boxes' is obtained from boxes by adding one additional value v with 1 <= v <= 10^9, up to permutation of the resulting multiset. -/
  theorem spec_11 (boxes boxes' warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
      (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
      (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hboxes'_range : ∀ b, b < boxes'.val.length →
        1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hlen : boxes'.val.length = boxes.val.length + 1)
      (hext : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000000000 ∧
        List.Perm (vals boxes') (vals boxes ++ [v])) :
      ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        max_boxes_in_warehouse boxes' warehouse = ok r' → r'.val ≤ r.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (boxes boxes' warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hboxes'_ne : 0 < boxes'.val.length)
        (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hboxes'_len : boxes'.val.length ≤ 100000)
        (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hboxes'_range : ∀ b, b < boxes'.val.length →
          1 ≤ boxAt boxes' b ∧ boxAt boxes' b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hlen : boxes'.val.length = boxes.val.length + 1)
        (hext : ∃ v : Int, 1 ≤ v ∧ v ≤ 1000000000 ∧
          List.Perm (vals boxes') (vals boxes ++ [v])), ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          max_boxes_in_warehouse boxes' warehouse = ok r' → r'.val ≤ r.val + 1) := by
    sorry

  /-- Let r be the result of the function on (boxes, warehouse) and r' the result on (boxes, warehouse'). Whenever both calls return, r' >= r.
    Preconditions: boxes, warehouse, and warehouse' are nonempty slices of 64-bit integers satisfying the problem constraints. len(warehouse') = len(warehouse), and warehouse'[i] >= warehouse[i] for every 0 <= i < len(warehouse). -/
  theorem spec_12 (boxes warehouse warehouse' : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hwarehouse'_ne : 0 < warehouse'.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hwarehouse'_len : warehouse'.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hwarehouse'_range : ∀ i, i < warehouse'.val.length →
        1 ≤ roomHeight warehouse' i ∧ roomHeight warehouse' i ≤ 1000000000)
      (hlen : warehouse'.val.length = warehouse.val.length)
      (hle : ∀ i, i < warehouse.val.length →
        roomHeight warehouse i ≤ roomHeight warehouse' i) :
      ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        max_boxes_in_warehouse boxes warehouse' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (boxes warehouse warehouse' : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hwarehouse'_ne : 0 < warehouse'.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hwarehouse'_len : warehouse'.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hwarehouse'_range : ∀ i, i < warehouse'.val.length →
          1 ≤ roomHeight warehouse' i ∧ roomHeight warehouse' i ≤ 1000000000)
        (hlen : warehouse'.val.length = warehouse.val.length)
        (hle : ∀ i, i < warehouse.val.length →
          roomHeight warehouse i ≤ roomHeight warehouse' i), ∀ r r' : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          max_boxes_in_warehouse boxes warehouse' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- For each room index i, define cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < len(warehouse) } ). Whenever the function returns a result r, r = min( len(boxes), the number of room indices i with 0 <= i < len(warehouse) and cap(i) >= h ).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers satisfying the problem constraints. There is a value h in [1, 10^9] such that boxes[b] = h for every 0 <= b < len(boxes). -/
  theorem spec_13 (boxes warehouse : Slice I64) (h : Int)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hlo : 1 ≤ h) (hhi : h ≤ 1000000000)
      (hconst : ∀ b, b < boxes.val.length → boxAt boxes b = h) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        r.val = ((min boxes.val.length (countGE (caps warehouse) h) : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (boxes warehouse : Slice I64) (h : Int)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hlo : 1 ≤ h) (hhi : h ≤ 1000000000)
        (hconst : ∀ b, b < boxes.val.length → boxAt boxes b = h), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          r.val = ((min boxes.val.length (countGE (caps warehouse) h) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = min( the number of box indices b with 0 <= b < len(boxes) and boxes[b] <= H, len(warehouse) ).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers satisfying the problem constraints. There is a value H in [1, 10^9] such that warehouse[i] = H for every 0 <= i < len(warehouse). -/
  theorem spec_14 (boxes warehouse : Slice I64) (H : Int)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
      (hHlo : 1 ≤ H) (hHhi : H ≤ 1000000000)
      (hconst : ∀ i, i < warehouse.val.length → roomHeight warehouse i = H) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        r.val = ((min (countLE (vals boxes) H) warehouse.val.length : Nat) : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (boxes warehouse : Slice I64) (H : Int)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000)
        (hHlo : 1 ≤ H) (hHhi : H ≤ 1000000000)
        (hconst : ∀ i, i < warehouse.val.length → roomHeight warehouse i = H), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          r.val = ((min (countLE (vals boxes) H) warehouse.val.length : Nat) : Int)) := by
    sorry

  /-- For each room index i, define cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < len(warehouse) } ). Whenever the function returns a result r, if r > 0 then there exist r distinct box indices b_1,...,b_r and r distinct room indices q_1,...,q_r such that boxes[b_t] <= cap(q_t) for every t = 1..r.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_15 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r → 0 < r.val →
        Feasible boxes warehouse r.val.toNat := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r → 0 < r.val →
          Feasible boxes warehouse r.val.toNat) := by
    sorry

  /-- Let cap(i) = max( min{ warehouse[j] | 0 <= j <= i }, min{ warehouse[j] | i <= j < len(warehouse) } ) for 0 <= i < len(warehouse). Let b[0] <= ... <= b[m-1] be the multiset of boxes sorted nondecreasing, and c[0] <= ... <= c[n-1] be the multiset { cap(i) } sorted nondecreasing, where m = len(boxes) and n = len(warehouse). Whenever the function returns r, r = max{ k | 0 <= k <= min(m,n) and for all t with 0 <= t < k, b[t] <= c[n-k+t] }.
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_16 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        r.val = ((bestFit (sortUp (vals boxes)) (sortUp (caps warehouse)) : Nat) : Int) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          r.val = ((bestFit (sortUp (vals boxes)) (sortUp (caps warehouse)) : Nat) : Int)) := by
    sorry

  /-- Let H = min{ warehouse[i] | 0 <= i < len(warehouse) } and let q be the number of box indices b with boxes[b] <= H. Whenever the function returns r, r >= min(q, len(warehouse)).
    Preconditions: boxes and warehouse are nonempty slices of 64-bit integers with len(boxes), len(warehouse) <= 100000 and every element in [1, 10^9]. -/
  theorem spec_17 (boxes warehouse : Slice I64)
      (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
      (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
      (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
      (hwarehouse_range : ∀ i, i < warehouse.val.length →
        1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000) :
      ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
        ((min (countLE (vals boxes) (warehouseMin warehouse))
          warehouse.val.length : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (boxes warehouse : Slice I64)
        (hboxes_ne : 0 < boxes.val.length) (hwarehouse_ne : 0 < warehouse.val.length)
        (hboxes_len : boxes.val.length ≤ 100000) (hwarehouse_len : warehouse.val.length ≤ 100000)
        (hboxes_range : ∀ b, b < boxes.val.length → 1 ≤ boxAt boxes b ∧ boxAt boxes b ≤ 1000000000)
        (hwarehouse_range : ∀ i, i < warehouse.val.length →
          1 ≤ roomHeight warehouse i ∧ roomHeight warehouse i ≤ 1000000000), ∀ r : I64, max_boxes_in_warehouse boxes warehouse = ok r →
          ((min (countLE (vals boxes) (warehouseMin warehouse))
            warehouse.val.length : Nat) : Int) ≤ r.val) := by
    sorry

  end AegisSpec.MaxBoxesInWarehouse
