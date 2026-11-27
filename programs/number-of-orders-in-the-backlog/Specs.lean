import Aegis.GetNumberOfBacklogOrders.Code.Funs

/-!
# Specifications of `Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders`

LeetCode problem `number-of-orders-in-the-backlog`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetNumberOfBacklogOrders

def priceOf (v : alloc.vec.Vec I64) : ℤ := ((v.val[0]! : I64) : ℤ)

def amountOf (v : alloc.vec.Vec I64) : ℤ := ((v.val[1]! : I64) : ℤ)

def amountNatOf (v : alloc.vec.Vec I64) : ℕ := (amountOf v).toNat

def typeOf (v : alloc.vec.Vec I64) : ℤ := ((v.val[2]! : I64) : ℤ)

def ValidInput (orders : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ orders.val.length ∧ orders.val.length ≤ 100000 ∧
    ∀ v ∈ orders.val,
      v.val.length = 3 ∧
        1 ≤ priceOf v ∧ priceOf v ≤ 1000000000 ∧
          1 ≤ amountOf v ∧ amountOf v ≤ 1000000000 ∧ (typeOf v = 0 ∨ typeOf v = 1)

structure Backlog where

  buys : List ℤ

  sells : List ℤ

def emptyBacklog : Backlog := ⟨[], []⟩

def listMin (l : List ℤ) : Option ℤ :=
  l.foldl (fun acc x =>
    match acc with
    | none => some x
    | some m => some (if x ≤ m then x else m)) none

def listMax (l : List ℤ) : Option ℤ :=
  l.foldl (fun acc x =>
    match acc with
    | none => some x
    | some m => some (if m ≤ x then x else m)) none

def eraseOne : List ℤ → ℤ → List ℤ
  | [], _ => []
  | y :: ys, x => if y = x then ys else y :: eraseOne ys x

def stepBuy (st : Backlog) (p : ℤ) : Backlog :=
  match listMin st.sells with
  | none => ⟨p :: st.buys, st.sells⟩
  | some q =>
    if q ≤ p then ⟨st.buys, eraseOne st.sells q⟩ else ⟨p :: st.buys, st.sells⟩

def stepSell (st : Backlog) (p : ℤ) : Backlog :=
  match listMax st.buys with
  | none => ⟨st.buys, p :: st.sells⟩
  | some q =>
    if p ≤ q then ⟨eraseOne st.buys q, st.sells⟩ else ⟨st.buys, p :: st.sells⟩

def applyBatch (st : Backlog) (p : ℤ) (a : ℕ) (t : ℤ) : Backlog :=
  if t = 0 then Nat.iterate (fun s => stepBuy s p) a st
  else if t = 1 then Nat.iterate (fun s => stepSell s p) a st
  else st

def processAll (orders : Slice (alloc.vec.Vec I64)) : Backlog :=
  orders.val.foldl
    (fun st v => applyBatch st (priceOf v) (amountNatOf v) (typeOf v)) emptyBacklog

def totalBacklog (st : Backlog) : ℕ := st.buys.length + st.sells.length

def buyCount (st : Backlog) (p : ℤ) : ℕ := st.buys.count p

def sellCount (st : Backlog) (p : ℤ) : ℕ := st.sells.count p

def placedByType (orders : Slice (alloc.vec.Vec I64)) (t : ℤ) : ℤ :=
  ((orders.val.filter (fun v => typeOf v == t)).map amountOf).sum

def buyPlaced (orders : Slice (alloc.vec.Vec I64)) : ℤ := placedByType orders 0

def sellPlaced (orders : Slice (alloc.vec.Vec I64)) : ℤ := placedByType orders 1

def placedTotal (orders : Slice (alloc.vec.Vec I64)) : ℤ := (orders.val.map amountOf).sum

/-- Let M = 1000000007. For a backlog state write B(p) for the number of buy orders of price p and S(p) for the number of sell orders of price p. Initially B(p)=S(p)=0 for every integer p. A single buy order of price p is processed as follows: if S is nonzero let q be the least price with S(q)>0; if q<=p then decrement S(q) by 1, otherwise increment B(p) by 1; if S is identically zero then increment B(p). A single sell order of price p is processed as follows: if B is nonzero let q be the greatest price with B(q)>0; if q>=p then decrement B(q) by 1, otherwise increment S(p) by 1; if B is identically zero then increment S(p). For i=0,...,len(orders)-1, with p_i=orders[i][0], a_i=orders[i][1], t_i=orders[i][2], process a_i consecutive single orders of type t_i at price p_i (type 0 = buy, type 1 = sell), starting after all earlier batches. Let B*,S* be the resulting state and let T = sum_p B*(p) + sum_p S*(p), a finite sum. Then the function returns a result r such that 0 <= r < M and r = T mod M.
  Preconditions: P: orders is a slice of i64 vectors with 1 <= len(orders) <= 100000; for every i with 0 <= i < len(orders), len(orders[i]) = 3; writing p_i = orders[i][0], a_i = orders[i][1], t_i = orders[i][2], we have 1 <= p_i <= 1000000000, 1 <= a_i <= 1000000000, and t_i is 0 or 1. -/
theorem spec_1 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) :
    ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        0 ≤ (r : ℤ) ∧ (r : ℤ) < 1000000007 ∧
          (r : ℤ) = ((totalBacklog (processAll orders) : ℕ) : ℤ) % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders), ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        0 ≤ (r : ℤ) ∧ (r : ℤ) < 1000000007 ∧
          (r : ℤ) = ((totalBacklog (processAll orders) : ℕ) : ℤ) % 1000000007) := by
  sorry

/-- Whenever get_number_of_backlog_orders returns a result r on an input satisfying P, r satisfies 0 <= r < 1000000007.
  Preconditions: P: orders is a slice of i64 vectors with 1 <= len(orders) <= 100000; for every i with 0 <= i < len(orders), len(orders[i]) = 3; writing p_i = orders[i][0], a_i = orders[i][1], t_i = orders[i][2], we have 1 <= p_i <= 1000000000, 1 <= a_i <= 1000000000, and t_i is 0 or 1. -/
theorem spec_2 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (r : I64)
    (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r) :
    0 ≤ (r : ℤ) ∧ (r : ℤ) < 1000000007 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (r : I64)
    (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r), 0 ≤ (r : ℤ) ∧ (r : ℤ) < 1000000007) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying P.
  Preconditions: P: orders is a slice of i64 vectors with 1 <= len(orders) <= 100000; for every i with 0 <= i < len(orders), len(orders[i]) = 3; writing p_i = orders[i][0], a_i = orders[i][1], t_i = orders[i][2], we have 1 <= p_i <= 1000000000, 1 <= a_i <= 1000000000, and t_i is 0 or 1. -/
theorem spec_3 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) :
    ∃ r : I64, Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders), ∃ r : I64, Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r) := by
  sorry

/-- Let A = sum_{i=0}^{len(orders)-1} a_i. The function returns r = A mod 1000000007.
  Preconditions: P holds and all order types are equal: there exists t in {0,1} such that t_i = t for every i with 0 <= i < len(orders). -/
theorem spec_4 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (t : ℤ)
    (ht : t = 0 ∨ t = 1) (h_type : ∀ v ∈ orders.val, typeOf v = t) :
    ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = placedTotal orders % 1000000007 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (t : ℤ)
    (ht : t = 0 ∨ t = 1) (h_type : ∀ v ∈ orders.val, typeOf v = t), ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = placedTotal orders % 1000000007) := by
  sorry

/-- Let Bsum = sum of a_i over i with t_i=0, and Ssum = sum of a_i over i with t_i=1. The function returns r = |Bsum - Ssum| mod 1000000007, the least non-negative residue.
  Preconditions: P holds; there is at least one buy batch and at least one sell batch; and there exists an integer p such that p_i = p for every i with 0 <= i < len(orders). -/
theorem spec_5 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (p : ℤ)
    (h_price : ∀ v ∈ orders.val, priceOf v = p)
    (h_buy : ∃ v ∈ orders.val, typeOf v = 0)
    (h_sell : ∃ v ∈ orders.val, typeOf v = 1) :
    ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = ((Int.natAbs (buyPlaced orders - sellPlaced orders) : ℕ) : ℤ) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (p : ℤ)
    (h_price : ∀ v ∈ orders.val, priceOf v = p)
    (h_buy : ∃ v ∈ orders.val, typeOf v = 0)
    (h_sell : ∃ v ∈ orders.val, typeOf v = 1), ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = ((Int.natAbs (buyPlaced orders - sellPlaced orders) : ℕ) : ℤ) % 1000000007) := by
  sorry

/-- Let r be the result on orders and r' the result on orders'. Then r' = (k * r) mod 1000000007, the least non-negative residue.
  Preconditions: P holds for orders; let k be an integer with k >= 1 such that k*a_i <= 1000000000 for every i. Define orders' by orders'[i] = [p_i, k*a_i, t_i]. -/
theorem spec_6 (orders orders' : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (k : ℤ)
    (hk : 1 ≤ k) (h_bound : ∀ v ∈ orders.val, k * amountOf v ≤ 1000000000)
    (h_orders' :
      orders'.val.map (fun v => (priceOf v, amountOf v, typeOf v)) =
        orders.val.map (fun v => (priceOf v, k * amountOf v, typeOf v)))
    (r r' : I64) (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r)
    (hr' : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders' = ok r') :
    (r' : ℤ) = (k * (r : ℤ)) % 1000000007 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (orders orders' : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders) (k : ℤ)
    (hk : 1 ≤ k) (h_bound : ∀ v ∈ orders.val, k * amountOf v ≤ 1000000000)
    (h_orders' :
      orders'.val.map (fun v => (priceOf v, amountOf v, typeOf v)) =
        orders.val.map (fun v => (priceOf v, k * amountOf v, typeOf v)))
    (r r' : I64) (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r)
    (hr' : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders' = ok r'), (r' : ℤ) = (k * (r : ℤ)) % 1000000007) := by
  sorry

/-- Let r be the result on orders and r' the result on orders'. Then r' = r.
  Preconditions: P holds. Let C = 1000000001, and define orders' by orders'[i] = [C - p_i, a_i, 1 - t_i]. -/
theorem spec_7 (orders orders' : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders)
    (h_orders' :
      orders'.val.map (fun v => (priceOf v, amountOf v, typeOf v)) =
        orders.val.map (fun v => (1000000001 - priceOf v, amountOf v, 1 - typeOf v)))
    (r r' : I64) (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r)
    (hr' : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders' = ok r') :
    (r' : ℤ) = (r : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (orders orders' : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders)
    (h_orders' :
      orders'.val.map (fun v => (priceOf v, amountOf v, typeOf v)) =
        orders.val.map (fun v => (1000000001 - priceOf v, amountOf v, 1 - typeOf v)))
    (r r' : I64) (hr : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r)
    (hr' : Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders' = ok r'), (r' : ℤ) = (r : ℤ)) := by
  sorry

/-- Let T be the exact total number of orders in the final backlog after the matching process. The function returns r = T. Consequently 0 <= r <= sum_i a_i < 1000000007.
  Preconditions: P holds and sum_{i=0}^{len(orders)-1} a_i < 1000000007. -/
theorem spec_8 (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders)
    (h_total : placedTotal orders < 1000000007) :
    ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = ((totalBacklog (processAll orders) : ℕ) : ℤ) ∧
          0 ≤ (r : ℤ) ∧ (r : ℤ) ≤ placedTotal orders := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (orders : Slice (alloc.vec.Vec I64)) (hP : ValidInput orders)
    (h_total : placedTotal orders < 1000000007), ∃ r : I64,
      Aegis.GetNumberOfBacklogOrders.get_number_of_backlog_orders orders = ok r ∧
        (r : ℤ) = ((totalBacklog (processAll orders) : ℕ) : ℤ) ∧
          0 ≤ (r : ℤ) ∧ (r : ℤ) ≤ placedTotal orders) := by
  sorry

end AegisSpec.GetNumberOfBacklogOrders
