import Aegis.LatestTimeCatchTheBus.Code.Funs

/-!
# Specifications of `Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus`

LeetCode problem `the-latest-time-to-catch-a-bus`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std

namespace AegisSpec.LatestTimeCatchTheBus

def elems (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def sortAsc (l : List ℤ) : List ℤ := List.insertionSort (· ≤ ·) l

def sortedElems (s : Slice I64) : List ℤ := sortAsc (elems s)

def listMax : List ℤ → Option ℤ
  | [] => none
  | x :: xs => some (xs.foldl (fun a b => if a ≤ b then b else a) x)

def capOf (capacity : I64) : ℕ := capacity.val.toNat

def boardBus (cap : ℕ) (d : ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([], [])
  | p :: ps =>
      if cap = 0 then ([], p :: ps)
      else if p ≤ d then
        let (b, r) := boardBus (cap - 1) d ps
        (p :: b, r)
      else ([], p :: ps)

def boardAll (cap : ℕ) : List ℤ → List ℤ → List ℤ × List ℤ
  | [], ps => ([], ps)
  | d :: ds, ps =>
      let (b1, r1) := boardBus cap d ps
      let (b2, r2) := boardAll cap ds r1
      (b1 ++ b2, r2)

def lastBusBoarders (cap : ℕ) : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | [d], ps => (boardBus cap d ps).1
  | d :: d' :: ds, ps => lastBusBoarders cap (d' :: ds) (boardBus cap d ps).2

def B (buses : Slice I64) : ℤ := (listMax (elems buses)).getD 0

def lastBusPassengers (buses passengers : Slice I64) (capacity : I64) : List ℤ :=
  lastBusBoarders (capOf capacity) (sortedElems buses) (sortedElems passengers)

def k (buses passengers : Slice I64) (capacity : I64) : ℕ :=
  (lastBusPassengers buses passengers capacity).length

def L (buses passengers : Slice I64) (capacity : I64) : ℤ :=
  (listMax (lastBusPassengers buses passengers capacity)).getD 0

def limit (buses passengers : Slice I64) (capacity : I64) : ℤ :=
  if k buses passengers capacity < capOf capacity then B buses
  else L buses passengers capacity - 1

def IsLatestTime (lim : ℤ) (ps : List ℤ) (r : ℤ) : Prop :=
  r ≤ lim ∧ r ∉ ps ∧ ∀ t : ℤ, r < t → t ≤ lim → t ∈ ps

def countLt (ps : List ℤ) (t : ℤ) : ℕ := ps.countP (fun p => decide (p < t))

def insertAsc (t : ℤ) : List ℤ → List ℤ
  | [] => [t]
  | p :: ps => if t ≤ p then t :: p :: ps else p :: insertAsc t ps

def boardsIfAdded (cap : ℕ) (bs ps : List ℤ) (t : ℤ) : Prop :=
  countLt ps t + 1 ≤ (boardAll cap bs (insertAsc t ps)).1.length

def boardsIfAddedArrays (buses passengers : Slice I64) (capacity : I64) (t : ℤ) : Prop :=
  boardsIfAdded (capOf capacity) (sortedElems buses) (sortedElems passengers) t

/-- Whenever the function returns a result r, r = max{ t ∈ Z : t <= limit and t != passengers[j] for all j with 0 <= j < m }, where B, S, k, L, limit are defined as follows. Let B = max(buses). Define the boarding assignment by processing buses in increasing order of departure time; for each bus departure d, among passengers with arrival <= d not yet assigned, assign up to capacity passengers with the earliest arrival times. Let S be the set of passengers assigned to the bus departing at B, k = |S|, and if k > 0 let L = max{ passengers[j] : j in S }. Set limit = B if k < capacity, and limit = L - 1 if k = capacity. Equivalently, r <= limit, r != passengers[j] for all j, and for every integer t with r < t <= limit there exists j such that t = passengers[j].
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_1 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      IsLatestTime (limit buses passengers capacity) (elems passengers) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      IsLatestTime (limit buses passengers capacity) (elems passengers) r.val) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow).
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_2 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∃ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∃ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= max(buses).
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_3 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ≤ B buses := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ≤ B buses) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(passengers), r != passengers[j].
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_4 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ∉ elems passengers := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ∉ elems passengers) := by
  sorry

/-- Whenever the function returns a result r, if we add a new passenger with arrival time r to the array passengers (keeping buses and capacity unchanged) and run the boarding assignment (process buses in increasing departure order, each bus takes up to capacity earliest-arriving unboarded passengers with arrival <= departure), then the new passenger is assigned to some bus.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_5 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      boardsIfAddedArrays buses passengers capacity r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      boardsIfAddedArrays buses passengers capacity r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer t such that r < t <= max(buses) and t != passengers[j] for all j with 0 <= j < len(passengers), if we add a new passenger with arrival time t to passengers and run the boarding assignment, then the new passenger is not assigned to any bus (misses all buses).
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_6 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      ∀ t : ℤ, r.val < t → t ≤ B buses → t ∉ elems passengers →
        ¬ boardsIfAddedArrays buses passengers capacity t := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      ∀ t : ℤ, r.val < t → t ≤ B buses → t ∉ elems passengers →
        ¬ boardsIfAddedArrays buses passengers capacity t) := by
  sorry

/-- For any arrays buses' and passengers' that are permutations of buses and passengers respectively (so len(buses') = len(buses) and len(passengers') = len(passengers)), if the function returns r on (buses, passengers, capacity) and r' on (buses', passengers', capacity), then r = r'.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_7 (buses passengers buses' passengers' : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hb_perm : List.Perm (elems buses') (elems buses))
    (hp_perm : List.Perm (elems passengers') (elems passengers)) :
    ∀ r r' : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses' passengers' capacity
        = Result.ok r' →
      r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (buses passengers buses' passengers' : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hb_perm : List.Perm (elems buses') (elems buses))
    (hp_perm : List.Perm (elems passengers') (elems passengers)), ∀ r r' : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses' passengers' capacity
        = Result.ok r' →
      r.val = r'.val) := by
  sorry

/-- Using the notation B, S, k, L, limit defined as in spec_1, whenever the function returns a result r, either r = limit, or there exists j with 0 <= j < len(passengers) such that r + 1 = passengers[j].
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_8 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = limit buses passengers capacity ∨
        ∃ p ∈ elems passengers, r.val + 1 = p := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = limit buses passengers capacity ∨
        ∃ p ∈ elems passengers, r.val + 1 = p) := by
  sorry

/-- Using the notation limit defined as in spec_1, whenever the function returns a result r, limit - len(passengers) <= r <= limit.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_9 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      limit buses passengers capacity - (passengers.val.length : ℤ) ≤ r.val ∧
        r.val ≤ limit buses passengers capacity := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      limit buses passengers capacity - (passengers.val.length : ℤ) ≤ r.val ∧
        r.val ≤ limit buses passengers capacity) := by
  sorry

/-- Using the notation B, S, k from spec_1, assume k < capacity (the last bus has spare capacity). If B is not equal to any passenger arrival (B != passengers[j] for all j), then whenever the function returns a result r, r = B.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_10 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity < capOf capacity)
    (hB : B buses ∉ elems passengers) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = B buses := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity < capOf capacity)
    (hB : B buses ∉ elems passengers), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = B buses) := by
  sorry

/-- Using the notation B, S, k, L from spec_1, assume k = capacity (the last bus is full). If L - 1 is not equal to any passenger arrival, then whenever the function returns a result r, r = L - 1.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_11 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity = capOf capacity)
    (hL : L buses passengers capacity - 1 ∉ elems passengers) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = L buses passengers capacity - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity = capOf capacity)
    (hL : L buses passengers capacity - 1 ∉ elems passengers), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = L buses passengers capacity - 1) := by
  sorry

/-- Whenever the function returns a result r, r is the maximum integer t such that (i) t != passengers[j] for all j with 0 <= j < len(passengers), and (ii) if we add a new passenger with arrival time t to passengers and run the boarding assignment, the new passenger is assigned to some bus.
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_12 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ∉ elems passengers ∧
        boardsIfAddedArrays buses passengers capacity r.val ∧
        ∀ t : ℤ, t ∉ elems passengers →
          boardsIfAddedArrays buses passengers capacity t → t ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val ∉ elems passengers ∧
        boardsIfAddedArrays buses passengers capacity r.val ∧
        ∀ t : ℤ, t ∉ elems passengers →
          boardsIfAddedArrays buses passengers capacity t → t ≤ r.val) := by
  sorry

/-- Using the notation B, S, k from spec_1, assume k = capacity (the last bus is full). Whenever the function returns a result r, r < B, where B = max(buses).
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_13 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity = capOf capacity) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val < B buses := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hk : k buses passengers capacity = capOf capacity), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val < B buses) := by
  sorry

/-- If the function returns r1 on (buses, passengers, c1) and r2 on (buses, passengers, c2), then r1 <= r2.
  Preconditions: Let n = len(buses) and m = len(passengers). The arrays satisfy the problem Constraints: n >= 1, m >= 1, 2 <= buses[i] <= 1000000000 for all i, 2 <= passengers[j] <= 1000000000 for all j, all buses distinct, all passengers distinct. Let c1 and c2 be integers with 1 <= c1 <= c2 <= 100000. -/
theorem spec_14 (buses passengers : Slice I64) (c1 c2 : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hc1 : 1 ≤ c1.val) (hc12 : c1.val ≤ c2.val) (hc2 : c2.val ≤ 100000) :
    ∀ r1 r2 : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers c1
        = Result.ok r1 →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers c2
        = Result.ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (buses passengers : Slice I64) (c1 c2 : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hc1 : 1 ≤ c1.val) (hc12 : c1.val ≤ c2.val) (hc2 : c2.val ≤ 100000), ∀ r1 r2 : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers c1
        = Result.ok r1 →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers c2
        = Result.ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r on (buses, passengers, capacity) and r' on (buses', passengers', capacity), then r' = r + d.
  Preconditions: Let n = len(buses) and m = len(passengers). Assume n >= 1, m >= 1, n <= 100000, m <= 100000, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for all i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for all j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. Let d be an integer with d >= 0 such that buses[i] + d <= 1000000000 for all i and passengers[j] + d <= 1000000000 for all j. Define buses'[i] = buses[i] + d and passengers'[j] = passengers[j] + d. -/
theorem spec_15 (buses passengers buses' passengers' : Slice I64) (capacity : I64)
    (d : ℤ)
    (hn : 1 ≤ buses.val.length) (hn' : buses.val.length ≤ 100000)
    (hm : 1 ≤ passengers.val.length) (hm' : passengers.val.length ≤ 100000)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hd : 0 ≤ d)
    (hb_shift : ∀ x ∈ buses.val, x.val + d ≤ 1000000000)
    (hp_shift : ∀ x ∈ passengers.val, x.val + d ≤ 1000000000)
    (hb' : elems buses' = (elems buses).map (fun v => v + d))
    (hp' : elems passengers' = (elems passengers).map (fun v => v + d)) :
    ∀ r r' : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses' passengers' capacity
        = Result.ok r' →
      r'.val = r.val + d := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (buses passengers buses' passengers' : Slice I64) (capacity : I64)
    (d : ℤ)
    (hn : 1 ≤ buses.val.length) (hn' : buses.val.length ≤ 100000)
    (hm : 1 ≤ passengers.val.length) (hm' : passengers.val.length ≤ 100000)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup)
    (hd : 0 ≤ d)
    (hb_shift : ∀ x ∈ buses.val, x.val + d ≤ 1000000000)
    (hp_shift : ∀ x ∈ passengers.val, x.val + d ≤ 1000000000)
    (hb' : elems buses' = (elems buses).map (fun v => v + d))
    (hp' : elems passengers' = (elems passengers).map (fun v => v + d)), ∀ r r' : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses' passengers' capacity
        = Result.ok r' →
      r'.val = r.val + d) := by
  sorry

/-- Whenever the function returns a result r, either r = max(buses), or there exists j with 0 <= j < len(passengers) such that r + 1 = passengers[j].
  Preconditions: Let n = len(buses) and m = len(passengers). The parameters satisfy the problem Constraints: n >= 1, m >= 1, 1 <= capacity <= 100000, 2 <= buses[i] <= 1000000000 for every i with 0 <= i < n, 2 <= passengers[j] <= 1000000000 for every j with 0 <= j < m, all elements of buses are pairwise distinct, and all elements of passengers are pairwise distinct. -/
theorem spec_16 (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup) :
    ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = B buses ∨ ∃ p ∈ elems passengers, r.val + 1 = p := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (buses passengers : Slice I64) (capacity : I64)
    (hn : 1 ≤ buses.val.length) (hm : 1 ≤ passengers.val.length)
    (hcap_pos : 1 ≤ capacity.val) (hcap_le : capacity.val ≤ 100000)
    (hb_lo : ∀ x ∈ buses.val, 2 ≤ x.val) (hb_hi : ∀ x ∈ buses.val, x.val ≤ 1000000000)
    (hp_lo : ∀ x ∈ passengers.val, 2 ≤ x.val)
    (hp_hi : ∀ x ∈ passengers.val, x.val ≤ 1000000000)
    (hb_nd : buses.val.Nodup) (hp_nd : passengers.val.Nodup), ∀ r : I64,
      Aegis.LatestTimeCatchTheBus.latest_time_catch_the_bus buses passengers capacity
        = Result.ok r →
      r.val = B buses ∨ ∃ p ∈ elems passengers, r.val + 1 = p) := by
  sorry

end AegisSpec.LatestTimeCatchTheBus
