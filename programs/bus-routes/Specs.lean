import Aegis.NumBusesToDestination.Code.Funs

/-!
# Specifications of `Aegis.NumBusesToDestination.num_buses_to_destination`

LeetCode problem `bus-routes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumBusesToDestination

def routesView (routes : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  routes.val.map (fun route => route.val.map (fun s => s.val))

def RoutesLenOk (routes : Slice (alloc.vec.Vec I64)) : Prop :=
  1 ≤ routes.val.length ∧ routes.val.length ≤ 500

def RoutesShapeOk (routes : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ route ∈ routes.val, 1 ≤ route.val.length ∧ route.val.length ≤ 100000 ∧ route.val.Nodup

def TotalStopsOk (routes : Slice (alloc.vec.Vec I64)) : Prop :=
  (routes.val.map (fun route => route.val.length)).sum ≤ 100000

def StopsInRange (routes : Slice (alloc.vec.Vec I64)) : Prop :=
  ∀ route ∈ routes.val, ∀ s ∈ route.val, 0 ≤ s.val ∧ s.val < 1000000

def EndpointsInRange (source target : I64) : Prop :=
  0 ≤ source.val ∧ source.val < 1000000 ∧ 0 ≤ target.val ∧ target.val < 1000000

def OccursIn (s : Int) (route : List Int) : Prop :=
  ∃ j : Nat, route[j]? = some s

def ShareStop (route₁ route₂ : List Int) : Prop :=
  ∃ s : Int, OccursIn s route₁ ∧ OccursIn s route₂

def ContainsBoth (source target : Int) (route : List Int) : Prop :=
  OccursIn source route ∧ OccursIn target route

def IsRouteIndexSeq (routes : List (List Int)) (chain : List Nat) : Prop :=
  ∀ i ∈ chain, i < routes.length

def ChainStartsAt (routes : List (List Int)) (source : Int) (chain : List Nat) : Prop :=
  ∃ i : Nat, chain.head? = some i ∧ OccursIn source (routes.getD i [])

def ChainEndsAt (routes : List (List Int)) (target : Int) (chain : List Nat) : Prop :=
  ∃ i : Nat, chain.getLast? = some i ∧ OccursIn target (routes.getD i [])

def ChainConsecutive (routes : List (List Int)) (chain : List Nat) : Prop :=
  ∀ (t i j : Nat),
    chain[t]? = some i → chain[t + 1]? = some j →
      ShareStop (routes.getD i []) (routes.getD j [])

def IsPositiveBusChain (routes : List (List Int)) (source target : Int) (k : Nat) : Prop :=
  0 < k ∧
    ∃ chain : List Nat,
      chain.length = k ∧
        IsRouteIndexSeq routes chain ∧
          ChainStartsAt routes source chain ∧
            ChainEndsAt routes target chain ∧ ChainConsecutive routes chain

def IsRouteChain (routes : List (List Int)) (source target : Int) (k : Nat) : Prop :=
  (k = 0 ∧ source = target) ∨ IsPositiveBusChain routes source target k

def IsLeastRouteChain (routes : List (List Int)) (source target : Int) (k : Nat) : Prop :=
  IsRouteChain routes source target k ∧ ∀ k' : Nat, IsRouteChain routes source target k' → k ≤ k'

/-- Under these preconditions, the function returns a result r and r is the least integer k >= 0 such that either (a) k = 0 and source = target, or (b) k >= 1 and there exist route indices i_0,...,i_{k-1} with 0 <= i_t < len(routes) for all t, source occurs in routes[i_0], target occurs in routes[i_{k-1}], and for every t with 0 <= t < k-1 there is a stop s that occurs in both routes[i_t] and routes[i_{t+1}]; here a stop s occurs in a route vector v if there is j with 0 <= j < len(v) and v[j] = s. If no such k exists, r = -1.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_1
    (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    ∃ r : I64,
      Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r ∧
        ((∃ k : Nat,
            IsLeastRouteChain (routesView routes) source.val target.val k ∧ r.val = (k : Int)) ∨
          ((∀ k : Nat, ¬ IsRouteChain (routesView routes) source.val target.val k) ∧
            r.val = -1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), ∃ r : I64,
      Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r ∧
        ((∃ k : Nat,
            IsLeastRouteChain (routesView routes) source.val target.val k ∧ r.val = (k : Int)) ∨
          ((∀ k : Nat, ¬ IsRouteChain (routesView routes) source.val target.val k) ∧
            r.val = -1))) := by
  sorry

/-- Under these preconditions, the function returns a result; it does not fail (no overflow, panic, out-of-bounds access, or Lean failure).
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_2
    (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    ∃ r : I64, Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), ∃ r : I64, Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r) := by
  sorry

/-- Under these preconditions, the function returns a result r and r = 0.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; 0 <= source < 1000000, 0 <= target < 1000000; and source = target. All values are interpreted as mathematical integers. -/
theorem spec_3
    (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) (h_same : source.val = target.val) :
    ∃ r : I64,
      Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r ∧
        r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) (h_same : source.val = target.val), ∃ r : I64,
      Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r ∧
        r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if r = 0 then source = target.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_4
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = 0 → source.val = target.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = 0 → source.val = target.val) := by
  sorry

/-- Whenever the function returns a result r, if source != target and there is an index i with 0 <= i < len(routes) such that both source and target occur in routes[i] (a stop s occurs in a route vector v if some entry of v equals s), then r = 1.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_5
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      source.val ≠ target.val →
        (∃ route : List Int,
            route ∈ routesView routes ∧ ContainsBoth source.val target.val route) →
          r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      source.val ≠ target.val →
        (∃ route : List Int,
            route ∈ routesView routes ∧ ContainsBoth source.val target.val route) →
          r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, r = -1.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; 0 <= source < 1000000, 0 <= target < 1000000; source != target; and for every i with 0 <= i < len(routes), source does not occur in routes[i]. All values are interpreted as mathematical integers. -/
theorem spec_6
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      source.val ≠ target.val →
        (∀ route : List Int, route ∈ routesView routes → ¬ OccursIn source.val route) →
          r.val = -1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      source.val ≠ target.val →
        (∀ route : List Int, route ∈ routesView routes → ¬ OccursIn source.val route) →
          r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, if r = -1 then source != target and there is no positive bus chain from source to target, where a positive bus chain of length k >= 1 is a sequence i_0,...,i_{k-1} of route indices with 0 <= i_t < len(routes) for all t, source occurs in routes[i_0], target occurs in routes[i_{k-1}], and for every t with 0 <= t < k-1 the routes routes[i_t] and routes[i_{t+1}] share a common stop (some stop occurs in both).
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_7
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 →
        source.val ≠ target.val ∧
          (∀ k : Nat,
            ¬ IsPositiveBusChain (routesView routes) source.val target.val k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 →
        source.val ≠ target.val ∧
          (∀ k : Nat,
            ¬ IsPositiveBusChain (routesView routes) source.val target.val k)) := by
  sorry

/-- Whenever the function returns a result r, if r >= 1 then there exists a positive bus chain from source to target of length r, where a positive bus chain of length r is a sequence i_0,...,i_{r-1} of route indices with 0 <= i_t < len(routes), source occurring in routes[i_0], target occurring in routes[i_{r-1}], and every consecutive pair of routes sharing a common stop.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_8
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      1 ≤ r.val →
        ∃ k : Nat,
          (k : Int) = r.val ∧
            IsPositiveBusChain (routesView routes) source.val target.val k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      1 ≤ r.val →
        ∃ k : Nat,
          (k : Int) = r.val ∧
            IsPositiveBusChain (routesView routes) source.val target.val k) := by
  sorry

/-- Whenever the function returns a result r, if r >= 1 then for every positive bus chain from source to target of length k (k >= 1, defined as a sequence of k route indices beginning with a route containing source, ending with a route containing target, and with each consecutive pair sharing a stop), r <= k.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_9
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      1 ≤ r.val →
        ∀ k : Nat,
          IsPositiveBusChain (routesView routes) source.val target.val k → r.val ≤ (k : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      1 ≤ r.val →
        ∀ k : Nat,
          IsPositiveBusChain (routesView routes) source.val target.val k → r.val ≤ (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r <= len(routes).
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; and 0 <= source < 1000000, 0 <= target < 1000000. All values are interpreted as mathematical integers. -/
theorem spec_10
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (routes.val.length : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (routes.val.length : Int))) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(routes).
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; 0 <= source < 1000000, 0 <= target < 1000000; and source != target. All values are interpreted as mathematical integers. -/
theorem spec_11
    (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) (h_diff : source.val ≠ target.val) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (routes.val.length : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (routes : Slice (alloc.vec.Vec I64)) (source target r : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_ends : EndpointsInRange source target) (h_diff : source.val ≠ target.val), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (routes.val.length : Int))) := by
  sorry

/-- Whenever num_buses_to_destination(routes, source, target) returns r and num_buses_to_destination(routes', source, target) returns r', we have r = r'.
  Preconditions: Assume: 1 <= len(routes) <= 500; for every i with 0 <= i < len(routes), 1 <= len(routes[i]) <= 100000 and the entries of routes[i] are pairwise distinct; sum_{i=0}^{len(routes)-1} len(routes[i]) <= 100000; for every i,j with 0 <= i < len(routes) and 0 <= j < len(routes[i]), 0 <= routes[i][j] < 1000000; 0 <= source < 1000000, 0 <= target < 1000000. Let routes' be any slice of vectors satisfying the same constraints and such that len(routes') = len(routes) and there is a bijection pi on {0,...,len(routes)-1} with routes'[i] = routes[pi(i)] for every i. All values are interpreted as mathematical integers. -/
theorem spec_12
    (routes routes' : Slice (alloc.vec.Vec I64)) (source target r r' : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_len' : RoutesLenOk routes') (h_shape' : RoutesShapeOk routes')
    (h_total' : TotalStopsOk routes') (h_range' : StopsInRange routes')
    (h_ends : EndpointsInRange source target)
    (h_same_len : (routesView routes').length = (routesView routes).length)
    (h_perm : ∃ π : Equiv.Perm (Fin (routesView routes).length),
      ∀ i : Fin (routesView routes).length,
        (routesView routes')[i.val]? = (routesView routes)[(π i).val]?) :
    Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      Aegis.NumBusesToDestination.num_buses_to_destination routes' source target = ok r' →
        r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (routes routes' : Slice (alloc.vec.Vec I64)) (source target r r' : I64)
    (h_len : RoutesLenOk routes) (h_shape : RoutesShapeOk routes)
    (h_total : TotalStopsOk routes) (h_range : StopsInRange routes)
    (h_len' : RoutesLenOk routes') (h_shape' : RoutesShapeOk routes')
    (h_total' : TotalStopsOk routes') (h_range' : StopsInRange routes')
    (h_ends : EndpointsInRange source target)
    (h_same_len : (routesView routes').length = (routesView routes).length)
    (h_perm : ∃ π : Equiv.Perm (Fin (routesView routes).length),
      ∀ i : Fin (routesView routes).length,
        (routesView routes')[i.val]? = (routesView routes)[(π i).val]?), Aegis.NumBusesToDestination.num_buses_to_destination routes source target = ok r →
      Aegis.NumBusesToDestination.num_buses_to_destination routes' source target = ok r' →
        r = r') := by
  sorry

end AegisSpec.NumBusesToDestination
