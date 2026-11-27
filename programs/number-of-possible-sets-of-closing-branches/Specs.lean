import Aegis.NumberOfSets.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSets.number_of_sets`

LeetCode problem `number-of-possible-sets-of-closing-branches`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Classical

  namespace AegisSpec.NumberOfSets

  def roadTriples (roads : Slice (alloc.vec.Vec I64)) : List (Int × Int × Int) :=
    roads.val.filterMap fun r =>
      match r.val with
      | [a, b, c] => some (a.val, b.val, c.val)
      | _ => none

  def IsRoad (roads : Slice (alloc.vec.Vec I64)) (u v w : Int) : Prop :=
    ∃ e ∈ roadTriples roads, ({e.1, e.2.1} : Finset Int) = {u, v} ∧ e.2.2 = w

  structure Walk (roads : Slice (alloc.vec.Vec I64)) (u v : Int) where

    k : Nat

    p : Nat → Int

    w : Nat → Int

    start : p 0 = u

    finish : p k = v

    edge : ∀ j, j < k → IsRoad roads (p j) (p (j + 1)) (w j)

  namespace Walk

  variable {roads : Slice (alloc.vec.Vec I64)} {u v : Int}

  def Inside (W : Walk roads u v) (A : Finset Int) : Prop := ∀ j, j ≤ W.k → W.p j ∈ A

  def weight (W : Walk roads u v) : Int := ∑ j ∈ Finset.range W.k, W.w j

  end Walk

  def ReachWithin (roads : Slice (alloc.vec.Vec I64)) (A : Finset Int) (D u v : Int) : Prop :=
    ∃ W : Walk roads u v, W.Inside A ∧ W.weight ≤ D

  def Reachable (roads : Slice (alloc.vec.Vec I64)) (A : Finset Int) (u v : Int) : Prop :=
    ∃ W : Walk roads u v, W.Inside A

  def AllVerts (n : I64) : Finset Int :=
    (Finset.range n.val.toNat).image (fun k : Nat => (k : Int))

  def closedToActive (n : I64) (S : Finset Int) : Finset Int := AllVerts n \ S

  def ValidClosed (n : I64) (roads : Slice (alloc.vec.Vec I64)) (D : Int)
      (S : Finset Int) : Prop :=
    S ⊆ AllVerts n ∧
      ∀ u ∈ closedToActive n S, ∀ v ∈ closedToActive n S,
        ReachWithin roads (closedToActive n S) D u v

  noncomputable def countValid (n : I64) (roads : Slice (alloc.vec.Vec I64)) (D : Int) : Nat :=
    ((AllVerts n).powerset.filter fun S => ValidClosed n roads D S).card

  def ActiveConnected (n : I64) (roads : Slice (alloc.vec.Vec I64)) (A : Finset Int) : Prop :=
    A ⊆ AllVerts n ∧ ∀ u ∈ A, ∀ v ∈ A, Reachable roads A u v

  noncomputable def countActiveConnected (n : I64) (roads : Slice (alloc.vec.Vec I64)) : Nat :=
    ((AllVerts n).powerset.filter fun A => ActiveConnected n roads A).card

  def totalRoadLength (roads : Slice (alloc.vec.Vec I64)) : Int :=
    (roadTriples roads).foldl (fun acc e => acc + e.2.2) 0

  def minRoadLength (roads : Slice (alloc.vec.Vec I64)) : Int :=
    match (roadTriples roads).map fun e => e.2.2 with
    | [] => 0
    | w :: ws => ws.foldl (fun acc x => if x < acc then x else acc) w

  def Constraints (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 10 ∧
    1 ≤ maxDistance.val ∧ maxDistance.val ≤ 100000 ∧
    roads.val.length ≤ 1000 ∧
    (∀ (i : Nat) (h : i < roads.val.length), ∃ a b c : I64,
      (roads.val.get ⟨i, h⟩).val = [a, b, c] ∧
      0 ≤ a.val ∧ a.val ≤ n.val - 1 ∧
      0 ≤ b.val ∧ b.val ≤ n.val - 1 ∧
      a.val ≠ b.val ∧
      1 ≤ c.val ∧ c.val ≤ 1000) ∧
    (∀ u ∈ AllVerts n, ∀ v ∈ AllVerts n, Reachable roads (AllVerts n) u v)

  /-- The function returns a result r, and r is exactly the number of subsets S of {0,...,n-1} for which the following holds. Put A = {0,...,n-1} \ S. For every u,v in A there exist k >= 0 and vertices p_0,...,p_k such that p_0 = u, p_k = v, every p_j is in A, and for each j = 0,...,k-1 there is a road index t_j with {roads[t_j][0], roads[t_j][1]} = {p_j, p_{j+1}}; moreover the sum over j = 0,...,k-1 of roads[t_j][2] is at most maxDistance. For u = v, k = 0 is allowed. In words, after closing exactly S, every two remaining branches are connected by a route of total length at most maxDistance using only remaining branches, with empty and one-element active sets valid vacuously. The quantification is over all subsets S, including S = {} and S = {0,...,n-1}; each subset contributes to r exactly when the displayed condition holds.
    Preconditions: The input satisfies the problem constraints: 1 <= n <= 10; 1 <= maxDistance <= 100000; 0 <= len(roads) <= 1000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are in [0,n-1], roads[i][0] != roads[i][1], and 1 <= roads[i][2] <= 1000; and the undirected graph on {0,...,n-1} whose edges are the road entries is connected. -/
  theorem spec_1 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        r.val = (countValid n roads maxDistance.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          r.val = (countValid n roads maxDistance.val : Int)) := by
    sorry

  /-- For every input satisfying these preconditions, the function returns a result r; it does not return Err, panic, overflow, or access roads out of bounds.
    Preconditions: The input satisfies the problem constraints: 1 <= n <= 10; 1 <= maxDistance <= 100000; len(roads) <= 1000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are in [0,n-1], roads[i][0] != roads[i][1], and 1 <= roads[i][2] <= 1000; and the undirected graph on {0,...,n-1} whose edges are the road entries is connected. -/
  theorem spec_2 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 2^n; in particular, since n <= 10, 0 <= r <= 1024.
    Preconditions: The input satisfies the problem constraints: 1 <= n <= 10; 1 <= maxDistance <= 100000; len(roads) <= 1000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are in [0,n-1], roads[i][0] != roads[i][1], and 1 <= roads[i][2] <= 1000; and the undirected graph on {0,...,n-1} whose edges are the road entries is connected. -/
  theorem spec_3 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) :
      ∀ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r →
        0 ≤ r.val ∧ r.val ≤ 2 ^ n.val.toNat ∧ r.val ≤ 1024 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads), ∀ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r →
          0 ≤ r.val ∧ r.val ≤ 2 ^ n.val.toNat ∧ r.val ≤ 1024) := by
    sorry

  /-- The function returns r and r >= n+1. Indeed, all subsets S with active set {0,...,n-1} \ S of size 0 or 1 are valid, and there are exactly n+1 such subsets.
    Preconditions: The input satisfies the problem constraints: 1 <= n <= 10; 1 <= maxDistance <= 100000; len(roads) <= 1000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are in [0,n-1], roads[i][0] != roads[i][1], and 1 <= roads[i][2] <= 1000; and the undirected graph on {0,...,n-1} whose edges are the road entries is connected. -/
  theorem spec_4 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        n.val + 1 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          n.val + 1 ≤ r.val) := by
    sorry

  /-- The function returns 2.
    Preconditions: The input satisfies the problem constraints and n = 1. -/
  theorem spec_5 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) (hn : n.val = 1) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads) (hn : n.val = 1), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧ r.val = 2) := by
    sorry

  /-- The function returns r, and r = 4 if m <= maxDistance, while r = 3 if m > maxDistance.
    Preconditions: The input satisfies the problem constraints and n = 2. Let m = min{roads[i][2] | 0 <= i < len(roads)}. Since n = 2 and the graph is connected, this minimum is over a nonempty set and every road joins 0 and 1. -/
  theorem spec_6 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) (hn : n.val = 2) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        (minRoadLength roads ≤ maxDistance.val → r.val = 4) ∧
        (maxDistance.val < minRoadLength roads → r.val = 3) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads) (hn : n.val = 2), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          (minRoadLength roads ≤ maxDistance.val → r.val = 4) ∧
          (maxDistance.val < minRoadLength roads → r.val = 3)) := by
    sorry

  /-- The function returns r, and the empty closed set S = {} is counted among the sets defining r if and only if, in the original graph using all branches, for every u,v in {0,...,n-1} there is a path from u to v of total length at most maxDistance. Equivalently, the diameter of the original road graph is at most maxDistance.
    Preconditions: The input satisfies the problem constraints: 1 <= n <= 10; 1 <= maxDistance <= 100000; len(roads) <= 1000; for every i with 0 <= i < len(roads), roads[i] has length 3, roads[i][0] and roads[i][1] are in [0,n-1], roads[i][0] != roads[i][1], and 1 <= roads[i][2] <= 1000; and the undirected graph on {0,...,n-1} whose edges are the road entries is connected. -/
  theorem spec_7 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        r.val = (countValid n roads maxDistance.val : Int) ∧
        (ValidClosed n roads maxDistance.val ∅ ↔
          ∀ u ∈ AllVerts n, ∀ v ∈ AllVerts n,
            ReachWithin roads (AllVerts n) maxDistance.val u v) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          r.val = (countValid n roads maxDistance.val : Int) ∧
          (ValidClosed n roads maxDistance.val ∅ ↔
            ∀ u ∈ AllVerts n, ∀ v ∈ AllVerts n,
              ReachWithin roads (AllVerts n) maxDistance.val u v)) := by
    sorry

  /-- The function returns r1 and r2, and r1 <= r2.
    Preconditions: Fix n and roads satisfying the structural and connectivity constraints for n. Let D1 and D2 be integers with 1 <= D1 <= D2 <= 100000. Let r1 and r2 be the results of the function on (n,D1,roads) and (n,D2,roads), respectively. -/
  theorem spec_8 (n d1 d2 : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc1 : Constraints n d1 roads) (hc2 : Constraints n d2 roads)
      (hd : d1.val ≤ d2.val) :
      ∃ r1 r2 : I64, Aegis.NumberOfSets.number_of_sets n d1 roads = ok r1 ∧
        Aegis.NumberOfSets.number_of_sets n d2 roads = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n d1 d2 : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc1 : Constraints n d1 roads) (hc2 : Constraints n d2 roads)
        (hd : d1.val ≤ d2.val), ∃ r1 r2 : I64, Aegis.NumberOfSets.number_of_sets n d1 roads = ok r1 ∧
          Aegis.NumberOfSets.number_of_sets n d2 roads = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- The function returns r1 and r2, and r1 = r2.
    Preconditions: Fix n and maxDistance satisfying the constraints. Let roads1 and roads2 be two road lists satisfying the constraints for n, such that roads2 is a permutation (reordering) of roads1, including multiplicities. Let r1 and r2 be the results on (n,maxDistance,roads1) and (n,maxDistance,roads2). -/
  theorem spec_9 (n maxDistance : I64) (roads1 roads2 : Slice (alloc.vec.Vec I64))
      (hc1 : Constraints n maxDistance roads1) (hc2 : Constraints n maxDistance roads2)
      (hperm : List.Perm roads1.val roads2.val) :
      ∃ r1 r2 : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads1 = ok r1 ∧
        Aegis.NumberOfSets.number_of_sets n maxDistance roads2 = ok r2 ∧ r1.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n maxDistance : I64) (roads1 roads2 : Slice (alloc.vec.Vec I64))
        (hc1 : Constraints n maxDistance roads1) (hc2 : Constraints n maxDistance roads2)
        (hperm : List.Perm roads1.val roads2.val), ∃ r1 r2 : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads1 = ok r1 ∧
          Aegis.NumberOfSets.number_of_sets n maxDistance roads2 = ok r2 ∧ r1.val = r2.val) := by
    sorry

  /-- The function returns r and r = n+1.
    Preconditions: The input satisfies the problem constraints, and for every i with 0 <= i < len(roads), roads[i][2] > maxDistance. -/
  theorem spec_10 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads)
      (hlong : ∀ e ∈ roadTriples roads, maxDistance.val < e.2.2) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        r.val = n.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads)
        (hlong : ∀ e ∈ roadTriples roads, maxDistance.val < e.2.2), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          r.val = n.val + 1) := by
    sorry

  /-- The function returns r, and r equals the number of subsets A of {0,...,n-1} such that for every u,v in A there is a path from u to v whose intermediate vertices all lie in A. Equivalently, r is the number of active sets A whose induced subgraph is connected in the path sense, with the empty set and singleton sets counted as connected vacuously. The corresponding closed set is S = {0,...,n-1} \ A.
    Preconditions: The input satisfies the problem constraints. Let W be the sum of roads[i][2] over all 0 <= i < len(roads). Assume maxDistance >= W. -/
  theorem spec_11 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads)
      (hD : totalRoadLength roads ≤ maxDistance.val) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        r.val = (countActiveConnected n roads : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads)
        (hD : totalRoadLength roads ≤ maxDistance.val), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          r.val = (countActiveConnected n roads : Int)) := by
    sorry

  /-- The function returns r and r = 2^n.
    Preconditions: The input satisfies the problem constraints, and for every pair of distinct vertices u,v with 0 <= u < v < n there exists a road index i such that {roads[i][0], roads[i][1]} = {u,v} and roads[i][2] <= maxDistance. -/
  theorem spec_12 (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
      (hc : Constraints n maxDistance roads)
      (hpair : ∀ u ∈ AllVerts n, ∀ v ∈ AllVerts n, u ≠ v →
        ∃ w : Int, w ≤ maxDistance.val ∧ IsRoad roads u v w) :
      ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
        r.val = 2 ^ n.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n maxDistance : I64) (roads : Slice (alloc.vec.Vec I64))
        (hc : Constraints n maxDistance roads)
        (hpair : ∀ u ∈ AllVerts n, ∀ v ∈ AllVerts n, u ≠ v →
          ∃ w : Int, w ≤ maxDistance.val ∧ IsRoad roads u v w), ∃ r : I64, Aegis.NumberOfSets.number_of_sets n maxDistance roads = ok r ∧
          r.val = 2 ^ n.val.toNat) := by
    sorry

  end AegisSpec.NumberOfSets
