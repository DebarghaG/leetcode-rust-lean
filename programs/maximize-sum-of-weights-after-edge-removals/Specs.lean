import Aegis.MaximizeSumOfWeights.Code.Funs

/-!
# Specifications of `Aegis.MaximizeSumOfWeights.maximize_sum_of_weights`

LeetCode problem `maximize-sum-of-weights-after-edge-removals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.MaximizeSumOfWeights

  namespace AegisSpec.MaximizeSumOfWeights

  def edgeRow (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
    match edges.val[i]? with
    | none => []
    | some e => e.val.map (fun x => x.val)

  def edgeVal (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    (edgeRow edges i)[j]?.getD 0

  def incident (edges : Slice (alloc.vec.Vec Std.I64)) (i v : Nat) : Prop :=
    edgeVal edges i 0 = (v : Int) ∨ edgeVal edges i 1 = (v : Int)

  def incidentEdges (edges : Slice (alloc.vec.Vec Std.I64)) (m v : Nat) : Finset Nat :=
    (Finset.range m).filter
      (fun i => edgeVal edges i 0 = (v : Int) ∨ edgeVal edges i 1 = (v : Int))

  def degree (edges : Slice (alloc.vec.Vec Std.I64)) (m v : Nat) : Nat :=
    (incidentEdges edges m v).card

  def maxDegree (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Nat :=
    (Finset.range (m + 1)).sup (fun v => degree edges m v)

  def totalWeight (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Int :=
    (Finset.range m).sum (fun i => edgeVal edges i 2)

  def setWeight (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset Nat) : Int :=
    S.sum (fun i => edgeVal edges i 2)

  def Feasible (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) (k : Int)
      (S : Finset Nat) : Prop :=
    S ⊆ Finset.range m ∧
      ∀ v : Nat, v ≤ m → ((incidentEdges edges m v ∩ S).card : Int) ≤ k

  def IsMatching (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) (S : Finset Nat) : Prop :=
    S ⊆ Finset.range m ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ v : Nat, ¬ (incident edges i v ∧ incident edges j v)

  def Endpoints (edges : Slice (alloc.vec.Vec Std.I64)) (i u v : Nat) : Prop :=
    (edgeVal edges i 0 = (u : Int) ∧ edgeVal edges i 1 = (v : Int)) ∨
      (edgeVal edges i 0 = (v : Int) ∧ edgeVal edges i 1 = (u : Int))

  def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (m u v : Nat) : Prop :=
    ∃ i, i < m ∧ Endpoints edges i u v

  def AdjRemove (edges : Slice (alloc.vec.Vec Std.I64)) (m i0 u v : Nat) : Prop :=
    ∃ i, i < m ∧ i ≠ i0 ∧ Endpoints edges i u v

  def Connected (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Prop :=
    ∀ u v : Nat, u ≤ m → v ≤ m → Relation.ReflTransGen (Adj edges m) u v

  def ConnectedRemove (edges : Slice (alloc.vec.Vec Std.I64)) (m i0 : Nat) : Prop :=
    ∀ u v : Nat, u ≤ m → v ≤ m → Relation.ReflTransGen (AdjRemove edges m i0) u v

  def IsTree (edges : Slice (alloc.vec.Vec Std.I64)) (m : Nat) : Prop :=
    Connected edges m ∧ ∀ i0, i0 < m → ¬ ConnectedRemove edges m i0

  def incidentWeights (edges : Slice (alloc.vec.Vec Std.I64)) (m v : Nat) : List Int :=
    ((List.range m).filter
        (fun i => edgeVal edges i 0 == (v : Int) || edgeVal edges i 1 == (v : Int))).map
      (fun i => edgeVal edges i 2)

  def sumTopList (l : List Int) (t : Nat) : Int :=
    ((List.insertionSort (fun x y : Int => x ≥ y) l).take t).sum

  def starTopSum (edges : Slice (alloc.vec.Vec Std.I64)) (m v : Nat) (t : Nat) : Int :=
    sumTopList (incidentWeights edges m v) (min t (degree edges m v))

  /-- The function returns a result r and r is the maximum possible sum of weights of a set of remaining edges: (1) for every subset S of {0,...,m-1} such that for every v in {0,...,m}, #{i in S : a_i = v or b_i = v} <= k, we have sum_{i in S} c_i <= r; and (2) there exists such a subset S with sum_{i in S} c_i = r.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∃ r : Std.I64,
        maximize_sum_of_weights edges k = ok r ∧
          (∀ S : Finset Nat,
            Feasible edges edges.val.length k.val S → setWeight edges S ≤ r.val) ∧
          (∃ S : Finset Nat,
            Feasible edges edges.val.length k.val S ∧ setWeight edges S = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∃ r : Std.I64,
          maximize_sum_of_weights edges k = ok r ∧
            (∀ S : Finset Nat,
              Feasible edges edges.val.length k.val S → setWeight edges S ≤ r.val) ∧
            (∃ S : Finset Nat,
              Feasible edges edges.val.length k.val S ∧ setWeight edges S = r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or return an error on any input satisfying these preconditions.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∃ r : Std.I64, maximize_sum_of_weights edges k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∃ r : Std.I64, maximize_sum_of_weights edges k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{m-1} c_i, the sum of all input edge weights.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∀ r : Std.I64,
        maximize_sum_of_weights edges k = ok r → r.val ≤ totalWeight edges edges.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∀ r : Std.I64,
          maximize_sum_of_weights edges k = ok r → r.val ≤ totalWeight edges edges.val.length) := by
    sorry

  /-- Whenever the function returns a result r, r >= max { c_i : 0 <= i < m }.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
        ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
          ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S of {0,...,m-1} such that for every v in {0,...,m}, #{i in S : a_i = v or b_i = v} <= k, and sum_{i in S} c_i = r.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
        ∃ S : Finset Nat, Feasible edges edges.val.length k.val S ∧
          setWeight edges S = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
          ∃ S : Finset Nat, Feasible edges edges.val.length k.val S ∧
            setWeight edges S = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every subset S of {0,...,m-1} such that for every v in {0,...,m}, #{i in S : a_i = v or b_i = v} <= k, we have sum_{i in S} c_i <= r.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
        ∀ S : Finset Nat, Feasible edges edges.val.length k.val S → setWeight edges S ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
          ∀ S : Finset Nat, Feasible edges edges.val.length k.val S → setWeight edges S ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{m-1} c_i.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Let D = max_{v in {0,...,m}} #{i : 0 <= i < m and (a_i = v or b_i = v)}. Assume 1 <= k <= m and k >= D. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
      (hk_D : (maxDegree edges edges.val.length : Int) ≤ k.val) :
      ∀ r : Std.I64,
        maximize_sum_of_weights edges k = ok r → r.val = totalWeight edges edges.val.length := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
        (hk_D : (maxDegree edges edges.val.length : Int) ≤ k.val), ∀ r : Std.I64,
          maximize_sum_of_weights edges k = ok r → r.val = totalWeight edges edges.val.length) := by
    sorry

  /-- Whenever the function returns a result r, r is the maximum total weight of a matching in the input tree: r = max { sum_{i in S} c_i : S subset of {0,...,m-1} and for all distinct i,j in S, the edges {a_i,b_i} and {a_j,b_j} have no common endpoint }.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume k = 1; since m >= 1, this implies 1 <= k <= m. -/
  theorem spec_8 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk : k.val = 1) :
      ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
        (∀ S : Finset Nat, IsMatching edges edges.val.length S → setWeight edges S ≤ r.val) ∧
          (∃ S : Finset Nat,
            IsMatching edges edges.val.length S ∧ setWeight edges S = r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk : k.val = 1), ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
          (∀ S : Finset Nat, IsMatching edges edges.val.length S → setWeight edges S ≤ r.val) ∧
            (∃ S : Finset Nat,
              IsMatching edges edges.val.length S ∧ setWeight edges S = r.val)) := by
    sorry

  /-- Let r1 be the result of the function on (edges,k1) and r2 the result on (edges,k2). Whenever both calls return results, r1 <= r2.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Let k1 and k2 be integers with 1 <= k1 <= k2 <= m. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2_le : k2.val ≤ (edges.val.length : Int)) :
      ∀ r1 r2 : Std.I64,
        maximize_sum_of_weights edges k1 = ok r1 →
          maximize_sum_of_weights edges k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk1_pos : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2_le : k2.val ≤ (edges.val.length : Int)), ∀ r1 r2 : Std.I64,
          maximize_sum_of_weights edges k1 = ok r1 →
            maximize_sum_of_weights edges k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r on (edges,k) and r' on (edges',k), we have r = r'.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. Let pi be any permutation of {0,...,m-1}, and define edges' by len(edges') = m and edges'[i] = edges[pi(i)] for 0 <= i < m. -/
  theorem spec_10 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
      (h_perm : edges'.val.Perm edges.val) :
      ∀ r r' : Std.I64,
        maximize_sum_of_weights edges k = ok r →
          maximize_sum_of_weights edges' k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
        (h_perm : edges'.val.Perm edges.val), ∀ r r' : Std.I64,
          maximize_sum_of_weights edges k = ok r →
            maximize_sum_of_weights edges' k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r on (edges,k) and r' on (edges',k), we have r <= r'.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. Choose j with 0 <= j < m and an integer c'_j with c_j <= c'_j <= 10^6. Define edges' by len(edges') = m, edges'[i] = edges[i] for i != j, and edges'[j] = [a_j, b_j, c'_j]. -/
  theorem spec_11 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
      (h_len' : edges'.val.length = edges.val.length)
      (j : Nat) (hj : j < edges.val.length) (c' : Int)
      (hc'_lo : edgeVal edges j 2 ≤ c') (hc'_hi : c' ≤ 10 ^ 6)
      (h_row_j : edgeRow edges' j = [edgeVal edges j 0, edgeVal edges j 1, c'])
      (h_rows' : ∀ i, i < edges.val.length → i ≠ j → edgeRow edges' i = edgeRow edges i) :
      ∀ r r' : Std.I64,
        maximize_sum_of_weights edges k = ok r →
          maximize_sum_of_weights edges' k = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int))
        (h_len' : edges'.val.length = edges.val.length)
        (j : Nat) (hj : j < edges.val.length) (c' : Int)
        (hc'_lo : edgeVal edges j 2 ≤ c') (hc'_hi : c' ≤ 10 ^ 6)
        (h_row_j : edgeRow edges' j = [edgeVal edges j 0, edgeVal edges j 1, c'])
        (h_rows' : ∀ i, i < edges.val.length → i ≠ j → edgeRow edges' i = edgeRow edges i), ∀ r r' : Std.I64,
          maximize_sum_of_weights edges k = ok r →
            maximize_sum_of_weights edges' k = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns a result r, for every v in {0,...,m}, let I_v = {i : 0 <= i < m and (a_i = v or b_i = v)}. If d_v = #I_v and T_v is the sum of the min(k,d_v) largest values of c_i over i in I_v, then r >= T_v.
    Preconditions: Let m = len(edges). Assume 1 <= m <= 10^5 - 1. For every i with 0 <= i < m, edges[i] has length 3; write a_i = edges[i][0], b_i = edges[i][1], c_i = edges[i][2]. Assume 0 <= a_i <= m, 0 <= b_i <= m, a_i != b_i, and 1 <= c_i <= 10^6. Assume the simple undirected graph with vertex set {0,...,m} and edge set {{a_i,b_i} : 0 <= i < m} is a tree. Assume 1 <= k <= m. -/
  theorem spec_12 (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
      (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
      (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
      (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
      (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
      (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
      (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
      (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
      (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
      (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
      (h_tree : IsTree edges edges.val.length)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)) :
      ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
        ∀ v : Nat, v ≤ edges.val.length →
          starTopSum edges edges.val.length v k.val.toNat ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
        (hm_pos : 1 ≤ edges.val.length) (hm_le : edges.val.length ≤ 10 ^ 5 - 1)
        (h_rows : ∀ i, i < edges.val.length → (edgeRow edges i).length = 3)
        (h_a_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 0)
        (h_a_hi : ∀ i, i < edges.val.length → edgeVal edges i 0 ≤ (edges.val.length : Int))
        (h_b_lo : ∀ i, i < edges.val.length → 0 ≤ edgeVal edges i 1)
        (h_b_hi : ∀ i, i < edges.val.length → edgeVal edges i 1 ≤ (edges.val.length : Int))
        (h_ab : ∀ i, i < edges.val.length → edgeVal edges i 0 ≠ edgeVal edges i 1)
        (h_c_lo : ∀ i, i < edges.val.length → 1 ≤ edgeVal edges i 2)
        (h_c_hi : ∀ i, i < edges.val.length → edgeVal edges i 2 ≤ 10 ^ 6)
        (h_tree : IsTree edges edges.val.length)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (edges.val.length : Int)), ∀ r : Std.I64, maximize_sum_of_weights edges k = ok r →
          ∀ v : Nat, v ≤ edges.val.length →
            starTopSum edges edges.val.length v k.val.toNat ≤ r.val) := by
    sorry

  end AegisSpec.MaximizeSumOfWeights
