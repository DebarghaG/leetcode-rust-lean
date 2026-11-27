import Aegis.FindCriticalAndPseudoCriticalEdges.Code.Funs

/-!
# Specifications of `Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges`

LeetCode problem `find-critical-and-pseudo-critical-edges-in-minimum-spanning-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open scoped BigOperators

  namespace AegisSpec.FindCriticalAndPseudoCriticalEdges

  def edgeCoords (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def edgeRows (edges : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    edges.val.map edgeCoords

  def edgeLen (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    ((edgeRows edges).getD i []).length

  def edgeA (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    ((edgeRows edges).getD i []).getD 0 0

  def edgeB (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    ((edgeRows edges).getD i []).getD 1 0

  def edgeW (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ :=
    ((edgeRows edges).getD i []).getD 2 0

  def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) (u v : ℤ) : Prop :=
    ∃ i ∈ T,
      (edgeA edges i = u ∧ edgeB edges i = v) ∨ (edgeA edges i = v ∧ edgeB edges i = u)

  def Reach (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) (u v : ℤ) : Prop :=
    Relation.ReflTransGen (Adj edges T) u v

  def ConnectsAll (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) (n : ℤ) : Prop :=
    ∀ u v : ℤ, 0 ≤ u → u < n → 0 ≤ v → v < n → Reach edges T u v

  def ConsecutiveAdj (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) : List ℤ → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => Adj edges T x y ∧ ConsecutiveAdj edges T (y :: rest)

  def IsCycle (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) (c : List ℤ) : Prop :=
    3 ≤ c.length ∧ c.Nodup ∧ ConsecutiveAdj edges T (c ++ [c.getD 0 0])

  def Acyclic (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) : Prop :=
    ¬ ∃ c : List ℤ, IsCycle edges T c

  def IsSpanningTree (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (T : Finset ℕ) : Prop :=
    T ⊆ Finset.range m ∧ ConnectsAll edges T n ∧ Acyclic edges T

  def totalWeight (edges : Slice (alloc.vec.Vec Std.I64)) (T : Finset ℕ) : ℤ :=
    ∑ i ∈ T, edgeW edges i

  def IsMST (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (T : Finset ℕ) : Prop :=
    IsSpanningTree edges n m T ∧
      ∀ T', IsSpanningTree edges n m T' → totalWeight edges T ≤ totalWeight edges T'

  def IsMSTWeight (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (W : ℤ) : Prop :=
    ∃ T, IsMST edges n m T ∧ totalWeight edges T = W

  def IsMSTWithout (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (i : ℕ)
      (T : Finset ℕ) : Prop :=
    IsSpanningTree edges n m T ∧ i ∉ T ∧
      ∀ T', IsSpanningTree edges n m T' → i ∉ T' → totalWeight edges T ≤ totalWeight edges T'

  def IsMSTWeightWithout (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (i : ℕ)
      (W : ℤ) : Prop :=
    ∃ T, IsMSTWithout edges n m i T ∧ totalWeight edges T = W

  def InEveryMST (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (i : ℕ) : Prop :=
    ∀ T, IsMST edges n m T → i ∈ T

  def InSomeMST (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (i : ℕ) : Prop :=
    ∃ T, IsMST edges n m T ∧ i ∈ T

  def InSomeMSTOmitted (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (i : ℕ) : Prop :=
    ∃ T, IsMST edges n m T ∧ i ∉ T

  def InSomeButNotAllMST (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (i : ℕ) : Prop :=
    InSomeMST edges n m i ∧ InSomeMSTOmitted edges n m i

  def IsBridge (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ) (i : ℕ) : Prop :=
    ¬ ConnectsAll edges ((Finset.range m).erase i) n

  def DeletionKeepsConnected (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (i : ℕ) : Prop :=
    ConnectsAll edges ((Finset.range m).erase i) n

  def DeletionRaisesMSTWeight (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (i : ℕ) : Prop :=
    DeletionKeepsConnected edges n m i ∧
      ∃ W₀ W₁ : ℤ,
        IsMSTWeight edges n m W₀ ∧ IsMSTWeightWithout edges n m i W₁ ∧ W₀ < W₁

  def DeletionKeepsMSTWeight (edges : Slice (alloc.vec.Vec Std.I64)) (n : ℤ) (m : ℕ)
      (i : ℕ) : Prop :=
    DeletionKeepsConnected edges n m i ∧
      ∃ W₀ W₁ : ℤ,
        IsMSTWeight edges n m W₀ ∧ IsMSTWeightWithout edges n m i W₁ ∧ W₀ = W₁

  def outVec (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (k : ℕ) : List ℤ :=
    edgeCoords (r.val.getD k (alloc.vec.Vec.new Std.I64))

  def Occurs (l : List ℤ) (i : ℕ) : Prop := (i : ℤ) ∈ l

  def AllValidIndices (m : ℕ) (l : List ℤ) : Prop := ∀ x ∈ l, 0 ≤ x ∧ x < (m : ℤ)

  def Pre (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) : Prop :=
    2 ≤ n.val ∧
    n.val ≤ 100 ∧
    edges.val.length = m ∧
    1 ≤ m ∧
    m ≤ 200 ∧
    (m : ℤ) ≤ n.val * (n.val - 1) / 2 ∧
    (∀ i, i < m → edgeLen edges i = 3) ∧
    (∀ i, i < m →
      0 ≤ edgeA edges i ∧ edgeA edges i < edgeB edges i ∧ edgeB edges i < n.val ∧
        1 ≤ edgeW edges i ∧ edgeW edges i ≤ 1000) ∧
    (∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      ({edgeA edges i, edgeB edges i} : Finset ℤ) = {edgeA edges j, edgeB edges j} → i = j) ∧
    ConnectsAll edges (Finset.range m) n.val

  /-- Whenever the function returns a result r, len(r)=2. The first component r[0] contains exactly, with no repetitions and in arbitrary order, those edge indices i with 0 <= i < m that belong to every minimum spanning tree of G. The second component r[1] contains exactly, with no repetitions and in arbitrary order, those edge indices i with 0 <= i < m for which there exists a minimum spanning tree of G containing i and there also exists a minimum spanning tree of G not containing i. No other integers occur in either component. Here a minimum spanning tree means a subset T of the edge indices forming a connected acyclic spanning subgraph of G whose total weight sum_{i in T} w_i is minimal.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      (∀ i, i < m → (Occurs (outVec r 0) i ↔ InEveryMST edges n.val m i)) ∧
      (∀ i, i < m → (Occurs (outVec r 1) i ↔ InSomeButNotAllMST edges n.val m i)) ∧
      AllValidIndices m (outVec r 0) ∧
      AllValidIndices m (outVec r 1) ∧
      (outVec r 0).Nodup ∧
      (outVec r 1).Nodup := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), (∀ i, i < m → (Occurs (outVec r 0) i ↔ InEveryMST edges n.val m i)) ∧
        (∀ i, i < m → (Occurs (outVec r 1) i ↔ InSomeButNotAllMST edges n.val m i)) ∧
        AllValidIndices m (outVec r 0) ∧
        AllValidIndices m (outVec r 1) ∧
        (outVec r 0).Nodup ∧
        (outVec r 1).Nodup) := by
    sorry

  /-- The function returns a result r and does not fail, panic, or overflow on every input satisfying the preconditions.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) :
      ∃ r, Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m), ∃ r, Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the outer vector has exactly two components: len(r)=2.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r) :
      r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r), r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every element of the first component is a valid edge index: for every j with 0 <= j < len(r[0]), 0 <= r[0][j] < m.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ (j : ℕ) (hj : j < (outVec r 0).length),
        0 ≤ (outVec r 0).get ⟨j, hj⟩ ∧ (outVec r 0).get ⟨j, hj⟩ < (m : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ (j : ℕ) (hj : j < (outVec r 0).length),
          0 ≤ (outVec r 0).get ⟨j, hj⟩ ∧ (outVec r 0).get ⟨j, hj⟩ < (m : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every element of the second component is a valid edge index: for every j with 0 <= j < len(r[1]), 0 <= r[1][j] < m.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ (j : ℕ) (hj : j < (outVec r 1).length),
        0 ≤ (outVec r 1).get ⟨j, hj⟩ ∧ (outVec r 1).get ⟨j, hj⟩ < (m : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ (j : ℕ) (hj : j < (outVec r 1).length),
          0 ≤ (outVec r 1).get ⟨j, hj⟩ ∧ (outVec r 1).get ⟨j, hj⟩ < (m : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, the first component contains no repeated edge index: for all j,k with 0 <= j < k < len(r[0]), r[0][j] != r[0][k].
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ (j k : ℕ) (hj : j < (outVec r 0).length) (hk : k < (outVec r 0).length),
        j < k → (outVec r 0).get ⟨j, hj⟩ ≠ (outVec r 0).get ⟨k, hk⟩ := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ (j k : ℕ) (hj : j < (outVec r 0).length) (hk : k < (outVec r 0).length),
          j < k → (outVec r 0).get ⟨j, hj⟩ ≠ (outVec r 0).get ⟨k, hk⟩) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, the second component contains no repeated edge index: for all j,k with 0 <= j < k < len(r[1]), r[1][j] != r[1][k].
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ (j k : ℕ) (hj : j < (outVec r 1).length) (hk : k < (outVec r 1).length),
        j < k → (outVec r 1).get ⟨j, hj⟩ ≠ (outVec r 1).get ⟨k, hk⟩ := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ (j k : ℕ) (hj : j < (outVec r 1).length) (hk : k < (outVec r 1).length),
          j < k → (outVec r 1).get ⟨j, hj⟩ ≠ (outVec r 1).get ⟨k, hk⟩) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, the two components are disjoint: there is no integer i such that i occurs in r[0] and i also occurs in r[1].
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ x : ℤ, ¬ (x ∈ outVec r 0 ∧ x ∈ outVec r 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ x : ℤ, ¬ (x ∈ outVec r 0 ∧ x ∈ outVec r 1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every edge that belongs to every minimum spanning tree of G is included in r[0]: for every edge index i with 0 <= i < m, if every minimum spanning tree contains i, then i occurs in r[0].
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m → InEveryMST edges n.val m i → Occurs (outVec r 0) i := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m → InEveryMST edges n.val m i → Occurs (outVec r 0) i) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every edge listed in r[0] belongs to every minimum spanning tree of G: for every edge index i with 0 <= i < m, if i occurs in r[0], then every minimum spanning tree contains i.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m → Occurs (outVec r 0) i → InEveryMST edges n.val m i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m → Occurs (outVec r 0) i → InEveryMST edges n.val m i) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every edge that appears in some but not all minimum spanning trees of G is included in r[1]: for every edge index i with 0 <= i < m, if there exists a minimum spanning tree containing i and there exists a minimum spanning tree not containing i, then i occurs in r[1].
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m → InSomeButNotAllMST edges n.val m i → Occurs (outVec r 1) i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m → InSomeButNotAllMST edges n.val m i → Occurs (outVec r 1) i) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, every edge listed in r[1] has an MST containing it and an MST omitting it: for every edge index i with 0 <= i < m, if i occurs in r[1], then there exists a minimum spanning tree of G containing i and there exists a minimum spanning tree of G not containing i.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m → Occurs (outVec r 1) i → InSomeButNotAllMST edges n.val m i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m → Occurs (outVec r 1) i → InSomeButNotAllMST edges n.val m i) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, for every edge index i with 0 <= i < m, i occurs in r[0] or i occurs in r[1] if and only if there exists a minimum spanning tree of G containing i.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_13 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m →
        (Occurs (outVec r 0) i ∨ Occurs (outVec r 1) i ↔ InSomeMST edges n.val m i) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m →
          (Occurs (outVec r 0) i ∨ Occurs (outVec r 1) i ↔ InSomeMST edges n.val m i)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, for every edge index i with 0 <= i < m, i occurs in r[0] if and only if deleting edge i from G either disconnects G or leaves a connected graph whose minimum spanning-tree total weight is strictly greater than the minimum spanning-tree total weight of G.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_14 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m →
        (Occurs (outVec r 0) i ↔
          IsBridge edges n.val m i ∨ DeletionRaisesMSTWeight edges n.val m i) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m →
          (Occurs (outVec r 0) i ↔
            IsBridge edges n.val m i ∨ DeletionRaisesMSTWeight edges n.val m i)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, for every edge index i with 0 <= i < m, i occurs in r[1] if and only if there exists a minimum spanning tree of G containing i and the graph obtained by deleting edge i from G is connected and has minimum spanning-tree total weight equal to that of G.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_15 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2) :
      ∀ i, i < m →
        (Occurs (outVec r 1) i ↔
          InSomeMST edges n.val m i ∧ DeletionKeepsMSTWeight edges n.val m i) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2), ∀ i, i < m →
          (Occurs (outVec r 1) i ↔
            InSomeMST edges n.val m i ∧ DeletionKeepsMSTWeight edges n.val m i)) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, if all edge weights w_i are equal to one another, then for every edge index i with 0 <= i < m: i occurs in r[0] if and only if edge i is a bridge of G, and i occurs in r[1] if and only if edge i is not a bridge of G.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_16 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2)
      (heq : ∀ i j, i < m → j < m → edgeW edges i = edgeW edges j) :
      ∀ i, i < m →
        ((Occurs (outVec r 0) i ↔ IsBridge edges n.val m i) ∧
          (Occurs (outVec r 1) i ↔ ¬ IsBridge edges n.val m i)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2)
        (heq : ∀ i j, i < m → j < m → edgeW edges i = edgeW edges j), ∀ i, i < m →
          ((Occurs (outVec r 0) i ↔ IsBridge edges n.val m i) ∧
            (Occurs (outVec r 1) i ↔ ¬ IsBridge edges n.val m i))) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, if m = n-1, then the first component contains exactly all edge indices 0 through m-1, with no repetitions and in arbitrary order, and the second component is empty.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_17 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2)
      (hm : (m : ℤ) = n.val - 1) :
      (∀ i, i < m → Occurs (outVec r 0) i) ∧
      AllValidIndices m (outVec r 0) ∧
      (outVec r 0).Nodup ∧
      outVec r 1 = [] := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2)
        (hm : (m : ℤ) = n.val - 1), (∀ i, i < m → Occurs (outVec r 0) i) ∧
        AllValidIndices m (outVec r 0) ∧
        (outVec r 0).Nodup ∧
        outVec r 1 = []) := by
    sorry

  /-- Whenever the function returns a result r with len(r)=2, if G has exactly one minimum spanning tree T, where T is a set of edge indices, then r[0] contains exactly the elements of T, with no repetitions and in arbitrary order, and r[1] is empty.
    Preconditions: n is an integer with 2 <= n <= 100; edges has length m with 1 <= m <= min(200, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3, and, writing a_i=edges[i][0], b_i=edges[i][1], w_i=edges[i][2], we have 0 <= a_i < b_i < n and 1 <= w_i <= 1000; all unordered pairs {a_i,b_i} are distinct; the undirected graph G on vertices {0,...,n-1} with edge i joining a_i and b_i is connected. -/
  theorem spec_18 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
      (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
        n edges = ok r)
      (hlen : r.val.length = 2)
      (huniq : ∃ T, IsMST edges n.val m T ∧ ∀ T', IsMST edges n.val m T' → T' = T) :
      ∀ T, IsMST edges n.val m T →
        (∀ i, i < m → (Occurs (outVec r 0) i ↔ i ∈ T)) ∧
        AllValidIndices m (outVec r 0) ∧
        (outVec r 0).Nodup ∧
        outVec r 1 = [] := by
    sorry

  theorem spec_18_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
        (hpre : Pre n edges m) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hres : Aegis.FindCriticalAndPseudoCriticalEdges.find_critical_and_pseudo_critical_edges
          n edges = ok r)
        (hlen : r.val.length = 2)
        (huniq : ∃ T, IsMST edges n.val m T ∧ ∀ T', IsMST edges n.val m T' → T' = T), ∀ T, IsMST edges n.val m T →
          (∀ i, i < m → (Occurs (outVec r 0) i ↔ i ∈ T)) ∧
          AllValidIndices m (outVec r 0) ∧
          (outVec r 0).Nodup ∧
          outVec r 1 = []) := by
    sorry

  end AegisSpec.FindCriticalAndPseudoCriticalEdges
