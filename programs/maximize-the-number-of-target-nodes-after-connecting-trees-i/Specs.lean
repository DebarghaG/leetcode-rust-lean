import Aegis.MaxTargetNodes.Code.Funs

/-!
# Specifications of `Aegis.MaxTargetNodes.max_target_nodes`

LeetCode problem `maximize-the-number-of-target-nodes-after-connecting-trees-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxTargetNodes

def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  edges.val.map (fun v => v.val.map (fun x => x.val))

def nodeCount (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := edges.val.length + 1

def isEdge (es : List (List Int)) (u v : Int) : Prop :=
  ∃ a b : Int, [a, b] ∈ es ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

def isWalk (es : List (List Int)) : List Int → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => isEdge es u v ∧ isWalk es (v :: rest)

def walkTo (es : List (List Int)) (u v : Int) (d : Nat) : Prop :=
  ∃ p : List Int, p.length = d + 1 ∧ p.head? = some u ∧ p.getLast? = some v ∧
    isWalk es p

def distRel (es : List (List Int)) (u v : Int) (d : Nat) : Prop :=
  walkTo es u v d ∧ ∀ d' : Nat, d' < d → ¬ walkTo es u v d'

def distAtMost (es : List (List Int)) (u v : Int) (k : Int) : Prop :=
  ∃ d : Nat, distRel es u v d ∧ (d : Int) ≤ k

def isCycle (es : List (List Int)) (u : Int) (p : List Int) : Prop :=
  2 ≤ p.length ∧ p.Nodup ∧ u ∉ p ∧ isWalk es (u :: (p ++ [u]))

def isTreeOn (n : Nat) (es : List (List Int)) : Prop :=
  (∀ e ∈ es, ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < (n : Int) ∧ 0 ≤ b ∧ b < (n : Int)) ∧
  (∀ u v : Int, 0 ≤ u → u < (n : Int) → 0 ≤ v → v < (n : Int) →
    ∃ d : Nat, walkTo es u v d) ∧
  (∀ (u : Int) (p : List Int), isCycle es u p → False)

section Counts

open Classical

noncomputable def C1 (n : Nat) (es : List (List Int)) (k : Int) (i : Nat) : Int :=
  ((((List.range n).filter
      (fun j => if distAtMost es (i : Int) (j : Int) k then true else false)).length : Nat) : Int)

noncomputable def C2 (m : Nat) (es : List (List Int)) (k : Int) (j : Nat) : Int :=
  ((((List.range m).filter
      (fun u => if ∃ d : Nat, distRel es (j : Int) (u : Int) d ∧ (d : Int) + 1 ≤ k
        then true else false)).length : Nat) : Int)

end Counts

noncomputable def M (m : Nat) (es : List (List Int)) (k : Int) : Int :=
  ((List.range m).map (fun j => C2 m es k j)).foldr max 0

def coversAll (m : Nat) (es : List (List Int)) (k : Int) (j : Nat) : Prop :=
  ∀ u : Nat, u < m → ∃ d : Nat, distRel es (j : Int) (u : Int) d ∧ (d : Int) + 1 ≤ k

structure ValidTrees (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) : Prop where

  n_lower : 2 ≤ nodeCount edges1

  n_upper : nodeCount edges1 ≤ 1000

  m_lower : 2 ≤ nodeCount edges2

  m_upper : nodeCount edges2 ≤ 1000

  tree1 : isTreeOn (nodeCount edges1) (edgeList edges1)

  tree2 : isTreeOn (nodeCount edges2) (edgeList edges2)

structure ValidInput (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) : Prop where

  trees : ValidTrees edges1 edges2

  k_nonneg : 0 ≤ k.val

  k_upper : k.val ≤ 1000

def swapEnds (e e' : List Int) : Prop := e' = e ∨ e'.reverse = e

def edgeListsRel (es es' : List (List Int)) : Prop :=
  ∃ l : List (List Int), l.Perm es ∧ List.Forall₂ swapEnds l es'

/-- The function returns a result r with len(r) = n, and for every i with 0 <= i < n, r[i] = C1(i) + M.
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. For a tree T and nodes u, v of T, dist_T(u, v) denotes the number of edges on the unique simple path from u to v in T. Let T1 be the first tree and T2 the second tree. Define C1(i) = #{v : 0 <= v < n and dist_T1(i, v) <= k} for 0 <= i < n, C2(j) = #{u : 0 <= u < m and dist_T2(j, u) + 1 <= k} for 0 <= j < m, and M = max({0} ∪ {C2(j) : 0 <= j < m}). -/
theorem spec_1
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r ∧
      r.val.length = nodeCount edges1 ∧
      ∀ i : Nat, i < nodeCount edges1 →
        (r.val[i]!).val =
          C1 (nodeCount edges1) (edgeList edges1) k.val i +
            M (nodeCount edges2) (edgeList edges2) k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r ∧
      r.val.length = nodeCount edges1 ∧
      ∀ i : Nat, i < nodeCount edges1 →
        (r.val[i]!).val =
          C1 (nodeCount edges1) (edgeList edges1) k.val i +
            M (nodeCount edges2) (edgeList edges2) k.val) := by
  sorry

/-- The function returns a result r with len(r) = n = len(edges1) + 1.
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. -/
theorem spec_2
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r ∧
      r.val.length = nodeCount edges1 ∧
      nodeCount edges1 = edges1.val.length + 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r ∧
      r.val.length = nodeCount edges1 ∧
      nodeCount edges1 = edges1.val.length + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, C1(i) <= r[i] <= C1(i) + m.
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. For a tree T and nodes u, v of T, dist_T(u, v) denotes the number of edges on the unique simple path from u to v in T. Let T1 be the first tree. Define C1(i) = #{v : 0 <= v < n and dist_T1(i, v) <= k} for 0 <= i < n. -/
theorem spec_3
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∀ i : Nat, i < nodeCount edges1 →
        C1 (nodeCount edges1) (edgeList edges1) k.val i ≤ (r.val[i]!).val ∧
          (r.val[i]!).val ≤
            C1 (nodeCount edges1) (edgeList edges1) k.val i + (nodeCount edges2 : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∀ i : Nat, i < nodeCount edges1 →
        C1 (nodeCount edges1) (edgeList edges1) k.val i ≤ (r.val[i]!).val ∧
          (r.val[i]!).val ≤
            C1 (nodeCount edges1) (edgeList edges1) k.val i + (nodeCount edges2 : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n and every j with 0 <= j < m, r[i] >= C1(i) + C2(j).
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. For a tree T and nodes u, v of T, dist_T(u, v) denotes the number of edges on the unique simple path from u to v in T. Let T1 be the first tree and T2 the second tree. Define C1(i) = #{v : 0 <= v < n and dist_T1(i, v) <= k} for 0 <= i < n and C2(j) = #{u : 0 <= u < m and dist_T2(j, u) + 1 <= k} for 0 <= j < m. -/
theorem spec_4
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∀ i : Nat, i < nodeCount edges1 → ∀ j : Nat, j < nodeCount edges2 →
        C1 (nodeCount edges1) (edgeList edges1) k.val i +
            C2 (nodeCount edges2) (edgeList edges2) k.val j ≤ (r.val[i]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∀ i : Nat, i < nodeCount edges1 → ∀ j : Nat, j < nodeCount edges2 →
        C1 (nodeCount edges1) (edgeList edges1) k.val i +
            C2 (nodeCount edges2) (edgeList edges2) k.val j ≤ (r.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, there exists j* with 0 <= j* < m such that for every i with 0 <= i < n, r[i] = C1(i) + C2(j*).
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. For a tree T and nodes u, v of T, dist_T(u, v) denotes the number of edges on the unique simple path from u to v in T. Let T1 be the first tree and T2 the second tree. Define C1(i) = #{v : 0 <= v < n and dist_T1(i, v) <= k} for 0 <= i < n and C2(j) = #{u : 0 <= u < m and dist_T2(j, u) + 1 <= k} for 0 <= j < m. -/
theorem spec_5
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∃ j : Nat, j < nodeCount edges2 ∧
        ∀ i : Nat, i < nodeCount edges1 →
          (r.val[i]!).val =
            C1 (nodeCount edges1) (edgeList edges1) k.val i +
              C2 (nodeCount edges2) (edgeList edges2) k.val j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      ∃ j : Nat, j < nodeCount edges2 ∧
        ∀ i : Nat, i < nodeCount edges1 →
          (r.val[i]!).val =
            C1 (nodeCount edges1) (edgeList edges1) k.val i +
              C2 (nodeCount edges2) (edgeList edges2) k.val j) := by
  sorry

/-- Whenever the function returns a result r, if k >= 1 and there exists j0 with 0 <= j0 < m such that for every u with 0 <= u < m, dist_T2(j0, u) + 1 <= k, then for every i with 0 <= i < n, r[i] = C1(i) + m.
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. For a tree T and nodes u, v of T, dist_T(u, v) denotes the number of edges on the unique simple path from u to v in T. Let T1 be the first tree and T2 the second tree. Define C1(i) = #{v : 0 <= v < n and dist_T1(i, v) <= k} for 0 <= i < n. -/
theorem spec_6
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      1 ≤ k.val →
      (∃ j0 : Nat, j0 < nodeCount edges2 ∧
        coversAll (nodeCount edges2) (edgeList edges2) k.val j0) →
      ∀ i : Nat, i < nodeCount edges1 →
        (r.val[i]!).val =
          C1 (nodeCount edges1) (edgeList edges1) k.val i + (nodeCount edges2 : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      1 ≤ k.val →
      (∃ j0 : Nat, j0 < nodeCount edges2 ∧
        coversAll (nodeCount edges2) (edgeList edges2) k.val j0) →
      ∀ i : Nat, i < nodeCount edges1 →
        (r.val[i]!).val =
          C1 (nodeCount edges1) (edgeList edges1) k.val i + (nodeCount edges2 : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or access out of bounds).
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. For each i with 0 <= i < len(edges1), len(edges1[i]) = 2; writing edges1[i] = [a_i, b_i], we have 0 <= a_i, b_i < n, and the undirected graph on node set {0,...,n-1} with edge set {{a_i, b_i} : 0 <= i < len(edges1)} is a tree. For each i with 0 <= i < len(edges2), len(edges2[i]) = 2; writing edges2[i] = [c_i, d_i], we have 0 <= c_i, d_i < m, and the undirected graph on node set {0,...,m-1} with edge set {{c_i, d_i} : 0 <= i < len(edges2)} is a tree. k is an integer with 0 <= k <= 1000. -/
theorem spec_7
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (h : ValidInput edges1 edges2 k), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r) := by
  sorry

/-- Let r1 be the result of the function on (edges1, edges2, k1) and r2 the result on (edges1, edges2, k2). Whenever both calls return results, len(r1) = len(r2) = n and for every i with 0 <= i < n, r1[i] <= r2[i].
  Preconditions: Let n = len(edges1) + 1 and m = len(edges2) + 1, so 2 <= n, m <= 1000. edges1 is a list of n-1 pairs of integers in [0,n) forming a tree on {0,...,n-1}; edges2 is a list of m-1 pairs of integers in [0,m) forming a tree on {0,...,m-1}. k1 and k2 are integers with 0 <= k1 <= k2 <= 1000. -/
theorem spec_8
    (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (htrees : ValidTrees edges1 edges2)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000) :
    ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k1 = ok r1 →
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k2 = ok r2 →
      r1.val.length = nodeCount edges1 ∧
        r2.val.length = nodeCount edges1 ∧
        ∀ i : Nat, i < nodeCount edges1 → (r1.val[i]!).val ≤ (r2.val[i]!).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges1 edges2 : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (htrees : ValidTrees edges1 edges2)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000), ∀ r1 r2 : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k1 = ok r1 →
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k2 = ok r2 →
      r1.val.length = nodeCount edges1 ∧
        r2.val.length = nodeCount edges1 ∧
        ∀ i : Nat, i < nodeCount edges1 → (r1.val[i]!).val ≤ (r2.val[i]!).val) := by
  sorry

/-- Let r be the result of the function on (edges1, edges2, k) and r' the result on (edges1', edges2', k). Whenever both calls return results, len(r) = len(r') and for every i with 0 <= i < len(r), r[i] = r'[i].
  Preconditions: edges1 and edges2 are valid tree edge lists as in the problem statement: with n = len(edges1)+1, m = len(edges2)+1, edges1 consists of n-1 pairs of integers in [0,n) forming a tree on {0,...,n-1}, and edges2 consists of m-1 pairs of integers in [0,m) forming a tree on {0,...,m-1}. edges1' is obtained from edges1 by permuting its elements and optionally swapping the two entries of some elements; edges2' is obtained from edges2 similarly. k is an integer with 0 <= k <= 1000. -/
theorem spec_9
    (edges1 edges2 edges1' edges2' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (htrees : ValidTrees edges1 edges2)
    (h1 : edgeListsRel (edgeList edges1) (edgeList edges1'))
    (h2 : edgeListsRel (edgeList edges2) (edgeList edges2'))
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000) :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      Aegis.MaxTargetNodes.max_target_nodes edges1' edges2' k = ok r' →
      r.val.length = r'.val.length ∧
        ∀ i : Nat, i < r.val.length → (r.val[i]!).val = (r'.val[i]!).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges1 edges2 edges1' edges2' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (htrees : ValidTrees edges1 edges2)
    (h1 : edgeListsRel (edgeList edges1) (edgeList edges1'))
    (h2 : edgeListsRel (edgeList edges2) (edgeList edges2'))
    (hk : 0 ≤ k.val ∧ k.val ≤ 1000), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.MaxTargetNodes.max_target_nodes edges1 edges2 k = ok r →
      Aegis.MaxTargetNodes.max_target_nodes edges1' edges2' k = ok r' →
      r.val.length = r'.val.length ∧
        ∀ i : Nat, i < r.val.length → (r.val[i]!).val = (r'.val[i]!).val) := by
  sorry

end AegisSpec.MaxTargetNodes
