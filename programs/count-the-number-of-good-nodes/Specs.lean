import Aegis.CountGoodNodes.Code.Funs

/-!
# Specifications of `Aegis.CountGoodNodes.count_good_nodes`

LeetCode problem `count-the-number-of-good-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountGoodNodes

  namespace AegisSpec.CountGoodNodes

  abbrev Edge : Type := Int × Int

  noncomputable def vertexSet (n : Nat) : Finset Int :=
    (Finset.range n).image (fun k : Nat => (k : Int))

  def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List Edge :=
    edges.val.map fun row =>
      match row.val with
      | [a, b] => (a.val, b.val)
      | _ => (0, 0)

  def adj (E : List Edge) (u v : Int) : Prop := (u, v) ∈ E ∨ (v, u) ∈ E

  def isWalk (E : List Edge) (p : List Int) : Prop :=
    p ≠ [] ∧ ∀ q ∈ p.zip p.tail, adj E q.1 q.2

  def reach (E : List Edge) (u v : Int) : Prop :=
    ∃ p : List Int, isWalk E p ∧ p.head? = some u ∧ p.getLast? = some v

  def connected (E : List Edge) (n : Nat) : Prop :=
    ∀ v : Int, 0 ≤ v → v < (n : Int) → reach E 0 v

  def acyclic (E : List Edge) : Prop :=
    ∀ (u : Int) (p : List Int), isWalk E p → p.head? = some u → p.getLast? = some u →
      p.length = 1

  def isTree (E : List Edge) (n : Nat) : Prop := connected E n ∧ acyclic E

  def dist (E : List Edge) (v : Int) (d : Nat) : Prop :=
    (∃ p : List Int, p.length = d + 1 ∧ isWalk E p ∧ p.head? = some 0 ∧
        p.getLast? = some v) ∧
    ∀ d' : Nat, d' < d → ¬ ∃ p : List Int, p.length = d' + 1 ∧ isWalk E p ∧
      p.head? = some 0 ∧ p.getLast? = some v

  def parentOf (E : List Edge) (v u : Int) : Prop :=
    u ≠ v ∧ adj E u v ∧ ∃ d : Nat, 1 ≤ d ∧ dist E v d ∧ dist E u (d - 1)

  noncomputable def children (E : List Edge) (n : Nat) (u : Int) : Finset Int := by
    classical
    exact (vertexSet n).filter fun c => parentOf E c u

  def inSubtree (E : List Edge) (u w : Int) : Prop :=
    ∀ p : List Int, isWalk E p → p.head? = some 0 → p.getLast? = some w → u ∈ p

  noncomputable def subtree (E : List Edge) (n : Nat) (u : Int) : Finset Int := by
    classical
    exact (vertexSet n).filter fun w => inSubtree E u w

  noncomputable def subtreeSize (E : List Edge) (n : Nat) (u : Int) : Nat :=
    (subtree E n u).card

  def isGood (E : List Edge) (n : Nat) (u : Int) : Prop :=
    ∀ c1 ∈ children E n u, ∀ c2 ∈ children E n u, subtreeSize E n c1 = subtreeSize E n c2

  noncomputable def goodCount (E : List Edge) (n : Nat) : Nat := by
    classical
    exact ((vertexSet n).filter fun u => isGood E n u).card

  noncomputable def atMostOneChildCount (E : List Edge) (n : Nat) : Nat := by
    classical
    exact ((vertexSet n).filter fun u => (children E n u).card ≤ 1).card

  def perfectBinary (E : List Edge) (n : Nat) : Prop :=
    (∀ u : Int, 0 ≤ u → u < (n : Int) →
        (children E n u).card = 0 ∨ (children E n u).card = 2) ∧
      ∃ d : Nat, ∀ v : Int, 0 ≤ v → v < (n : Int) → ((children E n v).card = 0 ↔ dist E v d)

  def isStar (E : List Edge) (n : Nat) : Prop :=
    ∃ s : Int, 0 ≤ s ∧ s < (n : Int) ∧
      ∀ v : Int, 0 ≤ v → v < (n : Int) → v ≠ s → adj E s v

  def isPermOn (m : Nat) (pi : Nat → Nat) : Prop :=
    (∀ i : Nat, i < m → pi i < m) ∧
      (∀ i : Nat, i < m → ∀ j : Nat, j < m → pi i = pi j → i = j) ∧
      (∀ i : Nat, i < m → ∃ j : Nat, j < m ∧ pi j = i)

  def IsTreeInput (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    n = edges.val.length + 1 ∧
      2 ≤ n ∧
      n ≤ 100000 ∧
      (∀ row ∈ edges.val, row.val.length = 2) ∧
      (∀ p ∈ edgeList edges,
        0 ≤ p.1 ∧ p.1 < (n : Int) ∧ 0 ≤ p.2 ∧ p.2 < (n : Int) ∧ p.1 ≠ p.2) ∧
      isTree (edgeList edges) n

  /-- Whenever count_good_nodes(edges) returns a result r, r equals the number of good nodes, defined as follows. Two vertices u,v are adjacent if some edge has endpoints u and v in either order. Because the graph is a tree rooted at 0, for each vertex v != 0 there is a unique neighbor parent(v) on the unique simple path from 0 to v; children(u) = {v : parent(v)=u}. For any vertex u, subtree(u) is the set of vertices w whose unique simple path from 0 to w contains u, and size(u) = card(subtree(u)). A vertex u is good iff for all c1,c2 in children(u), size(c1)=size(c2); equivalently, u has at most one child, or all its children have the same subtree size.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 100000; for every i with 0 <= i < len(edges), len(edges[i]) = 2; writing edges[i] = [a_i,b_i] as integers, 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; the undirected graph with vertex set {0,...,n-1} and edge set {{a_i,b_i} : 0 <= i < len(edges)} is a tree (connected and acyclic). -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (r : Std.I64) (hr : count_good_nodes edges = ok r) :
      r.val = (goodCount (edgeList edges) n : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (r : Std.I64) (hr : count_good_nodes edges = ok r), r.val = (goodCount (edgeList edges) n : ℤ)) := by
    sorry

  /-- count_good_nodes(edges) returns a result r; that is, the Result is not a failure: no overflow, out-of-bounds access, or panic occurs.
    Preconditions: Let n = len(edges)+1. The input satisfies: 2 <= n <= 100000; for every i with 0 <= i < len(edges), len(edges[i]) = 2; writing edges[i] = [a_i,b_i] as integers, 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; the undirected graph with vertex set {0,...,n-1} and edge set {{a_i,b_i} : 0 <= i < len(edges)} is a tree (connected and acyclic). -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n) :
      ∃ r : Std.I64, count_good_nodes edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n), ∃ r : Std.I64, count_good_nodes edges = ok r) := by
    sorry

  /-- Whenever count_good_nodes(edges) returns a result r, 0 <= r <= n, where n = len(edges)+1.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (r : Std.I64) (hr : count_good_nodes edges = ok r) :
      0 ≤ r.val ∧ r.val ≤ (n : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (r : Std.I64) (hr : count_good_nodes edges = ok r), 0 ≤ r.val ∧ r.val ≤ (n : ℤ)) := by
    sorry

  /-- Whenever count_good_nodes(edges) returns a result r, r >= M, where M is the number of vertices u with 0 <= u < n that have at most one child in the tree rooted at 0, with children defined via unique paths from 0 as in spec_1.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (r : Std.I64) (hr : count_good_nodes edges = ok r) :
      (atMostOneChildCount (edgeList edges) n : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (r : Std.I64) (hr : count_good_nodes edges = ok r), (atMostOneChildCount (edgeList edges) n : ℤ) ≤ r.val) := by
    sorry

  /-- If there exists a vertex s with 0 <= s < n such that every other vertex v != s is adjacent to s in the underlying unrooted tree (i.e. the tree is a star, possibly with center s not equal to 0), then whenever count_good_nodes(edges) returns a result r, r = n.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (hstar : isStar (edgeList edges) n) (r : Std.I64) (hr : count_good_nodes edges = ok r) :
      r.val = (n : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (hstar : isStar (edgeList edges) n) (r : Std.I64) (hr : count_good_nodes edges = ok r), r.val = (n : ℤ)) := by
    sorry

  /-- If every vertex u with 0 <= u < n has at most one child in the tree rooted at 0, then whenever count_good_nodes(edges) returns a result r, r = n.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (hmono : ∀ u : ℤ, 0 ≤ u → u < (n : ℤ) → (children (edgeList edges) n u).card ≤ 1)
      (r : Std.I64) (hr : count_good_nodes edges = ok r) :
      r.val = (n : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (hmono : ∀ u : ℤ, 0 ≤ u → u < (n : ℤ) → (children (edgeList edges) n u).card ≤ 1)
        (r : Std.I64) (hr : count_good_nodes edges = ok r), r.val = (n : ℤ)) := by
    sorry

  /-- If the tree rooted at 0 is perfect binary, meaning every vertex has either 0 or 2 children and all leaves have the same depth from root 0 (depth is the number of edges on the unique path from 0), then whenever count_good_nodes(edges) returns a result r, r = n.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (hperfect : perfectBinary (edgeList edges) n) (r : Std.I64)
      (hr : count_good_nodes edges = ok r) :
      r.val = (n : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (hperfect : perfectBinary (edgeList edges) n) (r : Std.I64)
        (hr : count_good_nodes edges = ok r), r.val = (n : ℤ)) := by
    sorry

  /-- Whenever count_good_nodes(edges) returns r and count_good_nodes(edges') returns r', we have r = r'.
    Preconditions: Let n = len(edges)+1. edges satisfies the same tree preconditions as spec_1. Let edges' be another list satisfying the same problem constraints for the same n and such that there is a bijection pi on {0,...,len(edges)-1} with edges'[i] = edges[pi(i)] for every i (the same ordered pairs, only reordered). -/
  theorem spec_8 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hinput : IsTreeInput edges n) (hinput' : IsTreeInput edges' n)
      (hperm : ∃ pi : Nat → Nat,
        isPermOn edges.val.length pi ∧
          ∀ i : Nat, i < edges'.val.length →
            (edgeList edges')[i]? = (edgeList edges)[pi i]?)
      (r r' : Std.I64) (hr : count_good_nodes edges = ok r)
      (hr' : count_good_nodes edges' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hinput : IsTreeInput edges n) (hinput' : IsTreeInput edges' n)
        (hperm : ∃ pi : Nat → Nat,
          isPermOn edges.val.length pi ∧
            ∀ i : Nat, i < edges'.val.length →
              (edgeList edges')[i]? = (edgeList edges)[pi i]?)
        (r r' : Std.I64) (hr : count_good_nodes edges = ok r)
        (hr' : count_good_nodes edges' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever count_good_nodes(edges) returns r, if M is the number of vertices u with 0 <= u < n that have at most one child in the tree rooted at 0, and r > M, then there exists a vertex u with at least two children such that all children of u have the same subtree size (so u is a good vertex with at least two children).
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (r : Std.I64) (hr : count_good_nodes edges = ok r)
      (hgt : (atMostOneChildCount (edgeList edges) n : ℤ) < r.val) :
      ∃ u : ℤ, 0 ≤ u ∧ u < (n : ℤ) ∧ 2 ≤ (children (edgeList edges) n u).card ∧
        isGood (edgeList edges) n u := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (r : Std.I64) (hr : count_good_nodes edges = ok r)
        (hgt : (atMostOneChildCount (edgeList edges) n : ℤ) < r.val), ∃ u : ℤ, 0 ≤ u ∧ u < (n : ℤ) ∧ 2 ≤ (children (edgeList edges) n u).card ∧
          isGood (edgeList edges) n u) := by
    sorry

  /-- Whenever count_good_nodes(edges) returns r, if r < n then there exists a vertex u with at least two children c1 and c2 such that size(c1) != size(c2), where size is the subtree size in the tree rooted at 0 as defined in spec_1.
    Preconditions: Let n = len(edges)+1. The input satisfies the same tree preconditions as spec_1. -/
  theorem spec_10 (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
      (r : Std.I64) (hr : count_good_nodes edges = ok r) (hlt : r.val < (n : ℤ)) :
      ∃ u : ℤ, 0 ≤ u ∧ u < (n : ℤ) ∧
        ∃ c1 ∈ children (edgeList edges) n u, ∃ c2 ∈ children (edgeList edges) n u,
          subtreeSize (edgeList edges) n c1 ≠ subtreeSize (edgeList edges) n c2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (hinput : IsTreeInput edges n)
        (r : Std.I64) (hr : count_good_nodes edges = ok r) (hlt : r.val < (n : ℤ)), ∃ u : ℤ, 0 ≤ u ∧ u < (n : ℤ) ∧
          ∃ c1 ∈ children (edgeList edges) n u, ∃ c2 ∈ children (edgeList edges) n u,
            subtreeSize (edgeList edges) n c1 ≠ subtreeSize (edgeList edges) n c2) := by
    sorry

  end AegisSpec.CountGoodNodes
