import Aegis.FindSmallestSetOfVertices.Code.Funs

/-!
# Specifications of `Aegis.FindSmallestSetOfVertices.find_smallest_set_of_vertices`

LeetCode problem `minimum-number-of-vertices-to-reach-all-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindSmallestSetOfVertices (find_smallest_set_of_vertices)

  namespace AegisSpec.FindSmallestSetOfVertices

  def valuesList (l : List Std.I64) : List Int :=
    l.map (fun x => x.val)

  def edgeRows (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    edges.val.map (fun row => valuesList row.val)

  def occursIn (r : List Std.I64) (v : Int) : Prop :=
    v ∈ valuesList r

  def HasEdge (edges : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
    ∃ row ∈ edgeRows edges, row = [a, b]

  inductive Reach (edges : Slice (alloc.vec.Vec Std.I64)) : Int → Int → Prop where
    | refl (v : Int) : Reach edges v v
    | step {a b t : Int} : HasEdge edges a b → Reach edges b t → Reach edges a t

  def HasCycle (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ a b : Int, HasEdge edges a b ∧ Reach edges b a

  def Acyclic (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ¬ HasCycle edges

  /-- The function returns a result r such that, for every vertex v with 0 <= v < n, v occurs in r if and only if there is no index i with 0 <= i < len(edges) and edges[i][1] = v; furthermore, every element of r lies in [0,n) and no vertex occurs more than once in r.
    Preconditions: 2 <= n <= 100000; 1 <= len(edges) <= min(100000, n*(n-1)/2); for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, and 0 <= edges[i][1] < n; all ordered pairs (edges[i][0], edges[i][1]) are distinct; and the directed graph on vertices 0,1,...,n-1 with these directed edges is acyclic. -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
      (h_edges_lower : 1 ≤ edges.val.length)
      (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
      (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
      (h_src_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
      (h_src_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_tgt_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
      (h_tgt_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_distinct : (edgeRows edges).Nodup)
      (h_acyclic : Acyclic edges) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_smallest_set_of_vertices n edges = ok r ∧
          (∀ v : Int, 0 ≤ v → v < n.val →
            (occursIn r.val v ↔
              ¬ ∃ i : Nat, ∃ _hi : i < edges.val.length,
                ((edges.val[i]).val[1]'(by have h2 := h_len i _hi; omega)).val = v)) ∧
          (∀ v : Int, v ∈ valuesList r.val → 0 ≤ v ∧ v < n.val) ∧
          (valuesList r.val).Nodup := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
        (h_edges_lower : 1 ≤ edges.val.length)
        (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
        (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
        (h_src_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
        (h_src_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_tgt_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
        (h_tgt_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_distinct : (edgeRows edges).Nodup)
        (h_acyclic : Acyclic edges), ∃ r : alloc.vec.Vec Std.I64,
          find_smallest_set_of_vertices n edges = ok r ∧
            (∀ v : Int, 0 ≤ v → v < n.val →
              (occursIn r.val v ↔
                ¬ ∃ i : Nat, ∃ _hi : i < edges.val.length,
                  ((edges.val[i]).val[1]'(by have h2 := h_len i _hi; omega)).val = v)) ∧
            (∀ v : Int, v ∈ valuesList r.val → 0 ≤ v ∧ v < n.val) ∧
            (valuesList r.val).Nodup) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: 2 <= n <= 100000; 1 <= len(edges) <= min(100000, n*(n-1)/2); for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, and 0 <= edges[i][1] < n; all ordered pairs (edges[i][0], edges[i][1]) are distinct; and the directed graph on vertices 0,1,...,n-1 with these directed edges is acyclic. -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
      (h_edges_lower : 1 ≤ edges.val.length)
      (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
      (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
      (h_src_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
      (h_src_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_tgt_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
      (h_tgt_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_distinct : (edgeRows edges).Nodup)
      (h_acyclic : Acyclic edges) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_smallest_set_of_vertices n edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
        (h_edges_lower : 1 ≤ edges.val.length)
        (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
        (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
        (h_src_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
        (h_src_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_tgt_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
        (h_tgt_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_distinct : (edgeRows edges).Nodup)
        (h_acyclic : Acyclic edges), ∃ r : alloc.vec.Vec Std.I64,
          find_smallest_set_of_vertices n edges = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every vertex v with 0 <= v < n, there exists j with 0 <= j < len(r) such that v is reachable from r[j], where a vertex t is reachable from a vertex s if either s = t (zero-length path) or there are k >= 1 and vertices s = v0, v1, ..., vk = t with each ordered pair (v_{h-1}, v_h) appearing in edges for 1 <= h <= k.
    Preconditions: 2 <= n <= 100000; 1 <= len(edges) <= min(100000, n*(n-1)/2); for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, and 0 <= edges[i][1] < n; all ordered pairs (edges[i][0], edges[i][1]) are distinct; and the directed graph on vertices 0,1,...,n-1 with these directed edges is acyclic. -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
      (h_edges_lower : 1 ≤ edges.val.length)
      (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
      (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
      (h_src_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
      (h_src_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_tgt_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
      (h_tgt_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_distinct : (edgeRows edges).Nodup)
      (h_acyclic : Acyclic edges) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_smallest_set_of_vertices n edges = ok r →
          ∀ v : Int, 0 ≤ v → v < n.val →
            ∃ j : Nat, ∃ _hj : j < r.val.length, Reach edges (r.val[j]).val v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
        (h_edges_lower : 1 ≤ edges.val.length)
        (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
        (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
        (h_src_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
        (h_src_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_tgt_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
        (h_tgt_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_distinct : (edgeRows edges).Nodup)
        (h_acyclic : Acyclic edges), ∀ r : alloc.vec.Vec Std.I64,
          find_smallest_set_of_vertices n edges = ok r →
            ∀ v : Int, 0 ≤ v → v < n.val →
              ∃ j : Nat, ∃ _hj : j < r.val.length, Reach edges (r.val[j]).val v) := by
    sorry

  /-- Whenever the function returns a result r, there is no list S such that (i) every element of S is an integer v with 0 <= v < n, (ii) no vertex occurs more than once in S, (iii) len(S) < len(r), and (iv) for every vertex v with 0 <= v < n, v is reachable from some element of S, where t is reachable from s if either s = t or there are k >= 1 and vertices s = v0, v1, ..., vk = t with each ordered pair (v_{h-1}, v_h) appearing in edges for 1 <= h <= k.
    Preconditions: 2 <= n <= 100000; 1 <= len(edges) <= min(100000, n*(n-1)/2); for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, and 0 <= edges[i][1] < n; all ordered pairs (edges[i][0], edges[i][1]) are distinct; and the directed graph on vertices 0,1,...,n-1 with these directed edges is acyclic. -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
      (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
      (h_edges_lower : 1 ≤ edges.val.length)
      (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
      (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
      (h_src_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
      (h_src_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_tgt_lower : ∀ i (hi : i < edges.val.length),
        0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
      (h_tgt_upper : ∀ i (hi : i < edges.val.length),
        ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
      (h_distinct : (edgeRows edges).Nodup)
      (h_acyclic : Acyclic edges) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_smallest_set_of_vertices n edges = ok r →
          ¬ ∃ S : List Int,
              (∀ v : Int, v ∈ S → 0 ≤ v ∧ v < n.val) ∧
              S.Nodup ∧
              S.length < r.val.length ∧
              (∀ v : Int, 0 ≤ v → v < n.val → ∃ s : Int, s ∈ S ∧ Reach edges s v) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
        (h_n_lower : 2 ≤ n.val) (h_n_upper : n.val ≤ 100000)
        (h_edges_lower : 1 ≤ edges.val.length)
        (h_edges_upper : (edges.val.length : Int) ≤ min 100000 (n.val * (n.val - 1) / 2))
        (h_len : ∀ i (_ : i < edges.val.length), (edges.val[i]).val.length = 2)
        (h_src_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val)
        (h_src_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[0]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_tgt_lower : ∀ i (hi : i < edges.val.length),
          0 ≤ ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val)
        (h_tgt_upper : ∀ i (hi : i < edges.val.length),
          ((edges.val[i]).val[1]'(by have h2 := h_len i hi; omega)).val < n.val)
        (h_distinct : (edgeRows edges).Nodup)
        (h_acyclic : Acyclic edges), ∀ r : alloc.vec.Vec Std.I64,
          find_smallest_set_of_vertices n edges = ok r →
            ¬ ∃ S : List Int,
                (∀ v : Int, v ∈ S → 0 ≤ v ∧ v < n.val) ∧
                S.Nodup ∧
                S.length < r.val.length ∧
                (∀ v : Int, 0 ≤ v → v < n.val → ∃ s : Int, s ∈ S ∧ Reach edges s v)) := by
    sorry

  end AegisSpec.FindSmallestSetOfVertices
