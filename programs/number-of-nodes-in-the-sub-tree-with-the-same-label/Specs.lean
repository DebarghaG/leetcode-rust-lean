import Aegis.CountSubTrees.Code.Funs

/-!
# Specifications of `Aegis.CountSubTrees.count_sub_trees`

LeetCode problem `number-of-nodes-in-the-sub-tree-with-the-same-label`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open scoped Classical
  open Aegis.CountSubTrees

  namespace AegisSpec.CountSubTrees

  def nv (n : Std.I64) : ℕ := n.val.toNat

  def edgeEndpoints (e : alloc.vec.Vec Std.I64) : List ℤ := e.val.map (fun x => x.val)

  def edgePairs (edges : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    edges.val.map edgeEndpoints

  def labelSeq (labels : Slice Std.U8) : List ℕ := labels.val.map (fun x => x.val)

  def lab (labels : Slice Std.U8) (i : ℕ) : ℕ := (labelSeq labels).getD i 0

  def out (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ := ((r.val[i]?).map (fun x => x.val)).getD 0

  def Adj (es : List (List ℤ)) (u v : ℕ) : Prop :=
    ∃ e ∈ es, e = [(u : ℤ), (v : ℤ)] ∨ e = [(v : ℤ), (u : ℤ)]

  def IsWalk (es : List (List ℤ)) : List ℕ → Prop
    | [] => False
    | [_] => True
    | u :: v :: rest => Adj es u v ∧ IsWalk es (v :: rest)

  def SimplePathFromTo (es : List (List ℤ)) (p : List ℕ) (a b : ℕ) : Prop :=
    IsWalk es p ∧ p.Nodup ∧ p.head? = some a ∧ p.getLast? = some b

  def IsTreeOn (es : List (List ℤ)) (n : ℕ) : Prop :=
    ∀ j, j < n → ∃! p : List ℕ, SimplePathFromTo es p 0 j

  def InSubtree (es : List (List ℤ)) (i j : ℕ) : Prop :=
    ∃ p, SimplePathFromTo es p 0 j ∧ i ∈ p

  def IsChild (es : List (List ℤ)) (i c : ℕ) : Prop :=
    Adj es i c ∧ InSubtree es i c

  noncomputable def Card (n : ℕ) (p : ℕ → Prop) : ℕ := ((Finset.range n).filter p).card

  noncomputable def SumRange (n : ℕ) (f : ℕ → ℤ) : ℤ := (Finset.range n).sum f

  noncomputable def childSumOut (es : List (List ℤ)) (n : ℕ) (labels : Slice Std.U8)
      (r : alloc.vec.Vec Std.I64) (i : ℕ) : ℤ :=
    SumRange n (fun c => if IsChild es i c ∧ lab labels c = lab labels i then out r c else 0)

  noncomputable def cardSubtreeLab (es : List (List ℤ)) (n : ℕ) (labels : Slice Std.U8)
      (c i : ℕ) : ℕ :=
    Card n (fun j => InSubtree es c j ∧ lab labels j = lab labels i)

  noncomputable def childSubtreeLabSum (es : List (List ℤ)) (n : ℕ) (labels : Slice Std.U8)
      (i : ℕ) : ℤ :=
    SumRange n (fun c => if IsChild es i c then (cardSubtreeLab es n labels c i : ℤ) else 0)

  def EdgeReshuffle (es es' : List (List ℤ)) : Prop :=
    ∃ f : List ℤ → List ℤ, (∀ e, f e = e ∨ f e = e.reverse) ∧ List.Perm es' (es.map f)

  /-- The function returns a result r such that len(r) = n and for every i with 0 <= i < n, r[i] = |{ j : 0 <= j < n, j ∈ subtree(i), and labels[j] = labels[i] }|, where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n)) :
      ∃ r : alloc.vec.Vec Std.I64,
        count_sub_trees n edges labels = ok r ∧
          r.val.length = nv n ∧
          ∀ i, i < nv n →
            out r i =
              ((Card (nv n)
                  (fun j => InSubtree (edgePairs edges) i j ∧ lab labels j = lab labels i) : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n)), ∃ r : alloc.vec.Vec Std.I64,
          count_sub_trees n edges labels = ok r ∧
            r.val.length = nv n ∧
            ∀ i, i < nv n →
              out r i =
                ((Card (nv n)
                    (fun j => InSubtree (edgePairs edges) i j ∧ lab labels j = lab labels i) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail).
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n)) :
      ∃ r : alloc.vec.Vec Std.I64, count_sub_trees n edges labels = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n)), ∃ r : alloc.vec.Vec Std.I64, count_sub_trees n edges labels = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      r.val.length = nv n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), r.val.length = nv n) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, 1 <= r[i] <= |{ j : 0 <= j < n and j ∈ subtree(i) }|, where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        1 ≤ out r i ∧
          out r i ≤ ((Card (nv n) (fun j => InSubtree (edgePairs edges) i j) : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          1 ≤ out r i ∧
            out r i ≤ ((Card (nv n) (fun j => InSubtree (edgePairs edges) i j) : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r such that len(r) = 1 and r[0] = 1.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic); n = 1. -/
  theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (hn_one : n.val = 1) :
      ∃ r : alloc.vec.Vec Std.I64,
        count_sub_trees n edges labels = ok r ∧ r.val.length = 1 ∧ out r 0 = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (hn_one : n.val = 1), ∃ r : alloc.vec.Vec Std.I64,
          count_sub_trees n edges labels = ok r ∧ r.val.length = 1 ∧ out r 0 = 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = |{ j : 0 <= j < n and j ∈ subtree(i) }|, where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic); for every i with 0 <= i < n, labels[i] = labels[0]. -/
  theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (hlabels_const : ∀ i, i < nv n → lab labels i = lab labels 0)
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        out r i = ((Card (nv n) (fun j => InSubtree (edgePairs edges) i j) : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (hlabels_const : ∀ i, i < nv n → lab labels i = lab labels 0)
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          out r i = ((Card (nv n) (fun j => InSubtree (edgePairs edges) i j) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n such that |{ j : 0 <= j < n and j ∈ subtree(i) }| = 1, r[i] = 1, where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        Card (nv n) (fun j => InSubtree (edgePairs edges) i j) = 1 → out r i = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          Card (nv n) (fun j => InSubtree (edgePairs edges) i j) = 1 → out r i = 1) := by
    sorry

  /-- Whenever the function returns a result r, r[0] = |{ j : 0 <= j < n and labels[j] = labels[0] }|.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      out r 0 = ((Card (nv n) (fun j => lab labels j = lab labels 0) : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), out r 0 = ((Card (nv n) (fun j => lab labels j = lab labels 0) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 1 if and only if for every j with 0 <= j < n such that j ∈ subtree(i) and j != i, labels[j] != labels[i], where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        (out r i = 1 ↔
          ∀ j, j < nv n → InSubtree (edgePairs edges) i j → j ≠ i → lab labels j ≠ lab labels i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          (out r i = 1 ↔
            ∀ j, j < nv n → InSubtree (edgePairs edges) i j → j ≠ i → lab labels j ≠ lab labels i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < n, 0 <= j < n, j ∈ subtree(i), and labels[j] = labels[i], we have r[i] >= r[j], where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i j, i < nv n → j < nv n → InSubtree (edgePairs edges) i j →
        lab labels j = lab labels i → out r j ≤ out r i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i j, i < nv n → j < nv n → InSubtree (edgePairs edges) i j →
          lab labels j = lab labels i → out r j ≤ out r i) := by
    sorry

  /-- For any edges' that is a permutation of edges and/or has the endpoints of any edge swapped, whenever the function returns a result r on (n, edges, labels) and a result r' on (n, edges', labels), we have r = r'.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_11 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
      (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (hreshuffle : EdgeReshuffle (edgePairs edges) (edgePairs edges'))
      (r r' : alloc.vec.Vec Std.I64)
      (hr : count_sub_trees n edges labels = ok r)
      (hr' : count_sub_trees n edges' labels = ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
        (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (hreshuffle : EdgeReshuffle (edgePairs edges) (edgePairs edges'))
        (r r' : alloc.vec.Vec Std.I64)
        (hr : count_sub_trees n edges labels = ok r)
        (hr' : count_sub_trees n edges' labels = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= |{ j : 0 <= j < n and labels[j] = labels[i] }|.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        out r i ≤ ((Card (nv n) (fun j => lab labels j = lab labels i) : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          out r i ≤ ((Card (nv n) (fun j => lab labels j = lab labels i) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and every c with 0 <= c < n such that c is a child of i (i.e., c is a neighbor of i in the tree and i lies on the unique simple path from 0 to c), if labels[c] = labels[i], then r[i] >= r[c] + 1.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_13 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n → ∀ c, c < nv n → IsChild (edgePairs edges) i c →
        lab labels c = lab labels i → out r c + 1 ≤ out r i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n → ∀ c, c < nv n → IsChild (edgePairs edges) i c →
          lab labels c = lab labels i → out r c + 1 ≤ out r i) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < n, 0 <= j < n, i != j, j ∈ subtree(i), and labels[j] = labels[i], we have r[i] >= r[j] + 1, where j ∈ subtree(i) iff i lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_14 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i j, i < nv n → j < nv n → i ≠ j → InSubtree (edgePairs edges) i j →
        lab labels j = lab labels i → out r j + 1 ≤ out r i := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i j, i < nv n → j < nv n → i ≠ j → InSubtree (edgePairs edges) i j →
          lab labels j = lab labels i → out r j + 1 ≤ out r i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] >= 1 + Σ_{c : c is a child of i and labels[c] = labels[i]} r[c], where c is a child of i iff c is a neighbor of i and i lies on the unique simple path from 0 to c in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_15 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        1 + childSumOut (edgePairs edges) (nv n) labels r i ≤ out r i := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          1 + childSumOut (edgePairs edges) (nv n) labels r i ≤ out r i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] = 1 + Σ_{c : c is a child of i} |{ j : 0 <= j < n, j ∈ subtree(c), and labels[j] = labels[i] }|, where c is a child of i iff c is a neighbor of i and i lies on the unique simple path from 0 to c, and j ∈ subtree(c) iff c lies on the unique simple path from 0 to j in the tree.
    Preconditions: 1 <= n <= 10^5; len(labels) = n; for every i with 0 <= i < n, 97 <= labels[i] <= 122; len(edges) = n-1; for every edge e in edges, len(e) = 2, 0 <= e[0] < n, 0 <= e[1] < n, e[0] != e[1]; the undirected graph on vertices {0,...,n-1} with edges given by edges is a tree (connected and acyclic). -/
  theorem spec_16 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
      (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
      (hlen_labels : labels.val.length = nv n)
      (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
      (hlen_edges : edges.val.length = nv n - 1)
      (hedges_wf : ∀ e ∈ edgePairs edges,
        e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
          0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
      (htree : IsTreeOn (edgePairs edges) (nv n))
      (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r) :
      ∀ i, i < nv n →
        out r i = 1 + childSubtreeLabSum (edgePairs edges) (nv n) labels i := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (labels : Slice Std.U8)
        (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000)
        (hlen_labels : labels.val.length = nv n)
        (hlabels_ascii : ∀ x ∈ labels.val, 97 ≤ x.val ∧ x.val ≤ 122)
        (hlen_edges : edges.val.length = nv n - 1)
        (hedges_wf : ∀ e ∈ edgePairs edges,
          e.length = 2 ∧ 0 ≤ e.getD 0 0 ∧ e.getD 0 0 < n.val ∧
            0 ≤ e.getD 1 0 ∧ e.getD 1 0 < n.val ∧ e.getD 0 0 ≠ e.getD 1 0)
        (htree : IsTreeOn (edgePairs edges) (nv n))
        (r : alloc.vec.Vec Std.I64) (hr : count_sub_trees n edges labels = ok r), ∀ i, i < nv n →
          out r i = 1 + childSubtreeLabSum (edgePairs edges) (nv n) labels i) := by
    sorry

  end AegisSpec.CountSubTrees
