import Aegis.ModifiedGraphEdges.Code.Funs

/-!
# Specifications of `Aegis.ModifiedGraphEdges.modified_graph_edges`

LeetCode problem `modify-graph-edge-weights`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.alloc.vec

  namespace AegisSpec.ModifiedGraphEdges

  structure Edge where

    u : Int

    v : Int

    w : Int

  def endsEq (e₁ e₂ : Edge) : Prop :=
    (e₁.u = e₂.u ∧ e₁.v = e₂.v) ∨ (e₁.u = e₂.v ∧ e₁.v = e₂.u)

  def incident (e : Edge) (x : Int) : Prop := e.u = x ∨ e.v = x

  def shareVertex (e₁ e₂ : Edge) : Prop :=
    e₁.u = e₂.u ∨ e₁.u = e₂.v ∨ e₁.v = e₂.u ∨ e₁.v = e₂.v

  def IsPath (G : List Edge) (s t : Int) (p : List Edge) : Prop :=
    (∃ e, p.head? = some e ∧ incident e s) ∧
    (∃ e, p.getLast? = some e ∧ incident e t) ∧
    (∀ e ∈ p, e ∈ G) ∧
    (∀ k (hk : k + 1 < p.length),
      shareVertex (p.get ⟨k, by omega⟩) (p.get ⟨k+1, hk⟩))

  def pathWeight (p : List Edge) : Int := (p.map Edge.w).sum

  def ShortestDist (G : List Edge) (s t d : Int) : Prop :=
    (∃ p, IsPath G s t p ∧ pathWeight p = d) ∧
    (∀ p, IsPath G s t p → d ≤ pathWeight p)

  def Connected (n : Int) (G : List Edge) : Prop :=
    ∀ u v, 0 ≤ u → u < n → 0 ≤ v → v < n → u ≠ v → ∃ p, IsPath G u v p

  def vecTriple (v : Vec I64) : Edge :=
    ⟨v.val.getD 0 0#i64, v.val.getD 1 0#i64, v.val.getD 2 0#i64⟩

  def inputEdges (edges : Slice (Vec I64)) : List Edge :=
    edges.val.map vecTriple

  def inputEdgesReplaceNeg (edges : Slice (Vec I64)) (c : Int) : List Edge :=
    edges.val.map (fun v =>
      let e := vecTriple v
      if e.w = -1 then ⟨e.u, e.v, c⟩ else e)

  def inputEdgesW (edges : Slice (Vec I64)) (w : Nat → Int) : List Edge :=
    ((List.range edges.val.length).zip edges.val).map (fun iv =>
      let e := vecTriple iv.2
      if e.w > 0 then e else ⟨e.u, e.v, w iv.1⟩)

  def outputEdges (r : Vec (Vec I64)) : List Edge :=
    r.val.map vecTriple

  def WAdmissible (edges : Slice (Vec I64)) (w : Nat → Int) : Prop :=
    ∀ i (hi : i < edges.val.length),
      (vecTriple (edges.val[i]'hi)).w = -1 → 1 ≤ w i ∧ w i ≤ 2000000000

  def NoSolution (edges : Slice (Vec I64)) (s t target : Int) : Prop :=
    ∀ w, WAdmissible edges w →
      ∀ d, ShortestDist (inputEdgesW edges w) s t d → d ≠ target

  def HasSolution (edges : Slice (Vec I64)) (s t target : Int) : Prop :=
    ∃ w, WAdmissible edges w ∧ ShortestDist (inputEdgesW edges w) s t target

  def RowOk (v : Vec I64) (n : Int) : Prop :=
    v.val.length = 3 ∧
    (let e := vecTriple v
     0 ≤ e.u ∧ e.u < n ∧ 0 ≤ e.v ∧ e.v < n ∧ e.u ≠ e.v ∧
     (e.w = -1 ∨ (1 ≤ e.w ∧ e.w ≤ 10000000)))

  def AllRowsOk (edges : Slice (Vec I64)) (n : Int) : Prop :=
    ∀ i (hi : i < edges.val.length), RowOk (edges.val[i]'hi) n

  def NoRepeatedEdges (edges : Slice (Vec I64)) : Prop :=
    ∀ i (hi : i < edges.val.length) j (hj : j < edges.val.length),
      i ≠ j → ¬ endsEq (vecTriple (edges.val[i]'hi)) (vecTriple (edges.val[j]'hj))

  def Pre (n : I64) (edges : Slice (Vec I64)) (source destination target : I64) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 100 ∧
    1 ≤ (edges.val.length : Int) ∧
    (edges.val.length : Int) ≤ n.val * (n.val - 1) / 2 ∧
    AllRowsOk edges n.val ∧
    0 ≤ source.val ∧ source.val < n.val ∧
    0 ≤ destination.val ∧ destination.val < n.val ∧
    source.val ≠ destination.val ∧
    1 ≤ target.val ∧ target.val ≤ 1000000000 ∧
    Connected n.val (inputEdges edges) ∧
    NoRepeatedEdges edges

  def IsValidOutput (edges : Slice (Vec I64)) (r : Vec (Vec I64)) (s t target : Int) : Prop :=
    r.val ≠ [] ∧
    (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) ∧
    (∃ pi : Nat → Nat,
      (∀ j, j < r.val.length → pi j < edges.val.length) ∧
      (∀ i, i < edges.val.length → ∃ j, j < r.val.length ∧ pi j = i) ∧
      (∀ j₁, j₁ < r.val.length → ∀ j₂, j₂ < r.val.length → pi j₁ = pi j₂ → j₁ = j₂) ∧
      (∀ j (hj : j < r.val.length) (hpi : pi j < edges.val.length),
        endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[pi j]'hpi)) ∧
        ((vecTriple (edges.val[pi j]'hpi)).w > 0 →
          (vecTriple (r.val[j]'hj)).w = (vecTriple (edges.val[pi j]'hpi)).w) ∧
        ((vecTriple (edges.val[pi j]'hpi)).w = -1 →
          1 ≤ (vecTriple (r.val[j]'hj)).w ∧
          (vecTriple (r.val[j]'hj)).w ≤ 2000000000))) ∧
    ShortestDist (outputEdges r) s t target

  /-- Let m = len(edges). The function returns a result r. Exactly one of the following holds. (A) r is empty, and for every function w mapping each index i with 0 <= i < m and edges[i][2] = -1 to an integer in [1, 2*10^9], the shortest distance from source to destination in the undirected graph with nodes 0..n-1 and edge list E_w (whose i-th edge is [edges[i][0], edges[i][1], edges[i][2]] if edges[i][2] > 0, and [edges[i][0], edges[i][1], w(i)] otherwise) is not equal to target. Here distance is the minimum sum of edge weights over all paths from source to destination. (B) r is non-empty, for every j with 0 <= j < len(r) we have len(r[j]) = 3, and there is a bijection pi from {0,...,len(r)-1} to {0,...,m-1} such that for every j: the unordered pair {r[j][0], r[j][1]} equals {edges[pi(j)][0], edges[pi(j)][1]}; if edges[pi(j)][2] > 0 then r[j][2] = edges[pi(j)][2], and if edges[pi(j)][2] = -1 then 1 <= r[j][2] <= 2*10^9; and the shortest distance from source to destination in the undirected graph with nodes 0..n-1 and edges r is exactly target.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_1 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∃ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r ∧
        ((r.val = [] ∧ NoSolution edges source.val destination.val target.val) ∨
          IsValidOutput edges r source.val destination.val target.val) ∧
        ¬ ((r.val = [] ∧ NoSolution edges source.val destination.val target.val) ∧
            IsValidOutput edges r source.val destination.val target.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∃ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r ∧
          ((r.val = [] ∧ NoSolution edges source.val destination.val target.val) ∨
            IsValidOutput edges r source.val destination.val target.val) ∧
          ¬ ((r.val = [] ∧ NoSolution edges source.val destination.val target.val) ∧
              IsValidOutput edges r source.val destination.val target.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_2 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∃ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∃ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r) := by
    sorry

  /-- Whenever the function returns a non-empty result r, len(r) = len(edges) and for every j with 0 <= j < len(r), len(r[j]) = 3.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_3 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        r.val.length = edges.val.length ∧
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          r.val.length = edges.val.length ∧
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3)) := by
    sorry

  /-- Whenever the function returns a non-empty result r such that len(r[j]) = 3 for every j, for every input index i with 0 <= i < len(edges) there is exactly one output index j with 0 <= j < len(r) such that {r[j][0], r[j][1]} = {edges[i][0], edges[i][1]}; and conversely, for every output index j with 0 <= j < len(r) there is exactly one input index i with 0 <= i < len(edges) such that the same equality holds.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_4 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
        (∀ i (hi : i < edges.val.length),
          ∃ j, ∃ (hj : j < r.val.length),
            endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) ∧
            ∀ j' (hj' : j' < r.val.length),
              endsEq (vecTriple (r.val[j']'hj')) (vecTriple (edges.val[i]'hi)) → j' = j) ∧
        (∀ j (hj : j < r.val.length),
          ∃ i, ∃ (hi : i < edges.val.length),
            endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) ∧
            ∀ i' (hi' : i' < edges.val.length),
              endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i']'hi')) → i' = i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
          (∀ i (hi : i < edges.val.length),
            ∃ j, ∃ (hj : j < r.val.length),
              endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) ∧
              ∀ j' (hj' : j' < r.val.length),
                endsEq (vecTriple (r.val[j']'hj')) (vecTriple (edges.val[i]'hi)) → j' = j) ∧
          (∀ j (hj : j < r.val.length),
            ∃ i, ∃ (hi : i < edges.val.length),
              endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) ∧
              ∀ i' (hi' : i' < edges.val.length),
                endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i']'hi')) → i' = i)) := by
    sorry

  /-- Whenever the function returns a non-empty result r such that len(r[j]) = 3 for every j, for every input index i with edges[i][2] > 0, if j is the unique output index with {r[j][0], r[j][1]} = {edges[i][0], edges[i][1]}, then r[j][2] = edges[i][2].
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_5 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
        ∀ i (hi : i < edges.val.length),
          (vecTriple (edges.val[i]'hi)).w > 0 →
          ∀ j (hj : j < r.val.length),
            endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) →
            (vecTriple (r.val[j]'hj)).w = (vecTriple (edges.val[i]'hi)).w := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
          ∀ i (hi : i < edges.val.length),
            (vecTriple (edges.val[i]'hi)).w > 0 →
            ∀ j (hj : j < r.val.length),
              endsEq (vecTriple (r.val[j]'hj)) (vecTriple (edges.val[i]'hi)) →
              (vecTriple (r.val[j]'hj)).w = (vecTriple (edges.val[i]'hi)).w) := by
    sorry

  /-- Whenever the function returns a non-empty result r such that len(r[j]) = 3 for every j, for every output index j with 0 <= j < len(r), 1 <= r[j][2] <= 2*10^9.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_6 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
        ∀ j (hj : j < r.val.length),
          1 ≤ (vecTriple (r.val[j]'hj)).w ∧ (vecTriple (r.val[j]'hj)).w ≤ 2000000000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
          ∀ j (hj : j < r.val.length),
            1 ≤ (vecTriple (r.val[j]'hj)).w ∧ (vecTriple (r.val[j]'hj)).w ≤ 2000000000) := by
    sorry

  /-- Whenever the function returns a non-empty result r, let d_min be the shortest distance from source to destination in the undirected graph with nodes 0..n-1 whose edge list is obtained from edges by replacing every weight -1 with 1 (and keeping every positive weight unchanged). Then d_min <= target.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_7 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        ∃ d, ShortestDist (inputEdgesReplaceNeg edges 1) source.val destination.val d ∧
          d ≤ target.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          ∃ d, ShortestDist (inputEdgesReplaceNeg edges 1) source.val destination.val d ∧
            d ≤ target.val) := by
    sorry

  /-- Whenever the function returns a non-empty result r, let d_max be the shortest distance from source to destination in the undirected graph with nodes 0..n-1 whose edge list is obtained from edges by replacing every weight -1 with 2*10^9 (and keeping every positive weight unchanged). Then d_max >= target.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_8 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        ∃ d, ShortestDist (inputEdgesReplaceNeg edges 2000000000) source.val destination.val d ∧
          target.val ≤ d := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          ∃ d, ShortestDist (inputEdgesReplaceNeg edges 2000000000) source.val destination.val d ∧
            target.val ≤ d) := by
    sorry

  /-- Whenever the function returns a non-empty result r such that len(r[j]) = 3 for every j, for every path from source to destination in the undirected graph with nodes 0..n-1 and edges r, the sum of the edge weights along the path is at least target. A path here is a finite sequence of edges in r such that consecutive edges share a vertex, the first edge is incident to source, and the last edge is incident to destination.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_9 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
        ∀ p, IsPath (outputEdges r) source.val destination.val p →
          target.val ≤ pathWeight p := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
          ∀ p, IsPath (outputEdges r) source.val destination.val p →
            target.val ≤ pathWeight p) := by
    sorry

  /-- Whenever the function returns a non-empty result r such that len(r[j]) = 3 for every j, there exists a path from source to destination in the undirected graph with nodes 0..n-1 and edges r whose edge-weight sum is exactly target. A path here is a finite sequence of edges in r such that consecutive edges share a vertex, the first edge is incident to source, and the last edge is incident to destination.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_10 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val ≠ [] →
        (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
        ∃ p, IsPath (outputEdges r) source.val destination.val p ∧
          pathWeight p = target.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val ≠ [] →
          (∀ j (hj : j < r.val.length), (r.val[j]'hj).val.length = 3) →
          ∃ p, IsPath (outputEdges r) source.val destination.val p ∧
            pathWeight p = target.val) := by
    sorry

  /-- Whenever the function returns an empty result r, for every function w mapping each index i with 0 <= i < len(edges) and edges[i][2] = -1 to an integer in [1, 2*10^9], the shortest distance from source to destination in the undirected graph with nodes 0..n-1 and edge list E_w (whose i-th edge is [edges[i][0], edges[i][1], edges[i][2]] if edges[i][2] > 0, and [edges[i][0], edges[i][1], w(i)] otherwise) is not equal to target.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_11 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      ∀ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
        r.val = [] →
        NoSolution edges source.val destination.val target.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), ∀ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r →
          r.val = [] →
          NoSolution edges source.val destination.val target.val) := by
    sorry

  /-- If there exists a function w mapping each index i with 0 <= i < len(edges) and edges[i][2] = -1 to an integer in [1, 2*10^9] such that the shortest distance from source to destination in the undirected graph with nodes 0..n-1 and edge list E_w (whose i-th edge is [edges[i][0], edges[i][1], edges[i][2]] if edges[i][2] > 0, and [edges[i][0], edges[i][1], w(i)] otherwise) equals target, then the function returns a non-empty result r.
    Preconditions: n, edges, source, destination, target satisfy: 1 <= n <= 100; 1 <= len(edges) <= n*(n-1)/2; each edges[i] has length 3; for every i, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and (edges[i][2] = -1 or 1 <= edges[i][2] <= 10^7); 0 <= source < n, 0 <= destination < n, source != destination; 1 <= target <= 10^9; the undirected graph with nodes 0..n-1 and an edge {edges[i][0], edges[i][1]} for each i is connected; no two edges have the same unordered endpoint pair (no repeated edges). -/
  theorem spec_12 (n : I64) (edges : Slice (Vec I64))
      (source destination target : I64) (h : Pre n edges source destination target) :
      HasSolution edges source.val destination.val target.val →
      ∃ r : Vec (Vec I64),
        Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r ∧
        r.val ≠ [] := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (edges : Slice (Vec I64))
        (source destination target : I64) (h : Pre n edges source destination target), HasSolution edges source.val destination.val target.val →
        ∃ r : Vec (Vec I64),
          Aegis.ModifiedGraphEdges.modified_graph_edges n edges source destination target = ok r ∧
          r.val ≠ []) := by
    sorry

  end AegisSpec.ModifiedGraphEdges
