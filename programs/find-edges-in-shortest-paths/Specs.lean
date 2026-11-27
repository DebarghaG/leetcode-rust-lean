import Aegis.FindAnswer.Code.Funs

/-!
# Specifications of `Aegis.FindAnswer.find_answer`

LeetCode problem `find-edges-in-shortest-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  set_option autoImplicit false

  namespace AegisSpec.FindAnswer

  def edgeRows (edges : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    edges.val.map (fun v => v.val.map (fun x => x.val))

  def numEdges (edges : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    edges.val.length

  def edgeSrc (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option ℤ :=
    ((edgeRows edges)[i]?).bind (fun r => r[0]?)

  def edgeDst (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option ℤ :=
    ((edgeRows edges)[i]?).bind (fun r => r[1]?)

  def edgeWeight (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option ℤ :=
    ((edgeRows edges)[i]?).bind (fun r => r[2]?)

  def edgeWeightENat (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ENat :=
    match edgeWeight edges i with
    | some w => (w.toNat : ENat)
    | none => ⊤

  def SameEndpoints (edges : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : Prop :=
    (edgeSrc edges i = edgeSrc edges j ∧ edgeDst edges i = edgeDst edges j) ∨
      (edgeSrc edges i = edgeDst edges j ∧ edgeDst edges i = edgeSrc edges j)

  def Step (edges : Slice (alloc.vec.Vec Std.I64)) (e : ℕ) (u v : ℤ) : Prop :=
    ∃ a b : ℤ, edgeSrc edges e = some a ∧ edgeDst edges e = some b ∧
      ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

  def IsPathFromTo (edges : Slice (alloc.vec.Vec Std.I64)) (u v : ℤ) (vs : List ℤ)
      (es : List ℕ) : Prop :=
    vs.Nodup ∧ vs.head? = some u ∧ vs.getLast? = some v ∧ es.length + 1 = vs.length ∧
      ∀ j, j < es.length → Step edges (es[j]!) (vs[j]!) (vs[j + 1]!)

  def IsPath (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) (vs : List ℤ) (es : List ℕ) : Prop :=
    IsPathFromTo edges 0 (n - 1) vs es ∧ 2 ≤ vs.length

  def sumWeights (edges : Slice (alloc.vec.Vec Std.I64)) : List ℕ → Option ℕ
    | [] => some 0
    | e :: tl =>
      (edgeWeight edges e).bind (fun w => (sumWeights edges tl).map (fun s => w.toNat + s))

  def pathWeight (edges : Slice (alloc.vec.Vec Std.I64)) (es : List ℕ) : ENat :=
    match sumWeights edges es with
    | some W => (W : ENat)
    | none => ⊤

  noncomputable def distTo (edges : Slice (alloc.vec.Vec Std.I64)) (u v : ℤ) : ENat :=
    ⨅ (D : ENat), ⨅ (_ : ∃ vs es, IsPathFromTo edges u v vs es ∧ pathWeight edges es = D), D

  noncomputable def shortestDist (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) : ENat :=
    ⨅ (D : ENat), ⨅ (_ : ∃ vs es, IsPath n edges vs es ∧ pathWeight edges es = D), D

  noncomputable def d0 (edges : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : ENat :=
    distTo edges 0 v

  noncomputable def dT (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : ENat :=
    distTo edges v (n - 1)

  def UsesEdge (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) (vs : List ℤ) : Prop :=
    ∃ a b : ℤ, edgeSrc edges i = some a ∧ edgeDst edges i = some b ∧
      ∃ j, j + 1 < vs.length ∧
        ((vs[j]! = a ∧ vs[j + 1]! = b) ∨ (vs[j]! = b ∧ vs[j + 1]! = a))

  def UsesEdgeIdx (es : List ℕ) (i : ℕ) : Prop :=
    i ∈ es

  def WF (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    2 ≤ n.val ∧ n.val ≤ 50000 ∧
      1 ≤ numEdges edges ∧
      numEdges edges ≤ min 50000 (n.val.toNat * (n.val.toNat - 1) / 2) ∧
      (∀ i, i < numEdges edges → ∃ a b w : ℤ,
        (edgeRows edges)[i]? = some [a, b, w] ∧
          0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b ∧ 1 ≤ w ∧ w ≤ 100000) ∧
      (∀ i j, i < numEdges edges → j < numEdges edges → i ≠ j → ¬ SameEndpoints edges i j)

  def SwapEdge (edges edges' : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Prop :=
    edges'.val.length = edges.val.length ∧
      (∀ j, j < edges.val.length → j ≠ i → edges'.val[j]? = edges.val[j]?) ∧
      edgeSrc edges' i = edgeDst edges i ∧ edgeDst edges' i = edgeSrc edges i ∧
      edgeWeight edges' i = edgeWeight edges i

  def IsIndexPermutation (π : List ℕ) (m : ℕ) : Prop :=
    π.length = m ∧ π.Nodup ∧ ∀ j, j ∈ π → j < m

  /-- Whenever the function returns a result r, let m = len(edges). A path from 0 to n-1 is a sequence v_0,...,v_k with k >= 1, v_0 = 0, v_k = n-1, pairwise distinct vertices v_j, and for each j < k some edge index e_j < m with {v_j,v_{j+1}} = {a_{e_j},b_{e_j}}; its weight is the sum of w_{e_j}. Let D be the minimum weight of such a path, or infinity if no such path exists. Then len(r) = m, and for every i with 0 <= i < m, r[i] = true if and only if there is a path from 0 to n-1 of weight D that uses edge i, meaning some consecutive pair of its vertices equals {a_i,b_i}. In particular, if D is infinite then every r[i] is false.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      r.val.length = numEdges edges ∧
        ∀ i, i < numEdges edges →
          (r.val[i]! = true ↔
            ∃ vs es, IsPath n.val edges vs es ∧
              pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), r.val.length = numEdges edges ∧
          ∀ i, i < numEdges edges →
            (r.val[i]! = true ↔
              ∃ vs es, IsPath n.val edges vs es ∧
                pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs)) := by
    sorry

  /-- The function returns a result on every such input; it does not fail. In particular, no i64 overflow is required: a simple path uses at most n-1 <= 49999 edges, each of weight at most 100000, so every relevant path weight is at most 49999 * 100000 = 4,999,900,000, which is below 2^63.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges) :
      ∃ r : alloc.vec.Vec Bool, Aegis.FindAnswer.find_answer n edges = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges), ∃ r : alloc.vec.Vec Bool, Aegis.FindAnswer.find_answer n edges = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(edges). Thus r has exactly one Boolean entry for each input edge, with the same index i from 0 to len(edges)-1.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      r.val.length = numEdges edges := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), r.val.length = numEdges edges) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(edges), if r[i] = true then there exists a path P from 0 to n-1 whose total weight equals the shortest-path distance D and such that edge i is one of the edges of P, traversed in either direction. Here D is the minimum weight of a path from 0 to n-1, with D = infinity if no such path exists.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ i, i < numEdges edges → r.val[i]! = true →
        ∃ vs es, IsPath n.val edges vs es ∧
          pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ i, i < numEdges edges → r.val[i]! = true →
          ∃ vs es, IsPath n.val edges vs es ∧
            pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(edges), if r[i] = false then no path from 0 to n-1 of minimum weight D uses edge i. Equivalently, there is no shortest path from 0 to n-1 in which edge i appears as a consecutive pair of vertices.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ i, i < numEdges edges → r.val[i]! = false →
        ¬ ∃ vs es, IsPath n.val edges vs es ∧
          pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ i, i < numEdges edges → r.val[i]! = false →
          ¬ ∃ vs es, IsPath n.val edges vs es ∧
            pathWeight edges es = shortestDist n.val edges ∧ UsesEdge edges i vs) := by
    sorry

  /-- Whenever the function returns a result r, r[i] = false for every i with 0 <= i < len(edges) if and only if there is no path from 0 to n-1 in the undirected graph represented by edges. Thus, if 0 can reach n-1, at least one entry of r is true.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ((∀ i, i < numEdges edges → r.val[i]! = false) ↔
        ¬ ∃ vs es, IsPath n.val edges vs es) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ((∀ i, i < numEdges edges → r.val[i]! = false) ↔
          ¬ ∃ vs es, IsPath n.val edges vs es)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(edges), if r[i] = true then w_i <= D, where D is the minimum weight of a path from 0 to n-1. In this case D is finite, and edge i cannot have weight larger than the whole shortest-path distance.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ i, i < numEdges edges → r.val[i]! = true →
        shortestDist n.val edges ≠ ⊤ ∧ edgeWeightENat edges i ≤ shortestDist n.val edges := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ i, i < numEdges edges → r.val[i]! = true →
          shortestDist n.val edges ≠ ⊤ ∧ edgeWeightENat edges i ≤ shortestDist n.val edges) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(edges), r[i] = true if and only if D is finite and min(d0[a_i] + w_i + dT[b_i], d0[b_i] + w_i + dT[a_i]) = D. Here d0[v] is the minimum total weight of a simple path from 0 to v, or infinity if no such path exists; dT[v] is the minimum total weight of a simple path from v to n-1, or infinity if no such path exists; D = d0[n-1]; addition and min are extended to infinity by infinity + x = infinity and min(infinity, x) = x.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ i, i < numEdges edges →
        (r.val[i]! = true ↔
          shortestDist n.val edges ≠ ⊤ ∧
            ∃ a b : ℤ, edgeSrc edges i = some a ∧ edgeDst edges i = some b ∧
              min (d0 edges a + edgeWeightENat edges i + dT n.val edges b)
                  (d0 edges b + edgeWeightENat edges i + dT n.val edges a) =
                shortestDist n.val edges) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ i, i < numEdges edges →
          (r.val[i]! = true ↔
            shortestDist n.val edges ≠ ⊤ ∧
              ∃ a b : ℤ, edgeSrc edges i = some a ∧ edgeDst edges i = some b ∧
                min (d0 edges a + edgeWeightENat edges i + dT n.val edges b)
                    (d0 edges b + edgeWeightENat edges i + dT n.val edges a) =
                  shortestDist n.val edges)) := by
    sorry

  /-- Whenever n and edges satisfy the preconditions and r is the result of find_answer n edges, then for every i with 0 <= i < len(edges), if edges' is obtained by replacing edges[i] = [a_i,b_i,w_i] with [b_i,a_i,w_i] and leaving all other entries unchanged, and if find_answer n edges' returns r', then r' = r: the two Boolean vectors have the same length and agree at every index.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ i, i < numEdges edges →
        ∀ edges' : Slice (alloc.vec.Vec Std.I64), SwapEdge edges edges' i →
          ∀ r' : alloc.vec.Vec Bool,
            Aegis.FindAnswer.find_answer n edges' = Result.ok r' → r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ i, i < numEdges edges →
          ∀ edges' : Slice (alloc.vec.Vec Std.I64), SwapEdge edges edges' i →
            ∀ r' : alloc.vec.Vec Bool,
              Aegis.FindAnswer.find_answer n edges' = Result.ok r' → r'.val = r.val) := by
    sorry

  /-- Whenever n and edges satisfy the preconditions, for every permutation π of {0,...,m-1}, if edges' is defined by edges'[j] = edges[π(j)] for 0 <= j < m, and if find_answer n edges returns r and find_answer n edges' returns r', then len(r') = m and for every j with 0 <= j < m, r'[j] = r[π(j)]. Reordering the edge list merely permutes the answer entries in the same way.
    Preconditions: n and edges satisfy: n is an i64 with 2 <= n <= 50000; edges is a slice of i64 vectors, m = len(edges), 1 <= m <= min(50000, n*(n-1)/2); for every i with 0 <= i < m, edges[i] has length 3 and edges[i] = [a_i,b_i,w_i] with 0 <= a_i,b_i < n, a_i != b_i, and 1 <= w_i <= 100000; and no two distinct indices i,j have {a_i,b_i} = {a_j,b_j}. -/
  theorem spec_10 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
      (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r) :
      ∀ π : List ℕ, IsIndexPermutation π (numEdges edges) →
        ∀ edges' : Slice (alloc.vec.Vec Std.I64),
          edges'.val = π.map (fun j => edges.val[j]!) →
            ∀ r' : alloc.vec.Vec Bool,
              Aegis.FindAnswer.find_answer n edges' = Result.ok r' →
                r'.val.length = numEdges edges ∧
                  ∀ j, j < numEdges edges → r'.val[j]! = r.val[π[j]!]! := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (h : WF n edges)
        (r : alloc.vec.Vec Bool) (hr : Aegis.FindAnswer.find_answer n edges = Result.ok r), ∀ π : List ℕ, IsIndexPermutation π (numEdges edges) →
          ∀ edges' : Slice (alloc.vec.Vec Std.I64),
            edges'.val = π.map (fun j => edges.val[j]!) →
              ∀ r' : alloc.vec.Vec Bool,
                Aegis.FindAnswer.find_answer n edges' = Result.ok r' →
                  r'.val.length = numEdges edges ∧
                    ∀ j, j < numEdges edges → r'.val[j]! = r.val[π[j]!]!) := by
    sorry

  end AegisSpec.FindAnswer
