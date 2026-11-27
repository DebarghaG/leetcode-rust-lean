import Aegis.MinimumDistance.Code.Funs

/-!
# Specifications of `Aegis.MinimumDistance.minimum_distance`

LeetCode problem `find-the-closest-marked-node`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumDistance

  open Aegis.MinimumDistance

  structure Edge where

    src : ℤ

    tgt : ℤ

    weight : ℤ
  deriving DecidableEq, Inhabited

  def edgeTriple (e : alloc.vec.Vec Std.I64) : Option Edge :=
    match e.val.map IScalar.val with
    | [u, v, w] => some ⟨u, v, w⟩
    | _ => none

  def edgeList (edges : Slice (alloc.vec.Vec Std.I64)) : List Edge :=
    edges.val.filterMap edgeTriple

  def markedVals (marked : Slice Std.I64) : List ℤ :=
    marked.val.map IScalar.val

  def IsPathFrom (edges : Slice (alloc.vec.Vec Std.I64)) : ℤ → List Edge → ℤ → Prop
    | x, [], y => x = y
    | x, e :: rest, y => e.src = x ∧ e ∈ edgeList edges ∧ IsPathFrom edges e.tgt rest y

  def pathWeight (p : List Edge) : ℤ := (p.map Edge.weight).sum

  def Reaches (edges : Slice (alloc.vec.Vec Std.I64)) (x y : ℤ) : Prop :=
    ∃ p : List Edge, IsPathFrom edges x p y

  def IsSimplePathFrom (edges : Slice (alloc.vec.Vec Std.I64)) (x : ℤ) (p : List Edge)
      (y : ℤ) : Prop :=
    IsPathFrom edges x p y ∧ (x :: p.map Edge.tgt).Nodup

  def Pre (n : ℤ) (edges : Slice (alloc.vec.Vec Std.I64)) (s : ℤ)
      (marked : Slice Std.I64) : Prop :=
    2 ≤ n ∧ n ≤ 500 ∧
    1 ≤ edges.val.length ∧ edges.val.length ≤ 10 ^ 4 ∧
    (∀ e ∈ edges.val, (e.val.map IScalar.val).length = 3) ∧
    (∀ e ∈ edges.val, ∀ u v w : ℤ, e.val.map IScalar.val = [u, v, w] →
      0 ≤ u ∧ u < n ∧ 0 ≤ v ∧ v < n ∧ u ≠ v ∧ 1 ≤ w ∧ w ≤ 10 ^ 6) ∧
    1 ≤ marked.val.length ∧ (marked.val.length : ℤ) ≤ n - 1 ∧
    0 ≤ s ∧ s < n ∧
    (∀ x ∈ markedVals marked, 0 ≤ x ∧ x < n) ∧
    (markedVals marked).Nodup ∧
    (∀ x ∈ markedVals marked, s ≠ x)

  def IsMaxWeight (edges : Slice (alloc.vec.Vec Std.I64)) (W : ℤ) : Prop :=
    (∃ e ∈ edgeList edges, e.weight = W) ∧ ∀ e ∈ edgeList edges, e.weight ≤ W

  def IsMinWeight (edges : Slice (alloc.vec.Vec Std.I64)) (W : ℤ) : Prop :=
    (∃ e ∈ edgeList edges, e.weight = W) ∧ ∀ e ∈ edgeList edges, W ≤ e.weight

  def IsMinDist (edges : Slice (alloc.vec.Vec Std.I64)) (s : ℤ) (marked : Slice Std.I64)
      (r : ℤ) : Prop :=
    (∀ m ∈ markedVals marked, ∀ p : List Edge, IsPathFrom edges s p m → r ≤ pathWeight p) ∧
    ((r = -1 ∧ ∀ m ∈ markedVals marked, ¬ Reaches edges s m) ∨
      ∃ m ∈ markedVals marked, ∃ p : List Edge, IsPathFrom edges s p m ∧ pathWeight p = r)

  /-- Call an edge entry [u,v,w] a directed edge from u to v of weight w. Define a path from a node x to a node y to be a finite sequence of edge entries e_1, ..., e_k (k >= 0) such that: if k = 0 then x = y; if k > 0 then source(e_1) = x, target(e_j) = source(e_{j+1}) for 1 <= j < k, and target(e_k) = y. The weight of this path is the sum of the weights of e_1, ..., e_k (the empty path has weight 0). Let D be the minimum of weight(P) over all marked nodes m (i.e. m = marked[j] for some j with 0 <= j < len(marked)) and all paths P from s to m; if no such path exists, let D = -1. Whenever minimum_distance returns a result r, r = D.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_1
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
        IsMinDist edges s.val marked r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
          IsMinDist edges s.val marked r.val) := by
    sorry

  /-- minimum_distance returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_2
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∃ r : Std.I64, minimum_distance n edges s marked = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∃ r : Std.I64, minimum_distance n edges s marked = ok r) := by
    sorry

  /-- Whenever minimum_distance returns a result r, r = -1 if and only if there is no path from s to any node in marked (paths as defined in spec_1).
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_3
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
        (r.val = -1 ↔ ∀ m ∈ markedVals marked, ¬ Reaches edges s.val m) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
          (r.val = -1 ↔ ∀ m ∈ markedVals marked, ¬ Reaches edges s.val m)) := by
    sorry

  /-- Whenever minimum_distance returns a result r with r != -1, there exists a marked node m and a simple path P from s to m (a path with no repeated node) such that weight(P) = r.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_4
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
        ∃ m ∈ markedVals marked, ∃ p : List Edge,
          IsSimplePathFrom edges s.val p m ∧ pathWeight p = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
          ∃ m ∈ markedVals marked, ∃ p : List Edge,
            IsSimplePathFrom edges s.val p m ∧ pathWeight p = r.val) := by
    sorry

  /-- Whenever minimum_distance returns a result r with r != -1, for every marked node m and every path P from s to m, weight(P) >= r.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_5
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
        ∀ m ∈ markedVals marked, ∀ p : List Edge, IsPathFrom edges s.val p m →
          r.val ≤ pathWeight p := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
          ∀ m ∈ markedVals marked, ∀ p : List Edge, IsPathFrom edges s.val p m →
            r.val ≤ pathWeight p) := by
    sorry

  /-- Whenever minimum_distance returns a result r with r != -1, r <= (n - 1) * Wmax, where Wmax is the maximum of edges[i][2] over all i with 0 <= i < len(edges).
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_6
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
        ∀ W : ℤ, IsMaxWeight edges W → r.val ≤ (n.val - 1) * W := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
          ∀ W : ℤ, IsMaxWeight edges W → r.val ≤ (n.val - 1) * W) := by
    sorry

  /-- Whenever minimum_distance returns a result r with r != -1, r >= Wmin, where Wmin is the minimum of edges[i][2] over all i with 0 <= i < len(edges).
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_7
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
        ∀ W : ℤ, IsMinWeight edges W → W ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r → r.val ≠ -1 →
          ∀ W : ℤ, IsMinWeight edges W → W ≤ r.val) := by
    sorry

  /-- Let r1 be the result of minimum_distance(n, edges, s, marked1) and r2 be the result of minimum_distance(n, edges, s, marked2). Whenever both results are returned, if r1 != -1 then r2 != -1 and r2 <= r1.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 0 <= s < n. For A in {marked1, marked2}: 1 <= len(A) <= n - 1; every A[j] satisfies 0 <= A[j] < n; entries of A are pairwise distinct; and s != A[j] for every j. The set of entries of marked1 is a subset of the set of entries of marked2. All numeric values are within the signed 64-bit range. -/
  theorem spec_8
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked1 marked2 : Slice Std.I64)
      (h1 : Pre n.val edges s.val marked1) (h2 : Pre n.val edges s.val marked2)
      (hsub : ∀ x ∈ markedVals marked1, x ∈ markedVals marked2) :
      ∀ r1 r2 : Std.I64,
        minimum_distance n edges s marked1 = ok r1 →
        minimum_distance n edges s marked2 = ok r2 →
        r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked1 marked2 : Slice Std.I64)
        (h1 : Pre n.val edges s.val marked1) (h2 : Pre n.val edges s.val marked2)
        (hsub : ∀ x ∈ markedVals marked1, x ∈ markedVals marked2), ∀ r1 r2 : Std.I64,
          minimum_distance n edges s marked1 = ok r1 →
          minimum_distance n edges s marked2 = ok r2 →
          r1.val ≠ -1 → r2.val ≠ -1 ∧ r2.val ≤ r1.val) := by
    sorry

  /-- Let r be the result for edges and r' be the result for edges'. Whenever both results are returned, r = r'.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. The list edges' is a permutation (same multiset of entries) of edges, and the same constraints hold with edges replaced by edges'. All numeric values are within the signed 64-bit range. -/
  theorem spec_9
      (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64)
      (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
      (hperm : (edgeList edges).Perm (edgeList edges')) :
      ∀ r r' : Std.I64,
        minimum_distance n edges s marked = ok r →
        minimum_distance n edges' s marked = ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64)
        (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
        (hperm : (edgeList edges).Perm (edgeList edges')), ∀ r r' : Std.I64,
          minimum_distance n edges s marked = ok r →
          minimum_distance n edges' s marked = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever minimum_distance returns a result r, if there exists a marked node m and a path P from s to m of weight L, then r != -1 and r <= L.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. All numeric values are within the signed 64-bit range. -/
  theorem spec_10
      (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (h : Pre n.val edges s.val marked) :
      ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
        ∀ (m L : ℤ) (p : List Edge), m ∈ markedVals marked →
          IsPathFrom edges s.val p m → pathWeight p = L →
          r.val ≠ -1 ∧ r.val ≤ L := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (h : Pre n.val edges s.val marked), ∀ r : Std.I64, minimum_distance n edges s marked = ok r →
          ∀ (m L : ℤ) (p : List Edge), m ∈ markedVals marked →
            IsPathFrom edges s.val p m → pathWeight p = L →
            r.val ≠ -1 ∧ r.val ≤ L) := by
    sorry

  /-- Let r be the result for edges and r' be the result for edges'. Whenever both results are returned, if r = -1 then r' = -1, and if r != -1 then r' = c * r.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. c is a positive integer; edges' is obtained from edges by replacing each [u,v,w] with [u,v,c*w]; every new weight is at most 10^6; and edges' satisfies the same constraints. All numeric values are within the signed 64-bit range. -/
  theorem spec_11
      (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64) (c : ℤ)
      (hc : 0 < c)
      (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
      (hlen : edges'.val.length = edges.val.length)
      (hscale : ∀ (i : ℕ) (hi : i < edges.val.length) (hi' : i < edges'.val.length)
        (u v w : ℤ), (edges.val.get ⟨i, hi⟩).val.map IScalar.val = [u, v, w] →
        (edges'.val.get ⟨i, hi'⟩).val.map IScalar.val = [u, v, c * w]) :
      ∀ r r' : Std.I64,
        minimum_distance n edges s marked = ok r →
        minimum_distance n edges' s marked = ok r' →
        (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val = c * r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64) (c : ℤ)
        (hc : 0 < c)
        (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
        (hlen : edges'.val.length = edges.val.length)
        (hscale : ∀ (i : ℕ) (hi : i < edges.val.length) (hi' : i < edges'.val.length)
          (u v w : ℤ), (edges.val.get ⟨i, hi⟩).val.map IScalar.val = [u, v, w] →
          (edges'.val.get ⟨i, hi'⟩).val.map IScalar.val = [u, v, c * w]), ∀ r r' : Std.I64,
          minimum_distance n edges s marked = ok r →
          minimum_distance n edges' s marked = ok r' →
          (r.val = -1 → r'.val = -1) ∧ (r.val ≠ -1 → r'.val = c * r.val)) := by
    sorry

  /-- Let r be the result for edges and r' be the result for edges'. Whenever both results are returned, if r != -1 then r' != -1 and r' <= r.
    Preconditions: 2 <= n <= 500; 1 <= len(edges) <= 10^4; for every i with 0 <= i < len(edges), edges[i] has length 3, and if edges[i] = [u, v, w] then 0 <= u < n, 0 <= v < n, u != v, and 1 <= w <= 10^6; 1 <= len(marked) <= n - 1; 0 <= s < n; for every j with 0 <= j < len(marked), 0 <= marked[j] < n; marked entries are pairwise distinct; and s != marked[j] for every j. Every edge triple that occurs in edges also occurs in edges', and edges' satisfies the same constraints. All numeric values are within the signed 64-bit range. -/
  theorem spec_12
      (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
      (marked : Slice Std.I64)
      (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
      (hsub : ∀ e ∈ edgeList edges, e ∈ edgeList edges') :
      ∀ r r' : Std.I64,
        minimum_distance n edges s marked = ok r →
        minimum_distance n edges' s marked = ok r' →
        r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (s : Std.I64)
        (marked : Slice Std.I64)
        (h : Pre n.val edges s.val marked) (h' : Pre n.val edges' s.val marked)
        (hsub : ∀ e ∈ edgeList edges, e ∈ edgeList edges'), ∀ r r' : Std.I64,
          minimum_distance n edges s marked = ok r →
          minimum_distance n edges' s marked = ok r' →
          r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
    sorry

  end AegisSpec.MinimumDistance
