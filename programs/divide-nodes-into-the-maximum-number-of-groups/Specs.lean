import Aegis.MagnificentSets.Code.Funs

/-!
# Specifications of `Aegis.MagnificentSets.magnificent_sets`

LeetCode problem `divide-nodes-into-the-maximum-number-of-groups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MagnificentSets

  namespace AegisSpec.MagnificentSets

  def edgeEntries (edges : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    edges.val.map (fun v => v.val.map (fun x => x.val))

  def upair (a b : ℤ) : ℤ × ℤ := if a ≤ b then (a, b) else (b, a)

  def edgePairsOpt (edges : Slice (alloc.vec.Vec I64)) : List (Option (ℤ × ℤ)) :=
    (edgeEntries edges).map (fun e =>
      match e with
      | [a, b] => some (upair a b)
      | _ => none)

  def Vertex (n : I64) (v : ℤ) : Prop := 1 ≤ v ∧ v ≤ n.val

  def Adj (n : I64) (edges : Slice (alloc.vec.Vec I64)) (a b : ℤ) : Prop :=
    Vertex n a ∧ Vertex n b ∧ ([a, b] ∈ edgeEntries edges ∨ [b, a] ∈ edgeEntries edges)

  def Reach (n : I64) (edges : Slice (alloc.vec.Vec I64)) : ℤ → ℤ → Prop :=
    Relation.ReflTransGen (Adj n edges)

  def Walk (n : I64) (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) : ℕ → Prop
    | 0 => u = v
    | k + 1 => ∃ w, Walk n edges u w k ∧ Adj n edges w v

  def Dist (n : I64) (edges : Slice (alloc.vec.Vec I64)) (u v : ℤ) (d : ℕ) : Prop :=
    Walk n edges u v d ∧ ∀ d' : ℕ, Walk n edges u v d' → d ≤ d'

  def Comp (n : I64) (edges : Slice (alloc.vec.Vec I64)) (v : ℤ) : Set ℤ :=
    {u | Vertex n u ∧ Reach n edges u v}

  def ComponentDiam (n : I64) (edges : Slice (alloc.vec.Vec I64)) (v : ℤ) (d : ℕ) : Prop :=
    (∀ u w : ℤ, u ∈ Comp n edges v → w ∈ Comp n edges v →
        ∀ dd : ℕ, Dist n edges u w dd → dd ≤ d) ∧
      (∃ u w : ℤ, u ∈ Comp n edges v ∧ w ∈ Comp n edges v ∧
        ∃ dd : ℕ, Dist n edges u w dd ∧ dd = d)

  def Reps (n : I64) (edges : Slice (alloc.vec.Vec I64)) (L : List ℤ) : Prop :=
    L.Nodup ∧
      (∀ v ∈ L, Vertex n v) ∧
      (∀ v : ℤ, Vertex n v → ∃ u ∈ L, Reach n edges u v) ∧
      (∀ u ∈ L, ∀ w ∈ L, Reach n edges u w → w = u)

  def SumComponentDiams (n : I64) (edges : Slice (alloc.vec.Vec I64)) (L : List ℤ) (s : ℤ) : Prop :=
    ∃ diamOf : ℤ → ℕ, (∀ v ∈ L, ComponentDiam n edges v (diamOf v)) ∧
      s = (L.map (fun v => (diamOf v : ℤ) + 1)).sum

  def Bipartite (n : I64) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ c : ℤ → ℤ, (∀ v : ℤ, Vertex n v → c v = 0 ∨ c v = 1) ∧
      ∀ a b : ℤ, Adj n edges a b → c a ≠ c b

  def HasOddCycle (n : I64) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ v : ℤ, Vertex n v ∧ ∃ k : ℕ, Walk n edges v v (2 * k + 1)

  def IsPathComp (n : I64) (edges : Slice (alloc.vec.Vec I64)) (v : ℤ) : Prop :=
    ∃ (s : ℕ) (vs : Fin s → ℤ),
      Function.Injective vs ∧
        (∀ i : Fin s, vs i ∈ Comp n edges v) ∧
        (∀ u : ℤ, u ∈ Comp n edges v → ∃ i : Fin s, vs i = u) ∧
        (∀ i j : Fin s,
          Adj n edges (vs i) (vs j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))

  def IsValidDivision (n : I64) (edges : Slice (alloc.vec.Vec I64)) (m : ℤ) (g : ℤ → ℤ) : Prop :=
    (∀ v : ℤ, Vertex n v → 1 ≤ g v ∧ g v ≤ m) ∧
      (∀ j : ℤ, 1 ≤ j → j ≤ m → ∃ v : ℤ, Vertex n v ∧ g v = j) ∧
      (∀ a b : ℤ, Adj n edges a b → |g a - g b| = 1)

  def HasValidDivision (n : I64) (edges : Slice (alloc.vec.Vec I64)) (m : ℤ) : Prop :=
    ∃ g : ℤ → ℤ, IsValidDivision n edges m g

  def ValidInput (n : I64) (edges : Slice (alloc.vec.Vec I64)) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 500 ∧
      1 ≤ edges.length ∧ edges.length ≤ 10000 ∧
      (∀ e ∈ edgeEntries edges,
        e.length = 2 ∧ ∀ a b : ℤ, e = [a, b] → Vertex n a ∧ Vertex n b ∧ a ≠ b) ∧
      (edgePairsOpt edges).Nodup

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. A valid division into m groups is a function g from {1,...,n} to {1,...,m} such that every group j in {1,...,m} is nonempty (there exists v with g(v)=j) and for every edge {a,b} of G, |g(a)-g(b)| = 1. Whenever magnificent_sets returns a result r: if there exists a valid division into some m >= 1, then r is the largest such m; otherwise r = -1.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) :
      ((∃ m : ℤ, 1 ≤ m ∧ HasValidDivision n edges m) →
        HasValidDivision n edges r.val ∧
          ∀ m : ℤ, 1 ≤ m → HasValidDivision n edges m → m ≤ r.val) ∧
      ((¬ ∃ m : ℤ, 1 ≤ m ∧ HasValidDivision n edges m) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r), ((∃ m : ℤ, 1 ≤ m ∧ HasValidDivision n edges m) →
          HasValidDivision n edges r.val ∧
            ∀ m : ℤ, 1 ≤ m → HasValidDivision n edges m → m ≤ r.val) ∧
        ((¬ ∃ m : ℤ, 1 ≤ m ∧ HasValidDivision n edges m) → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, magnificent_sets returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges) :
      ∃ r : I64, magnificent_sets n edges = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges), ∃ r : I64, magnificent_sets n edges = Result.ok r) := by
    sorry

  /-- Whenever magnificent_sets returns a result r, either r = -1 or 1 <= r <= n.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) :
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val)) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r, r = -1 if and only if G is not bipartite. Equivalently, r = -1 if and only if G contains a cycle of odd length.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) :
      (r.val = -1 ↔ ¬ Bipartite n edges) ∧ (r.val = -1 ↔ HasOddCycle n edges) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r), (r.val = -1 ↔ ¬ Bipartite n edges) ∧ (r.val = -1 ↔ HasOddCycle n edges)) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r and G is bipartite, let C_1,...,C_k be the connected components of G. For each component C, let diam(C) be the maximum, over all ordered pairs of vertices u,v in C, of the length of a shortest u-v path in G (so diam(C)=0 if C is a singleton). Then r = sum_{j=1..k} (diam(C_j) + 1).
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hbip : Bipartite n edges) :
      ∃ L : List ℤ, Reps n edges L ∧ SumComponentDiams n edges L r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hbip : Bipartite n edges), ∃ L : List ℤ, Reps n edges L ∧ SumComponentDiams n edges L r.val) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r with r >= 1, there exists a valid division of {1,...,n} into exactly r nonempty groups, meaning a function g from {1,...,n} to {1,...,r} such that every group is nonempty and for every edge {a,b} of G, |g(a)-g(b)| = 1.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : 1 ≤ r.val) :
      ∃ g : ℤ → ℤ, IsValidDivision n edges r.val g := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : 1 ≤ r.val), ∃ g : ℤ → ℤ, IsValidDivision n edges r.val g) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r with r >= 1, for every integer m > r there is no valid division of {1,...,n} into m nonempty groups satisfying the edge condition: there is no function g from {1,...,n} to {1,...,m} such that every group is nonempty and for every edge {a,b} of G, |g(a)-g(b)| = 1.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : 1 ≤ r.val) :
      ∀ m : ℤ, r.val < m → ¬ HasValidDivision n edges m := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : 1 ≤ r.val), ∀ m : ℤ, r.val < m → ¬ HasValidDivision n edges m) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns r = -1, for every integer m >= 1 there is no valid division of {1,...,n} into m nonempty groups satisfying the edge condition: there is no function g from {1,...,n} to {1,...,m} such that every group is nonempty and for every edge {a,b} of G, |g(a)-g(b)| = 1.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : r.val = -1) :
      ∀ m : ℤ, 1 ≤ m → ¬ HasValidDivision n edges m := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : r.val = -1), ∀ m : ℤ, 1 ≤ m → ¬ HasValidDivision n edges m) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r with r >= 1, if G has k connected components, then r >= k.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : 1 ≤ r.val) :
      ∃ L : List ℤ, Reps n edges L ∧ (L.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : 1 ≤ r.val), ∃ L : List ℤ, Reps n edges L ∧ (L.length : ℤ) ≤ r.val) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r with r >= 1, for every connected component C of G, r >= diam(C) + 1, where diam(C) is the maximum shortest-path distance between two vertices of C in G, with diam(C)=0 for a singleton component.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : 1 ≤ r.val) :
      ∀ v : ℤ, Vertex n v → ∀ d : ℕ, ComponentDiam n edges v d → (d : ℤ) + 1 ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : 1 ≤ r.val), ∀ v : ℤ, Vertex n v → ∀ d : ℕ, ComponentDiam n edges v d → (d : ℤ) + 1 ≤ r.val) := by
    sorry

  /-- Let G be the undirected graph on vertices {1,...,n} induced by edges. Consider the call magnificent_sets(n, edges) and the call magnificent_sets(n+k, edges), where in the second call the vertices n+1,...,n+k are isolated because all edge entries are at most n. If the first call returns r and the second returns r', then: if G is bipartite, r' = r + k; if G is not bipartite, r' = r = -1.
    Preconditions: n and k are integers with 1 <= n <= 500, k >= 0, and n+k <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_11 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      (k : ℤ) (hk0 : 0 ≤ k) (hnk : n.val + k ≤ 500) {n' : I64} (hn' : n'.val = n.val + k)
      {r r' : I64} (hr : magnificent_sets n edges = .ok r)
      (hr' : magnificent_sets n' edges = .ok r) :
      (Bipartite n edges → r'.val = r.val + k) ∧
        (¬ Bipartite n edges → r'.val = -1 ∧ r.val = -1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        (k : ℤ) (hk0 : 0 ≤ k) (hnk : n.val + k ≤ 500) {n' : I64} (hn' : n'.val = n.val + k)
        {r r' : I64} (hr : magnificent_sets n edges = Result.ok r)
        (hr' : magnificent_sets n' edges = Result.ok r), (Bipartite n edges → r'.val = r.val + k) ∧
          (¬ Bipartite n edges → r'.val = -1 ∧ r.val = -1)) := by
    sorry

  /-- For every such permutation pi and corresponding edge slice edges', if magnificent_sets(n, edges) returns r and magnificent_sets(n, edges') returns r', then r = r'.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. Also pi is a permutation of {1,...,n}, and edges' is obtained from edges by replacing each entry [a,b] with [pi(a),pi(b)] in the same list order. -/
  theorem spec_12 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (pi : ℤ → ℤ)
      (h : ValidInput n edges)
      (hperm : (∀ v : ℤ, Vertex n v → Vertex n (pi v)) ∧
        ∀ u w : ℤ, Vertex n u → Vertex n w → pi u = pi w → u = w)
      (hedges' : edgeEntries edges' = (edgeEntries edges).map (fun e => e.map pi))
      {r r' : I64} (hr : magnificent_sets n edges = .ok r)
      (hr' : magnificent_sets n edges' = .ok r') : r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (pi : ℤ → ℤ)
        (h : ValidInput n edges)
        (hperm : (∀ v : ℤ, Vertex n v → Vertex n (pi v)) ∧
          ∀ u w : ℤ, Vertex n u → Vertex n w → pi u = pi w → u = w)
        (hedges' : edgeEntries edges' = (edgeEntries edges).map (fun e => e.map pi))
        {r r' : I64} (hr : magnificent_sets n edges = Result.ok r)
        (hr' : magnificent_sets n edges' = Result.ok r'), r = r') := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r, r = n if and only if every connected component of G is a path, where a single vertex counts as a path of length 0 and a path means a graph whose vertices can be ordered v_0,...,v_{s-1} so that its edges are exactly {v_i,v_{i+1}} for 0 <= i < s-1.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_13 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) :
      r.val = n.val ↔ ∀ v : ℤ, Vertex n v → IsPathComp n edges v := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r), r.val = n.val ↔ ∀ v : ℤ, Vertex n v → IsPathComp n edges v) := by
    sorry

  /-- Let G be the undirected graph with vertex set {1,...,n} and an edge between a and b iff [a,b] or [b,a] occurs in edges. Whenever magnificent_sets returns a result r with r >= 1, there exists a valid division g from {1,...,n} to {1,...,r} into exactly r nonempty groups such that, for every connected component C of G, the set {g(v) | v in C} is an interval of integers of cardinality diam(C)+1, where diam(C) is the maximum shortest-path distance between two vertices of C (0 for a singleton); these intervals are pairwise disjoint and their union is {1,...,r}.
    Preconditions: n is a 64-bit integer with 1 <= n <= 500; edges is a slice of vectors of 64-bit integers with 1 <= len(edges) <= 10000; every edges[i] has length 2; if edges[i] = [a,b] then 1 <= a,b <= n and a != b; and no unordered pair {a,b} occurs in more than one entry. -/
  theorem spec_14 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
      {r : I64} (hr : magnificent_sets n edges = .ok r) (hr1 : 1 ≤ r.val) :
      ∃ g : ℤ → ℤ, IsValidDivision n edges r.val g ∧
        (∀ v : ℤ, Vertex n v → ∀ d : ℕ, ComponentDiam n edges v d →
          ∃ lo : ℤ, (∀ u : ℤ, u ∈ Comp n edges v → lo ≤ g u ∧ g u ≤ lo + (d : ℤ)) ∧
            (∀ j : ℤ, lo ≤ j → j ≤ lo + (d : ℤ) →
              ∃ u : ℤ, u ∈ Comp n edges v ∧ g u = j)) ∧
        (∀ u w : ℤ, Vertex n u → Vertex n w → g u = g w →
          Reach n edges u w ∨ Reach n edges w u) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (h : ValidInput n edges)
        {r : I64} (hr : magnificent_sets n edges = Result.ok r) (hr1 : 1 ≤ r.val), ∃ g : ℤ → ℤ, IsValidDivision n edges r.val g ∧
          (∀ v : ℤ, Vertex n v → ∀ d : ℕ, ComponentDiam n edges v d →
            ∃ lo : ℤ, (∀ u : ℤ, u ∈ Comp n edges v → lo ≤ g u ∧ g u ≤ lo + (d : ℤ)) ∧
              (∀ j : ℤ, lo ≤ j → j ≤ lo + (d : ℤ) →
                ∃ u : ℤ, u ∈ Comp n edges v ∧ g u = j)) ∧
          (∀ u w : ℤ, Vertex n u → Vertex n w → g u = g w →
            Reach n edges u w ∨ Reach n edges w u)) := by
    sorry

  end AegisSpec.MagnificentSets
