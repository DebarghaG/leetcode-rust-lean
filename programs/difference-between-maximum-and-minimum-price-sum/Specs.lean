import Aegis.MaxOutput.Code.Funs

/-!
# Specifications of `Aegis.MaxOutput.max_output`

LeetCode problem `difference-between-maximum-and-minimum-price-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxOutput

  def priceList (price : Slice I64) : List ℤ := price.val.map (fun x => x.val)

  def edgeVerts (edges : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    edges.val.map (fun v => v.val.map (fun x => x.val))

  def priceAt (P : List ℤ) (i : ℤ) : ℤ := P.getD i.toNat 0

  def numNodes (n : I64) : ℕ := n.val.toNat

  def IsNode (n : I64) (i : ℤ) : Prop := 0 ≤ i ∧ i < n.val

  def maxList (l : List ℤ) : ℤ := l.max?.getD 0

  def minList (l : List ℤ) : ℤ := l.min?.getD 0

  def Adj (E : List (List ℤ)) (a b : ℤ) : Prop :=
    a ≠ b ∧ ∃ e ∈ E, e = [a, b] ∨ e = [b, a]

  def ChainAdj (E : List (List ℤ)) (l : List ℤ) : Prop :=
    ∀ p ∈ l.zip l.tail, Adj E p.1 p.2

  def IsSimplePath (E : List (List ℤ)) (u v : ℤ) (l : List ℤ) : Prop :=
    l.head? = some u ∧ l.getLast? = some v ∧ l.Nodup ∧ ChainAdj E l

  def IsCycle (E : List (List ℤ)) (l : List ℤ) : Prop :=
    3 ≤ l.length ∧ l.Nodup ∧ ChainAdj E l ∧
      ∃ a b : ℤ, l.getLast? = some a ∧ l.head? = some b ∧ Adj E a b

  def Acyclic (E : List (List ℤ)) : Prop := ∀ l : List ℤ, ¬ IsCycle E l

  def Connected (E : List (List ℤ)) (n : ℕ) : Prop :=
    ∀ u v : ℤ, 0 ≤ u → u < ↑n → 0 ≤ v → v < ↑n → ∃ l : List ℤ, IsSimplePath E u v l

  def edgeCount (E : List (List ℤ)) (a b : ℤ) : ℕ :=
    (E.filter (fun e => decide (e = [a, b] ∨ e = [b, a]))).length

  def degree (E : List (List ℤ)) (w : ℤ) : ℕ :=
    (E.filter (fun e => decide (w ∈ e))).length

  def IsLeaf (E : List (List ℤ)) (w : ℤ) : Prop := degree E w = 1

  def SimpleEdges (E : List (List ℤ)) (n : ℕ) : Prop :=
    (∀ e ∈ E, e.length = 2) ∧
      (∀ e ∈ E, ∀ a b : ℤ, e = [a, b] → 0 ≤ a ∧ a < ↑n ∧ 0 ≤ b ∧ b < ↑n ∧ a ≠ b) ∧
      (∀ a b : ℤ, edgeCount E a b ≤ 1)

  def IsTree (E : List (List ℤ)) (n : ℕ) : Prop :=
    SimpleEdges E n ∧ Connected E n ∧ Acyclic E

  def NodesBounds (n : I64) : Prop := 1 ≤ n.val ∧ n.val ≤ 100000

  def Lengths (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64) : Prop :=
    (priceList price).length = numNodes n ∧ (edgeVerts edges).length = numNodes n - 1

  def PriceBounds (price : Slice I64) : Prop :=
    ∀ p ∈ priceList price, 1 ≤ p ∧ p ≤ 100000

  def ProblemConstraints (n : I64) (edges : Slice (alloc.vec.Vec I64))
      (price : Slice I64) : Prop :=
    NodesBounds n ∧ Lengths n edges price ∧ IsTree (edgeVerts edges) (numNodes n) ∧
      PriceBounds price

  def pathWeight (P : List ℤ) (l : List ℤ) : ℤ := (l.map (priceAt P)).sum

  def IsPathSum (P : List ℤ) (E : List (List ℤ)) (u v : ℤ) (s : ℤ) : Prop :=
    ∃ l : List ℤ, IsSimplePath E u v l ∧ s = pathWeight P l

  noncomputable def pathSum (P : List ℤ) (E : List (List ℤ)) (u v : ℤ) : ℤ :=
    by
      classical
      exact
        if h : ∃ l : List ℤ, IsSimplePath E u v l then pathWeight P (Classical.choose h)
        else 0

  def maxOverNodes (n : ℕ) (f : ℤ → ℤ) : ℤ := maxList ((List.range n).map fun k => f (k : ℤ))

  def minOverNodes (n : ℕ) (f : ℤ → ℤ) : ℤ := minList ((List.range n).map fun k => f (k : ℤ))

  def maxOverNodesNe (n : ℕ) (c : ℤ) (f : ℤ → ℤ) : ℤ :=
    maxList (((List.range n).filter fun k => decide ((k : ℤ) ≠ c)).map fun k => f (k : ℤ))

  noncomputable def cost (P : List ℤ) (E : List (List ℤ)) (n : ℕ) (s : ℤ) : ℤ :=
    maxOverNodes n (fun v => pathSum P E s v) - minOverNodes n (fun v => pathSum P E s v)

  def IsDiameterEdges (E : List (List ℤ)) (D : ℕ) : Prop :=
    (∃ u v : ℤ, ∃ l : List ℤ, IsSimplePath E u v l ∧ l.length = D + 1) ∧
      (∀ u v : ℤ, ∀ l : List ℤ, IsSimplePath E u v l → l.length ≤ D + 1)

  noncomputable def diameterEdges (E : List (List ℤ)) : ℕ :=
    by
      classical
      exact if h : ∃ D, IsDiameterEdges E D then Classical.choose h else 0

  noncomputable def leaves (E : List (List ℤ)) (n : ℕ) : List ℤ :=
    by
      classical
      exact ((List.range n).filter fun k => decide (IsLeaf E (k : ℤ))).map fun k => (k : ℤ)

  noncomputable def maxOverLeaves (E : List (List ℤ)) (n : ℕ) (f : ℤ → ℤ → ℤ) : ℤ :=
    maxList ((leaves E n).map fun u => maxList ((leaves E n).map fun v => f u v))

  def IsPermutationOnRange (n : ℕ) (pi : ℤ → ℤ) : Prop :=
    (∀ i : ℤ, 0 ≤ i → i < ↑n → 0 ≤ pi i ∧ pi i < ↑n) ∧
      (∀ i j : ℤ, 0 ≤ i → i < ↑n → 0 ≤ j → j < ↑n → pi i = pi j → i = j)

  /-- Whenever max_output n edges price returns a result r, r equals max_{0 <= s < n} cost(s), where for a node s, cost(s) = max_{0 <= v < n} pathSum(s,v) - min_{0 <= v < n} pathSum(s,v), and pathSum(u,v) is the sum of price[w] over all nodes w on the unique simple path between u and v in the tree represented by edges (the path includes both endpoints).
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = maxOverNodes (numNodes n)
          (fun s => cost (priceList price) (edgeVerts edges) (numNodes n) s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = maxOverNodes (numNodes n)
            (fun s => cost (priceList price) (edgeVerts edges) (numNodes n) s)) := by
    sorry

  /-- The call max_output n edges price returns a Result.ok value; it does not panic, access an out-of-range index, or overflow a signed 64-bit integer.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∃ r : I64, Aegis.MaxOutput.max_output n edges price = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∃ r : I64, Aegis.MaxOutput.max_output n edges price = ok r) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r >= 0.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r <= (sum_{i=0}^{n-1} price[i]) - min_{0 <= i < n} price[i].
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val ≤ (priceList price).sum - minList (priceList price) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val ≤ (priceList price).sum - minList (priceList price)) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r >= max_{0 <= i < n} price[i].
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally n >= 2. -/
  theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        maxList (priceList price) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          maxList (priceList price) ≤ r.val) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = 0.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally n = 1. -/
  theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : n.val = 1) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r → r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : n.val = 1), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r → r.val = 0) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = max(price[0], price[1]).
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally n = 2. -/
  theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : n.val = 2) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = max (priceAt (priceList price) 0) (priceAt (priceList price) 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : n.val = 2), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = max (priceAt (priceList price) 0) (priceAt (priceList price) 1)) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = p * D, where D is the maximum number of edges on a simple path between two nodes of the tree; if n = 1, D = 0.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally there is an integer p such that price[i] = p for every i with 0 <= i < n. -/
  theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (p : ℤ)
      (hp : ∀ i : ℤ, IsNode n i → priceAt (priceList price) i = p) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = p * ((diameterEdges (edgeVerts edges) : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (p : ℤ)
        (hp : ∀ i : ℤ, IsNode n i → priceAt (priceList price) i = p), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = p * ((diameterEdges (edgeVerts edges) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = (sum_{i=0}^{n-1} price[i]) - min(price[e1], price[e2]).
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally n >= 2 and the tree is a path, with e1 and e2 its two nodes of degree 1. -/
  theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val) (e1 e2 : ℤ)
      (he1 : IsNode n e1) (he2 : IsNode n e2) (hne : e1 ≠ e2)
      (hl1 : IsLeaf (edgeVerts edges) e1) (hl2 : IsLeaf (edgeVerts edges) e2)
      (htwo : ∀ w : ℤ, IsNode n w → IsLeaf (edgeVerts edges) w → w = e1 ∨ w = e2) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = (priceList price).sum - min (priceAt (priceList price) e1)
          (priceAt (priceList price) e2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val) (e1 e2 : ℤ)
        (he1 : IsNode n e1) (he2 : IsNode n e2) (hne : e1 ≠ e2)
        (hl1 : IsLeaf (edgeVerts edges) e1) (hl2 : IsLeaf (edgeVerts edges) e2)
        (htwo : ∀ w : ℤ, IsNode n w → IsLeaf (edgeVerts edges) w → w = e1 ∨ w = e2), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = (priceList price).sum - min (priceAt (priceList price) e1)
            (priceAt (priceList price) e2)) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = price[c] + max_{0 <= i < n, i != c} price[i].
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000; additionally n >= 3 and the tree is a star, with a center node c adjacent to every other node. -/
  theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : 3 ≤ n.val) (c : ℤ)
      (hc : IsNode n c)
      (hstar : ∀ w : ℤ, IsNode n w → w ≠ c → Adj (edgeVerts edges) c w) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = priceAt (priceList price) c +
          maxOverNodesNe (numNodes n) c (priceAt (priceList price)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : 3 ≤ n.val) (c : ℤ)
        (hc : IsNode n c)
        (hstar : ∀ w : ℤ, IsNode n w → w ≠ c → Adj (edgeVerts edges) c w), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = priceAt (priceList price) c +
            maxOverNodesNe (numNodes n) c (priceAt (priceList price))) := by
    sorry

  /-- If max_output n edges price returns r and max_output n edges' price returns r', then r = r'.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. Additionally edges' is a slice of length n - 1 representing the same undirected tree as edges, for example any permutation of the entries of edges with each pair possibly reversed, and all common constraints hold for edges' in place of edges. -/
  theorem spec_11 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
      (price : Slice I64) (h : ProblemConstraints n edges price)
      (h' : ProblemConstraints n edges' price)
      (hsame : ∀ a b : ℤ, Adj (edgeVerts edges) a b ↔ Adj (edgeVerts edges') a b) :
      ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        Aegis.MaxOutput.max_output n edges' price = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
        (price : Slice I64) (h : ProblemConstraints n edges price)
        (h' : ProblemConstraints n edges' price)
        (hsame : ∀ a b : ℤ, Adj (edgeVerts edges) a b ↔ Adj (edgeVerts edges') a b), ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          Aegis.MaxOutput.max_output n edges' price = ok r' → r.val = r'.val) := by
    sorry

  /-- If max_output n edges price returns r and max_output n edges' price' returns r', then r = r'.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. Additionally pi is a bijection from {0,...,n-1} to itself; edges' is a slice of length n - 1 representing the tree obtained from edges by replacing each edge [a,b] by [pi(a),pi(b)] in some order; price' is an array of length n with price'[pi(j)] = price[j] for every j; and all common constraints hold for edges' and price'. -/
  theorem spec_12 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
      (price price' : Slice I64) (h : ProblemConstraints n edges price)
      (h' : ProblemConstraints n edges' price') (pi : ℤ → ℤ)
      (hpi : IsPermutationOnRange (numNodes n) pi)
      (hedges : ∀ a b : ℤ, IsNode n a → IsNode n b →
        (Adj (edgeVerts edges') (pi a) (pi b) ↔ Adj (edgeVerts edges) a b))
      (hprice : ∀ j : ℤ, IsNode n j → priceAt (priceList price') (pi j) =
        priceAt (priceList price) j) :
      ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        Aegis.MaxOutput.max_output n edges' price' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64))
        (price price' : Slice I64) (h : ProblemConstraints n edges price)
        (h' : ProblemConstraints n edges' price') (pi : ℤ → ℤ)
        (hpi : IsPermutationOnRange (numNodes n) pi)
        (hedges : ∀ a b : ℤ, IsNode n a → IsNode n b →
          (Adj (edgeVerts edges') (pi a) (pi b) ↔ Adj (edgeVerts edges) a b))
        (hprice : ∀ j : ℤ, IsNode n j → priceAt (priceList price') (pi j) =
          priceAt (priceList price) j), ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          Aegis.MaxOutput.max_output n edges' price' = ok r' → r.val = r'.val) := by
    sorry

  /-- If max_output n edges price returns r and max_output n edges price' returns r', then r' = c * r.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. Additionally c is an integer with c >= 1, price' is an array of length n with price'[i] = c * price[i] for every i, and every price'[i] is in [1,100000]. -/
  theorem spec_13 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price price' : Slice I64)
      (h : ProblemConstraints n edges price) (c : ℤ) (hc : 1 ≤ c)
      (hlen : (priceList price').length = numNodes n)
      (hprices : ∀ i : ℤ, IsNode n i → priceAt (priceList price') i =
        c * priceAt (priceList price) i)
      (hbounds : ∀ p ∈ priceList price', 1 ≤ p ∧ p ≤ 100000) :
      ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        Aegis.MaxOutput.max_output n edges price' = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price price' : Slice I64)
        (h : ProblemConstraints n edges price) (c : ℤ) (hc : 1 ≤ c)
        (hlen : (priceList price').length = numNodes n)
        (hprices : ∀ i : ℤ, IsNode n i → priceAt (priceList price') i =
          c * priceAt (priceList price) i)
        (hbounds : ∀ p ∈ priceList price', 1 ≤ p ∧ p ≤ 100000), ∀ r r' : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          Aegis.MaxOutput.max_output n edges price' = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, there exist nodes s and v with 0 <= s,v < n such that r = pathSum(s,v) - price[s], where pathSum(u,v) is the sum of price[w] over the unique simple path between u and v in the tree represented by edges.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_14 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        ∃ s v : ℤ, IsNode n s ∧ IsNode n v ∧
          r.val = pathSum (priceList price) (edgeVerts edges) s v -
            priceAt (priceList price) s := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          ∃ s v : ℤ, IsNode n s ∧ IsNode n v ∧
            r.val = pathSum (priceList price) (edgeVerts edges) s v -
              priceAt (priceList price) s) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, for every pair of nodes s and v with 0 <= s,v < n, pathSum(s,v) - price[s] <= r, where pathSum(u,v) is the sum of price[w] over the unique simple path between u and v in the tree represented by edges.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; for every i with 0 <= i < len(edges), edges[i] has length 2, its two entries are distinct integers in [0, n-1], and the undirected graph on vertices {0,...,n-1} having these edge pairs is a tree (connected and acyclic, with no duplicate edge pairs); for every i with 0 <= i < n, 1 <= price[i] <= 100000. -/
  theorem spec_15 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        ∀ s v : ℤ, IsNode n s → IsNode n v →
          pathSum (priceList price) (edgeVerts edges) s v - priceAt (priceList price) s ≤
            r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          ∀ s v : ℤ, IsNode n s → IsNode n v →
            pathSum (priceList price) (edgeVerts edges) s v - priceAt (priceList price) s ≤
              r.val) := by
    sorry

  /-- Whenever max_output n edges price returns a result r, r = max_{u in L, v in L} (pathSum(u,v) - min(price[u], price[v])), where pathSum(u,v) is the sum of price[w] over all nodes w on the unique simple path between u and v, including both endpoints. Equivalently, r = max_{s in L, v in L} (pathSum(s,v) - price[s]). For n = 1, r = 0.
    Preconditions: Problem constraints hold: n is an integer with 1 <= n <= 100000; len(price) = n and len(edges) = n - 1; edges represents a valid tree on vertices {0,...,n-1}; for every i with 0 <= i < n, 1 <= price[i] <= 100000. Additionally n >= 2, and L = {i | node i has degree 1 in the tree represented by edges} is the set of leaves. -/
  theorem spec_16 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
      (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val) :
      ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
        r.val = maxOverLeaves (edgeVerts edges) (numNodes n)
          (fun u v => pathSum (priceList price) (edgeVerts edges) u v -
            min (priceAt (priceList price) u) (priceAt (priceList price) v)) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (price : Slice I64)
        (h : ProblemConstraints n edges price) (hn : 2 ≤ n.val), ∀ r : I64, Aegis.MaxOutput.max_output n edges price = ok r →
          r.val = maxOverLeaves (edgeVerts edges) (numNodes n)
            (fun u v => pathSum (priceList price) (edgeVerts edges) u v -
              min (priceAt (priceList price) u) (priceAt (priceList price) v))) := by
    sorry

  end AegisSpec.MaxOutput
