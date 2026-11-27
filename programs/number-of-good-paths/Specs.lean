import Aegis.NumberOfGoodPaths.Code.Funs

/-!
# Specifications of `Aegis.NumberOfGoodPaths.number_of_good_paths`

LeetCode problem `number-of-good-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.NumberOfGoodPaths

namespace AegisSpec.NumberOfGoodPaths

def size (vals : Slice (Std.I64)) : ℕ := (Slice.len vals).val

def valAtN (vals : Slice (Std.I64)) (i : ℕ) : ℤ :=
  ((vals.val[i]?).map (fun x => IScalar.val x)).getD 0

def valAt (vals : Slice (Std.I64)) (i : ℤ) : ℤ := valAtN vals i.toNat

def edgeAt (edges : Slice (alloc.vec.Vec (Std.I64))) (j : ℕ) : Option (List ℤ) :=
  (edges.val[j]?).map (fun e => e.val.map (fun x => IScalar.val x))

def edgeEnd (edges : Slice (alloc.vec.Vec (Std.I64))) (j k : ℕ) : ℤ :=
  ((edgeAt edges j).bind (fun e => e[k]?)).getD 0

def edgeLen (edges : Slice (alloc.vec.Vec (Std.I64))) (j : ℕ) : ℕ :=
  ((edgeAt edges j).map List.length).getD 0

def adj (edges : Slice (alloc.vec.Vec (Std.I64))) (u v : ℤ) : Prop :=
  ∃ j : ℕ, j < edges.val.length ∧
    ((edgeEnd edges j 0 = u ∧ edgeEnd edges j 1 = v) ∨
     (edgeEnd edges j 0 = v ∧ edgeEnd edges j 1 = u))

def walk (edges : Slice (alloc.vec.Vec (Std.I64))) : List ℤ → Prop
  | [] => False
  | [_] => True
  | x :: y :: rest => adj edges x y ∧ walk edges (y :: rest)

def IsSimplePath (edges : Slice (alloc.vec.Vec (Std.I64))) (p : List ℤ) : Prop :=
  walk edges p ∧ p.Nodup

def IsSimplePathFromTo (edges : Slice (alloc.vec.Vec (Std.I64))) (u v : ℤ) (p : List ℤ) : Prop :=
  IsSimplePath edges p ∧ p.head? = some u ∧ p.getLast? = some v

def onPath (edges : Slice (alloc.vec.Vec (Std.I64))) (u v w : ℤ) : Prop :=
  ∃ p : List ℤ, IsSimplePathFromTo edges u v p ∧ w ∈ p

def vertexSet (n : ℕ) : Finset ℤ := (Finset.range n).image (fun k : ℕ => (k : ℤ))

def edgesLenTwo (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ j : ℕ, j < edges.val.length → edgeLen edges j = 2

def edgesInBounds (n : ℕ) (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ j : ℕ, j < edges.val.length →
    0 ≤ edgeEnd edges j 0 ∧ edgeEnd edges j 0 < (n : ℤ) ∧
    0 ≤ edgeEnd edges j 1 ∧ edgeEnd edges j 1 < (n : ℤ) ∧
    edgeEnd edges j 0 ≠ edgeEnd edges j 1

def edgesDistinct (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ i j : ℕ, i < edges.val.length → j < edges.val.length →
    ((edgeEnd edges i 0 = edgeEnd edges j 0 ∧ edgeEnd edges i 1 = edgeEnd edges j 1) ∨
     (edgeEnd edges i 0 = edgeEnd edges j 1 ∧ edgeEnd edges i 1 = edgeEnd edges j 0)) → i = j

def connected (n : ℕ) (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ u v : ℤ, 0 ≤ u → u < (n : ℤ) → 0 ≤ v → v < (n : ℤ) →
    Relation.ReflTransGen (adj edges) u v

def acyclic (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ u : ℤ, ¬ Relation.TransGen (adj edges) u u

def IsSimpleTree (n : ℕ) (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  edges.val.length + 1 = n ∧
  edgesLenTwo edges ∧
  edgesInBounds n edges ∧
  edgesDistinct edges ∧
  connected n edges ∧
  acyclic edges

def SameUndirectedEdges (edges edges' : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  ∀ u v : ℤ, adj edges u v ↔ adj edges' u v

def valsInRange (vals : Slice (Std.I64)) : Prop :=
  ∀ x ∈ vals.val, 0 ≤ IScalar.val x ∧ IScalar.val x ≤ 100000

def SatisfiesPre (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64))) : Prop :=
  1 ≤ size vals ∧
  size vals ≤ 30000 ∧
  IsSimpleTree (size vals) edges ∧
  valsInRange vals

def PathIsGood (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (u v : ℤ) : Prop :=
  valAt vals u = valAt vals v ∧ ∀ w : ℤ, onPath edges u v w → valAt vals w ≤ valAt vals u

def IsGoodPair (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (u v : ℤ) : Prop :=
  u ≤ v ∧ PathIsGood vals edges u v

def adjLe (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64))) (x u v : ℤ) : Prop :=
  adj edges u v ∧ valAt vals u ≤ x ∧ valAt vals v ≤ x

def sameComponent (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (x u v : ℤ) : Prop :=
  Relation.ReflTransGen (adjLe vals edges x) u v

noncomputable def numPairs (n : ℕ) (P : ℤ → ℤ → Prop) : ℕ := by
  classical
  exact (((vertexSet n).product (vertexSet n)).filter (fun p : ℤ × ℤ => P p.1 p.2)).card

noncomputable def goodPathCount (vals : Slice (Std.I64))
    (edges : Slice (alloc.vec.Vec (Std.I64))) : ℕ :=
  numPairs (size vals) (fun u v => IsGoodPair vals edges u v)

noncomputable def countGoodPairs (vals : Slice (Std.I64))
    (edges : Slice (alloc.vec.Vec (Std.I64))) : ℕ :=
  numPairs (size vals) (fun u v => u < v ∧ PathIsGood vals edges u v)

noncomputable def componentPairCount (vals : Slice (Std.I64))
    (edges : Slice (alloc.vec.Vec (Std.I64))) : ℕ :=
  numPairs (size vals)
    (fun u v => u < v ∧ valAt vals u = valAt vals v ∧ sameComponent vals edges (valAt vals u) u v)

def occCount (vals : Slice (Std.I64)) (x : ℤ) : ℕ :=
  (Finset.range (size vals)).filter (fun i : ℕ => valAtN vals i = x) |>.card

def choose2 (c : ℕ) : ℕ := c * (c - 1) / 2

def sumChoose2ByValue (vals : Slice (Std.I64)) : ℕ :=
  ((vals.val.map (fun x => IScalar.val x)).toFinset).sum (fun x => choose2 (occCount vals x))

def totalPairs (n : ℕ) : ℕ := n * (n + 1) / 2

def maxVal (vals : Slice (Std.I64)) : ℤ :=
  (vals.val.map (fun x => IScalar.val x)).foldr max 0

def allDistinct (vals : Slice (Std.I64)) : Prop :=
  ∀ i j : ℕ, i < vals.val.length → j < vals.val.length → i < j → valAtN vals i ≠ valAtN vals j

/-- The function returns a result r and r equals the number of unordered pairs {u,v} of nodes, allowing u = v, such that vals[u] = vals[v] and every node w on P(u,v) satisfies vals[w] <= vals[u]. This is exactly the number of distinct good paths: a path and its reverse are the same path, and every singleton [u] is included.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]. Assume 0 <= vals[i] <= 100000 for every i with 0 <= i < n. The unordered pairs {edges[j][0], edges[j][1]} are pairwise distinct and form a simple undirected tree T on vertex set {0,...,n-1} (connected and acyclic). For nodes u,v, let P(u,v) be the unique simple path from u to v in T, including both endpoints, with P(u,u) = [u]. -/
theorem spec_1 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (goodPathCount vals edges : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (goodPathCount vals edges : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]. Assume 0 <= vals[i] <= 100000 for every i with 0 <= i < n. The unordered pairs {edges[j][0], edges[j][1]} are pairwise distinct and form a simple undirected tree T on vertex set {0,...,n-1}. -/
theorem spec_2 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64, number_of_good_paths vals edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64, number_of_good_paths vals edges = ok r) := by
  sorry

/-- The function returns a result r and r >= n.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. -/
theorem spec_3 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧ (size vals : ℤ) ≤ IScalar.val r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧ (size vals : ℤ) ≤ IScalar.val r) := by
  sorry

/-- The function returns a result r and r <= n + sum over all integers x of c_x*(c_x-1)/2.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. For each integer x, let c_x = #{i | 0 <= i < n and vals[i] = x}. -/
theorem spec_4 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r ≤ (size vals : ℤ) + (sumChoose2ByValue vals : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r ≤ (size vals : ℤ) + (sumChoose2ByValue vals : ℤ)) := by
  sorry

/-- The function returns a result r and r >= n + c*(c-1)/2.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. Let M = max_{0 <= i < n} vals[i] and c = #{i | 0 <= i < n and vals[i] = M}. -/
theorem spec_5 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      (size vals : ℤ) + (choose2 (occCount vals (maxVal vals)) : ℤ) ≤ IScalar.val r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      (size vals : ℤ) + (choose2 (occCount vals (maxVal vals)) : ℤ) ≤ IScalar.val r) := by
  sorry

/-- If there is an integer c such that vals[i] = c for every i with 0 <= i < n, then the function returns r = n*(n+1)/2.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. -/
theorem spec_6 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hconst : ∃ c : ℤ, ∀ x ∈ vals.val, IScalar.val x = c) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (totalPairs (size vals) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hconst : ∃ c : ℤ, ∀ x ∈ vals.val, IScalar.val x = c), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (totalPairs (size vals) : ℤ)) := by
  sorry

/-- If vals[i] != vals[j] for all 0 <= i < j < n, then the function returns r = n.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. -/
theorem spec_7 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hdistinct : allDistinct vals) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧ IScalar.val r = (size vals : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hdistinct : allDistinct vals), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧ IScalar.val r = (size vals : ℤ)) := by
  sorry

/-- The function returns a result r, and every unordered pair counted by K gives a distinct good path; in particular r >= n + K.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. For nodes u,v, P(u,v) is the unique simple path in T. Let K be the number of unordered pairs {u,v} with 0 <= u < v < n such that vals[u] = vals[v] and every node w on P(u,v) satisfies vals[w] <= vals[u]. -/
theorem spec_8 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      (size vals : ℤ) + (countGoodPairs vals edges : ℤ) ≤ IScalar.val r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      (size vals : ℤ) + (countGoodPairs vals edges : ℤ) ≤ IScalar.val r) := by
  sorry

/-- If the function returns r on input (vals, edges), then it returns the same r on input (vals, edges').
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. Let edges' be another list satisfying the same length, endpoint, and tree conditions and encoding exactly the same undirected edge set as edges, i.e. the set of unordered pairs {edges'[j][0], edges'[j][1]} equals the set of unordered pairs {edges[j][0], edges[j][1]}. -/
theorem spec_9 (vals : Slice (Std.I64)) (edges edges' : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hpre' : IsSimpleTree (size vals) edges')
    (hsame : SameUndirectedEdges edges edges')
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r) :
    number_of_good_paths vals edges' = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges edges' : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges)
    (hpre' : IsSimpleTree (size vals) edges')
    (hsame : SameUndirectedEdges edges edges')
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r), number_of_good_paths vals edges' = ok r) := by
  sorry

/-- If the function returns r on input (vals, edges), then on input ([f(vals[0]), f(vals[1]), ..., f(vals[n-1])], edges) it returns the same r.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and the edge list defines a simple tree T on {0,...,n-1} with the endpoint bounds from the problem constraints. Assume 0 <= vals[i] <= 100000 for all i. Let f be any strictly increasing function from integers to integers such that 0 <= f(vals[i]) <= 100000 for every i. -/
theorem spec_10 (vals vals' : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (f : ℤ → ℤ)
    (hpre : SatisfiesPre vals edges)
    (hmono : ∀ a b : ℤ, a < b → f a < f b)
    (hrange : ∀ i : ℕ, i < size vals → 0 ≤ f (valAtN vals i) ∧ f (valAtN vals i) ≤ 100000)
    (hvals' : size vals' = size vals ∧
      ∀ i : ℕ, i < size vals → valAtN vals' i = f (valAtN vals i))
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r) :
    number_of_good_paths vals' edges = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (vals vals' : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (f : ℤ → ℤ)
    (hpre : SatisfiesPre vals edges)
    (hmono : ∀ a b : ℤ, a < b → f a < f b)
    (hrange : ∀ i : ℕ, i < size vals → 0 ≤ f (valAtN vals i) ∧ f (valAtN vals i) ≤ 100000)
    (hvals' : size vals' = size vals ∧
      ∀ i : ℕ, i < size vals → valAtN vals' i = f (valAtN vals i))
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r), number_of_good_paths vals' edges = ok r) := by
  sorry

/-- The function returns a result r and r = n + sum over integers x of sum over C in Comp(T_x) of k_{x,C}*(k_{x,C}-1)/2, where k_{x,C} = #{w in C | vals[w] = x}. This counts the n singleton paths plus, for each value x, the unordered pairs of distinct vertices with value x that lie in the same component of T_x.
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]. Assume 0 <= vals[i] <= 100000 for every i with 0 <= i < n. The unordered pairs {edges[j][0], edges[j][1]} are pairwise distinct and form a simple undirected tree T on vertex set {0,...,n-1}. For each integer x, let T_x be the subgraph of T induced by vertices w with vals[w] <= x, and let Comp(T_x) be the set of connected components of T_x. -/
theorem spec_11 (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges) :
    ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (size vals : ℤ) + (componentPairCount vals edges : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (vals : Slice (Std.I64)) (edges : Slice (alloc.vec.Vec (Std.I64)))
    (hpre : SatisfiesPre vals edges), ∃ r : Std.I64,
      number_of_good_paths vals edges = ok r ∧
      IScalar.val r = (size vals : ℤ) + (componentPairCount vals edges : ℤ)) := by
  sorry

/-- If the function returns r on input (vals, edges), then it returns the same r on input (vals', edges').
  Preconditions: Let n = len(vals). Assume 1 <= n <= 30000, len(edges) = n - 1, and for every j with 0 <= j < len(edges), len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1]. Assume 0 <= vals[i] <= 100000 for every i with 0 <= i < n. The unordered pairs {edges[j][0], edges[j][1]} are pairwise distinct and form a simple undirected tree T on vertex set {0,...,n-1}. Let pi be a permutation of {0,...,n-1}; define vals' by vals'[pi(i)] = vals[i] for all i, and let edges' be any list of length n-1 obtained from edges by replacing each endpoint e with pi(e) and possibly reordering edges or endpoints, such that edges' satisfies the same length, endpoint, and tree conditions and represents the image tree pi(T). -/
theorem spec_12 (vals vals' : Slice (Std.I64)) (edges edges' : Slice (alloc.vec.Vec (Std.I64)))
    (π : ℤ ≃ ℤ)
    (hpre : SatisfiesPre vals edges)
    (hpre' : IsSimpleTree (size vals) edges')
    (hπ : ∀ u : ℤ, 0 ≤ u → u < (size vals : ℤ) → 0 ≤ π u ∧ π u < (size vals : ℤ))
    (hvals' : size vals' = size vals ∧
      ∀ u : ℤ, 0 ≤ u → u < (size vals : ℤ) → valAt vals' (π u) = valAt vals u)
    (hedges' : ∀ u v : ℤ, adj edges' (π u) (π v) ↔ adj edges u v)
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r) :
    number_of_good_paths vals' edges' = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (vals vals' : Slice (Std.I64)) (edges edges' : Slice (alloc.vec.Vec (Std.I64)))
    (π : ℤ ≃ ℤ)
    (hpre : SatisfiesPre vals edges)
    (hpre' : IsSimpleTree (size vals) edges')
    (hπ : ∀ u : ℤ, 0 ≤ u → u < (size vals : ℤ) → 0 ≤ π u ∧ π u < (size vals : ℤ))
    (hvals' : size vals' = size vals ∧
      ∀ u : ℤ, 0 ≤ u → u < (size vals : ℤ) → valAt vals' (π u) = valAt vals u)
    (hedges' : ∀ u v : ℤ, adj edges' (π u) (π v) ↔ adj edges u v)
    (r : Std.I64) (hret : number_of_good_paths vals edges = ok r), number_of_good_paths vals' edges' = ok r) := by
  sorry

end AegisSpec.NumberOfGoodPaths
