import Aegis.SumOfDistancesInTree.Code.Funs

/-!
# Specifications of `Aegis.SumOfDistancesInTree.sum_of_distances_in_tree`

LeetCode problem `sum-of-distances-in-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SumOfDistancesInTree (sum_of_distances_in_tree)

namespace AegisSpec.SumOfDistancesInTree

abbrev I64Vec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

abbrev I64Rows : Type := Aeneas.Std.Slice I64Vec

def nodeCount (n : Aeneas.Std.I64) : Nat := n.val.toNat

def rows (edges : I64Rows) : List (List ℤ) :=
  edges.val.map (fun v => v.val.map (fun x => x.val))

def rget (r : I64Vec) (i : Nat) : ℤ := ((r.val[i]?).map (fun x => x.val)).getD 0

def Adj (rs : List (List ℤ)) (u v : Nat) : Prop :=
  ∃ e ∈ rs, e = [(u : ℤ), (v : ℤ)] ∨ e = [(v : ℤ), (u : ℤ)]

def Connected (rs : List (List ℤ)) (N : Nat) : Prop :=
  ∀ u, u < N → ∀ v, v < N → Relation.ReflTransGen (Adj rs) u v

def Acyclic (rs : List (List ℤ)) : Prop := ∀ u, ¬ Relation.TransGen (Adj rs) u u

def IsTree (rs : List (List ℤ)) (N : Nat) : Prop := Connected rs N ∧ Acyclic rs

def AdjExcept (rs : List (List ℤ)) (a b : Nat) : Nat → Nat → Prop :=
  fun u v => Adj rs u v ∧ ¬(u = a ∧ v = b) ∧ ¬(u = b ∧ v = a)

def ChainAdj {α : Type} (r : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => r x y ∧ ChainAdj r (y :: rest)

def IsWalk (rs : List (List ℤ)) (u v : Nat) (p : List Nat) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ ChainAdj (Adj rs) p

noncomputable def walkDist (rs : List (List ℤ)) (u v : Nat) : Nat := by
  classical
  exact if h : ∃ k : Nat, ∃ p : List Nat, IsWalk rs u v p ∧ p.length = k + 1 then Nat.find h else 0

noncomputable def CompSize (rs : List (List ℤ)) (N a b : Nat) : Nat := by
  classical
  exact (Finset.univ.filter
    (fun v : Fin N => Relation.ReflTransGen (AdjExcept rs a b) b (v : Nat))).card

noncomputable def EdgeProduct (rs : List (List ℤ)) (N a b : Nat) : ℤ :=
  (CompSize rs N a b : ℤ) * ((N : ℤ) - (CompSize rs N a b : ℤ))

noncomputable def OffComponent (rs : List (List ℤ)) (N a b i : Nat) : ℤ := by
  classical
  exact if Relation.ReflTransGen (AdjExcept rs a b) b i
    then (N : ℤ) - (CompSize rs N a b : ℤ)
    else (CompSize rs N a b : ℤ)

noncomputable def degree (rs : List (List ℤ)) (N v : Nat) : Nat := by
  classical
  exact (Finset.univ.filter (fun w : Fin N => Adj rs v (w : Nat))).card

def IsCentroid (rs : List (List ℤ)) (N i : Nat) : Prop :=
  ∀ w, w < N → Adj rs i w → CompSize rs N i w ≤ N / 2

def IsPermutationOn (pi : Nat → Nat) (N : Nat) : Prop :=
  (∀ i, i < N → pi i < N) ∧ ∀ j, j < N → ∃! i, i < N ∧ pi i = j

def RelabelRow (pi : Nat → Nat) : List ℤ → List ℤ
  | [a, b] => [(pi a.toNat : ℤ), (pi b.toNat : ℤ)]
  | e => e

def UnorderedRows (rs : List (List ℤ)) : List (Nat × Nat) :=
  rs.filterMap (fun e =>
    match e with
    | [a, b] => some (min a.toNat b.toNat, max a.toNat b.toNat)
    | _ => none)

def TreeInput (n : Aeneas.Std.I64) (edges : I64Rows) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 30000 ∧
  (rows edges).length = nodeCount n - 1 ∧
  (∀ e ∈ rows edges, e.length = 2) ∧
  (∀ e ∈ rows edges, ∀ a b : ℤ, e = [a, b] →
    (0 : ℤ) ≤ a ∧ a < (nodeCount n : ℤ) ∧ (0 : ℤ) ≤ b ∧ b < (nodeCount n : ℤ) ∧ a ≠ b) ∧
  IsTree (rows edges) (nodeCount n)

/-- For every input satisfying the preconditions, the function returns a result r (so it does not fail) such that len(r) = N and, for every integer i with 0 <= i < N, r[i] = sum over j = 0,...,N-1 of d(i,j), where d(u,v) is the number of edges on the unique simple path between u and v in the tree represented by edges, with d(u,u)=0. Equivalently, r[i] is the sum of distances from node i to all other nodes 0,...,N-1; including i contributes 0.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_1 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges) :
    ∃ r : I64Vec, sum_of_distances_in_tree n edges = ok r ∧
      r.val.length = nodeCount n ∧
      ∀ i : Fin (nodeCount n),
        rget r i.val = ∑ j : Fin (nodeCount n),
          ((walkDist (rows edges) i.val (j : Nat) : Nat) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges), ∃ r : I64Vec, sum_of_distances_in_tree n edges = ok r ∧
      r.val.length = nodeCount n ∧
      ∀ i : Fin (nodeCount n),
        rget r i.val = ∑ j : Fin (nodeCount n),
          ((walkDist (rows edges) i.val (j : Nat) : Nat) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not overflow, go out of bounds, panic, or otherwise fail.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_2 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges) :
    ∃ r : I64Vec, sum_of_distances_in_tree n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges), ∃ r : I64Vec, sum_of_distances_in_tree n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] >= N - 1. For N = 1 this says r[0] >= 0.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_3 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n), (nodeCount n : ℤ) - 1 ≤ rget r i.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n), (nodeCount n : ℤ) - 1 ≤ rget r i.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] <= N*(N-1)/2.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_4 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      rget r i.val ≤ (nodeCount n : ℤ) * ((nodeCount n : ℤ) - 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      rget r i.val ≤ (nodeCount n : ℤ) * ((nodeCount n : ℤ) - 1) / 2) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, len(r) = 1 and r[0] = 0.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). Additionally assume N = 1. -/
theorem spec_5 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : nodeCount n = 1) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    r.val.length = 1 ∧ rget r 0 = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : nodeCount n = 1) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), r.val.length = 1 ∧ rget r 0 = 0) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, len(r) = 2, r[0] = 1, and r[1] = 1.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). Additionally assume N = 2. -/
theorem spec_6 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : nodeCount n = 2) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    r.val.length = 2 ∧ rget r 0 = 1 ∧ rget r 1 = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : nodeCount n = 2) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), r.val.length = 2 ∧ rget r 0 = 1 ∧ rget r 1 = 1) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r[c] = N - 1 and, for every i with 0 <= i < N and i != c, r[i] = 2*N - 3.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). Additionally assume N >= 2 and there exists a node c with 0 <= c < N such that every row of edges has c as one endpoint (equivalently, the tree is a star centered at c). -/
theorem spec_7 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : 2 ≤ nodeCount n) (c : Fin (nodeCount n))
    (hstar : ∀ e ∈ rows edges, ∀ a b : ℤ, e = [a, b] → a = (c.val : ℤ) ∨ b = (c.val : ℤ))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    rget r c.val = (nodeCount n : ℤ) - 1 ∧
      ∀ i : Fin (nodeCount n), i ≠ c → rget r i.val = 2 * (nodeCount n : ℤ) - 3 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : 2 ≤ nodeCount n) (c : Fin (nodeCount n))
    (hstar : ∀ e ∈ rows edges, ∀ a b : ℤ, e = [a, b] → a = (c.val : ℤ) ∨ b = (c.val : ℤ))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), rget r c.val = (nodeCount n : ℤ) - 1 ∧
      ∀ i : Fin (nodeCount n), i ≠ c → rget r i.val = 2 * (nodeCount n : ℤ) - 3) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] = i*(i+1)/2 + (N-1-i)*(N-i)/2.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). Additionally assume that for every k with 0 <= k < N - 1, the unordered pair {k,k+1} is an edge of the tree, so the tree is exactly the path 0-1-...-(N-1). -/
theorem spec_8 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hpath : ∀ k : Nat, k < nodeCount n - 1 → Adj (rows edges) k (k + 1))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      rget r i.val =
        (i.val : ℤ) * ((i.val : ℤ) + 1) / 2 +
          (((nodeCount n : ℤ) - 1 - (i.val : ℤ)) * ((nodeCount n : ℤ) - (i.val : ℤ))) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hpath : ∀ k : Nat, k < nodeCount n - 1 → Adj (rows edges) k (k + 1))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      rget r i.val =
        (i.val : ℤ) * ((i.val : ℤ) + 1) / 2 +
          (((nodeCount n : ℤ) - 1 - (i.val : ℤ)) * ((nodeCount n : ℤ) - (i.val : ℤ))) / 2) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every row [a,b] of edges, let S be the number of vertices in the connected component containing b after deleting the undirected edge {a,b} from the tree. Then r[b] - r[a] = N - 2*S.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_9 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ e ∈ rows edges, ∀ a b : ℤ, e = [a, b] →
      rget r b.toNat - rget r a.toNat =
        (nodeCount n : ℤ) - 2 * (CompSize (rows edges) (nodeCount n) a.toNat b.toNat : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ e ∈ rows edges, ∀ a b : ℤ, e = [a, b] →
      rget r b.toNat - rget r a.toNat =
        (nodeCount n : ℤ) - 2 * (CompSize (rows edges) (nodeCount n) a.toNat b.toNat : ℤ)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, sum over i = 0,...,N-1 of r[i] = 2 * sum over undirected edges e of S_e*(N-S_e), where for each edge e, S_e is the size of either one of the two connected components obtained by deleting e (the product S_e*(N-S_e) is independent of the choice).
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_10 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    (∑ i : Fin (nodeCount n), rget r i.val) =
      2 * ((rows edges).filterMap (fun e =>
        match e with
        | [a, b] => some (EdgeProduct (rows edges) (nodeCount n) a.toNat b.toNat)
        | _ => none)).sum := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), (∑ i : Fin (nodeCount n), rget r i.val) =
      2 * ((rows edges).filterMap (fun e =>
        match e with
        | [a, b] => some (EdgeProduct (rows edges) (nodeCount n) a.toNat b.toNat)
        | _ => none)).sum) := by
  sorry

/-- Let pi be any permutation of {0,...,N-1}. Let edges_pi be the array of length N-1 obtained from edges by replacing each row [a,b] by [pi(a),pi(b)]. Whenever the call on edges returns a result r and the call on edges_pi returns a result r_pi (the relabelled input also satisfies the preconditions), then len(r_pi) = N and, for every i with 0 <= i < N, r_pi[pi(i)] = r[i].
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_11 (n : Aeneas.Std.I64) (edges edges' : I64Rows) (pi : Nat → Nat)
    (h : TreeInput n edges) (hpi : IsPermutationOn pi (nodeCount n))
    (hrows : rows edges' = (rows edges).map (RelabelRow pi))
    (h' : TreeInput n edges') (r r' : I64Vec)
    (hr : sum_of_distances_in_tree n edges = ok r)
    (hr' : sum_of_distances_in_tree n edges' = ok r') :
    r'.val.length = nodeCount n ∧
      ∀ i : Fin (nodeCount n), rget r' (pi i.val) = rget r i.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges edges' : I64Rows) (pi : Nat → Nat)
    (h : TreeInput n edges) (hpi : IsPermutationOn pi (nodeCount n))
    (hrows : rows edges' = (rows edges).map (RelabelRow pi))
    (h' : TreeInput n edges') (r r' : I64Vec)
    (hr : sum_of_distances_in_tree n edges = ok r)
    (hr' : sum_of_distances_in_tree n edges' = ok r'), r'.val.length = nodeCount n ∧
      ∀ i : Fin (nodeCount n), rget r' (pi i.val) = rget r i.val) := by
  sorry

/-- Let edges' be any array of length N-1 whose rows are the same undirected edges as the rows of edges, in any order, with either endpoint order in each row. Whenever the function returns a result r on edges and a result r' on edges' (the second input also satisfies the preconditions), then r' = r.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_12 (n : Aeneas.Std.I64) (edges edges' : I64Rows)
    (h : TreeInput n edges)
    (hrows : List.Perm (UnorderedRows (rows edges')) (UnorderedRows (rows edges)))
    (h' : TreeInput n edges') (r r' : I64Vec)
    (hr : sum_of_distances_in_tree n edges = ok r)
    (hr' : sum_of_distances_in_tree n edges' = ok r') :
    r'.val.map (fun x => x.val) = r.val.map (fun x => x.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges edges' : I64Rows)
    (h : TreeInput n edges)
    (hrows : List.Perm (UnorderedRows (rows edges')) (UnorderedRows (rows edges)))
    (h' : TreeInput n edges') (r r' : I64Vec)
    (hr : sum_of_distances_in_tree n edges = ok r)
    (hr' : sum_of_distances_in_tree n edges' = ok r'), r'.val.map (fun x => x.val) = r.val.map (fun x => x.val)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] = N - 1 if and only if node i is adjacent in the tree to every other node (equivalently, its degree is N-1).
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). -/
theorem spec_13 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      (rget r i.val = (nodeCount n : ℤ) - 1 ↔
        degree (rows edges) (nodeCount n) i.val = nodeCount n - 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      (rget r i.val = (nodeCount n : ℤ) - 1 ↔
        degree (rows edges) (nodeCount n) i.val = nodeCount n - 1)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] = N*(N-1)/2 if and only if the tree is a path (every vertex has degree at most 2) and i is an endpoint of that path (degree(i) = 1).
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, and if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b. Also assume the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} for the rows e of edges is connected and acyclic (a tree). Additionally assume N >= 2. -/
theorem spec_14 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : 2 ≤ nodeCount n) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      (rget r i.val = (nodeCount n : ℤ) * ((nodeCount n : ℤ) - 1) / 2 ↔
        (∀ v : Fin (nodeCount n), degree (rows edges) (nodeCount n) v.val ≤ 2) ∧
          degree (rows edges) (nodeCount n) i.val = 1) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (hN : 2 ≤ nodeCount n) (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      (rget r i.val = (nodeCount n : ℤ) * ((nodeCount n : ℤ) - 1) / 2 ↔
        (∀ v : Fin (nodeCount n), degree (rows edges) (nodeCount n) v.val ≤ 2) ∧
          degree (rows edges) (nodeCount n) i.val = 1)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] = sum over the undirected edges {u,v} of the tree of the number of vertices in the connected component of the tree after deleting {u,v} that does not contain i.
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b, and the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} is a tree. -/
theorem spec_15 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      rget r i.val = ((rows edges).filterMap (fun e =>
        match e with
        | [a, b] => some (OffComponent (rows edges) (nodeCount n) a.toNat b.toNat i.val)
        | _ => none)).sum := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      rget r i.val = ((rows edges).filterMap (fun e =>
        match e with
        | [a, b] => some (OffComponent (rows edges) (nodeCount n) a.toNat b.toNat i.val)
        | _ => none)).sum) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[i] = (min over j = 0,...,N-1 of r[j]) if and only if i is a centroid of the tree, i.e. every connected component of the tree obtained by deleting i has at most N/2 vertices (equivalently, for every neighbor w of i, the component containing w after deleting the edge {i,w} has at most N/2 vertices).
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b, and the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} is a tree. -/
theorem spec_16 (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n),
      ((∀ j : Fin (nodeCount n), rget r i.val ≤ rget r j.val) ↔
        IsCentroid (rows edges) (nodeCount n) i.val) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (h : TreeInput n edges)
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n),
      ((∀ j : Fin (nodeCount n), rget r i.val ≤ rget r j.val) ↔
        IsCentroid (rows edges) (nodeCount n) i.val)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every i with 0 <= i < N, r[sigma(i)] = r[i].
  Preconditions: Let N be the integer value of n. Assume 1 <= N <= 30000, len(edges) = N - 1, every row e of edges has len(e) = 2, if e = [a,b] then 0 <= a < N, 0 <= b < N, and a != b, and the undirected simple graph with vertices 0,...,N-1 and edges {e[0],e[1]} is a tree. Additionally assume sigma is a permutation of {0,...,N-1} that is an automorphism of the tree (for every edge {a,b} of the tree, {sigma(a),sigma(b)} is also an edge of the tree). -/
theorem spec_17 (n : Aeneas.Std.I64) (edges : I64Rows) (sigma : Nat → Nat)
    (h : TreeInput n edges) (hperm : IsPermutationOn sigma (nodeCount n))
    (hauto : ∀ a b : Nat, Adj (rows edges) a b → Adj (rows edges) (sigma a) (sigma b))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r) :
    ∀ i : Fin (nodeCount n), rget r (sigma i.val) = rget r i.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (edges : I64Rows) (sigma : Nat → Nat)
    (h : TreeInput n edges) (hperm : IsPermutationOn sigma (nodeCount n))
    (hauto : ∀ a b : Nat, Adj (rows edges) a b → Adj (rows edges) (sigma a) (sigma b))
    (r : I64Vec) (hr : sum_of_distances_in_tree n edges = ok r), ∀ i : Fin (nodeCount n), rget r (sigma i.val) = rget r i.val) := by
  sorry

end AegisSpec.SumOfDistancesInTree
