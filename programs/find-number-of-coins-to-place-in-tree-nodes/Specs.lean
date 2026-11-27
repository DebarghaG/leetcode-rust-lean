import Aegis.PlacedCoins.Code.Funs

/-!
# Specifications of `Aegis.PlacedCoins.placed_coins`

LeetCode problem `find-number-of-coins-to-place-in-tree-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PlacedCoins

open Aegis.PlacedCoins (placed_coins)

def entries (v : alloc.vec.Vec I64) : List Int := v.val.map fun x => x.val

def edgeEntries (edges : Slice (alloc.vec.Vec I64)) (k : Nat) : List Int :=
  Option.elim (edges.val[k]?) [] entries

def costAt (cost : Slice I64) (i : Nat) : Int :=
  Option.elim (cost.val[i]?) 0 fun x => x.val

def coinAt (r : alloc.vec.Vec I64) (i : Nat) : Int :=
  Option.elim (r.val[i]?) 0 fun x => x.val

def EdgeShape (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  ∀ k, k < edges.val.length →
    ∃ a b : Nat, a < n ∧ b < n ∧ edgeEntries edges k = [Int.ofNat a, Int.ofNat b]

def Adj (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) : Prop :=
  ∃ k : Nat, ∃ a b : Nat,
    edgeEntries edges k = [Int.ofNat a, Int.ofNat b] ∧
      ((u = a ∧ v = b) ∨ (u = b ∧ v = a))

def ChainAdj (R : Nat → Nat → Prop) : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => R a b ∧ ChainAdj R (b :: t)

def IsWalk (edges : Slice (alloc.vec.Vec I64)) (u : Nat) (l : List Nat) (v : Nat) : Prop :=
  l.head? = some u ∧ l.getLast? = some v ∧ ChainAdj (Adj edges) l

def Connected (edges : Slice (alloc.vec.Vec I64)) (u v : Nat) : Prop :=
  ∃ l : List Nat, IsWalk edges u l v

def IsSimplePath (edges : Slice (alloc.vec.Vec I64)) (u : Nat) (l : List Nat) (v : Nat) : Prop :=
  l.Nodup ∧ IsWalk edges u l v

def IsTree (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
  (∀ v, v < n → Connected edges 0 v) ∧
    ∀ u v : Nat, Connected edges u v →
      ∃ l : List Nat, IsSimplePath edges u l v ∧
        ∀ l' : List Nat, IsSimplePath edges u l' v → l' = l

def OnRootPath (edges : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
  ∃ l : List Nat, IsSimplePath edges 0 l j ∧ i ∈ l

def subtree (edges : Slice (alloc.vec.Vec I64)) (n : Nat) (i : Nat) : Set Nat :=
  {j | j < n ∧ OnRootPath edges i j}

def AtLeastThree (S : Set Nat) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c

def AtMostTwo (S : Set Nat) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a = b ∨ a = c ∨ b = c

def IsTripleMax (f : Nat → Int) (S : Set Nat) (P : Int) : Prop :=
  (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ P = f a * f b * f c) ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → f a * f b * f c ≤ P

/-- Whenever placed_coins returns a result r, len(r) = n and for every i with 0 <= i < n the following holds. Let S_i = { j | 0 <= j < n and i lies on the unique simple path from 0 to j in the tree }; this is the subtree of i when the tree is rooted at 0. If |S_i| < 3, then r[i] = 1. If |S_i| >= 3, let P_i = max{ cost[a] * cost[b] * cost[c] | a,b,c are pairwise distinct nodes in S_i }; then r[i] = max(0, P_i).
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with both entries in {0,...,n-1}; the undirected graph on vertices {0,...,n-1} whose edges are the pairs {edges[k][0], edges[k][1]} for 0 <= k < n-1 is a tree; and for every i with 0 <= i < n, 1 <= |cost[i]| <= 10000. -/
theorem spec_1
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    r.val.length = n ∧
      ∀ i, i < n →
        (AtMostTwo (subtree edges n i) → coinAt r i = 1) ∧
          (AtLeastThree (subtree edges n i) →
            ∃ P : Int, IsTripleMax (costAt cost) (subtree edges n i) P ∧
              coinAt r i = max 0 P) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), r.val.length = n ∧
      ∀ i, i < n →
        (AtMostTwo (subtree edges n i) → coinAt r i = 1) ∧
          (AtLeastThree (subtree edges n i) →
            ∃ P : Int, IsTripleMax (costAt cost) (subtree edges n i) P ∧
              coinAt r i = max 0 P)) := by
  sorry

/-- Under these preconditions, placed_coins returns a result r; it does not fail due to arithmetic overflow, out-of-bounds indexing, or a panic.
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with both entries in {0,...,n-1}; the undirected graph on vertices {0,...,n-1} whose edges are the pairs {edges[k][0], edges[k][1]} for 0 <= k < n-1 is a tree; and for every i with 0 <= i < n, 1 <= |cost[i]| <= 10000. -/
theorem spec_2
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000) :
    ∃ r : alloc.vec.Vec I64, placed_coins edges cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000), ∃ r : alloc.vec.Vec I64, placed_coins edges cost = ok r) := by
  sorry

/-- Whenever placed_coins returns a result r, len(r) = n. Equivalently, there is exactly one coin entry for each node label 0,1,...,n-1.
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with both entries in {0,...,n-1}; the graph formed by edges is a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_3
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    r.val.length = n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), r.val.length = n) := by
  sorry

/-- Whenever placed_coins returns a result r, for every i with 0 <= i < n, 0 <= r[i] <= 1000000000000 (10^12).
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_4
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    ∀ i, i < n → 0 ≤ coinAt r i ∧ coinAt r i ≤ 1000000000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), ∀ i, i < n → 0 ≤ coinAt r i ∧ coinAt r i ≤ 1000000000000) := by
  sorry

/-- Whenever placed_coins returns a result r, for every i with 0 <= i < n and |S_i| >= 3, for all pairwise distinct nodes a,b,c in S_i, cost[a] * cost[b] * cost[c] <= r[i].
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_5
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    ∀ i, i < n → AtLeastThree (subtree edges n i) →
      ∀ a b c : Nat, a ∈ subtree edges n i → b ∈ subtree edges n i →
        c ∈ subtree edges n i → a ≠ b → a ≠ c → b ≠ c →
          costAt cost a * costAt cost b * costAt cost c ≤ coinAt r i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), ∀ i, i < n → AtLeastThree (subtree edges n i) →
      ∀ a b c : Nat, a ∈ subtree edges n i → b ∈ subtree edges n i →
        c ∈ subtree edges n i → a ≠ b → a ≠ c → b ≠ c →
          costAt cost a * costAt cost b * costAt cost c ≤ coinAt r i) := by
  sorry

/-- Whenever placed_coins returns a result r, for every i with 0 <= i < n, if |S_i| >= 3 and r[i] > 0, then there exist pairwise distinct nodes a,b,c in S_i such that cost[a] * cost[b] * cost[c] = r[i].
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_6
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    ∀ i, i < n → AtLeastThree (subtree edges n i) → 0 < coinAt r i →
      ∃ a ∈ subtree edges n i, ∃ b ∈ subtree edges n i, ∃ c ∈ subtree edges n i,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          costAt cost a * costAt cost b * costAt cost c = coinAt r i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), ∀ i, i < n → AtLeastThree (subtree edges n i) → 0 < coinAt r i →
      ∃ a ∈ subtree edges n i, ∃ b ∈ subtree edges n i, ∃ c ∈ subtree edges n i,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          costAt cost a * costAt cost b * costAt cost c = coinAt r i) := by
  sorry

/-- Whenever placed_coins returns a result r, for every i with 0 <= i < n and |S_i| >= 3, r[i] = 0 if and only if for every pairwise distinct a,b,c in S_i, cost[a] * cost[b] * cost[c] < 0.
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_7
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    ∀ i, i < n → AtLeastThree (subtree edges n i) →
      (coinAt r i = 0 ↔
        ∀ a b c : Nat, a ∈ subtree edges n i → b ∈ subtree edges n i →
          c ∈ subtree edges n i → a ≠ b → a ≠ c → b ≠ c →
            costAt cost a * costAt cost b * costAt cost c < 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), ∀ i, i < n → AtLeastThree (subtree edges n i) →
      (coinAt r i = 0 ↔
        ∀ a b c : Nat, a ∈ subtree edges n i → b ∈ subtree edges n i →
          c ∈ subtree edges n i → a ≠ b → a ≠ c → b ≠ c →
            costAt cost a * costAt cost b * costAt cost c < 0)) := by
  sorry

/-- Whenever placed_coins edges cost returns r and placed_coins edges' cost returns r', we have r = r'.
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. Also assume edges' is any permutation of the list edges (so edges' describes the same undirected tree). -/
theorem spec_8
    (edges edges' : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (hperm : edges'.val.Perm edges.val)
    (r r' : alloc.vec.Vec I64)
    (hr : placed_coins edges cost = ok r) (hr' : placed_coins edges' cost = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges edges' : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (hperm : edges'.val.Perm edges.val)
    (r r' : alloc.vec.Vec I64)
    (hr : placed_coins edges cost = ok r) (hr' : placed_coins edges' cost = ok r'), r = r') := by
  sorry

/-- Whenever placed_coins returns a result r, for all nodes i,j with 0 <= i,j < n, if i lies on the unique path from 0 to j (i is an ancestor of j, possibly i = j), |S_i| >= 3, and |S_j| >= 3, then r[i] >= r[j].
  Preconditions: Let n = len(cost). Assume 2 <= n <= 20000; len(edges) = n - 1; each edges[k] is a vector of length 2 with entries in {0,...,n-1}; edges form a tree on {0,...,n-1}; and 1 <= |cost[i]| <= 10000 for every i. -/
theorem spec_9
    (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r) :
    ∀ i j, i < n → j < n → OnRootPath edges i j →
      AtLeastThree (subtree edges n i) → AtLeastThree (subtree edges n j) →
        coinAt r i ≥ coinAt r j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (cost : Slice I64) (n : Nat)
    (hn_low : 2 ≤ n) (hn_high : n ≤ 20000)
    (hcost_len : cost.val.length = n)
    (hedges_len : edges.val.length = n - 1)
    (hshape : EdgeShape edges n)
    (htree : IsTree edges n)
    (hcost : ∀ i, i < n → 1 ≤ (costAt cost i).natAbs ∧ (costAt cost i).natAbs ≤ 10000)
    (r : alloc.vec.Vec I64) (hr : placed_coins edges cost = ok r), ∀ i j, i < n → j < n → OnRootPath edges i j →
      AtLeastThree (subtree edges n i) → AtLeastThree (subtree edges n j) →
        coinAt r i ≥ coinAt r j) := by
  sorry

end AegisSpec.PlacedCoins
