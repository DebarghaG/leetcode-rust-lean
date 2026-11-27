import Aegis.MaximumPoints.Code.Funs

/-!
# Specifications of `Aegis.MaximumPoints.maximum_points`

LeetCode problem `maximum-points-after-collecting-coins-from-all-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumPoints

  namespace AegisSpec.MaximumPoints

  def coinList (coins : Slice Std.I64) : List ℤ := coins.val.map (fun c => c.val)

  def coinAt (coins : Slice Std.I64) (i : ℕ) : ℤ := (coinList coins).getD i 0

  def edgeEnds (e : alloc.vec.Vec Std.I64) : Option (ℤ × ℤ) :=
    match e.val with
    | [a, b] => some (a.val, b.val)
    | _ => none

  def edgePairs (edges : Slice (alloc.vec.Vec Std.I64)) : List (ℕ × ℕ) :=
    edges.val.filterMap fun e =>
      Option.map (fun p : ℤ × ℤ => (p.1.toNat, p.2.toNat)) (edgeEnds e)

  def Adj (E : List (ℕ × ℕ)) (u v : ℕ) : Prop := (u, v) ∈ E ∨ (v, u) ∈ E

  def Reach (E : List (ℕ × ℕ)) (u v : ℕ) : Prop := Relation.ReflTransGen (Adj E) u v

  def IsTree (n : ℕ) (E : List (ℕ × ℕ)) : Prop :=
    (∀ p ∈ E, p.1 < n ∧ p.2 < n) ∧
      (∀ v, v < n → Reach E 0 v) ∧
        ∀ v, ¬ Relation.TransGen (Adj E) v v

  def IsStrictAncestor (E : List (ℕ × ℕ)) (a i : ℕ) : Prop :=
    a ≠ i ∧ Reach E 0 a ∧ Reach E a i

  open Classical in

  noncomputable def onesAbove (E : List (ℕ × ℕ)) (n : ℕ) (m : ℕ → Bool) (i : ℕ) : ℕ :=
    ((Finset.range n).filter fun a => IsStrictAncestor E a i ∧ m a = true).card

  noncomputable def nodeScore (E : List (ℕ × ℕ)) (coins : Slice Std.I64) (k : ℤ) (n : ℕ)
      (m : ℕ → Bool) (i : ℕ) : ℤ :=
    if m i then coinAt coins i / (2 : ℤ) ^ (onesAbove E n m i + 1)
    else coinAt coins i / (2 : ℤ) ^ onesAbove E n m i - k

  noncomputable def score (E : List (ℕ × ℕ)) (coins : Slice Std.I64) (k : ℤ) (n : ℕ)
      (m : ℕ → Bool) : ℤ :=
    ∑ i ∈ Finset.range n, nodeScore E coins k n m i

  def IsWalk (E : List (ℕ × ℕ)) (u v : ℕ) (p : List ℕ) : Prop :=
    p.head? = some u ∧ p.getLast? = some v ∧ ∀ q ∈ p.zip p.tail, Adj E q.1 q.2

  def IsDepth (E : List (ℕ × ℕ)) (v d : ℕ) : Prop :=
    (∃ p : List ℕ, IsWalk E 0 v p ∧ p.length = d + 1) ∧
      ∀ d' : ℕ, (∃ p : List ℕ, IsWalk E 0 v p ∧ p.length = d' + 1) → d ≤ d'

  open Classical in

  noncomputable def treeDepth (E : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
    if h : ∃ d, IsDepth E v d then Classical.choose h else 0

  def unorderedEdges (E : List (ℕ × ℕ)) : Multiset (ℕ × ℕ) :=
    ↑(E.map fun p => (min p.1 p.2, max p.1 p.2))

  noncomputable def IsMaxScore (E : List (ℕ × ℕ)) (coins : Slice Std.I64) (k : ℤ) (n : ℕ)
      (r : ℤ) : Prop :=
    (∀ m : ℕ → Bool, score E coins k n m ≤ r) ∧ ∃ m : ℕ → Bool, score E coins k n m = r

  /-- Whenever maximum_points returns a result r, r equals the maximum, over all functions m from {0,...,n-1} to {0,1}, of Sum_{i=0}^{n-1} f_i(m), where for each node i, A_i(m) is the set of strict ancestors of i in the tree rooted at 0, h_i(m) is the number of a in A_i(m) with m(a)=1, and f_i(m) = floor(coins[i] / 2^{h_i(m)}) - k if m(i)=0, while f_i(m) = floor(coins[i] / 2^{h_i(m)+1}) if m(i)=1. Here m(i)=0 means collect node i by the first way and m(i)=1 means collect node i by the second way; floor is integer floor division and the value is 0 once the power of 2 exceeds coins[i]. The maximum is over all 2^n assignments and is attained.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        IsMaxScore (edgePairs edges) coins k.val coins.val.length r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          IsMaxScore (edgePairs edges) coins k.val coins.val.length r.val) := by
    sorry

  /-- For every input satisfying the preconditions, maximum_points returns a result r (it does not fail by overflow, out-of-bounds access, division by zero, or panic).
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∃ r : Std.I64, maximum_points edges coins k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∃ r : Std.I64, maximum_points edges coins k = ok r) := by
    sorry

  /-- Whenever maximum_points returns r, r >= Sum_{i=0}^{n-1} coins[i] - n*k.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        (∑ i ∈ Finset.range coins.val.length, coinAt coins i) -
            (coins.val.length : ℤ) * k.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          (∑ i ∈ Finset.range coins.val.length, coinAt coins i) -
              (coins.val.length : ℤ) * k.val ≤ r.val) := by
    sorry

  /-- Whenever maximum_points returns r, r <= Sum_{i=0}^{n-1} max(coins[i] - k, floor(coins[i]/2)).
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        r.val ≤ ∑ i ∈ Finset.range coins.val.length,
          max (coinAt coins i - k.val) (coinAt coins i / 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          r.val ≤ ∑ i ∈ Finset.range coins.val.length,
            max (coinAt coins i - k.val) (coinAt coins i / 2)) := by
    sorry

  /-- Whenever maximum_points returns r, r = Sum_{i=0}^{n-1} coins[i].
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; k = 0. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k : k.val = 0) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        r.val = ∑ i ∈ Finset.range coins.val.length, coinAt coins i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k : k.val = 0), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          r.val = ∑ i ∈ Finset.range coins.val.length, coinAt coins i) := by
    sorry

  /-- Whenever maximum_points returns r, r = 0.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, coins[i] = 0; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_zero : ∀ i, i < coins.val.length → coinAt coins i = 0)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r → r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_zero : ∀ i, i < coins.val.length → coinAt coins i = 0)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r → r.val = 0) := by
    sorry

  /-- Whenever maximum_points(edges, coins, k1) returns r1 and maximum_points(edges, coins, k2) returns r2, r1 >= r2.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k1 <= k2 <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k1 k2 : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k1_lo : 0 ≤ k1.val) (h_k1_hi : k1.val ≤ 10000)
      (h_k2_lo : 0 ≤ k2.val) (h_k2_hi : k2.val ≤ 10000)
      (h_k_le : k1.val ≤ k2.val) :
      ∀ r1 r2 : Std.I64, maximum_points edges coins k1 = ok r1 →
        maximum_points edges coins k2 = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k1 k2 : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k1_lo : 0 ≤ k1.val) (h_k1_hi : k1.val ≤ 10000)
        (h_k2_lo : 0 ≤ k2.val) (h_k2_hi : k2.val ≤ 10000)
        (h_k_le : k1.val ≤ k2.val), ∀ r1 r2 : Std.I64, maximum_points edges coins k1 = ok r1 →
          maximum_points edges coins k2 = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- Whenever maximum_points(edges, coins, k) returns r and maximum_points(edges', coins, k) returns r', r = r'.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. Let edges' be any list of length n-1 of ordered pairs of vertices in {0,...,n-1} such that the multiset of unordered pairs {e'[0], e'[1]} over e' in edges' equals the multiset of unordered pairs {e[0], e[1]} over e in edges. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_8 (edges edges' : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_edges'_len : edges'.val.length = coins.val.length - 1)
      (h_edge'_len : ∀ e ∈ edges'.val, e.val.length = 2)
      (h_edge'_lo : ∀ e ∈ edges'.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge'_hi : ∀ e ∈ edges'.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_edges'_multiset : unorderedEdges (edgePairs edges') = unorderedEdges (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r r' : Std.I64, maximum_points edges coins k = ok r →
        maximum_points edges' coins k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges edges' : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_edges'_len : edges'.val.length = coins.val.length - 1)
        (h_edge'_len : ∀ e ∈ edges'.val, e.val.length = 2)
        (h_edge'_lo : ∀ e ∈ edges'.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge'_hi : ∀ e ∈ edges'.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_edges'_multiset : unorderedEdges (edgePairs edges') = unorderedEdges (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r r' : Std.I64, maximum_points edges coins k = ok r →
          maximum_points edges' coins k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever maximum_points returns r, r >= Sum_{i=0}^{n-1} floor(coins[i] / 2^{depth(i)+1}), where depth(i) is the number of edges on the unique path from root 0 to node i.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        (∑ i ∈ Finset.range coins.val.length,
            coinAt coins i / (2 : ℤ) ^ (treeDepth (edgePairs edges) i + 1)) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          (∑ i ∈ Finset.range coins.val.length,
              coinAt coins i / (2 : ℤ) ^ (treeDepth (edgePairs edges) i + 1)) ≤ r.val) := by
    sorry

  /-- Whenever maximum_points returns r, there exists a function m from {0,...,n-1} to {0,1} (m(i)=0 for the first way, m(i)=1 for the second way) such that the total score obtained by processing the tree top-down with these choices equals r. The score of m is Sum_i f_i(m), with f_i(m) = floor(coins[i]/2^{h_i(m)}) - k if m(i)=0 and f_i(m) = floor(coins[i]/2^{h_i(m)+1}) if m(i)=1, where h_i(m) is the number of strict ancestors a of i with m(a)=1.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_10 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        ∃ m : ℕ → Bool, score (edgePairs edges) coins k.val coins.val.length m = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          ∃ m : ℕ → Bool, score (edgePairs edges) coins k.val coins.val.length m = r.val) := by
    sorry

  /-- Whenever maximum_points returns r, for every function m from {0,...,n-1} to {0,1} (m(i)=0 for the first way, m(i)=1 for the second way), the score of m is at most r. The score of m is Sum_i f_i(m), with f_i(m) = floor(coins[i]/2^{h_i(m)}) - k if m(i)=0 and f_i(m) = floor(coins[i]/2^{h_i(m)+1}) if m(i)=1, where h_i(m) is the number of strict ancestors a of i with m(a)=1.
    Preconditions: Let n = len(coins). Assume 2 <= n <= 100000; len(edges) = n-1; every e in edges has len(e) = 2, 0 <= e[0] < n, and 0 <= e[1] < n; the undirected graph on {0,...,n-1} with an edge between e[0] and e[1] for each e in edges is a tree (connected and acyclic); for every i with 0 <= i < n, 0 <= coins[i] <= 10000; and 0 <= k <= 10000. All values are 64-bit machine integers and the stated inequalities are within range. -/
  theorem spec_11 (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
      (k : Std.I64)
      (h_n_lower : 2 ≤ coins.val.length)
      (h_n_upper : coins.val.length ≤ 100000)
      (h_edges_len : edges.val.length = coins.val.length - 1)
      (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
      (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
      (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
        a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
      (h_tree : IsTree coins.val.length (edgePairs edges))
      (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
      (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
      (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000) :
      ∀ r : Std.I64, maximum_points edges coins k = ok r →
        ∀ m : ℕ → Bool, score (edgePairs edges) coins k.val coins.val.length m ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (coins : Slice Std.I64)
        (k : Std.I64)
        (h_n_lower : 2 ≤ coins.val.length)
        (h_n_upper : coins.val.length ≤ 100000)
        (h_edges_len : edges.val.length = coins.val.length - 1)
        (h_edge_len : ∀ e ∈ edges.val, e.val.length = 2)
        (h_edge_lo : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) → 0 ≤ a ∧ 0 ≤ b)
        (h_edge_hi : ∀ e ∈ edges.val, ∀ a b : ℤ, edgeEnds e = some (a, b) →
          a < (coins.val.length : ℤ) ∧ b < (coins.val.length : ℤ))
        (h_tree : IsTree coins.val.length (edgePairs edges))
        (h_coins_lo : ∀ i, i < coins.val.length → 0 ≤ coinAt coins i)
        (h_coins_hi : ∀ i, i < coins.val.length → coinAt coins i ≤ 10000)
        (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 10000), ∀ r : Std.I64, maximum_points edges coins k = ok r →
          ∀ m : ℕ → Bool, score (edgePairs edges) coins k.val coins.val.length m ≤ r.val) := by
    sorry

  end AegisSpec.MaximumPoints
