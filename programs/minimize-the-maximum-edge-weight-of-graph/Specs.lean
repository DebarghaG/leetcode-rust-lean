import Aegis.MinMaxWeight.Code.Funs

/-!
# Specifications of `Aegis.MinMaxWeight.min_max_weight`

LeetCode problem `minimize-the-maximum-edge-weight-of-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinMaxWeight

def comp (edges : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  match edges.val[i]? with
  | none => 0
  | some e =>
    match e.val[j]? with
    | none => 0
    | some x => x.val

def srcAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := comp edges i 0

def dstAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := comp edges i 1

def wtAt (edges : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℤ := comp edges i 2

inductive Walk (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℕ) : ℤ → ℤ → List ℤ → Prop where
  | nil {v : ℤ} : Walk edges S v v []
  | cons {a b c w : ℤ} {ws : List ℤ} (i : ℕ) (hi : i ∈ S)
      (ha : srcAt edges i = a) (hb : dstAt edges i = b) (hw : wtAt edges i = w)
      (hp : Walk edges S b c ws) : Walk edges S a c (w :: ws)

def ReachIn (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℕ) (v w : ℤ) : Prop :=
  ∃ ws : List ℤ, Walk edges S v w ws

def pathMax (ws : List ℤ) : ℤ := ws.foldr max 0

def indicesUpTo (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) (W : ℤ) : Finset ℕ :=
  (Finset.range m).filter (fun i => wtAt edges i ≤ W)

def Feasible (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) (n threshold : ℤ)
    (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range m ∧
    (∀ u : ℤ, 0 ≤ u → u < n → ((S.filter (fun i => srcAt edges i = u)).card : ℤ) ≤ threshold) ∧
    (∀ v : ℤ, 0 ≤ v → v < n → ReachIn edges S v 0)

def maxWeight (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset ℕ) : ℤ :=
  ((S.image (fun i => wtAt edges i)).max).unbotD 0

def FeasibleOutDegOne (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) (n : ℤ)
    (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range m ∧
    (∀ u : ℤ, 0 ≤ u → u < n → u ≠ 0 →
      ((S.filter (fun i => srcAt edges i = u)).card : ℤ) ≤ 1) ∧
    (∀ v : ℤ, 0 ≤ v → v < n → ReachIn edges S v 0)

def IsBottleneck (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ) (v b : ℤ) : Prop :=
  (∃ ws : List ℤ, Walk edges (Finset.range m) v 0 ws ∧ pathMax ws = b) ∧
    ∀ ws : List ℤ, Walk edges (Finset.range m) v 0 ws → b ≤ pathMax ws

def Extends (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (edges' : Slice (alloc.vec.Vec Std.I64)) (m' : ℕ) : Prop :=
  ∃ emb : ℕ → ℕ,
    (∀ i : ℕ, i < m → emb i < m') ∧
      (∀ i j : ℕ, i < m → j < m → emb i = emb j → i = j) ∧
        (∀ i : ℕ, i < m →
          srcAt edges' (emb i) = srcAt edges i ∧
            dstAt edges' (emb i) = dstAt edges i ∧
              wtAt edges' (emb i) = wtAt edges i)

/-- The function returns a result r. Let a subset S ⊆ {0,...,m-1} be called feasible if: (i) for every u in {0,...,n-1}, the number of indices i ∈ S with A_i = u is at most threshold; and (ii) for every v in {0,...,n-1}, there exists a directed path from v to 0 using only edges whose indices belong to S. If no feasible S exists, then r = -1. Otherwise, r = min { max_{i∈S} W_i : S is feasible }.
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_1 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∃ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r ∧
      ((¬ ∃ S : Finset ℕ, Feasible edges m n.val threshold.val S) → r.val = -1) ∧
        ((∃ S : Finset ℕ, Feasible edges m n.val threshold.val S) →
          (∃ S : Finset ℕ, Feasible edges m n.val threshold.val S ∧ maxWeight edges S = r.val) ∧
            (∀ S : Finset ℕ, Feasible edges m n.val threshold.val S → r.val ≤ maxWeight edges S)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∃ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r ∧
      ((¬ ∃ S : Finset ℕ, Feasible edges m n.val threshold.val S) → r.val = -1) ∧
        ((∃ S : Finset ℕ, Feasible edges m n.val threshold.val S) →
          (∃ S : Finset ℕ, Feasible edges m n.val threshold.val S ∧ maxWeight edges S = r.val) ∧
            (∀ S : Finset ℕ, Feasible edges m n.val threshold.val S → r.val ≤ maxWeight edges S))) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then there exists an index i with 0 ≤ i < m such that r = W_i.
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_2 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 → ∃ i : ℕ, i < m ∧ wtAt edges i = r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 → ∃ i : ℕ, i < m ∧ wtAt edges i = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then in the directed graph G_{≤r} on nodes {0,...,n-1} that contains exactly the edges i with W_i ≤ r, every node v in {0,...,n-1} can reach 0.
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_3 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∀ v : ℤ, 0 ≤ v → v < n.val → ReachIn edges (indicesUpTo edges m r.val) v 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∀ v : ℤ, 0 ≤ v → v < n.val → ReachIn edges (indicesUpTo edges m r.val) v 0) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then for every integer W with W < r, there exists a node v in {0,...,n-1} such that v cannot reach 0 in the directed graph G_{≤W} (which contains exactly the edges i with W_i ≤ W).
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_4 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 → ∀ W : ℤ, W < r.val →
        ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (indicesUpTo edges m W) v 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 → ∀ W : ℤ, W < r.val →
        ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (indicesUpTo edges m W) v 0) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there exists a node v in {0,...,n-1} such that v cannot reach 0 using any sequence of edges from the input graph (i.e., in the graph containing all edges).
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_5 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      (r.val = -1 ↔
        ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (Finset.range m) v 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      (r.val = -1 ↔
        ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (Finset.range m) v 0)) := by
  sorry

/-- For any integer threshold' with 1 ≤ threshold' ≤ n-1, the result of min_max_weight(n, edges, threshold') equals the result of min_max_weight(n, edges, threshold).
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_6 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ threshold' : Std.I64, 1 ≤ threshold'.val → threshold'.val ≤ n.val - 1 →
      Aegis.MinMaxWeight.min_max_weight n edges threshold' =
        Aegis.MinMaxWeight.min_max_weight n edges threshold := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ threshold' : Std.I64, 1 ≤ threshold'.val → threshold'.val ≤ n.val - 1 →
      Aegis.MinMaxWeight.min_max_weight n edges threshold' =
        Aegis.MinMaxWeight.min_max_weight n edges threshold) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then there exists a subset S ⊆ {0,...,m-1} such that: (i) max_{i∈S} W_i = r; (ii) for every u in {0,...,n-1}, |{i ∈ S : A_i = u}| ≤ threshold; (iii) every node v in {0,...,n-1} can reach 0 using only edges with indices in S.
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_7 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∃ S : Finset ℕ, Feasible edges m n.val threshold.val S ∧ maxWeight edges S = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∃ S : Finset ℕ, Feasible edges m n.val threshold.val S ∧ maxWeight edges S = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then for every subset S ⊆ {0,...,m-1} that satisfies (i) |{i ∈ S : A_i = u}| ≤ threshold for all u, and (ii) every node v can reach 0 using only edges in S, it holds that max_{i∈S} W_i ≥ r.
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_8 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∀ S : Finset ℕ, Feasible edges m n.val threshold.val S → r.val ≤ maxWeight edges S := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∀ S : Finset ℕ, Feasible edges m n.val threshold.val S → r.val ≤ maxWeight edges S) := by
  sorry

/-- Whenever the function returns a result r: if there exists v in {1,...,n-1} with no directed path from v to 0 in the full input graph, then r = -1; otherwise r = max_{v in {1,...,n-1}} min_{P a directed path from v to 0 in the full graph} max_{e in P} W_e.
  Preconditions: n is an integer with 2 <= n <= 10^5; threshold is an integer with 1 <= threshold <= n-1; edges is a list of length m with 1 <= m <= min(10^5, n*(n-1)/2); for every i with 0 <= i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 <= A_i < n, 0 <= B_i < n, A_i != B_i, and 1 <= W_i <= 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i != W_j. -/
theorem spec_9 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      ((∃ v : ℤ, 1 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (Finset.range m) v 0) → r.val = -1) ∧
        ((∀ v : ℤ, 1 ≤ v → v < n.val → ReachIn edges (Finset.range m) v 0) →
          (∃ v : ℤ, 1 ≤ v ∧ v < n.val ∧ IsBottleneck edges m v r.val) ∧
            (∀ v b : ℤ, 1 ≤ v → v < n.val → IsBottleneck edges m v b → b ≤ r.val)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      ((∃ v : ℤ, 1 ≤ v ∧ v < n.val ∧ ¬ ReachIn edges (Finset.range m) v 0) → r.val = -1) ∧
        ((∀ v : ℤ, 1 ≤ v → v < n.val → ReachIn edges (Finset.range m) v 0) →
          (∃ v : ℤ, 1 ≤ v ∧ v < n.val ∧ IsBottleneck edges m v r.val) ∧
            (∀ v b : ℤ, 1 ≤ v → v < n.val → IsBottleneck edges m v b → b ≤ r.val))) := by
  sorry

/-- For all inputs satisfying the preconditions, the function returns a result r (it does not panic, overflow, or otherwise fail).
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_10 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∃ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∃ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, if r ≠ -1 then there exists a subset S ⊆ {0,...,m-1} such that: (i) max_{i∈S} W_i = r; (ii) every node v in {0,...,n-1} can reach 0 using only edges in S; and (iii) for every node u in {1,...,n-1}, |{i ∈ S : A_i = u}| ≤ 1 (i.e., out-degree at most 1 except possibly at node 0).
  Preconditions: n is an integer with 2 ≤ n ≤ 10^5; threshold is an integer with 1 ≤ threshold ≤ n-1; edges is a list of length m with 1 ≤ m ≤ min(10^5, n*(n-1)/2); for every i with 0 ≤ i < m, edges[i] is a list of length 3, and writing A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], we have 0 ≤ A_i < n, 0 ≤ B_i < n, A_i ≠ B_i, and 1 ≤ W_i ≤ 10^6; moreover, for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i ≠ W_j. -/
theorem spec_11 (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j) :
    ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∃ S : Finset ℕ, FeasibleOutDegOne edges m n.val S ∧ maxWeight edges S = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n threshold : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (m : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j), ∀ r : Std.I64, Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
      r.val ≠ -1 →
        ∃ S : Finset ℕ, FeasibleOutDegOne edges m n.val S ∧ maxWeight edges S = r.val) := by
  sorry

/-- Let r = min_max_weight(n, edges, threshold) and r' = min_max_weight(n, edges', threshold). If r != -1, then r' != -1 and r' <= r.
  Preconditions: n is an integer with 2 <= n <= 10^5; threshold is an integer with 1 <= threshold <= n-1; edges is a list of length m with 1 <= m <= min(10^5, n*(n-1)/2); for every i with 0 <= i < m, edges[i] is a list of length 3, with A_i = edges[i][0], B_i = edges[i][1], W_i = edges[i][2], and 0 <= A_i < n, 0 <= B_i < n, A_i != B_i, 1 <= W_i <= 10^6; for any two distinct indices i, j with A_i = A_j and B_i = B_j, W_i != W_j. Also edges' is a list of edges on the same node set that extends edges (contains every edge of edges with the same multiplicity) and satisfies the same edge constraints and unique-weight condition. -/
theorem spec_12 (n threshold : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64)) (m m' : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j)
    (hm'_len : edges'.val.length = m') (hm'_lb : 1 ≤ m') (hm'_ub : m' ≤ 10 ^ 5)
    (hm'_pair : (m' : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h'_shape : ∀ i : ℕ, i < m' →
      ∃ e : alloc.vec.Vec Std.I64, edges'.val[i]? = some e ∧ e.val.length = 3)
    (h'_bnds : ∀ i : ℕ, i < m' →
      0 ≤ srcAt edges' i ∧ srcAt edges' i < n.val ∧ 0 ≤ dstAt edges' i ∧
        dstAt edges' i < n.val ∧ srcAt edges' i ≠ dstAt edges' i ∧ 1 ≤ wtAt edges' i ∧
          wtAt edges' i ≤ 10 ^ 6)
    (h'_uniq : ∀ i j : ℕ, i < m' → j < m' → i ≠ j → srcAt edges' i = srcAt edges' j →
      dstAt edges' i = dstAt edges' j → wtAt edges' i ≠ wtAt edges' j)
    (h_ext : Extends edges m edges' m') :
    ∀ r r' : Std.I64,
      Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
        Aegis.MinMaxWeight.min_max_weight n edges' threshold = Result.ok r' →
          r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n threshold : Std.I64)
    (edges edges' : Slice (alloc.vec.Vec Std.I64)) (m m' : ℕ)
    (hn_lb : 2 ≤ n.val) (hn_ub : n.val ≤ 10 ^ 5)
    (ht_lb : 1 ≤ threshold.val) (ht_ub : threshold.val ≤ n.val - 1)
    (hm_len : edges.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 10 ^ 5)
    (hm_pair : (m : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h_shape : ∀ i : ℕ, i < m →
      ∃ e : alloc.vec.Vec Std.I64, edges.val[i]? = some e ∧ e.val.length = 3)
    (h_bnds : ∀ i : ℕ, i < m →
      0 ≤ srcAt edges i ∧ srcAt edges i < n.val ∧ 0 ≤ dstAt edges i ∧ dstAt edges i < n.val ∧
        srcAt edges i ≠ dstAt edges i ∧ 1 ≤ wtAt edges i ∧ wtAt edges i ≤ 10 ^ 6)
    (h_uniq : ∀ i j : ℕ, i < m → j < m → i ≠ j → srcAt edges i = srcAt edges j →
      dstAt edges i = dstAt edges j → wtAt edges i ≠ wtAt edges j)
    (hm'_len : edges'.val.length = m') (hm'_lb : 1 ≤ m') (hm'_ub : m' ≤ 10 ^ 5)
    (hm'_pair : (m' : ℤ) ≤ n.val * (n.val - 1) / 2)
    (h'_shape : ∀ i : ℕ, i < m' →
      ∃ e : alloc.vec.Vec Std.I64, edges'.val[i]? = some e ∧ e.val.length = 3)
    (h'_bnds : ∀ i : ℕ, i < m' →
      0 ≤ srcAt edges' i ∧ srcAt edges' i < n.val ∧ 0 ≤ dstAt edges' i ∧
        dstAt edges' i < n.val ∧ srcAt edges' i ≠ dstAt edges' i ∧ 1 ≤ wtAt edges' i ∧
          wtAt edges' i ≤ 10 ^ 6)
    (h'_uniq : ∀ i j : ℕ, i < m' → j < m' → i ≠ j → srcAt edges' i = srcAt edges' j →
      dstAt edges' i = dstAt edges' j → wtAt edges' i ≠ wtAt edges' j)
    (h_ext : Extends edges m edges' m'), ∀ r r' : Std.I64,
      Aegis.MinMaxWeight.min_max_weight n edges threshold = Result.ok r →
        Aegis.MinMaxWeight.min_max_weight n edges' threshold = Result.ok r' →
          r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
  sorry

end AegisSpec.MinMaxWeight
