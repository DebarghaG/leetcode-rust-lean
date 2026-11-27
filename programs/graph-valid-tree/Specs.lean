import Aegis.ValidTree.Code.Funs

/-!
# Specifications of `Aegis.ValidTree.valid_tree`

LeetCode problem `graph-valid-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ValidTree

abbrev Edge := alloc.vec.Vec Std.I64

abbrev EdgeList := Slice (alloc.vec.Vec Std.I64)

def edgePairAt (edges : EdgeList) (i : Nat) : Option (Int × Int) :=
  match edges.val[i]? with
  | some v =>
    match v.val.map (fun x => x.val) with
    | [a, b] => some (a, b)
    | _ => none
  | none => none

def HasEdge (edges : EdgeList) (u v : Int) : Prop :=
  ∃ i a b, edgePairAt edges i = some (a, b) ∧ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))

def Consecutive (edges : EdgeList) (ws : List Int) : Prop :=
  ∀ j a b, j + 1 < ws.length → ws[j]? = some a → ws[(j + 1)]? = some b → HasEdge edges a b

def Walk (edges : EdgeList) (u v : Int) : Prop :=
  ∃ vs : List Int, vs.head? = some u ∧ vs.getLast? = some v ∧ Consecutive edges vs

def Connected (n : Int) (edges : EdgeList) : Prop :=
  ∀ u v, 0 ≤ u → u < n → 0 ≤ v → v < n → Walk edges u v

def IsCycle (n : Int) (edges : EdgeList) (ws : List Int) : Prop :=
  3 ≤ ws.length ∧ ws.Nodup ∧ (∀ x ∈ ws, 0 ≤ x ∧ x < n) ∧
    ∀ j, j < ws.length →
      ∃ a b, ws[j]? = some a ∧ ws[(j + 1) % ws.length]? = some b ∧ HasEdge edges a b

def Acyclic (n : Int) (edges : EdgeList) : Prop :=
  ∀ ws, ¬ IsCycle n edges ws

def IsTree (n : Int) (edges : EdgeList) : Prop :=
  Connected n edges ∧ Acyclic n edges

def SimplePath (edges : EdgeList) (u v : Int) (ws : List Int) : Prop :=
  ws.Nodup ∧ ws.head? = some u ∧ ws.getLast? = some v ∧ Consecutive edges ws

def degree (edges : EdgeList) (x : Int) : Nat :=
  (List.range edges.val.length).countP fun i =>
    match edgePairAt edges i with
    | some (a, b) => decide (a = x ∨ b = x)
    | none => false

def ValidGraph (n : Std.I64) (edges : EdgeList) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 2000 ∧
    edges.val.length ≤ 5000 ∧

    (∀ i, i < edges.val.length → ∃ a b, edgePairAt edges i = some (a, b)) ∧

    (∀ i a b, edgePairAt edges i = some (a, b) →
      0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b) ∧

    (∀ i j, i < j → j < edges.val.length →
      ∀ a b c d, edgePairAt edges i = some (a, b) → edgePairAt edges j = some (c, d) →
        ¬((a = c ∧ b = d) ∨ (a = d ∧ b = c)))

def swapEndpoints (v : Edge) : Edge :=
  match v.val with
  | [a, b] => ⟨Slice.mk 2 (Aeneas.Data.ListN.ListN.fromList [b, a]) (by scalar_tac)⟩
  | _ => v

def swapEdgeAt (edges : EdgeList) (k : Nat) : EdgeList :=
  Slice.mk (edges.val.modify k swapEndpoints).length
    (Aeneas.Data.ListN.ListN.fromList (edges.val.modify k swapEndpoints)) (by
    rw [List.length_modify]
    simpa [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length] using edges.bound)

def zeroEdge : Edge :=
  ⟨Slice.mk 2 (Aeneas.Data.ListN.ListN.fromList [(0#i64), (0#i64)]) (by scalar_tac)⟩

def permuteEdges (edges : EdgeList) (π : Nat → Nat) : EdgeList :=
  Slice.mk
    ((List.range edges.val.length).map fun i => edges.val.getD (π i) zeroEdge).length
    (Aeneas.Data.ListN.ListN.fromList
      ((List.range edges.val.length).map fun i => edges.val.getD (π i) zeroEdge))
    (by
      rw [List.length_map, List.length_range]
      simpa [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length] using edges.bound)

def IsIndexPerm (m : Nat) (π : Nat → Nat) : Prop :=
  (∀ i, i < m → π i < m) ∧ (∀ i j, i < m → j < m → π i = π j → i = j)

/-- The function returns a result r, and r = true if and only if G is a tree. G is a tree means (1) G is connected: for every u and v with 0 <= u < n and 0 <= v < n there is a finite sequence of vertices v0,...,vk such that v0 = u, vk = v, and for each j with 0 <= j < k the unordered pair {v_j, v_{j+1}} is an edge of G; and (2) G is acyclic: there are no integer k >= 3 and distinct vertices w0,...,w_{k-1} in {0,...,n-1} such that {w_j, w_{(j+1) mod k}} is an edge of G for every j with 0 <= j < k. Equivalently under the preconditions, r = true if and only if G is connected and len(edges) = n - 1 (with n read as its integer value).
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_1 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∃ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        (r = true ↔ IsTree n.val edges) ∧
        (r = true ↔ Connected n.val edges ∧ (edges.val.length : Int) = n.val - 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∃ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        (r = true ↔ IsTree n.val edges) ∧
        (r = true ↔ Connected n.val edges ∧ (edges.val.length : Int) = n.val - 1)) := by
  sorry

/-- The function returns a result r (a Bool) and does not fail: there is no overflow, no out-of-bounds access to edges or to a pair entry, and no panic.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_2 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∃ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∃ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r, if len(edges) != n - 1 (with n read as its integer value), then r = false; equivalently, if r = true then len(edges) = n - 1.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_3 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        ((edges.val.length : Int) ≠ n.val - 1 → r = false) ∧
          (r = true → (edges.val.length : Int) = n.val - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        ((edges.val.length : Int) ≠ n.val - 1 → r = false) ∧
          (r = true → (edges.val.length : Int) = n.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, if r = true then G is connected: for every u and v with 0 <= u < n and 0 <= v < n there is a finite sequence of vertices v0,...,vk with v0 = u, vk = v, and {v_j, v_{j+1}} an edge of G for every 0 <= j < k.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_4 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r → r = true → Connected n.val edges := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r → r = true → Connected n.val edges) := by
  sorry

/-- Whenever the function returns a result r, if r = true then G is acyclic: there are no integer k >= 3 and distinct vertices w0,...,w_{k-1} in {0,...,n-1} such that {w_j, w_{(j+1) mod k}} is an edge of G for every 0 <= j < k.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_5 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r → r = true → Acyclic n.val edges := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool, Aegis.ValidTree.valid_tree n edges = ok r → r = true → Acyclic n.val edges) := by
  sorry

/-- Whenever the function returns a result r, if G is connected (as in spec_4) and len(edges) = n - 1 (with n read as its integer value), then r = true.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_6 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Connected n.val edges → (edges.val.length : Int) = n.val - 1 → r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Connected n.val edges → (edges.val.length : Int) = n.val - 1 → r = true) := by
  sorry

/-- Whenever the function returns a result r, if G is connected and r = false, then G contains a cycle: there exist integer k >= 3 and distinct vertices w0,...,w_{k-1} in {0,...,n-1} such that {w_j, w_{(j+1) mod k}} is an edge of G for every 0 <= j < k.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_7 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Connected n.val edges → r = false → ∃ ws : List Int, IsCycle n.val edges ws := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Connected n.val edges → r = false → ∃ ws : List Int, IsCycle n.val edges ws) := by
  sorry

/-- Whenever the function returns a result r, if len(edges) = n - 1 (with n read as its integer value) and r = false, then G is disconnected: there exist u and v with 0 <= u < n and 0 <= v < n such that no finite sequence of vertices v0,...,vk has v0 = u, vk = v, and {v_j, v_{j+1}} an edge of G for every 0 <= j < k.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_8 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        (edges.val.length : Int) = n.val - 1 → r = false →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ ¬ Walk edges u v := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        (edges.val.length : Int) = n.val - 1 → r = false →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ ¬ Walk edges u v) := by
  sorry

/-- For every k with 0 <= k < len(edges), let edges' be the list obtained from edges by replacing the k-th edge [a,b] with [b,a] and leaving all other entries unchanged. Then the function returns a result r on (n, edges) and a result r' on (n, edges'), and r = r'.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_9 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) (k : Nat)
    (hk : k < edges.val.length) :
    ∃ r r' : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        Aegis.ValidTree.valid_tree n (swapEdgeAt edges k) = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) (k : Nat)
    (hk : k < edges.val.length), ∃ r r' : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        Aegis.ValidTree.valid_tree n (swapEdgeAt edges k) = ok r' ∧ r = r') := by
  sorry

/-- For every permutation π of the index set {0,...,len(edges)-1}, let edges' be the list of length len(edges) with edges'[i] = edges[π(i)] for every 0 <= i < len(edges). Then the function returns a result r on (n, edges) and a result r' on (n, edges'), and r = r'.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_10 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) (π : Nat → Nat)
    (hπ : IsIndexPerm edges.val.length π) :
    ∃ r r' : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        Aegis.ValidTree.valid_tree n (permuteEdges edges π) = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) (π : Nat → Nat)
    (hπ : IsIndexPerm edges.val.length π), ∃ r r' : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r ∧
        Aegis.ValidTree.valid_tree n (permuteEdges edges π) = ok r' ∧ r = r') := by
  sorry

/-- Whenever the function returns a result r, if r = true then for every vertex v with 0 <= v < n there is exactly one simple path from 0 to v in G. A simple path from 0 to v is a finite sequence of distinct vertices w0,...,wk with w0 = 0, wk = v, and {w_j, w_{j+1}} an edge of G for every 0 <= j < k; the empty sequence (k = 0, w0 = 0 = v) counts as the unique simple path from 0 to 0.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_11 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        r = true → ∀ v, 0 ≤ v → v < n.val → ∃! ws : List Int, SimplePath edges 0 v ws := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        r = true → ∀ v, 0 ≤ v → v < n.val → ∃! ws : List Int, SimplePath edges 0 v ws) := by
  sorry

/-- Whenever the function returns a result r, if r = true and n > 1 then there exist two distinct vertices u and v in {0,...,n-1} such that degree_G(u) = 1 and degree_G(v) = 1, where degree_G(x) is the number of edges of G incident to x.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_12 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        r = true → 1 < n.val →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ u ≠ v ∧
            degree edges u = 1 ∧ degree edges v = 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        r = true → 1 < n.val →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ u ≠ v ∧
            degree edges u = 1 ∧ degree edges v = 1) := by
  sorry

/-- Whenever the function returns a result r, if G is acyclic (as in spec_5) and r = false, then G is disconnected: there exist u and v with 0 <= u < n and 0 <= v < n such that no finite sequence of vertices v0,...,vk has v0 = u, vk = v, and {v_j, v_{j+1}} an edge of G for every 0 <= j < k.
  Preconditions: Let G be the simple undirected graph with vertex set {0,1,...,n-1} and edge set { {edges[i][0], edges[i][1]} | 0 <= i < len(edges) }. Assume 1 <= n <= 2000; 0 <= len(edges) <= 5000; for every i with 0 <= i < len(edges), len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; and for all i,j with 0 <= i < j < len(edges), the unordered pairs {edges[i][0], edges[i][1]} and {edges[j][0], edges[j][1]} are distinct. -/
theorem spec_13 (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges) :
    ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Acyclic n.val edges → r = false →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ ¬ Walk edges u v := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeList) (hG : ValidGraph n edges), ∀ r : Bool,
      Aegis.ValidTree.valid_tree n edges = ok r →
        Acyclic n.val edges → r = false →
          ∃ u v, 0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ ¬ Walk edges u v) := by
  sorry

end AegisSpec.ValidTree
