import Aegis.MaxNumEdgesToRemove.Code.Funs

/-!
# Specifications of `Aegis.MaxNumEdgesToRemove.max_num_edges_to_remove`

LeetCode problem `remove-max-number-of-edges-to-keep-graph-fully-traversable`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MaxNumEdgesToRemove

namespace AegisSpec.MaxNumEdgesToRemove

def vecVals (e : alloc.vec.Vec Std.I64) : List Int := e.val.map (fun x => x.val)

def edgeTriples (edges : Slice (alloc.vec.Vec Std.I64)) : List (Int × Int × Int) :=
  edges.val.map (fun e =>
    match vecVals e with
    | [t, u, v] => (t, u, v)
    | _ => (0, 0, 0))

def EdgesShape (n : Int) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ (i : Nat) (h : i < edges.val.length), ∃ t u v : Int,
    vecVals (edges.val.get ⟨i, h⟩) = [t, u, v] ∧ 1 ≤ t ∧ t ≤ 3 ∧ 1 ≤ u ∧ u < v ∧ v ≤ n

def EdgeStep (E : List (Int × Int × Int)) (T : Finset Int) (S : Finset Nat) (x y : Int) :
    Prop :=
  ∃ i ∈ S, ∃ t u v : Int, E[i]? = some (t, u, v) ∧ t ∈ T ∧
    ((x = u ∧ y = v) ∨ (x = v ∧ y = u))

def Walk (E : List (Int × Int × Int)) (T : Finset Int) (S : Finset Nat) (x y : Int) : Prop :=
  Relation.ReflTransGen (EdgeStep E T S) x y

def Connects (E : List (Int × Int × Int)) (T : Finset Int) (S : Finset Nat) (n : Int) : Prop :=
  ∀ x y : Int, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ n → Walk E T S x y

def ConnectsAll (E : List (Int × Int × Int)) (T : Finset Int) (n : Int) : Prop :=
  Connects E T (Finset.range E.length) n

def Valid (E : List (Int × Int × Int)) (n : Int) (S : Finset Nat) : Prop :=
  (∀ i ∈ S, i < E.length) ∧ Connects E ({1, 3} : Finset Int) S n ∧
    Connects E ({2, 3} : Finset Int) S n

def IsMinValid (E : List (Int × Int × Int)) (n : Int) (m : Nat) : Prop :=
  (∃ S : Finset Nat, Valid E n S ∧ S.card = m) ∧
    ∀ S : Finset Nat, Valid E n S → m ≤ S.card

noncomputable def typedIndices (E : List (Int × Int × Int)) (T : Finset Int) (S : Finset Nat) :
    Finset Nat := by
  classical
  exact S.filter (fun i => ∃ t u v : Int, E[i]? = some (t, u, v) ∧ t ∈ T)

def swapTypeVal (t : Int) : Int := if t = 1 then 2 else if t = 2 then 1 else t

def IsSwappedTypes (E E' : List (Int × Int × Int)) : Prop :=
  E'.length = E.length ∧
    ∀ (i : Nat) (t u v : Int), E[i]? = some (t, u, v) →
      E'[i]? = some (swapTypeVal t, u, v)

def IsRelabeled (σ : Int → Int) (E E' : List (Int × Int × Int)) : Prop :=
  E'.length = E.length ∧
    ∀ (i : Nat) (t u v : Int), E[i]? = some (t, u, v) →
      E'[i]? = some (t, min (σ u) (σ v), max (σ u) (σ v))

/-- Let L = len(edges). Call a set S ⊆ {0,...,L-1} of edge indices valid when both of the following hold: (A) for every two nodes x, y ∈ {1,...,n} there is a sequence x = w_0, w_1, ..., w_k = y such that each consecutive pair {w_{j-1}, w_j} equals {u_i, v_i} for some index i ∈ S with t_i ∈ {1,3}; (B) the same condition with t_i ∈ {2,3} in place of {1,3}. If at least one valid S exists, the function returns r = L - m where m = min{|S| : S is valid}; otherwise it returns r = -1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) :
    ((∃ S : Finset Nat, Valid (edgeTriples edges) n.val S) →
        ∃ m : Nat, IsMinValid (edgeTriples edges) n.val m ∧
          r.val = (edges.val.length : Int) - (m : Int)) ∧
      ((∀ S : Finset Nat, ¬ Valid (edgeTriples edges) n.val S) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r), ((∃ S : Finset Nat, Valid (edgeTriples edges) n.val S) →
        ∃ m : Nat, IsMinValid (edgeTriples edges) n.val m ∧
          r.val = (edges.val.length : Int) - (m : Int)) ∧
      ((∀ S : Finset Nat, ¬ Valid (edgeTriples edges) n.val S) → r.val = -1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup) :
    ∃ r : Std.I64, max_num_edges_to_remove n edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup), ∃ r : Std.I64, max_num_edges_to_remove n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r with r != -1, 0 <= r <= len(edges).
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), 0 ≤ r.val ∧ r.val ≤ (edges.val.length : Int)) := by
  sorry

/-- Call S ⊆ {0,...,len(edges)-1} valid when the type-{1,3} edges of S connect all of {1,...,n} and the type-{2,3} edges of S connect all of {1,...,n}. The function returns -1 if and only if no valid S exists, equivalently if and only if the graph on {1,...,n} with edge set {{u_i, v_i} : t_i ∈ {1,3}} is disconnected or the graph on {1,...,n} with edge set {{u_i, v_i} : t_i ∈ {2,3}} is disconnected.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) :
    (r.val = -1 ↔ ∀ S : Finset Nat, ¬ Valid (edgeTriples edges) n.val S) ∧
      (r.val = -1 ↔ ¬ ConnectsAll (edgeTriples edges) ({1, 3} : Finset Int) n.val ∨
        ¬ ConnectsAll (edgeTriples edges) ({2, 3} : Finset Int) n.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r), (r.val = -1 ↔ ∀ S : Finset Nat, ¬ Valid (edgeTriples edges) n.val S) ∧
      (r.val = -1 ↔ ¬ ConnectsAll (edgeTriples edges) ({1, 3} : Finset Int) n.val ∨
        ¬ ConnectsAll (edgeTriples edges) ({2, 3} : Finset Int) n.val)) := by
  sorry

/-- Whenever the function returns r with r != -1, there exists a set S ⊆ {0,...,len(edges)-1} with |S| = len(edges) - r such that the type-{1,3} edges of S connect all of {1,...,n} and the type-{2,3} edges of S connect all of {1,...,n}.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    ∃ S : Finset Nat, Valid (edgeTriples edges) n.val S ∧
      (S.card : Int) = (edges.val.length : Int) - r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), ∃ S : Finset Nat, Valid (edgeTriples edges) n.val S ∧
      (S.card : Int) = (edges.val.length : Int) - r.val) := by
  sorry

/-- Whenever the function returns r with r != -1, for every S ⊆ {0,...,len(edges)-1} such that the type-{1,3} edges of S connect all of {1,...,n} and the type-{2,3} edges of S connect all of {1,...,n}, it holds that |S| >= len(edges) - r.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    ∀ S : Finset Nat, Valid (edgeTriples edges) n.val S →
      (edges.val.length : Int) - r.val ≤ (S.card : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), ∀ S : Finset Nat, Valid (edgeTriples edges) n.val S →
      (edges.val.length : Int) - r.val ≤ (S.card : Int)) := by
  sorry

/-- Whenever the function returns r with r != -1, r <= len(edges) - (n - 1).
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    r.val ≤ (edges.val.length : Int) - (n.val - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), r.val ≤ (edges.val.length : Int) - (n.val - 1)) := by
  sorry

/-- Let edges' be defined by edges'[i] = [t'_i, u_i, v_i] where t'_i = 2 if t_i = 1, t'_i = 1 if t_i = 2, and t'_i = 3 if t_i = 3. Then max_num_edges_to_remove(n, edges') = max_num_edges_to_remove(n, edges), with both equal to -1 in the infeasible case.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_8 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hswap : IsSwappedTypes (edgeTriples edges) (edgeTriples edges')) :
    max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hswap : IsSwappedTypes (edgeTriples edges) (edgeTriples edges')), max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges) := by
  sorry

/-- For any bijection σ from {1,...,n} onto {1,...,n}, define edges'[i] = [t_i, min(σ(u_i), σ(v_i)), max(σ(u_i), σ(v_i))] for each i. Then max_num_edges_to_remove(n, edges') = max_num_edges_to_remove(n, edges), including the case where both are -1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_9 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (σ : Int → Int)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hσrange : ∀ x : Int, 1 ≤ x → x ≤ n.val → 1 ≤ σ x ∧ σ x ≤ n.val)
    (hσinj : ∀ x y : Int, 1 ≤ x → x ≤ n.val → 1 ≤ y → y ≤ n.val → σ x = σ y → x = y)
    (hrelab : IsRelabeled σ (edgeTriples edges) (edgeTriples edges')) :
    max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (σ : Int → Int)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hσrange : ∀ x : Int, 1 ≤ x → x ≤ n.val → 1 ≤ σ x ∧ σ x ≤ n.val)
    (hσinj : ∀ x y : Int, 1 ≤ x → x ≤ n.val → 1 ≤ y → y ≤ n.val → σ x = σ y → x = y)
    (hrelab : IsRelabeled σ (edgeTriples edges) (edgeTriples edges')), max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges) := by
  sorry

/-- For any bijection π of {0,...,len(edges)-1}, define edges' by edges'[i] = edges[π(i)]. Then max_num_edges_to_remove(n, edges') = max_num_edges_to_remove(n, edges), including the case where both are -1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_10 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hperm : (edgeTriples edges').Perm (edgeTriples edges)) :
    max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hperm : (edgeTriples edges').Perm (edgeTriples edges)), max_num_edges_to_remove n edges' = max_num_edges_to_remove n edges) := by
  sorry

/-- Whenever max_num_edges_to_remove(n, edges) = r with r != -1, then max_num_edges_to_remove(n, edges') = r' satisfies r' != -1 and r' >= r + 1. When max_num_edges_to_remove(n, edges) = -1, no constraint is asserted.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) < min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct; fix a triple (t, u, v) with 1 <= t <= 3 and 1 <= u < v <= n that is not equal to any (t_i, u_i, v_i), and let edges' be edges with [t, u, v] appended (so len(edges') = len(edges) + 1). -/
theorem spec_11 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (t u v : Int) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) < min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 3) (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ n.val)
    (hfresh : (t, u, v) ∉ edgeTriples edges)
    (happend : edgeTriples edges' = edgeTriples edges ++ [(t, u, v)])
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    ∃ r' : Std.I64, max_num_edges_to_remove n edges' = ok r' ∧ r'.val ≠ -1 ∧
      r.val + 1 ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (t u v : Int) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) < min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (ht1 : 1 ≤ t) (ht2 : t ≤ 3) (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ n.val)
    (hfresh : (t, u, v) ∉ edgeTriples edges)
    (happend : edgeTriples edges' = edgeTriples edges ++ [(t, u, v)])
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), ∃ r' : Std.I64, max_num_edges_to_remove n edges' = ok r' ∧ r'.val ≠ -1 ∧
      r.val + 1 ≤ r'.val) := by
  sorry

/-- If the graph on {1,...,n} with edge set {{u_i, v_i} : 0 <= i < len(edges)} is connected, the function returns r = len(edges) - (n - 1); otherwise it returns r = -1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct; every edge has t_i = 3. -/
theorem spec_12 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hall3 : ∀ e ∈ edgeTriples edges, e.1 = 3)
    (hres : max_num_edges_to_remove n edges = ok r) :
    (ConnectsAll (edgeTriples edges) ({3} : Finset Int) n.val →
        r.val = (edges.val.length : Int) - (n.val - 1)) ∧
      (¬ ConnectsAll (edgeTriples edges) ({3} : Finset Int) n.val → r.val = -1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hall3 : ∀ e ∈ edgeTriples edges, e.1 = 3)
    (hres : max_num_edges_to_remove n edges = ok r), (ConnectsAll (edgeTriples edges) ({3} : Finset Int) n.val →
        r.val = (edges.val.length : Int) - (n.val - 1)) ∧
      (¬ ConnectsAll (edgeTriples edges) ({3} : Finset Int) n.val → r.val = -1)) := by
  sorry

/-- Let C1 be the graph on {1,...,n} with edge set {{u_i, v_i} : t_i = 1}, and spec_15 the graph on {1,...,n} with edge set {{u_i, v_i} : t_i = 2}. If both C1 and spec_15 are connected, the function returns r = len(edges) - 2*(n - 1); otherwise it returns r = -1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct; no edge has t_i = 3. -/
theorem spec_13 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hno3 : ∀ e ∈ edgeTriples edges, e.1 ≠ 3)
    (hres : max_num_edges_to_remove n edges = ok r) :
    ((ConnectsAll (edgeTriples edges) ({1} : Finset Int) n.val ∧
        ConnectsAll (edgeTriples edges) ({2} : Finset Int) n.val) →
        r.val = (edges.val.length : Int) - 2 * (n.val - 1)) ∧
      (¬ (ConnectsAll (edgeTriples edges) ({1} : Finset Int) n.val ∧
          ConnectsAll (edgeTriples edges) ({2} : Finset Int) n.val) → r.val = -1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hno3 : ∀ e ∈ edgeTriples edges, e.1 ≠ 3)
    (hres : max_num_edges_to_remove n edges = ok r), ((ConnectsAll (edgeTriples edges) ({1} : Finset Int) n.val ∧
        ConnectsAll (edgeTriples edges) ({2} : Finset Int) n.val) →
        r.val = (edges.val.length : Int) - 2 * (n.val - 1)) ∧
      (¬ (ConnectsAll (edgeTriples edges) ({1} : Finset Int) n.val ∧
          ConnectsAll (edgeTriples edges) ({2} : Finset Int) n.val) → r.val = -1)) := by
  sorry

/-- Whenever the function returns r with r != -1, r >= len(edges) - 2*(n-1).
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_14 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    (edges.val.length : Int) - 2 * (n.val - 1) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), (edges.val.length : Int) - 2 * (n.val - 1) ≤ r.val) := by
  sorry

/-- Call S ⊆ {0,...,len(edges)-1} valid when the type-{1,3} edges of S connect all of {1,...,n} and the type-{2,3} edges of S connect all of {1,...,n}. Whenever the function returns r with r != -1, every valid S with |S| = len(edges) - r satisfies |{i in S : t_i in {1,3}}| = n-1 and |{i in S : t_i in {2,3}}| = n-1.
  Preconditions: 1 <= n <= 10^5; 1 <= len(edges) <= min(10^5, 3*n*(n-1)/2); every edges[i] is a vector [t_i, u_i, v_i] of length 3 with 1 <= t_i <= 3 and 1 <= u_i < v_i <= n; all triples (t_i, u_i, v_i) are pairwise distinct. -/
theorem spec_15 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1) :
    ∀ S : Finset Nat, Valid (edgeTriples edges) n.val S →
      (S.card : Int) = (edges.val.length : Int) - r.val →
      ((typedIndices (edgeTriples edges) ({1, 3} : Finset Int) S).card : Int) = n.val - 1 ∧
        ((typedIndices (edgeTriples edges) ({2, 3} : Finset Int) S).card : Int) = n.val - 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (r : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 5)
    (hL1 : 1 ≤ edges.val.length)
    (hL2 : (edges.val.length : Int) ≤ min (10 ^ 5) (3 * n.val * (n.val - 1) / 2))
    (hshape : EdgesShape n.val edges)
    (hnd : (edgeTriples edges).Nodup)
    (hres : max_num_edges_to_remove n edges = ok r) (hne : r.val ≠ -1), ∀ S : Finset Nat, Valid (edgeTriples edges) n.val S →
      (S.card : Int) = (edges.val.length : Int) - r.val →
      ((typedIndices (edgeTriples edges) ({1, 3} : Finset Int) S).card : Int) = n.val - 1 ∧
        ((typedIndices (edgeTriples edges) ({2, 3} : Finset Int) S).card : Int) = n.val - 1) := by
  sorry

end AegisSpec.MaxNumEdgesToRemove
