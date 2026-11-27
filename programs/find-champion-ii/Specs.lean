import Aegis.FindChampion.Code.Funs

/-!
# Specifications of `Aegis.FindChampion.find_champion`

LeetCode problem `find-champion-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.FindChampion

abbrev EdgeSlice : Type := Slice (alloc.vec.Vec Std.I64)

def edgeEndpoints (edges : EdgeSlice) (i : Nat) : Option (Int × Int) :=
  match (Slice.val edges)[i]? with
  | some e =>
    match e.val with
    | [a, b] => some (a.val, b.val)
    | _ => none
  | none => none

def HasEdge (edges : EdgeSlice) (u v : Int) : Prop :=
  ∃ i : Nat, edgeEndpoints edges i = some (u, v)

def HasIncoming (edges : EdgeSlice) (t : Int) : Prop :=
  ∃ u : Int, HasEdge edges u t

def IsSource (edges : EdgeSlice) (t : Int) : Prop :=
  ¬ HasIncoming edges t

inductive Reach (edges : EdgeSlice) : Int → Int → Prop where

  | single {u v : Int} (h : HasEdge edges u v) : Reach edges u v

  | more {u v w : Int} (h₁ : HasEdge edges u v) (h₂ : Reach edges v w) : Reach edges u w

def IsAcyclic (edges : EdgeSlice) : Prop :=
  ¬ ∃ (k : Nat) (v : Nat → Int),
      1 ≤ k ∧ v 0 = v k ∧ ∀ j : Nat, j < k → HasEdge edges (v j) (v (j + 1))

def WellFormed (n : Std.I64) (edges : EdgeSlice) : Prop :=
  1 ≤ n.val ∧ n.val ≤ 100 ∧
    ((Slice.val edges).length : Int) ≤ n.val * (n.val - 1) / 2 ∧
    ∀ i : Nat, i < (Slice.val edges).length →
      ∃ u v : Int,
        edgeEndpoints edges i = some (u, v) ∧
          0 ≤ u ∧ u < n.val ∧ 0 ≤ v ∧ v < n.val ∧ u ≠ v

def Pre (n : Std.I64) (edges : EdgeSlice) : Prop :=
  WellFormed n edges ∧ IsAcyclic edges

def sourceSet (n : Std.I64) (edges : EdgeSlice) : Set Int :=
  {t | 0 ≤ t ∧ t < n.val ∧ IsSource edges t}

noncomputable def sourceCount (n : Std.I64) (edges : EdgeSlice) : Nat :=
  (sourceSet n edges).ncard

def UniqueSource (n : Std.I64) (edges : EdgeSlice) (t : Int) : Prop :=
  0 ≤ t ∧ t < n.val ∧ IsSource edges t ∧
    ∀ t' : Int, 0 ≤ t' → t' < n.val → IsSource edges t' → t' = t

/-- Whenever the function returns a result r, let S be the set of teams t with 0 <= t < n that are sources, i.e., such that there is no index i with 0 <= i < len(edges), len(edges[i]) = 2, and edges[i][1] = t. If S has exactly one element, then r is that element (r is in S and S = {r}); otherwise (S does not have exactly one element) r = -1.
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic, i.e., there is no non-empty directed cycle in G (equivalently, if a is stronger than b when there is a directed path from a to b, then 'stronger than' is transitive and antisymmetric). -/
theorem spec_1 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) :
    ((∃ t : Int, UniqueSource n edges t) → UniqueSource n edges r.val) ∧
      ((¬ ∃ t : Int, UniqueSource n edges t) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r), ((∃ t : Int, UniqueSource n edges t) → UniqueSource n edges r.val) ∧
      ((¬ ∃ t : Int, UniqueSource n edges t) → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or (0 <= r and r < n).
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_2 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val < n.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val < n.val)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) on every input satisfying the preconditions.
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_3 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) :
    ∃ r : Std.I64, Aegis.FindChampion.find_champion n edges = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges), ∃ r : Std.I64, Aegis.FindChampion.find_champion n edges = ok r) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, team r has no incoming edge: there is no index i with 0 <= i < len(edges), len(edges[i]) = 2, and edges[i][1] = r.
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_4 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val) :
    IsSource edges r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val), IsSource edges r.val) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every team t with 0 <= t < n and t != r, there exists an index i with 0 <= i < len(edges), len(edges[i]) = 2, and edges[i][1] = t (i.e., every other team has an incoming edge and is therefore not a source).
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_5 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val) :
    ∀ t : Int, 0 ≤ t → t < n.val → t ≠ r.val → HasIncoming edges t := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val), ∀ t : Int, 0 ≤ t → t < n.val → t ≠ r.val → HasIncoming edges t) := by
  sorry

/-- Whenever the function returns a result r with r = -1, there exist two distinct teams t1, t2 with 0 <= t1 < t2 < n such that neither t1 nor t2 has an incoming edge (for each of t1 and t2 there is no index i with 0 <= i < len(edges), len(edges[i]) = 2, and edges[i][1] = that team).
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_6 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr1 : r.val = -1) :
    ∃ t1 t2 : Int, 0 ≤ t1 ∧ t1 < t2 ∧ t2 < n.val ∧ IsSource edges t1 ∧ IsSource edges t2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr1 : r.val = -1), ∃ t1 t2 : Int, 0 ≤ t1 ∧ t1 < t2 ∧ t2 < n.val ∧ IsSource edges t1 ∧ IsSource edges t2) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, for every team t with 0 <= t < n and t != r there is a directed path from r to t: there exist an integer k >= 1 and vertices v0, ..., vk with v0 = r, vk = t, and for every j with 0 <= j < k there is an index i in [0, len(edges)) such that edges[i][0] = vj and edges[i][1] = v(j+1).
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_7 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val) :
    ∀ t : Int, 0 ≤ t → t < n.val → t ≠ r.val →
      ∃ (k : Nat) (v : Nat → Int),
        1 ≤ k ∧ v 0 = r.val ∧ v k = t ∧ ∀ j : Nat, j < k → HasEdge edges (v j) (v (j + 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val), ∀ t : Int, 0 ≤ t → t < n.val → t ≠ r.val →
      ∃ (k : Nat) (v : Nat → Int),
        1 ≤ k ∧ v 0 = r.val ∧ v k = t ∧ ∀ j : Nat, j < k → HasEdge edges (v j) (v (j + 1))) := by
  sorry

/-- Whenever the function returns a result r on (n, edges), for any edge list edges2 satisfying the same structural constraints (each edges2[i] has length 2, 0 <= edges2[i][0] < n, 0 <= edges2[i][1] < n, edges2[i][0] != edges2[i][1], and len(edges2) <= n*(n-1)/2) and with the same n and the same set E = {(edges2[i][0], edges2[i][1]) | 0 <= i < len(edges2)} = {(edges[i][0], edges[i][1]) | 0 <= i < len(edges)} of directed pairs, if find_champion(n, edges2) returns a result r2, then r2 = r. In particular, the result depends only on n and E, not on the order or multiplicities of entries in the list edges.
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_8 (n : Std.I64) (edges edges2 : EdgeSlice)
    (hpre : Pre n edges) (hwf2 : WellFormed n edges2)
    (hsame : ∀ u v : Int, HasEdge edges2 u v ↔ HasEdge edges u v)
    (r : Std.I64) (hr : Aegis.FindChampion.find_champion n edges = ok r)
    (r2 : Std.I64) (hr2 : Aegis.FindChampion.find_champion n edges2 = ok r2) :
    r2 = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges edges2 : EdgeSlice)
    (hpre : Pre n edges) (hwf2 : WellFormed n edges2)
    (hsame : ∀ u v : Int, HasEdge edges2 u v ↔ HasEdge edges u v)
    (r : Std.I64) (hr : Aegis.FindChampion.find_champion n edges = ok r)
    (r2 : Std.I64) (hr2 : Aegis.FindChampion.find_champion n edges2 = ok r2), r2 = r) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, the number of teams t with 0 <= t < n that have no incoming edge (no index i with 0 <= i < len(edges), len(edges[i]) = 2, and edges[i][1] = t) is exactly 1, and that unique source is r.
  Preconditions: n >= 1 and n <= 100; let m = len(edges); 0 <= m and m <= n*(n-1)/2; for every i with 0 <= i < m: len(edges[i]) = 2, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, and edges[i][0] != edges[i][1]; let G be the directed graph with vertex set {0, 1, ..., n-1} and directed edge set {(edges[i][0], edges[i][1]) | 0 <= i < m}; G is acyclic. -/
theorem spec_9 (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val) :
    sourceCount n edges = 1 ∧ UniqueSource n edges r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : EdgeSlice) (hpre : Pre n edges) (r : Std.I64)
    (hr : Aegis.FindChampion.find_champion n edges = ok r) (hr0 : 0 ≤ r.val), sourceCount n edges = 1 ∧ UniqueSource n edges r.val) := by
  sorry

end AegisSpec.FindChampion
