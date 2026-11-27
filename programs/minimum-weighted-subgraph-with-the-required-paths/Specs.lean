import Aegis.MinimumWeight.Code.Funs

/-!
# Specifications of `Aegis.MinimumWeight.minimum_weight`

LeetCode problem `minimum-weighted-subgraph-with-the-required-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumWeight

namespace AegisSpec.MinimumWeight

def edgeList (edges : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  edges.val.map (fun e => e.val)

def elen (es : List (List ℤ)) (i : ℕ) : ℕ :=
  ((es[i]?).getD []).length

def ecomp (es : List (List ℤ)) (i j : ℕ) : ℤ :=
  ((es[i]?).getD []).getD j 0

def efrm (es : List (List ℤ)) (i : ℕ) : ℤ := ecomp es i 0

def eto (es : List (List ℤ)) (i : ℕ) : ℤ := ecomp es i 1

def ewt (es : List (List ℤ)) (i : ℕ) : ℤ := ecomp es i 2

inductive Path (es : List (List ℤ)) (S : Finset ℕ) : ℤ → ℤ → Prop where
  | step {a b : ℤ} {e : ℕ} (hS : e ∈ S) (hlt : e < es.length)
      (hf : efrm es e = a) (ht : eto es e = b) : Path es S a b
  | trans {a b c : ℤ} (h₁ : Path es S a b) (h₂ : Path es S b c) : Path es S a c

inductive Walk (es : List (List ℤ)) : ℤ → ℤ → List ℕ → Prop where
  | nil (a : ℤ) : Walk es a a []
  | cons {a b c : ℤ} {e : ℕ} {l : List ℕ} (hlt : e < es.length)
      (hf : efrm es e = a) (ht : eto es e = b) (hw : Walk es b c l) :
      Walk es a c (e :: l)

def Feas (es : List (List ℤ)) (src1 src2 dest : ℤ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.range es.length ∧ Path es S src1 dest ∧ Path es S src2 dest

def Reachable (es : List (List ℤ)) (a b : ℤ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.range es.length ∧ Path es S a b

def wsum (es : List (List ℤ)) (S : Finset ℕ) : ℤ :=
  ∑ i ∈ S, ewt es i

def walkWeight (es : List (List ℤ)) (P : List ℕ) : ℤ :=
  (P.map (ewt es)).sum

def PathWeight (es : List (List ℤ)) (a b : ℤ) (w : ℤ) : Prop :=
  ∃ P : List ℕ, Walk es a b P ∧ walkWeight es P = w

def Dist (es : List (List ℤ)) (a b : ℤ) (m : ℤ) : Prop :=
  PathWeight es a b m ∧ ∀ w : ℤ, PathWeight es a b w → m ≤ w

/-- Write from(i)=edges[i][0], to(i)=edges[i][1], wt(i)=edges[i][2]. Whenever the function returns a result r, define Feas to be the set of all subsets S of {0,...,len(edges)-1} such that dest is reachable from src1 using only edges with indices in S and dest is reachable from src2 using only edges with indices in S. A path from a to b using S is a sequence v0,...,vk with k>=1, v0=a, vk=b, and for each j<k an edge index e_j in S with from(e_j)=v_j and to(e_j)=v_{j+1}. If Feas is empty then r = -1. If Feas is nonempty then r is the minimum of sum_{i in S} wt(i) over S in Feas: there exists S0 in Feas with sum_{i in S0} wt(i)=r, and for every S in Feas, r <= sum_{i in S} wt(i).
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_1 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      ((¬ ∃ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S) → r.val = -1) ∧
      ((∃ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S) →
        ∃ S0 : Finset ℕ,
          Feas (edgeList edges) src1.val src2.val dest.val S0 ∧
          wsum (edgeList edges) S0 = r.val ∧
          ∀ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S →
            r.val ≤ wsum (edgeList edges) S) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      ((¬ ∃ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S) → r.val = -1) ∧
      ((∃ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S) →
        ∃ S0 : Finset ℕ,
          Feas (edgeList edges) src1.val src2.val dest.val S0 ∧
          wsum (edgeList edges) S0 = r.val ∧
          ∀ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S →
            r.val ≤ wsum (edgeList edges) S)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, panic, or other failure) on any input satisfying the preconditions.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_2 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∃ r : I64, minimum_weight n edges src1 src2 dest = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∃ r : I64, minimum_weight n edges src1 src2 dest = ok r) := by
  sorry

/-- Write wt(i)=edges[i][2]. Whenever the function returns a result r, either r = -1 or 1 <= r <= sum_{i=0}^{len(edges)-1} wt(i).
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_3 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      r.val = -1 ∨
        (1 ≤ r.val ∧ r.val ≤ wsum (edgeList edges) (Finset.range (edgeList edges).length)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      r.val = -1 ∨
        (1 ≤ r.val ∧ r.val ≤ wsum (edgeList edges) (Finset.range (edgeList edges).length))) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if either there is no directed path from src1 to dest using any edge of the full graph, or there is no directed path from src2 to dest using any edge of the full graph. Equivalently, r != -1 if and only if both src1 and src2 can reach dest in the full graph.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_4 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      (r.val = -1 ↔
        (¬ Reachable (edgeList edges) src1.val dest.val ∨
          ¬ Reachable (edgeList edges) src2.val dest.val)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r →
      (r.val = -1 ↔
        (¬ Reachable (edgeList edges) src1.val dest.val ∨
          ¬ Reachable (edgeList edges) src2.val dest.val))) := by
  sorry

/-- Write wt(i)=edges[i][2]. Whenever the function returns a result r and r != -1, there exists a subset S of {0,...,len(edges)-1} such that dest is reachable from src1 using S, dest is reachable from src2 using S, and sum_{i in S} wt(i) = r.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_5 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ S : Finset ℕ,
        Feas (edgeList edges) src1.val src2.val dest.val S ∧ wsum (edgeList edges) S = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ S : Finset ℕ,
        Feas (edgeList edges) src1.val src2.val dest.val S ∧ wsum (edgeList edges) S = r.val) := by
  sorry

/-- Write wt(i)=edges[i][2]. Whenever the function returns a result r and r != -1, for every subset S of {0,...,len(edges)-1} such that dest is reachable from src1 using S and dest is reachable from src2 using S, it holds that r <= sum_{i in S} wt(i).
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_6 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∀ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S →
        r.val ≤ wsum (edgeList edges) S := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∀ S : Finset ℕ, Feas (edgeList edges) src1.val src2.val dest.val S →
        r.val ≤ wsum (edgeList edges) S) := by
  sorry

/-- Write wt(i)=edges[i][2]. Whenever the function returns a result r and r != -1, there exist a directed path P1 from src1 to dest and a directed path P2 from src2 to dest in the full graph such that, letting U be the set of edge indices that occur in at least one of P1 and P2, sum_{i in U} wt(i) = r.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_7 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ (P1 P2 : List ℕ) (U : Finset ℕ),
        P1 ≠ [] ∧ P2 ≠ [] ∧
        Walk (edgeList edges) src1.val dest.val P1 ∧
        Walk (edgeList edges) src2.val dest.val P2 ∧
        U = (P1 ++ P2).toFinset ∧
        wsum (edgeList edges) U = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ (P1 P2 : List ℕ) (U : Finset ℕ),
        P1 ≠ [] ∧ P2 ≠ [] ∧
        Walk (edgeList edges) src1.val dest.val P1 ∧
        Walk (edgeList edges) src2.val dest.val P2 ∧
        U = (P1 ++ P2).toFinset ∧
        wsum (edgeList edges) U = r.val) := by
  sorry

/-- For nodes a and b, let D(a,b) be the minimum total weight of a directed path from a to b in the full graph, with D(a,a)=0 for the empty path, and D(a,b)=infinity if no such path exists. Whenever the function returns a result r and r != -1, for every node v with 0 <= v < n for which D(src1,v), D(src2,v), and D(v,dest) are all finite, it holds that r <= D(src1,v) + D(src2,v) + D(v,dest).
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_8 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∀ v : ℤ, 0 ≤ v → v < n.val →
        ∀ m1 m2 m3 : ℤ,
          Dist (edgeList edges) src1.val v m1 →
          Dist (edgeList edges) src2.val v m2 →
          Dist (edgeList edges) v dest.val m3 →
          r.val ≤ m1 + m2 + m3 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∀ v : ℤ, 0 ≤ v → v < n.val →
        ∀ m1 m2 m3 : ℤ,
          Dist (edgeList edges) src1.val v m1 →
          Dist (edgeList edges) src2.val v m2 →
          Dist (edgeList edges) v dest.val m3 →
          r.val ≤ m1 + m2 + m3) := by
  sorry

/-- For nodes a and b, let D(a,b) be the minimum total weight of a directed path from a to b in the full graph, with D(a,a)=0 for the empty path, and D(a,b)=infinity if no such path exists. Whenever the function returns a result r and r != -1, there exists a node v with 0 <= v < n such that D(src1,v), D(src2,v), and D(v,dest) are all finite and r = D(src1,v) + D(src2,v) + D(v,dest).
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_9 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧
        ∃ m1 m2 m3 : ℤ,
          Dist (edgeList edges) src1.val v m1 ∧
          Dist (edgeList edges) src2.val v m2 ∧
          Dist (edgeList edges) v dest.val m3 ∧
          r.val = m1 + m2 + m3 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r : I64, minimum_weight n edges src1 src2 dest = ok r → r.val ≠ -1 →
      ∃ v : ℤ, 0 ≤ v ∧ v < n.val ∧
        ∃ m1 m2 m3 : ℤ,
          Dist (edgeList edges) src1.val v m1 ∧
          Dist (edgeList edges) src2.val v m2 ∧
          Dist (edgeList edges) v dest.val m3 ∧
          r.val = m1 + m2 + m3) := by
  sorry

/-- Whenever the function returns results r and r' on the inputs (n, edges, src1, src2, dest) and (n, edges, src2, src1, dest), respectively, it holds that r = r'.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges is a list with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_10 (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges src2 src1 dest = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (edges : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges src2 src1 dest = ok r' → r = r') := by
  sorry

/-- Suppose edges' is a permutation of edges: there is a bijection pi on {0,...,len(edges)-1} such that edges'[j] = edges[pi(j)] for every j. Whenever the function returns r on (n, edges, src1, src2, dest) and r' on (n, edges', src1, src2, dest), it holds that r = r'.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges and edges' are lists with 0 <= len(edges) <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; edges' satisfies the same entry constraints with len(edges') = len(edges); src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_11 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_edges' : (edgeList edges').length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges').length →
        elen (edgeList edges') i = 3 ∧
        0 ≤ efrm (edgeList edges') i ∧ efrm (edgeList edges') i < n.val ∧
        0 ≤ eto (edgeList edges') i ∧ eto (edgeList edges') i < n.val ∧
        efrm (edgeList edges') i ≠ eto (edgeList edges') i ∧
        1 ≤ ewt (edgeList edges') i ∧ ewt (edgeList edges') i ≤ 100000)
    (h_len : (edgeList edges').length = (edgeList edges).length)
    (h_perm : List.Perm (edgeList edges') (edgeList edges))
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges' src1 src2 dest = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_edges' : (edgeList edges').length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges').length →
        elen (edgeList edges') i = 3 ∧
        0 ≤ efrm (edgeList edges') i ∧ efrm (edgeList edges') i < n.val ∧
        0 ≤ eto (edgeList edges') i ∧ eto (edgeList edges') i < n.val ∧
        efrm (edgeList edges') i ≠ eto (edgeList edges') i ∧
        1 ≤ ewt (edgeList edges') i ∧ ewt (edgeList edges') i ≤ 100000)
    (h_len : (edgeList edges').length = (edgeList edges).length)
    (h_perm : List.Perm (edgeList edges') (edgeList edges))
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges' src1 src2 dest = ok r' → r = r') := by
  sorry

/-- Suppose every entry of edges occurs in edges' with at least the same multiplicity: equivalently, there is an injective map pi from {0,...,len(edges)-1} to {0,...,len(edges')-1} such that edges'[pi(i)] = edges[i] for every i. Whenever the function returns r on (n, edges, src1, src2, dest) and r' on (n, edges', src1, src2, dest), if r != -1 then r' != -1 and r' <= r.
  Preconditions: n is an integer with 3 <= n <= 10^5; edges and edges' are lists with 0 <= len(edges) <= 10^5 and 0 <= len(edges') <= 10^5; for every i with 0 <= i < len(edges), len(edges[i]) = 3, 0 <= edges[i][0] < n, 0 <= edges[i][1] < n, edges[i][0] != edges[i][1], and 1 <= edges[i][2] <= 10^5; for every i with 0 <= i < len(edges'), len(edges'[i]) = 3, 0 <= edges'[i][0] < n, 0 <= edges'[i][1] < n, edges'[i][0] != edges'[i][1], and 1 <= edges'[i][2] <= 10^5; src1, src2, dest are integers with 0 <= src1 < n, 0 <= src2 < n, 0 <= dest < n, and src1, src2, dest are pairwise distinct. -/
theorem spec_12 (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_edges' : (edgeList edges').length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges').length →
        elen (edgeList edges') i = 3 ∧
        0 ≤ efrm (edgeList edges') i ∧ efrm (edgeList edges') i < n.val ∧
        0 ≤ eto (edgeList edges') i ∧ eto (edgeList edges') i < n.val ∧
        efrm (edgeList edges') i ≠ eto (edgeList edges') i ∧
        1 ≤ ewt (edgeList edges') i ∧ ewt (edgeList edges') i ≤ 100000)
    (h_sub : ∃ pi : Fin (edgeList edges).length → Fin (edgeList edges').length,
      Function.Injective pi ∧
        ∀ i : Fin (edgeList edges).length,
          (edgeList edges').get (pi i) = (edgeList edges).get i)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val) :
    ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges' src1 src2 dest = ok r' →
      r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (edges edges' : Slice (alloc.vec.Vec I64)) (src1 src2 dest : I64)
    (hn : 3 ≤ n.val ∧ n.val ≤ 100000)
    (h_edges : (edgeList edges).length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges).length →
        elen (edgeList edges) i = 3 ∧
        0 ≤ efrm (edgeList edges) i ∧ efrm (edgeList edges) i < n.val ∧
        0 ≤ eto (edgeList edges) i ∧ eto (edgeList edges) i < n.val ∧
        efrm (edgeList edges) i ≠ eto (edgeList edges) i ∧
        1 ≤ ewt (edgeList edges) i ∧ ewt (edgeList edges) i ≤ 100000)
    (h_edges' : (edgeList edges').length ≤ 100000 ∧
      ∀ i : ℕ, i < (edgeList edges').length →
        elen (edgeList edges') i = 3 ∧
        0 ≤ efrm (edgeList edges') i ∧ efrm (edgeList edges') i < n.val ∧
        0 ≤ eto (edgeList edges') i ∧ eto (edgeList edges') i < n.val ∧
        efrm (edgeList edges') i ≠ eto (edgeList edges') i ∧
        1 ≤ ewt (edgeList edges') i ∧ ewt (edgeList edges') i ≤ 100000)
    (h_sub : ∃ pi : Fin (edgeList edges).length → Fin (edgeList edges').length,
      Function.Injective pi ∧
        ∀ i : Fin (edgeList edges).length,
          (edgeList edges').get (pi i) = (edgeList edges).get i)
    (h_pts : 0 ≤ src1.val ∧ src1.val < n.val ∧ 0 ≤ src2.val ∧ src2.val < n.val ∧
      0 ≤ dest.val ∧ dest.val < n.val)
    (h_ne : src1.val ≠ src2.val ∧ src1.val ≠ dest.val ∧ src2.val ≠ dest.val), ∀ r r' : I64,
      minimum_weight n edges src1 src2 dest = ok r →
      minimum_weight n edges' src1 src2 dest = ok r' →
      r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
  sorry

end AegisSpec.MinimumWeight
