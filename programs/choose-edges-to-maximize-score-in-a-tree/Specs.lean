import Aegis.MaxScore.Code.Funs

/-!
# Specifications of `Aegis.MaxScore.max_score`

LeetCode problem `choose-edges-to-maximize-score-in-a-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScore

def rows (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  edges.val.map (fun row => row.val.map (fun x => x.val))

def len (edges : Slice (alloc.vec.Vec Std.I64)) : Nat := (rows edges).length

def p (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  ((rows edges).getD i []).getD 0 0

def w (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  ((rows edges).getD i []).getD 1 0

def par (edges : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat := (p edges i).toNat

def iterPar (par : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iterPar par k (par x)

def ReachesRoot (par : Nat → Nat) (x : Nat) : Prop := ∃ k : Nat, iterPar par k x = 0

def ValidInput (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ len edges ∧ len edges ≤ 10 ^ 5 ∧
  (∀ i : Nat, i < len edges → ((rows edges).getD i []).length = 2) ∧
  p edges 0 = -1 ∧ w edges 0 = -1 ∧
  (∀ i : Nat, 1 ≤ i → i < len edges →
    0 ≤ p edges i ∧ p edges i < (len edges : Int) ∧ p edges i ≠ (i : Int) ∧
    -1000000 ≤ w edges i ∧ w edges i ≤ 1000000) ∧
  (∀ i : Nat, 1 ≤ i → i < len edges → ReachesRoot (par edges) i)

def Adjacent (edges : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
  par edges i = par edges j ∨ par edges i = j ∨ par edges j = i

def IsMatching (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset Nat) : Prop :=
  (∀ i ∈ S, 1 ≤ i ∧ i < len edges) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ Adjacent edges i j)

def setWeight (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset Nat) : Int :=
  ∑ i ∈ S, w edges i

def posSum (edges : Slice (alloc.vec.Vec Std.I64)) : Int :=
  ∑ i ∈ Finset.Ico (1 : Nat) (len edges), max (w edges i) 0

def maxWeight (edges : Slice (alloc.vec.Vec Std.I64)) : Int :=
  if h : (Finset.Ico (1 : Nat) (len edges)).Nonempty then
    (Finset.Ico (1 : Nat) (len edges)).sup' h (fun i => w edges i)
  else 0

def IsMaxOver {α : Type} [LinearOrder α] (P : Finset Nat → Prop) (f : Finset Nat → α)
    (v : α) : Prop :=
  (∃ S, P S ∧ f S = v) ∧ ∀ T, P T → f T ≤ v

def IsConsecFree (edges : Slice (alloc.vec.Vec Std.I64)) (S : Finset Nat) : Prop :=
  (∀ i ∈ S, 1 ≤ i ∧ i < len edges) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j → i + 1 ≠ j ∧ j + 1 ≠ i)

/-- Whenever max_score(edges) returns a result r, r is the maximum score over all choices of pairwise non-adjacent edges. Precisely, for distinct i,j with 1 ≤ i,j < n, call edges i and j adjacent iff p_i = p_j or p_i = j or p_j = i; call S ⊆ {1,...,n-1} a matching if no two distinct members of S are adjacent, and let weight(S) = ∑_{i∈S} w_i. Then there exists a matching S with r = weight(S), and for every matching T, weight(T) ≤ r. The empty set is a matching, so this maximum is at least 0.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_1 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    (∃ S : Finset Nat, IsMatching edges S ∧ r.val = setWeight edges S) ∧
      (∀ T : Finset Nat, IsMatching edges T → setWeight edges T ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), (∃ S : Finset Nat, IsMatching edges S ∧ r.val = setWeight edges S) ∧
      (∀ T : Finset Nat, IsMatching edges T → setWeight edges T ≤ r.val)) := by
  sorry

/-- max_score(edges) returns a result; it does not fail (no panic, out-of-bounds, or arithmetic overflow).
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_2 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges) :
    ∃ r : Std.I64, Aegis.MaxScore.max_score edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges), ∃ r : Std.I64, Aegis.MaxScore.max_score edges = ok r) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r ≤ ∑_{i=1}^{n-1} max(w_i, 0), with the sum being 0 when n = 1.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_3 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) : r.val ≤ posSum edges := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), r.val ≤ posSum edges) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r ≥ 0 and, for every i with 1 ≤ i < n, r ≥ w_i.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_4 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    0 ≤ r.val ∧ ∀ i : Nat, 1 ≤ i → i < len edges → w edges i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), 0 ≤ r.val ∧ ∀ i : Nat, 1 ≤ i → i < len edges → w edges i ≤ r.val) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r > 0 if and only if there exists i with 1 ≤ i < n and w_i > 0.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_5 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    0 < r.val ↔ ∃ i : Nat, 1 ≤ i ∧ i < len edges ∧ 0 < w edges i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), 0 < r.val ↔ ∃ i : Nat, 1 ≤ i ∧ i < len edges ∧ 0 < w edges i) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r = 0.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. Also, for every i with 1 ≤ i < n, w_i ≤ 0. -/
theorem spec_6 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hneg : ∀ i : Nat, 1 ≤ i → i < len edges → w edges i ≤ 0) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r) : r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hneg : ∀ i : Nat, 1 ≤ i → i < len edges → w edges i ≤ 0) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r), r.val = 0) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r = max(0, max_{1 ≤ i < n} w_i).
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. Additionally, n ≥ 2 and there exists a node v with 0 ≤ v < n such that every i with 1 ≤ i < n and w_i > 0 satisfies i = v or p_i = v. -/
theorem spec_7 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hn : 2 ≤ len edges)
    (hv : ∃ v : Nat, v < len edges ∧
      ∀ i : Nat, 1 ≤ i → i < len edges → 0 < w edges i → i = v ∨ par edges i = v)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    r.val = max 0 (maxWeight edges) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hn : 2 ≤ len edges)
    (hv : ∃ v : Nat, v < len edges ∧
      ∀ i : Nat, 1 ≤ i → i < len edges → 0 < w edges i → i = v ∨ par edges i = v)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), r.val = max 0 (maxWeight edges)) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r = max_{S ⊆ {1,...,n-1} and no two distinct elements of S are consecutive integers} ∑_{i∈S} w_i, where the maximum includes the empty set S.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. Also, for every i with 1 ≤ i < n, p_i = i - 1, so the tree is the path 0-1-...-(n-1). -/
theorem spec_8 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hpath : ∀ i : Nat, 1 ≤ i → i < len edges → par edges i = i - 1) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r) :
    IsMaxOver (IsConsecFree edges) (setWeight edges) r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (hpath : ∀ i : Nat, 1 ≤ i → i < len edges → par edges i = i - 1) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r), IsMaxOver (IsConsecFree edges) (setWeight edges) r.val) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r is the maximum weight of a matching all of whose edges have positive weight: there exists a matching S ⊆ {i | 1 ≤ i < n and w_i > 0} with r = ∑_{i∈S} w_i, and for every matching T ⊆ {i | 1 ≤ i < n and w_i > 0}, ∑_{i∈T} w_i ≤ r. Here a matching is a set of indices ≥ 1 no two distinct of which i,j satisfy p_i = p_j or p_i = j or p_j = i.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_9 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    (∃ S : Finset Nat, IsMatching edges S ∧ (∀ i ∈ S, 0 < w edges i) ∧
        r.val = setWeight edges S) ∧
      (∀ T : Finset Nat, IsMatching edges T → (∀ i ∈ T, 0 < w edges i) →
        setWeight edges T ≤ r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), (∃ S : Finset Nat, IsMatching edges S ∧ (∀ i ∈ S, 0 < w edges i) ∧
        r.val = setWeight edges S) ∧
      (∀ T : Finset Nat, IsMatching edges T → (∀ i ∈ T, 0 < w edges i) →
        setWeight edges T ≤ r.val)) := by
  sorry

/-- Whenever max_score(edges) returns a result r, there exists a matching S ⊆ {1,...,n-1}, where matching means no two distinct i,j∈S satisfy p_i = p_j or p_i = j or p_j = i, such that r = ∑_{i∈S} w_i and w_i ≥ 0 for every i ∈ S.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_10 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) :
    ∃ S : Finset Nat, IsMatching edges S ∧ r.val = setWeight edges S ∧
      ∀ i ∈ S, 0 ≤ w edges i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r), ∃ S : Finset Nat, IsMatching edges S ∧ r.val = setWeight edges S ∧
      ∀ i ∈ S, 0 ≤ w edges i) := by
  sorry

/-- Whenever max_score(edges) returns a result r, r = c · K, where K is the maximum cardinality of a matching, i.e. K = max{|S| : S ⊆ {1,...,n-1} is a matching}, with K = 0 when n = 1. Here a matching is a set of indices ≥ 1 no two distinct of which i,j satisfy p_i = p_j or p_i = j or p_j = i.
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. Also, there exists c with 0 ≤ c ≤ 10^6 such that w_i = c for every i with 1 ≤ i < n. -/
theorem spec_11 (edges : Slice (alloc.vec.Vec Std.I64)) (c : Int) (h : ValidInput edges)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000)
    (hw : ∀ i : Nat, 1 ≤ i → i < len edges → w edges i = c) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r) :
    ∃ K : Nat, IsMaxOver (IsMatching edges) (fun S => S.card) K ∧ r.val = c * (K : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (c : Int) (h : ValidInput edges)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1000000)
    (hw : ∀ i : Nat, 1 ≤ i → i < len edges → w edges i = c) (r : Std.I64)
    (hr : Aegis.MaxScore.max_score edges = ok r), ∃ K : Nat, IsMaxOver (IsMatching edges) (fun S => S.card) K ∧ r.val = c * (K : Int)) := by
  sorry

/-- Whenever max_score(edges) returns a result r, for every distinct i,j with 1 ≤ i,j < n, w_i > 0, w_j > 0, and (p_i = p_j or p_i = j or p_j = i), we have r ≤ (∑_{k=1}^{n-1} max(w_k, 0)) - min(w_i, w_j).
  Preconditions: Let n = len(edges). The input satisfies the problem constraints: n ≥ 1 and n ≤ 10^5; every edges[i] has length 2; edges[0][0] = edges[0][1] = -1; for every i with 1 ≤ i < n, setting p_i = edges[i][0] and w_i = edges[i][1], we have 0 ≤ p_i < n, p_i ≠ i, and -10^6 ≤ w_i ≤ 10^6; and the parent map is a tree rooted at 0, i.e. starting from any i ≥ 1 and repeatedly replacing the current node x by p_x while x ≠ 0 eventually reaches 0. -/
theorem spec_12 (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) (i j : Nat) (hij : i ≠ j)
    (hi1 : 1 ≤ i) (hi2 : i < len edges) (hj1 : 1 ≤ j) (hj2 : j < len edges)
    (hwi : 0 < w edges i) (hwj : 0 < w edges j) (hadj : Adjacent edges i j) :
    r.val ≤ posSum edges - min (w edges i) (w edges j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (edges : Slice (alloc.vec.Vec Std.I64)) (h : ValidInput edges)
    (r : Std.I64) (hr : Aegis.MaxScore.max_score edges = ok r) (i j : Nat) (hij : i ≠ j)
    (hi1 : 1 ≤ i) (hi2 : i < len edges) (hj1 : 1 ≤ j) (hj2 : j < len edges)
    (hwi : 0 < w edges i) (hwj : 0 < w edges j) (hadj : Adjacent edges i j), r.val ≤ posSum edges - min (w edges i) (w edges j)) := by
  sorry

end AegisSpec.MaxScore
