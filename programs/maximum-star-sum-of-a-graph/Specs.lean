import Aegis.MaxStarSum.Code.Funs

/-!
# Specifications of `Aegis.MaxStarSum.max_star_sum`

LeetCode problem `maximum-star-sum-of-a-graph`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option maxHeartbeats 1000000

namespace AegisSpec.MaxStarSum

open scoped BigOperators

def valAt (vals : Slice Std.I64) (i : ℤ) : ℤ :=
  (vals.val.getD i.toNat (0#i64)).val

def edgeFst (e : alloc.vec.Vec Std.I64) : ℤ :=
  (e.val.getD 0 (0#i64)).val

def edgeSnd (e : alloc.vec.Vec Std.I64) : ℤ :=
  (e.val.getD 1 (0#i64)).val

def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  ∃ (j : ℕ) (hj : j < edges.val.length),
    ((edgeFst (edges.val[j]) = a ∧ edgeSnd (edges.val[j]) = b) ∨
     (edgeFst (edges.val[j]) = b ∧ edgeSnd (edges.val[j]) = a))

def starSum (vals : Slice Std.I64) (c : ℤ) (S : Finset ℤ) : ℤ :=
  valAt vals c + ∑ s ∈ S, valAt vals s

def ValidStar (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : ℤ)
    (c : ℤ) (S : Finset ℤ) : Prop :=
  0 ≤ c ∧ c < (vals.val.length : ℤ) ∧
    (∀ s ∈ S, 0 ≤ s ∧ s < (vals.val.length : ℤ) ∧ Adj edges c s) ∧
    (S.card : ℤ) ≤ k

noncomputable def neighbors (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (c : ℤ) : Finset ℤ := by
  classical
  exact ((Finset.range vals.val.length).image (fun i : ℕ => (i : ℤ))).filter
    (fun s => Adj edges c s)

noncomputable def posNeighbors (vals : Slice Std.I64)
    (edges : Slice (alloc.vec.Vec Std.I64)) (c : ℤ) : Finset ℤ := by
  classical
  exact ((Finset.range vals.val.length).image (fun i : ℕ => (i : ℤ))).filter
    (fun s => Adj edges c s ∧ 0 < valAt vals s)

noncomputable def posNeighborSum (vals : Slice Std.I64)
    (edges : Slice (alloc.vec.Vec Std.I64)) (c : ℤ) : ℤ :=
  ∑ s ∈ posNeighbors vals edges c, valAt vals s

noncomputable def starSums (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (k : ℤ) : Finset ℤ := by
  classical
  exact (Finset.range vals.val.length).biUnion fun c =>
    ((neighbors vals edges (c : ℤ)).powerset.filter
        (fun S => (S.card : ℤ) ≤ k)).image (fun S => starSum vals (c : ℤ) S)

noncomputable def maxStarSum (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (k : ℤ) : ℤ :=
  if h : (starSums vals edges k).Nonempty then (starSums vals edges k).max' h else 0

noncomputable def maxOverCenters (vals : Slice Std.I64) (f : ℤ → ℤ) : ℤ :=
  if h : 1 ≤ vals.val.length then
    (Finset.range vals.val.length).sup'
      (by rw [Finset.nonempty_range_iff]; omega) fun c => f (c : ℤ)
  else 0

def IsTopSum (vals : Slice Std.I64) (P : Finset ℤ) (d : ℕ) (L : ℤ) : Prop :=
  ∃ S : Finset ℤ, S ⊆ P ∧ S.card = d ∧
    (∀ s ∈ S, ∀ t ∈ P, t ∉ S → valAt vals t ≤ valAt vals s) ∧
    L = ∑ s ∈ S, valAt vals s

/-- Define Adj(a,b) to hold iff there is some j with 0 <= j < len(edges) such that (edges[j][0] = a and edges[j][1] = b) or (edges[j][0] = b and edges[j][1] = a). For a node c and a finite set S of node indices, call (c,S) a valid star if 0 <= c < n, every s in S satisfies 0 <= s < n and Adj(c,s), and |S| <= k. Its star sum is vals[c] + sum over s in S of vals[s]. Let M be the maximum star sum over all valid stars, where the empty set S is allowed. Whenever max_star_sum(vals, edges, k) returns a result r, r = M.
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_1
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    r.val = maxStarSum vals edges k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), r.val = maxStarSum vals edges k.val) := by
  sorry

/-- For every input satisfying the preconditions, max_star_sum(vals, edges, k) returns a result; it does not panic, go out of bounds, or overflow.
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_2
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1) :
    ∃ r : Std.I64, Aegis.MaxStarSum.max_star_sum vals edges k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1), ∃ r : Std.I64, Aegis.MaxStarSum.max_star_sum vals edges k = ok r) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k) returns a result r, for every node i with 0 <= i < n we have r >= vals[i].
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_3
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) → valAt vals i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) → valAt vals i ≤ r.val) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k) returns a result r, r <= sum over i from 0 to n-1 of max(vals[i], 0).
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_4
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    r.val ≤ ∑ i ∈ Finset.range vals.val.length, max (valAt vals (i : ℤ)) 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), r.val ≤ ∑ i ∈ Finset.range vals.val.length, max (valAt vals (i : ℤ)) 0) := by
  sorry

/-- Define Adj(a,b) to hold iff there is some j with 0 <= j < len(edges) such that (edges[j][0] = a and edges[j][1] = b) or (edges[j][0] = b and edges[j][1] = a). Whenever max_star_sum(vals, edges, k) returns a result r, there exist a center c and a finite set S of node indices such that 0 <= c < n, every s in S satisfies 0 <= s < n, vals[s] > 0, and Adj(c,s), |S| <= k, and r = vals[c] + sum over s in S of vals[s].
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_5
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    ∃ (c : ℤ) (S : Finset ℤ),
      0 ≤ c ∧ c < (vals.val.length : ℤ) ∧
      (∀ s ∈ S, 0 ≤ s ∧ s < (vals.val.length : ℤ) ∧ 0 < valAt vals s ∧ Adj edges c s) ∧
      (S.card : ℤ) ≤ k.val ∧
      r.val = starSum vals c S := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), ∃ (c : ℤ) (S : Finset ℤ),
      0 ≤ c ∧ c < (vals.val.length : ℤ) ∧
      (∀ s ∈ S, 0 ≤ s ∧ s < (vals.val.length : ℤ) ∧ 0 < valAt vals s ∧ Adj edges c s) ∧
      (S.card : ℤ) ≤ k.val ∧
      r.val = starSum vals c S) := by
  sorry

/-- Define Adj(a,b) to hold iff there is some j with 0 <= j < len(edges) such that (edges[j][0] = a and edges[j][1] = b) or (edges[j][0] = b and edges[j][1] = a). Whenever max_star_sum(vals, edges, k) returns a result r, for every center c with 0 <= c < n and every finite set S of node indices such that every s in S satisfies 0 <= s < n and Adj(c,s), and |S| <= k, we have vals[c] + sum over s in S of vals[s] <= r.
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_6
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    ∀ (c : ℤ) (S : Finset ℤ), 0 ≤ c → c < (vals.val.length : ℤ) →
      (∀ s ∈ S, 0 ≤ s ∧ s < (vals.val.length : ℤ) ∧ Adj edges c s) →
      (S.card : ℤ) ≤ k.val → starSum vals c S ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), ∀ (c : ℤ) (S : Finset ℤ), 0 ≤ c → c < (vals.val.length : ℤ) →
      (∀ s ∈ S, 0 ≤ s ∧ s < (vals.val.length : ℤ) ∧ Adj edges c s) →
      (S.card : ℤ) ≤ k.val → starSum vals c S ≤ r.val) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k) returns a result r, r = max over i with 0 <= i < n of vals[i].
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], 0 <= k <= n-1, and k = 0. -/
theorem spec_7
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (hk0 : k.val = 0)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    r.val = maxOverCenters vals (fun i => valAt vals i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (hk0 : k.val = 0)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), r.val = maxOverCenters vals (fun i => valAt vals i)) := by
  sorry

/-- Define Adj(a,b) to hold iff there is some j with 0 <= j < len(edges) such that (edges[j][0] = a and edges[j][1] = b) or (edges[j][0] = b and edges[j][1] = a). Whenever max_star_sum(vals, edges, k) returns a result r, r = max over c with 0 <= c < n of ( vals[c] + sum over s with 0 <= s < n, Adj(c,s), and vals[s] > 0 of vals[s] ).
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and k = n-1. -/
theorem spec_8
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hkn : k.val = (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    r.val = maxOverCenters vals (fun c => valAt vals c + posNeighborSum vals edges c) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hkn : k.val = (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), r.val = maxOverCenters vals (fun c => valAt vals c + posNeighborSum vals edges c)) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k1) returns a result r1 and max_star_sum(vals, edges, k2) returns a result r2, we have r1 <= r2.
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k1 <= k2 <= n-1. -/
theorem spec_9
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (vals.val.length : ℤ) - 1)
    (r1 r2 : Std.I64)
    (hres1 : Aegis.MaxStarSum.max_star_sum vals edges k1 = ok r1)
    (hres2 : Aegis.MaxStarSum.max_star_sum vals edges k2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k1 k2 : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k1.val ∧ k1.val ≤ k2.val ∧ k2.val ≤ (vals.val.length : ℤ) - 1)
    (r1 r2 : Std.I64)
    (hres1 : Aegis.MaxStarSum.max_star_sum vals edges k1 = ok r1)
    (hres2 : Aegis.MaxStarSum.max_star_sum vals edges k2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k) returns a result r and max_star_sum(vals', edges, k) returns a result r', we have r <= r'.
  Preconditions: Let n = len(vals) = len(vals'). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= vals'[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_10
    (vals vals' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hn' : vals'.val.length = vals.val.length)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ valAt vals' i ∧ valAt vals' i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r r' : Std.I64)
    (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r)
    (hres' : Aegis.MaxStarSum.max_star_sum vals' edges k = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (vals vals' : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hn' : vals'.val.length = vals.val.length)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ valAt vals' i ∧ valAt vals' i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r r' : Std.I64)
    (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r)
    (hres' : Aegis.MaxStarSum.max_star_sum vals' edges k = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever max_star_sum(vals, edges, k) returns a result r and max_star_sum(vals, edges', k) returns a result r', we have r = r'.
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, 0 <= k <= n-1, and both edges and edges' satisfy: len(edges) <= min(n*(n-1)/2, 100000), len(edges') <= min(n*(n-1)/2, 100000), every edge vector has length 2, every endpoint is in [0,n), and every edge has distinct endpoints. Also assume edges' is a permutation of edges: len(edges') = len(edges) and there exists a bijection pi on {0,...,len(edges)-1} such that edges'[j] = edges[pi(j)] for every j. -/
theorem spec_11
    (vals : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hedges'_card : edges'.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges'_len : ∀ (j : ℕ), (hj : j < edges'.val.length) → (edges'.val[j]).val.length = 2)
    (hedges'_fst : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      0 ≤ edgeFst (edges'.val[j]) ∧ edgeFst (edges'.val[j]) < (vals.val.length : ℤ))
    (hedges'_snd : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      0 ≤ edgeSnd (edges'.val[j]) ∧ edgeSnd (edges'.val[j]) < (vals.val.length : ℤ))
    (hedges'_neq : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      edgeFst (edges'.val[j]) ≠ edgeSnd (edges'.val[j]))
    (hperm : edges'.val.Perm edges.val)
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r r' : Std.I64)
    (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r)
    (hres' : Aegis.MaxStarSum.max_star_sum vals edges' k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hedges'_card : edges'.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges'_len : ∀ (j : ℕ), (hj : j < edges'.val.length) → (edges'.val[j]).val.length = 2)
    (hedges'_fst : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      0 ≤ edgeFst (edges'.val[j]) ∧ edgeFst (edges'.val[j]) < (vals.val.length : ℤ))
    (hedges'_snd : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      0 ≤ edgeSnd (edges'.val[j]) ∧ edgeSnd (edges'.val[j]) < (vals.val.length : ℤ))
    (hedges'_neq : ∀ (j : ℕ), (hj : j < edges'.val.length) →
      edgeFst (edges'.val[j]) ≠ edgeSnd (edges'.val[j]))
    (hperm : edges'.val.Perm edges.val)
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r r' : Std.I64)
    (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r)
    (hres' : Aegis.MaxStarSum.max_star_sum vals edges' k = ok r'), r.val = r'.val) := by
  sorry

/-- Define Adj(a,b) to hold iff there is some j with 0 <= j < len(edges) such that (edges[j][0] = a and edges[j][1] = b) or (edges[j][0] = b and edges[j][1] = a). For each center c with 0 <= c < n, let P_c be the finite set of s such that 0 <= s < n, Adj(c,s), and vals[s] > 0. Let d_c = min(k, |P_c|). Let L_c be the sum of vals[s] over any subset S of P_c with |S| = d_c and vals[s] >= vals[t] for every s in S and t in P_c \ S. Then whenever max_star_sum(vals, edges, k) returns a result r, r = max over c with 0 <= c < n of (vals[c] + L_c).
  Preconditions: Let n = len(vals). Assume n = len(vals), 1 <= n <= 100000, for every i with 0 <= i < n we have -10000 <= vals[i] <= 10000, len(edges) <= min(n*(n-1)/2, 100000), for every j with 0 <= j < len(edges) we have len(edges[j]) = 2, 0 <= edges[j][0] < n, 0 <= edges[j][1] < n, and edges[j][0] != edges[j][1], and 0 <= k <= n-1. -/
theorem spec_12
    (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r) :
    ∃ L : ℤ → ℤ,
      (∀ c : ℤ, 0 ≤ c → c < (vals.val.length : ℤ) →
        IsTopSum vals (posNeighbors vals edges c)
          (min k.val.toNat (posNeighbors vals edges c).card) (L c)) ∧
      r.val = maxOverCenters vals (fun c => valAt vals c + L c) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (vals : Slice Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64)
    (hn : 1 ≤ vals.val.length) (hn_le : vals.val.length ≤ 100000)
    (hvals : ∀ i : ℤ, 0 ≤ i → i < (vals.val.length : ℤ) →
      -10000 ≤ valAt vals i ∧ valAt vals i ≤ 10000)
    (hedges_card : edges.val.length ≤ min (vals.val.length * (vals.val.length - 1) / 2) 100000)
    (hedges_len : ∀ (j : ℕ), (hj : j < edges.val.length) → (edges.val[j]).val.length = 2)
    (hedges_fst : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeFst (edges.val[j]) ∧ edgeFst (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_snd : ∀ (j : ℕ), (hj : j < edges.val.length) →
      0 ≤ edgeSnd (edges.val[j]) ∧ edgeSnd (edges.val[j]) < (vals.val.length : ℤ))
    (hedges_neq : ∀ (j : ℕ), (hj : j < edges.val.length) →
      edgeFst (edges.val[j]) ≠ edgeSnd (edges.val[j]))
    (hk : 0 ≤ k.val ∧ k.val ≤ (vals.val.length : ℤ) - 1)
    (r : Std.I64) (hres : Aegis.MaxStarSum.max_star_sum vals edges k = ok r), ∃ L : ℤ → ℤ,
      (∀ c : ℤ, 0 ≤ c → c < (vals.val.length : ℤ) →
        IsTopSum vals (posNeighbors vals edges c)
          (min k.val.toNat (posNeighbors vals edges c).card) (L c)) ∧
      r.val = maxOverCenters vals (fun c => valAt vals c + L c)) := by
  sorry

end AegisSpec.MaxStarSum
