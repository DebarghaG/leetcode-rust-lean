import Aegis.MaxKDivisibleComponents.Code.Funs

/-!
# Specifications of `Aegis.MaxKDivisibleComponents.max_k_divisible_components`

LeetCode problem `maximum-number-of-k-divisible-components`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxKDivisibleComponents

set_option autoImplicit false

namespace AegisSpec.MaxKDivisibleComponents

def valAt (values : Slice Std.I64) (i : Nat) : Int := (values.val.getD i 0#i64).val

def edgePair (e : alloc.vec.Vec Std.I64) : Nat × Nat :=
  match e.val with
  | a :: b :: _ => (a.val.toNat, b.val.toNat)
  | _ => (0, 0)

def totalSum (n : Nat) (values : Slice Std.I64) : Int :=
  ∑ i ∈ Finset.range n, valAt values i

def Adj (edges : Slice (alloc.vec.Vec Std.I64)) (R : Finset Nat) (u v : Nat) : Prop :=
  ∃ i : Fin edges.val.length, (i : Nat) ∉ R ∧
    (let p := edgePair (edges.val.get i); (u = p.1 ∧ v = p.2) ∨ (u = p.2 ∧ v = p.1))

def Reach (edges : Slice (alloc.vec.Vec Std.I64)) (R : Finset Nat) (u v : Nat) : Prop :=
  Relation.ReflTransGen (Adj edges R) u v

noncomputable def compSet (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
    (R : Finset Nat) (v : Nat) : Finset Nat :=
  letI := Classical.decPred (fun u : Nat => Reach edges R v u)
  (Finset.range n).filter (fun u => Reach edges R v u)

noncomputable def compSum (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (R : Finset Nat) (v : Nat) : Int :=
  ∑ u ∈ compSet n edges R v, valAt values u

def ValidRemoval (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Int) (R : Finset Nat) : Prop :=
  ∀ v ∈ Finset.range n, k ∣ compSum n edges values R v

def IsMaxComponents (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (k : Int) (r : Int) : Prop :=
  (∃ R : Finset Nat,
      R ⊆ Finset.range edges.val.length ∧ ValidRemoval n edges values k R ∧
        r = (R.card : Int) + 1) ∧
    (∀ R : Finset Nat,
      R ⊆ Finset.range edges.val.length → ValidRemoval n edges values k R →
        (R.card : Int) + 1 ≤ r)

def IsTree (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (∀ e ∈ edges.val, e.val.length = 2) ∧
    (∀ e ∈ edges.val, (edgePair e).1 < n ∧ (edgePair e).2 < n ∧ (edgePair e).1 ≠ (edgePair e).2) ∧
    edges.val.length = n - 1 ∧
    (∀ u v : Nat, u < n → v < n → Reach edges ∅ u v)

def CutDivisible (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Int) (i : Nat) : Prop :=
  ∃ v ∈ Finset.range n, k ∣ compSum n edges values {i} v

noncomputable def cutSet (n : Nat) (edges : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (k : Int) : Finset Nat :=
  letI := Classical.decPred (fun i : Nat => CutDivisible n edges values k i)
  (Finset.range edges.val.length).filter (fun i => CutDivisible n edges values k i)

/-- Let V = {0,...,n-1}. Let E be the set of unordered pairs {edges[i][0], edges[i][1]} for 0 <= i < len(edges). Let S = sum_{v in V} values[v]. For a subset R of E, let G_R be the graph with vertex set V and edge set E \ R; its connected components partition V. Call R valid if for every connected component C of G_R, the integer sum_{v in C} values[v] is divisible by k. If S is not divisible by k, set r = 0; otherwise set r = max { |R| + 1 | R is a valid subset of E }. The function returns Result.ok r, where r is the i64 representing this integer.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; all sums mentioned in the statement are within the i64 range. -/
theorem spec_1 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hsums : ∀ (R : Finset Nat) (v : Nat), R ⊆ Finset.range edges.val.length → v < n.val.toNat →
      -(2 ^ 63) ≤ compSum n.val.toNat edges values R v ∧
        compSum n.val.toNat edges values R v ≤ 2 ^ 63 - 1) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (k.val ∣ totalSum n.val.toNat values →
          IsMaxComponents n.val.toNat edges values k.val r.val) ∧
        (¬ k.val ∣ totalSum n.val.toNat values → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hsums : ∀ (R : Finset Nat) (v : Nat), R ⊆ Finset.range edges.val.length → v < n.val.toNat →
      -(2 ^ 63) ≤ compSum n.val.toNat edges values R v ∧
        compSum n.val.toNat edges values R v ≤ 2 ^ 63 - 1), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (k.val ∣ totalSum n.val.toNat values →
          IsMaxComponents n.val.toNat edges values k.val r.val) ∧
        (¬ k.val ∣ totalSum n.val.toNat values → r.val = 0)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result: there exists an i64 r such that max_k_divisible_components n edges values k = Result.ok r. It does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_2 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, max_k_divisible_components n edges values k = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9), ∃ r : Std.I64, max_k_divisible_components n edges values k = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, the integer value of r satisfies 0 <= r <= n.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9. -/
theorem spec_3 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9) :
    ∀ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r → 0 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9), ∀ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r → 0 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_4 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64, max_k_divisible_components n edges values k = Result.ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64, max_k_divisible_components n edges values k = Result.ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = n if and only if for every i with 0 <= i < n, values[i] is divisible by k.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_5 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (r.val = n.val ↔ ∀ i : Nat, i < n.val.toNat → k.val ∣ valAt values i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (r.val = n.val ↔ ∀ i : Nat, i < n.val.toNat → k.val ∣ valAt values i)) := by
  sorry

/-- The function returns a result r, and r >= 2 if and only if there exists an edge {a,b} in E such that in the graph (V, E \ {{a,b}}), the two connected components both have value divisible by k.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_6 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (2 ≤ r.val ↔ ∃ i : Fin edges.val.length,
          ValidRemoval n.val.toNat edges values k.val {(i : Nat)}) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (2 ≤ r.val ↔ ∃ i : Fin edges.val.length,
          ValidRemoval n.val.toNat edges values k.val {(i : Nat)})) := by
  sorry

/-- The function returns a result r, and for every integer j with 1 <= j <= r there exists a subset R of E such that |R| + 1 = j and every connected component of G_R has value divisible by k.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_7 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∀ j : Int, 1 ≤ j → j ≤ r.val → ∃ R : Finset Nat,
          R ⊆ Finset.range edges.val.length ∧ (R.card : Int) + 1 = j ∧
            ValidRemoval n.val.toNat edges values k.val R) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∀ j : Int, 1 ≤ j → j ≤ r.val → ∃ R : Finset Nat,
          R ⊆ Finset.range edges.val.length ∧ (R.card : Int) + 1 = j ∧
            ValidRemoval n.val.toNat edges values k.val R)) := by
  sorry

/-- The function returns a result r and there exists a subset R of E such that |R| = r - 1 and every connected component of G_R has value divisible by k.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_8 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∃ R : Finset Nat,
          R ⊆ Finset.range edges.val.length ∧ (R.card : Int) = r.val - 1 ∧
            ValidRemoval n.val.toNat edges values k.val R) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∃ R : Finset Nat,
          R ⊆ Finset.range edges.val.length ∧ (R.card : Int) = r.val - 1 ∧
            ValidRemoval n.val.toNat edges values k.val R)) := by
  sorry

/-- The function returns a result r, and for every subset R of E, if every connected component of G_R has value divisible by k, then |R| + 1 <= r.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_9 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∀ R : Finset Nat,
          R ⊆ Finset.range edges.val.length → ValidRemoval n.val.toNat edges values k.val R →
            (R.card : Int) + 1 ≤ r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        (∀ R : Finset Nat,
          R ⊆ Finset.range edges.val.length → ValidRemoval n.val.toNat edges values k.val R →
            (R.card : Int) + 1 ≤ r.val)) := by
  sorry

/-- Let r be the result of max_k_divisible_components n edges values k and let r' be the result of max_k_divisible_components n edges' values k. Whenever both calls return results, the integer values r and r' are equal.
  Preconditions: n, values, and k satisfy 1 <= n <= 30000, len(values) = n, 0 <= values[i] <= 10^9 for every i, and 1 <= k <= 10^9. Both edges and edges' are lists of unordered pairs that represent the same valid undirected tree on nodes 0,...,n-1; each has length n-1 and each pair has endpoints in 0,...,n-1. -/
theorem spec_10 (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges) (htree' : IsTree n.val.toNat edges')
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9) :
    ∀ r r' : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r →
        max_k_divisible_components n edges' values k = Result.ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (edges edges' : Slice (alloc.vec.Vec Std.I64))
    (values : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges) (htree' : IsTree n.val.toNat edges')
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9), ∀ r r' : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r →
        max_k_divisible_components n edges' values k = Result.ok r' → r.val = r'.val) := by
  sorry

/-- Let V = {0,...,n-1} and E = {{edges[i][0], edges[i][1]} | 0 <= i < len(edges)}. For each e in E, deleting e from the tree splits V into two connected components; define T as the set of e in E for which at least one of these two components has value divisible by k. Then the function returns Result.ok r with r = |T| + 1.
  Preconditions: 1 <= n <= 30000; len(edges) = n - 1; for every i with 0 <= i < len(edges), len(edges[i]) = 2 and 0 <= edges[i][0], edges[i][1] < n; edges represents a valid undirected tree on nodes 0,...,n-1; len(values) = n; for every i with 0 <= i < n, 0 <= values[i] <= 10^9; 1 <= k <= 10^9; sum_{i=0}^{n-1} values[i] is divisible by k. -/
theorem spec_11 (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values) :
    ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        r.val = ((cutSet n.val.toNat edges values k.val).card : Int) + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64)) (values : Slice Std.I64)
    (k : Std.I64)
    (hn_pos : 1 ≤ n.val) (hn_bound : n.val ≤ 30000)
    (htree : IsTree n.val.toNat edges)
    (hvalues_len : values.val.length = n.val.toNat)
    (hvalues_bound : ∀ i : Nat, i < n.val.toNat → 0 ≤ valAt values i ∧ valAt values i ≤ 10 ^ 9)
    (hk_pos : 1 ≤ k.val) (hk_bound : k.val ≤ 10 ^ 9)
    (hdiv : k.val ∣ totalSum n.val.toNat values), ∃ r : Std.I64,
      max_k_divisible_components n edges values k = Result.ok r ∧
        r.val = ((cutSet n.val.toNat edges values k.val).card : Int) + 1) := by
  sorry

end AegisSpec.MaxKDivisibleComponents
