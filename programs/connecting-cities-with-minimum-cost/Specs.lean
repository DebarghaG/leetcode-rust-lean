import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `connecting-cities-with-minimum-cost`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumCost

open Aegis.MinimumCost

def connA (connections : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (connections.val[i]!).val[0]!.val

def connB (connections : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (connections.val[i]!).val[1]!.val

def connC (connections : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (connections.val[i]!).val[2]!.val

def IsCity (n : Int) (u : Int) : Prop :=
  1 ≤ u ∧ u ≤ n

def IsSelectedEdge (connections : Slice (alloc.vec.Vec I64)) (S : Finset Nat) (u v : Int) : Prop :=
  ∃ i ∈ S,
    (u = connA connections i ∧ v = connB connections i) ∨
      (u = connB connections i ∧ v = connA connections i)

inductive Walk (connections : Slice (alloc.vec.Vec I64)) (S : Finset Nat) : Int → Int → Prop where

  | nil (u : Int) : Walk connections S u u

  | step {u v w : Int} :
      IsSelectedEdge connections S u v → Walk connections S v w → Walk connections S u w

def Connects (n : Int) (connections : Slice (alloc.vec.Vec I64)) (S : Finset Nat) : Prop :=
  ∀ u, IsCity n u → ∀ v, IsCity n v → Walk connections S u v

def Feasible (n : Int) (connections : Slice (alloc.vec.Vec I64)) (S : Finset Nat) : Prop :=
  S ⊆ Finset.range connections.val.length ∧ Connects n connections S

def Cost (connections : Slice (alloc.vec.Vec I64)) (S : Finset Nat) : Int :=
  ∑ i ∈ S, connC connections i

/-- Let V = {1,...,n}. For each index i with 0 <= i < len(connections), let a_i = connections[i][0], b_i = connections[i][1], and c_i = connections[i][2]. A subset S of the index set {0,...,len(connections)-1} is feasible if, for every pair of cities u,v in V, there is a walk using only selected connections: there exist m >= 0 and vertices p_0,...,p_m such that p_0 = u, p_m = v, and for each j = 1,...,m there is an index t_j in S such that the unordered pair {p_{j-1}, p_j} equals {a_{t_j}, b_{t_j}}. For such S, let Cost(S) = sum over i in S of c_i. The function returns a result r and: if some feasible S exists, then r is the minimum of Cost(S) over all feasible S, meaning there is a feasible S0 with Cost(S0) = r and r <= Cost(T) for every feasible T; if no feasible S exists, then r = -1.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. All quantities fit in 64-bit integers. -/
theorem spec_1 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∃ r : I64,
      minimum_cost n connections = ok r ∧
        ((∃ S : Finset Nat, Feasible n.val connections S) →
          ∃ S0 : Finset Nat,
            Feasible n.val connections S0 ∧ Cost connections S0 = r.val ∧
              ∀ T : Finset Nat, Feasible n.val connections T → r.val ≤ Cost connections T) ∧
        ((¬ ∃ S : Finset Nat, Feasible n.val connections S) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∃ r : I64,
      minimum_cost n connections = ok r ∧
        ((∃ S : Finset Nat, Feasible n.val connections S) →
          ∃ S0 : Finset Nat,
            Feasible n.val connections S0 ∧ Cost connections S0 = r.val ∧
              ∀ T : Finset Nat, Feasible n.val connections T → r.val ≤ Cost connections T) ∧
        ((¬ ∃ S : Finset Nat, Feasible n.val connections S) → r.val = -1)) := by
  sorry

/-- There exists an integer r such that minimum_cost n connections evaluates to Result.ok r. The function does not fail, panic, overflow, or access out of bounds.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. All quantities fit in 64-bit integers. -/
theorem spec_2 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∃ r : I64, minimum_cost n connections = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∃ r : I64, minimum_cost n connections = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then 0 <= r.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_3 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64, minimum_cost n connections = ok r → r.val ≠ -1 → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64, minimum_cost n connections = ok r → r.val ≠ -1 → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then r <= sum over i from 0 to len(connections)-1 of connections[i][2].
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_4 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        r.val ≤ ∑ i ∈ Finset.range connections.val.length, connC connections i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        r.val ≤ ∑ i ∈ Finset.range connections.val.length, connC connections i) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if no subset S of the connection indices connects all cities in {1,...,n}; here a subset connects all cities when every pair of cities can be joined by a path whose edges are exactly the connections with indices in S, and the empty subset is allowed.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_5 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r →
        (r.val = -1 ↔ ¬ ∃ S : Finset Nat, Feasible n.val connections S) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r →
        (r.val = -1 ↔ ¬ ∃ S : Finset Nat, Feasible n.val connections S)) := by
  sorry

/-- Whenever the function returns a result r, if n > 1 and len(connections) < n - 1, then r = -1.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_6 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r → 1 < n.val →
        (connections.val.length : Int) < n.val - 1 → r.val = -1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r → 1 < n.val →
        (connections.val.length : Int) < n.val - 1 → r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then there exists a subset S of the connection indices such that S connects all cities in {1,...,n} and the sum of connections[i][2] over i in S equals r.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_7 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∃ S : Finset Nat, Feasible n.val connections S ∧ Cost connections S = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∃ S : Finset Nat, Feasible n.val connections S ∧ Cost connections S = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then for every subset T of the connection indices that connects all cities in {1,...,n}, r <= sum over i in T of connections[i][2].
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_8 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∀ T : Finset Nat, Feasible n.val connections T → r.val ≤ Cost connections T := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∀ T : Finset Nat, Feasible n.val connections T → r.val ≤ Cost connections T) := by
  sorry

/-- Whenever the function returns a result r, if r != -1 then there exists a subset S of the connection indices such that S connects all cities in {1,...,n}, the cardinality of S is exactly n - 1, and the sum of connections[i][2] over i in S equals r.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_9 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∃ S : Finset Nat,
          Feasible n.val connections S ∧ (S.card : Int) = n.val - 1 ∧
            Cost connections S = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 →
        ∃ S : Finset Nat,
          Feasible n.val connections S ∧ (S.card : Int) = n.val - 1 ∧
            Cost connections S = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a subset S of the connection indices such that S connects all cities in {1,...,n} and the sum of connections[i][2] over i in S is 0.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_10 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000) :
    ∀ r : I64,
      minimum_cost n connections = ok r →
        (r.val = 0 ↔ ∃ S : Finset Nat, Feasible n.val connections S ∧ Cost connections S = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000), ∀ r : I64,
      minimum_cost n connections = ok r →
        (r.val = 0 ↔ ∃ S : Finset Nat, Feasible n.val connections S ∧ Cost connections S = 0)) := by
  sorry

/-- Whenever both calls return results r and r_prime, we have r = r_prime.
  Preconditions: Both (n, connections) and (n, connections_prime) satisfy the problem constraints, and connections_prime is any permutation of the entries of connections; equivalently, connections_prime has the same length and the same multiset of triples as connections. -/
theorem spec_11 (n : I64) (connections connections_prime : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (hm2_lo : 1 ≤ connections_prime.val.length)
    (hm2_hi : connections_prime.val.length ≤ 10000)
    (h2_row : ∀ i, i < connections_prime.val.length →
      (connections_prime.val[i]!).val.length = 3)
    (h2_a : ∀ i, i < connections_prime.val.length →
      1 ≤ connA connections_prime i ∧ connA connections_prime i ≤ n.val)
    (h2_b : ∀ i, i < connections_prime.val.length →
      1 ≤ connB connections_prime i ∧ connB connections_prime i ≤ n.val)
    (h2_ne : ∀ i, i < connections_prime.val.length →
      connA connections_prime i ≠ connB connections_prime i)
    (h2_c : ∀ i, i < connections_prime.val.length →
      0 ≤ connC connections_prime i ∧ connC connections_prime i ≤ 100000)
    (h_perm : connections.val.Perm connections_prime.val) :
    ∀ r r_prime : I64,
      minimum_cost n connections = ok r → minimum_cost n connections_prime = ok r_prime →
        r = r_prime := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : I64) (connections connections_prime : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (hm2_lo : 1 ≤ connections_prime.val.length)
    (hm2_hi : connections_prime.val.length ≤ 10000)
    (h2_row : ∀ i, i < connections_prime.val.length →
      (connections_prime.val[i]!).val.length = 3)
    (h2_a : ∀ i, i < connections_prime.val.length →
      1 ≤ connA connections_prime i ∧ connA connections_prime i ≤ n.val)
    (h2_b : ∀ i, i < connections_prime.val.length →
      1 ≤ connB connections_prime i ∧ connB connections_prime i ≤ n.val)
    (h2_ne : ∀ i, i < connections_prime.val.length →
      connA connections_prime i ≠ connB connections_prime i)
    (h2_c : ∀ i, i < connections_prime.val.length →
      0 ≤ connC connections_prime i ∧ connC connections_prime i ≤ 100000)
    (h_perm : connections.val.Perm connections_prime.val), ∀ r r_prime : I64,
      minimum_cost n connections = ok r → minimum_cost n connections_prime = ok r_prime →
        r = r_prime) := by
  sorry

/-- Let m be the minimum of connections[i][2] over all 0 <= i < len(connections). Whenever the function returns a result r, if r != -1 then r >= (n - 1) * m.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_12 (n : I64) (connections : Slice (alloc.vec.Vec I64)) (m : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_m_lb : ∀ i, i < connections.val.length → m ≤ connC connections i)
    (h_m_at : ∃ i, i < connections.val.length ∧ connC connections i = m) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 → (n.val - 1) * m ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64)) (m : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_m_lb : ∀ i, i < connections.val.length → m ≤ connC connections i)
    (h_m_at : ∃ i, i < connections.val.length ∧ connC connections i = m), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 → (n.val - 1) * m ≤ r.val) := by
  sorry

/-- Let M be the maximum of connections[i][2] over all 0 <= i < len(connections). Whenever the function returns a result r, if r != -1 then r <= (n - 1) * M.
  Preconditions: n and connections satisfy the problem constraints: 1 <= n <= 10^4; 1 <= len(connections) <= 10^4; for every i with 0 <= i < len(connections), len(connections[i]) = 3, 1 <= connections[i][0] <= n, 1 <= connections[i][1] <= n, connections[i][0] != connections[i][1], and 0 <= connections[i][2] <= 10^5. -/
theorem spec_13 (n : I64) (connections : Slice (alloc.vec.Vec I64)) (M : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_M_ub : ∀ i, i < connections.val.length → connC connections i ≤ M)
    (h_M_at : ∃ i, i < connections.val.length ∧ connC connections i = M) :
    ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 → r.val ≤ (n.val - 1) * M := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64)) (M : Int)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_M_ub : ∀ i, i < connections.val.length → connC connections i ≤ M)
    (h_M_at : ∃ i, i < connections.val.length ∧ connC connections i = M), ∀ r : I64,
      minimum_cost n connections = ok r → r.val ≠ -1 → r.val ≤ (n.val - 1) * M) := by
  sorry

/-- Whenever the function returns a result r, r = sum over i from 0 to len(connections)-1 of connections[i][2].
  Preconditions: n and connections satisfy the problem constraints, and additionally len(connections) = n - 1 and the graph using all given connections connects all cities in {1,...,n}. -/
theorem spec_14 (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_len : (connections.val.length : Int) = n.val - 1)
    (h_conn : Connects n.val connections (Finset.range connections.val.length)) :
    ∀ r : I64,
      minimum_cost n connections = ok r →
        r.val = ∑ i ∈ Finset.range connections.val.length, connC connections i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : I64) (connections : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (h_len : (connections.val.length : Int) = n.val - 1)
    (h_conn : Connects n.val connections (Finset.range connections.val.length)), ∀ r : I64,
      minimum_cost n connections = ok r →
        r.val = ∑ i ∈ Finset.range connections.val.length, connC connections i) := by
  sorry

/-- Whenever both calls return results r and r_prime, either r = -1 and r_prime = -1, or r != -1, r_prime != -1, and r <= r_prime.
  Preconditions: Both (n, connections) and (n, connections_prime) satisfy the problem constraints. They have the same length, and for every i with 0 <= i < len(connections): connections_prime[i][0] = connections[i][0], connections_prime[i][1] = connections[i][1], and connections[i][2] <= connections_prime[i][2]. -/
theorem spec_15 (n : I64) (connections connections_prime : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (hm2_lo : 1 ≤ connections_prime.val.length)
    (hm2_hi : connections_prime.val.length ≤ 10000)
    (h2_row : ∀ i, i < connections_prime.val.length →
      (connections_prime.val[i]!).val.length = 3)
    (h2_a : ∀ i, i < connections_prime.val.length →
      1 ≤ connA connections_prime i ∧ connA connections_prime i ≤ n.val)
    (h2_b : ∀ i, i < connections_prime.val.length →
      1 ≤ connB connections_prime i ∧ connB connections_prime i ≤ n.val)
    (h2_ne : ∀ i, i < connections_prime.val.length →
      connA connections_prime i ≠ connB connections_prime i)
    (h2_c : ∀ i, i < connections_prime.val.length →
      0 ≤ connC connections_prime i ∧ connC connections_prime i ≤ 100000)
    (h_len : connections.val.length = connections_prime.val.length)
    (h_same_a : ∀ i, i < connections.val.length →
      connA connections_prime i = connA connections i)
    (h_same_b : ∀ i, i < connections.val.length →
      connB connections_prime i = connB connections i)
    (h_c_le : ∀ i, i < connections.val.length →
      connC connections i ≤ connC connections_prime i) :
    ∀ r r_prime : I64,
      minimum_cost n connections = ok r → minimum_cost n connections_prime = ok r_prime →
        (r.val = -1 ∧ r_prime.val = -1) ∨
          (r.val ≠ -1 ∧ r_prime.val ≠ -1 ∧ r.val ≤ r_prime.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : I64) (connections connections_prime : Slice (alloc.vec.Vec I64))
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000)
    (hm_lo : 1 ≤ connections.val.length) (hm_hi : connections.val.length ≤ 10000)
    (h_row : ∀ i, i < connections.val.length → (connections.val[i]!).val.length = 3)
    (h_a : ∀ i, i < connections.val.length →
      1 ≤ connA connections i ∧ connA connections i ≤ n.val)
    (h_b : ∀ i, i < connections.val.length →
      1 ≤ connB connections i ∧ connB connections i ≤ n.val)
    (h_ne : ∀ i, i < connections.val.length → connA connections i ≠ connB connections i)
    (h_c : ∀ i, i < connections.val.length →
      0 ≤ connC connections i ∧ connC connections i ≤ 100000)
    (hm2_lo : 1 ≤ connections_prime.val.length)
    (hm2_hi : connections_prime.val.length ≤ 10000)
    (h2_row : ∀ i, i < connections_prime.val.length →
      (connections_prime.val[i]!).val.length = 3)
    (h2_a : ∀ i, i < connections_prime.val.length →
      1 ≤ connA connections_prime i ∧ connA connections_prime i ≤ n.val)
    (h2_b : ∀ i, i < connections_prime.val.length →
      1 ≤ connB connections_prime i ∧ connB connections_prime i ≤ n.val)
    (h2_ne : ∀ i, i < connections_prime.val.length →
      connA connections_prime i ≠ connB connections_prime i)
    (h2_c : ∀ i, i < connections_prime.val.length →
      0 ≤ connC connections_prime i ∧ connC connections_prime i ≤ 100000)
    (h_len : connections.val.length = connections_prime.val.length)
    (h_same_a : ∀ i, i < connections.val.length →
      connA connections_prime i = connA connections i)
    (h_same_b : ∀ i, i < connections.val.length →
      connB connections_prime i = connB connections i)
    (h_c_le : ∀ i, i < connections.val.length →
      connC connections i ≤ connC connections_prime i), ∀ r r_prime : I64,
      minimum_cost n connections = ok r → minimum_cost n connections_prime = ok r_prime →
        (r.val = -1 ∧ r_prime.val = -1) ∨
          (r.val ≠ -1 ∧ r_prime.val ≠ -1 ∧ r.val ≤ r_prime.val)) := by
  sorry

end AegisSpec.MinimumCost
