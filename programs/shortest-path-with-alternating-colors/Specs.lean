import Aegis.ShortestAlternatingPaths.Code.Funs

/-!
# Specifications of `Aegis.ShortestAlternatingPaths.shortest_alternating_paths`

LeetCode problem `shortest-path-with-alternating-colors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.ShortestAlternatingPaths (shortest_alternating_paths)

namespace AegisSpec.ShortestAlternatingPaths

abbrev VecI64 : Type := alloc.vec.Vec Std.I64

abbrev EdgeList : Type := Slice VecI64

def vecVals (v : VecI64) : List Int := v.val.map fun e => e.val

def vecGet (v : VecI64) (x : Nat) : Option Int := (vecVals v)[x]?

def EdgeMem (E : EdgeList) (a b : Int) : Prop := ∃ v, v ∈ E.val ∧ vecVals v = [a, b]

mutual

  inductive RedWalk (R B : EdgeList) : Int → Int → Nat → Prop

    | one {a b : Int} (h : EdgeMem R a b) : RedWalk R B a b 1

    | cons {a b x : Int} {k : Nat} (h : EdgeMem R a b) (t : BlueWalk R B b x k) :
        RedWalk R B a x (k + 1)

  inductive BlueWalk (R B : EdgeList) : Int → Int → Nat → Prop

    | one {a b : Int} (h : EdgeMem B a b) : BlueWalk R B a b 1

    | cons {a b x : Int} {k : Nat} (h : EdgeMem B a b) (t : RedWalk R B b x k) :
        BlueWalk R B a x (k + 1)
end

def AltWalk (R B : EdgeList) (x : Int) (k : Nat) : Prop :=
  (k = 0 ∧ x = 0) ∨ RedWalk R B 0 x k ∨ BlueWalk R B 0 x k

/-- Whenever the function returns a result r, len(r) = n and for every x with 0 <= x < n the following holds. Let W_x be the set of all k >= 0 for which there exists an alternating walk from node 0 to node x of length k. If W_x is nonempty, then r[x] = min(W_x); if W_x is empty, then r[x] = -1. An alternating walk of length k is a sequence of nodes p_0, ..., p_k with p_0 = 0 and p_k = x together with colors c_0, ..., c_{k-1} in {red, blue} such that for each j with 0 <= j < k, c_j = red implies redEdges contains [p_j, p_{j+1}] and c_j = blue implies blueEdges contains [p_j, p_{j+1}], and for each j with 0 <= j < k-1, c_j != c_{j+1}. Here redEdges contains [a,b] means there is an index i with redEdges[i] = [a,b], and similarly for blueEdges. For k = 0 the sequence has no colors and the walk exists exactly when x = 0. Length means number of edges.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_1
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      (r.val.length : Int) = n.val ∧
        ∀ x : Nat, (x : Int) < n.val →
          ((∃ k : Nat, AltWalk redEdges blueEdges (x : Int) k) →
              ∃ m : Nat, AltWalk redEdges blueEdges (x : Int) m ∧
                (∀ k : Nat, AltWalk redEdges blueEdges (x : Int) k → m ≤ k) ∧
                vecGet r x = some (m : Int)) ∧
          ((¬ ∃ k : Nat, AltWalk redEdges blueEdges (x : Int) k) →
              vecGet r x = some (-1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      (r.val.length : Int) = n.val ∧
        ∀ x : Nat, (x : Int) < n.val →
          ((∃ k : Nat, AltWalk redEdges blueEdges (x : Int) k) →
              ∃ m : Nat, AltWalk redEdges blueEdges (x : Int) m ∧
                (∀ k : Nat, AltWalk redEdges blueEdges (x : Int) k → m ≤ k) ∧
                vecGet r x = some (m : Int)) ∧
          ((¬ ∃ k : Nat, AltWalk redEdges blueEdges (x : Int) k) →
              vecGet r x = some (-1))) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_2
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      (r.val.length : Int) = n.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      (r.val.length : Int) = n.val) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, r[x] >= -1.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_3
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∃ v : Int, vecGet r x = some v ∧ -1 ≤ v := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∃ v : Int, vecGet r x = some v ∧ -1 ≤ v) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, r[x] <= 2 * n.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_4
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∃ v : Int, vecGet r x = some v ∧ v ≤ 2 * n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∃ v : Int, vecGet r x = some v ∧ v ≤ 2 * n.val) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, r[x] = 0 if and only if x = 0.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_5
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val →
        ∃ v : Int, vecGet r x = some v ∧ (v = 0 ↔ x = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val →
        ∃ v : Int, vecGet r x = some v ∧ (v = 0 ↔ x = 0)) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, if r[x] >= 0 then there exists an alternating walk from node 0 to node x of length exactly r[x], where an alternating walk is a sequence of edges from 0 to x whose colors alternate and whose length is the number of edges.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_6
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∀ v : Int, vecGet r x = some v → 0 ≤ v →
        ∃ k : Nat, (k : Int) = v ∧ AltWalk redEdges blueEdges (x : Int) k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∀ v : Int, vecGet r x = some v → 0 ≤ v →
        ∃ k : Nat, (k : Int) = v ∧ AltWalk redEdges blueEdges (x : Int) k) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, if r[x] >= 0 then for every integer k with 0 <= k < r[x], there is no alternating walk from node 0 to node x of length k.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_7
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∀ v : Int, vecGet r x = some v → 0 ≤ v →
        ∀ k : Nat, (k : Int) < v → ¬ AltWalk redEdges blueEdges (x : Int) k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → ∀ v : Int, vecGet r x = some v → 0 ≤ v →
        ∀ k : Nat, (k : Int) < v → ¬ AltWalk redEdges blueEdges (x : Int) k) := by
  sorry

/-- Whenever the function returns a result r, for every x with 0 <= x < n, if r[x] = -1 then there is no alternating walk from node 0 to node x of any length k >= 0.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_8
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → vecGet r x = some (-1) →
        ∀ k : Nat, ¬ AltWalk redEdges blueEdges (x : Int) k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, (x : Int) < n.val → vecGet r x = some (-1) →
        ∀ k : Nat, ¬ AltWalk redEdges blueEdges (x : Int) k) := by
  sorry

/-- Whenever the function returns a result r, for every x with 1 <= x < n, r[x] = 1 if and only if there exists an index i with redEdges[i] = [0, x] or there exists an index j with blueEdges[j] = [0, x].
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_9
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, 1 ≤ x → (x : Int) < n.val → ∀ v : Int, vecGet r x = some v →
        (v = 1 ↔ EdgeMem redEdges 0 (x : Int) ∨ EdgeMem blueEdges 0 (x : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r →
      ∀ x : Nat, 1 ≤ x → (x : Int) < n.val → ∀ v : Int, vecGet r x = some v →
        (v = 1 ↔ EdgeMem redEdges 0 (x : Int) ∨ EdgeMem blueEdges 0 (x : Int))) := by
  sorry

/-- Whenever the call on (n, redEdges, blueEdges) returns r and the call on (n, blueEdges, redEdges) returns r', we have r = r'.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_10
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∀ r r' : VecI64,
      shortest_alternating_paths n redEdges blueEdges = ok r →
      shortest_alternating_paths n blueEdges redEdges = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∀ r r' : VecI64,
      shortest_alternating_paths n redEdges blueEdges = ok r →
      shortest_alternating_paths n blueEdges redEdges = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the call on (n, redEdges, blueEdges) returns r and the call on (n, redEdges', blueEdges') returns r', we have r = r'.
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. Additionally, redEdges' and blueEdges' satisfy the same length and range constraints, and for every a,b with 0 <= a < n and 0 <= b < n, redEdges' contains [a,b] if and only if redEdges contains [a,b], and blueEdges' contains [a,b] if and only if blueEdges contains [a,b]. -/
theorem spec_11
    (n : Std.I64) (redEdges blueEdges redEdges' blueEdges' : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hred_len' : redEdges'.val.length ≤ 400)
    (hblue_len' : blueEdges'.val.length ≤ 400)
    (hred_wf' : ∀ e ∈ redEdges'.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf' : ∀ e ∈ blueEdges'.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hred_eq : ∀ a b : Int, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val →
      (EdgeMem redEdges' a b ↔ EdgeMem redEdges a b))
    (hblue_eq : ∀ a b : Int, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val →
      (EdgeMem blueEdges' a b ↔ EdgeMem blueEdges a b)) :
    ∀ r r' : VecI64,
      shortest_alternating_paths n redEdges blueEdges = ok r →
      shortest_alternating_paths n redEdges' blueEdges' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges redEdges' blueEdges' : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hred_len' : redEdges'.val.length ≤ 400)
    (hblue_len' : blueEdges'.val.length ≤ 400)
    (hred_wf' : ∀ e ∈ redEdges'.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf' : ∀ e ∈ blueEdges'.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hred_eq : ∀ a b : Int, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val →
      (EdgeMem redEdges' a b ↔ EdgeMem redEdges a b))
    (hblue_eq : ∀ a b : Int, 0 ≤ a → a < n.val → 0 ≤ b → b < n.val →
      (EdgeMem blueEdges' a b ↔ EdgeMem blueEdges a b)), ∀ r r' : VecI64,
      shortest_alternating_paths n redEdges blueEdges = ok r →
      shortest_alternating_paths n redEdges' blueEdges' = ok r' →
      r.val = r'.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, overflow, or access an out-of-bounds index).
  Preconditions: n is an i64 with 1 <= n <= 100. The slices redEdges and blueEdges satisfy 0 <= len(redEdges) <= 400, 0 <= len(blueEdges) <= 400, and for every i with 0 <= i < len(redEdges), len(redEdges[i]) = 2, 0 <= redEdges[i][0] < n, and 0 <= redEdges[i][1] < n; for every j with 0 <= j < len(blueEdges), len(blueEdges[j]) = 2, 0 <= blueEdges[j][0] < n, and 0 <= blueEdges[j][1] < n. Edges are 0-indexed pairs [source, target]; self-edges and parallel edges are allowed. -/
theorem spec_12
    (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val) :
    ∃ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (redEdges blueEdges : EdgeList)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hred_len : redEdges.val.length ≤ 400)
    (hblue_len : blueEdges.val.length ≤ 400)
    (hred_wf : ∀ e ∈ redEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val)
    (hblue_wf : ∀ e ∈ blueEdges.val, e.val.length = 2 ∧ ∀ y ∈ e.val, 0 ≤ y.val ∧ y.val < n.val), ∃ r : VecI64, shortest_alternating_paths n redEdges blueEdges = ok r) := by
  sorry

end AegisSpec.ShortestAlternatingPaths
