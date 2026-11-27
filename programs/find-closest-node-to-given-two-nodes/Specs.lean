import Aegis.ClosestMeetingNode.Code.Funs

/-!
# Specifications of `Aegis.ClosestMeetingNode.closest_meeting_node`

LeetCode problem `find-closest-node-to-given-two-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosestMeetingNode

def edgeAt (edges : Slice Std.I64) (i : ℕ) : Option ℤ :=
  (edges.val[i]?).map (fun e => e.val)

def edgeAtZ (edges : Slice Std.I64) (u : ℤ) : Option ℤ :=
  if 0 ≤ u then edgeAt edges u.toNat else none

def Walk (edges : Slice Std.I64) (u v : ℤ) : ℕ → Prop
  | 0 => v = u
  | k + 1 =>
    (0 ≤ u ∧ u < (edges.length : ℤ)) ∧
      ∃ w : ℤ, edgeAtZ edges u = some w ∧ Walk edges w v k

noncomputable def dist (edges : Slice Std.I64) (u v : ℤ) : Option ℕ := by
  classical
  exact if h : ∃ k, Walk edges u v k then some (Nat.find h) else none

noncomputable def cost (edges : Slice Std.I64) (node1 node2 x : ℤ) : Option ℕ :=
  match dist edges node1 x, dist edges node2 x with
  | some d1, some d2 => some (Nat.max d1 d2)
  | _, _ => none

noncomputable def Common (edges : Slice Std.I64) (node1 node2 x : ℤ) : Prop :=
  (cost edges node1 node2 x).isSome

noncomputable def CostLe (edges : Slice Std.I64) (node1 node2 x y : ℤ) : Prop :=
  ∀ cx cy : ℕ, cost edges node1 node2 x = some cx → cost edges node1 node2 y = some cy → cx ≤ cy

noncomputable def CostLt (edges : Slice Std.I64) (node1 node2 x y : ℤ) : Prop :=
  ∀ cx cy : ℕ, cost edges node1 node2 x = some cx → cost edges node1 node2 y = some cy → cx < cy

theorem toNat_lt_length (edges : Slice Std.I64) (z : ℤ)
    (h_lo : 0 ≤ z) (h_hi : z < (edges.length : ℤ)) : z.toNat < edges.length := by
  omega

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. A node x with 0 <= x < n is common iff dist(node1,x) and dist(node2,x) are both defined, and its cost is max(dist(node1,x), dist(node2,x)). The function returns a result r and the following holds. If some node x with 0 <= x < n is common, then 0 <= r < n, r is common, for every common x with 0 <= x < n cost(r) <= cost(x), and for every integer y with 0 <= y < r, either y is not common or cost(y) > cost(r). If no node x with 0 <= x < n is common, then r = -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_1
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∃ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r ∧
        ((∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          (0 ≤ r.val ∧ r.val < (edges.length : ℤ) ∧
            Common edges node1.val node2.val r.val ∧
            (∀ x : ℤ, 0 ≤ x → x < (edges.length : ℤ) →
              Common edges node1.val node2.val x →
                CostLe edges node1.val node2.val r.val x) ∧
            (∀ y : ℤ, 0 ≤ y → y < r.val →
              ¬ Common edges node1.val node2.val y ∨
                CostLt edges node1.val node2.val r.val y))) ∧
        ((¬ ∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∃ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r ∧
        ((∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          (0 ≤ r.val ∧ r.val < (edges.length : ℤ) ∧
            Common edges node1.val node2.val r.val ∧
            (∀ x : ℤ, 0 ≤ x → x < (edges.length : ℤ) →
              Common edges node1.val node2.val x →
                CostLe edges node1.val node2.val r.val x) ∧
            (∀ y : ℤ, 0 ≤ y → y < r.val →
              ¬ Common edges node1.val node2.val y ∨
                CostLt edges node1.val node2.val r.val y))) ∧
        ((¬ ∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_2
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∃ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∃ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 0 <= r < len(edges).
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_3
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (edges.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (edges.length : ℤ))) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. Whenever the function returns a result r with r != -1, both dist(node1,r) and dist(node2,r) are defined.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_4
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        (∃ d : ℕ, dist edges node1.val r.val = some d) ∧
          (∃ d : ℕ, dist edges node2.val r.val = some d) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        (∃ d : ℕ, dist edges node1.val r.val = some d) ∧
          (∃ d : ℕ, dist edges node2.val r.val = some d)) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. A node x with 0 <= x < n is common iff dist(node1,x) and dist(node2,x) are both defined, and its cost is max(dist(node1,x), dist(node2,x)). Whenever the function returns a result r with r != -1, r is common and for every common x with 0 <= x < n, cost(r) <= cost(x).
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_5
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        Common edges node1.val node2.val r.val ∧
          (∀ x : ℤ, 0 ≤ x → x < (edges.length : ℤ) → Common edges node1.val node2.val x →
            CostLe edges node1.val node2.val r.val x) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        Common edges node1.val node2.val r.val ∧
          (∀ x : ℤ, 0 ≤ x → x < (edges.length : ℤ) → Common edges node1.val node2.val x →
            CostLe edges node1.val node2.val r.val x)) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. A node x with 0 <= x < n is common iff dist(node1,x) and dist(node2,x) are both defined, and its cost is max(dist(node1,x), dist(node2,x)). Whenever the function returns a result r with r != -1, r is common and for every integer y with 0 <= y < r, either y is not common or cost(y) > cost(r).
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_6
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        Common edges node1.val node2.val r.val ∧
          (∀ y : ℤ, 0 ≤ y → y < r.val →
            ¬ Common edges node1.val node2.val y ∨
              CostLt edges node1.val node2.val r.val y) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r → r.val ≠ -1 →
        Common edges node1.val node2.val r.val ∧
          (∀ y : ℤ, 0 ≤ y → y < r.val →
            ¬ Common edges node1.val node2.val y ∨
              CostLt edges node1.val node2.val r.val y)) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. A node x with 0 <= x < n is common iff dist(node1,x) and dist(node2,x) are both defined. Whenever the function returns a result r, if no node x with 0 <= x < n is common, then r = -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_7
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (¬ ∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (¬ ∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val = -1) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. A node x with 0 <= x < n is common iff dist(node1,x) and dist(node2,x) are both defined. Whenever the function returns a result r, if there exists a node x with 0 <= x < n that is common, then r != -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_8
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val ≠ -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (∃ x : ℤ, 0 ≤ x ∧ x < (edges.length : ℤ) ∧ Common edges node1.val node2.val x) →
          r.val ≠ -1) := by
  sorry

/-- Whenever the function returns a result r, if node1 = node2, then r = node1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_9
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        node1 = node2 → r = node1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        node1 = node2 → r = node1) := by
  sorry

/-- Whenever the function returns a result r, if edges[i] = -1 for every i with 0 <= i < n and node1 != node2, then r = -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. -/
theorem spec_10
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (∀ (i : ℕ) (hi : i < edges.length), (edges.val[i]).val = -1) →
          node1 ≠ node2 → r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ)), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        (∀ (i : ℕ) (hi : i < edges.length), (edges.val[i]).val = -1) →
          node1 ≠ node2 → r.val = -1) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. Whenever the function returns a result r, if dist(node1,node2) is defined then r = node2; otherwise r = -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. Additionally edges[node2] = -1. -/
theorem spec_11
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_edge2 : (edges.val[node2.val.toNat]'
      (toNat_lt_length edges node2.val h_node2_lo h_node2_hi)).val = -1) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        ((∃ d : ℕ, dist edges node1.val node2.val = some d) → r = node2) ∧
          ((¬ ∃ d : ℕ, dist edges node1.val node2.val = some d) → r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_edge2 : (edges.val[node2.val.toNat]'
      (toNat_lt_length edges node2.val h_node2_lo h_node2_hi)).val = -1), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        ((∃ d : ℕ, dist edges node1.val node2.val = some d) → r = node2) ∧
          ((¬ ∃ d : ℕ, dist edges node1.val node2.val = some d) → r.val = -1)) := by
  sorry

/-- Let n = len(edges). For u and v with 0 <= u,v < n, dist(u,v) is the least integer k >= 0 for which there exist nodes w_0,...,w_k with w_0 = u, w_k = v, and for every j with 0 <= j < k, 0 <= w_j < n and edges[w_j] = w_{j+1}; dist(u,v) is undefined if no such k exists. Whenever the function returns a result r, if dist(node2,node1) is defined then r = node1; otherwise r = -1.
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. Additionally edges[node1] = -1. -/
theorem spec_12
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_edge1 : (edges.val[node1.val.toNat]'
      (toNat_lt_length edges node1.val h_node1_lo h_node1_hi)).val = -1) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        ((∃ d : ℕ, dist edges node2.val node1.val = some d) → r = node1) ∧
          ((¬ ∃ d : ℕ, dist edges node2.val node1.val = some d) → r.val = -1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_edge1 : (edges.val[node1.val.toNat]'
      (toNat_lt_length edges node1.val h_node1_lo h_node1_hi)).val = -1), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        ((∃ d : ℕ, dist edges node2.val node1.val = some d) → r = node1) ∧
          ((¬ ∃ d : ℕ, dist edges node2.val node1.val = some d) → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r, r = min(node1,node2).
  Preconditions: Let n = len(edges). 2 <= n <= 100000. For every i with 0 <= i < n, -1 <= edges[i] < n and edges[i] != i. Also 0 <= node1 < n and 0 <= node2 < n. Additionally node1 != node2, edges[node1] = node2, and edges[node2] = node1. -/
theorem spec_13
    (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_node1_ne : node1 ≠ node2)
    (h_edge1 : (edges.val[node1.val.toNat]'
      (toNat_lt_length edges node1.val h_node1_lo h_node1_hi)).val = node2.val)
    (h_edge2 : (edges.val[node2.val.toNat]'
      (toNat_lt_length edges node2.val h_node2_lo h_node2_hi)).val = node1.val) :
    ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        r.val = min node1.val node2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (edges : Slice Std.I64) (node1 node2 : Std.I64)
    (h_n_ge : 2 ≤ edges.length) (h_n_le : edges.length ≤ 100000)
    (h_edges : ∀ (i : ℕ) (hi : i < edges.length),
      -1 ≤ (edges.val[i]).val ∧ (edges.val[i]).val < (edges.length : ℤ) ∧
        (edges.val[i]).val ≠ (i : ℤ))
    (h_node1_lo : 0 ≤ node1.val) (h_node1_hi : node1.val < (edges.length : ℤ))
    (h_node2_lo : 0 ≤ node2.val) (h_node2_hi : node2.val < (edges.length : ℤ))
    (h_node1_ne : node1 ≠ node2)
    (h_edge1 : (edges.val[node1.val.toNat]'
      (toNat_lt_length edges node1.val h_node1_lo h_node1_hi)).val = node2.val)
    (h_edge2 : (edges.val[node2.val.toNat]'
      (toNat_lt_length edges node2.val h_node2_lo h_node2_hi)).val = node1.val), ∀ r : Std.I64,
      Aegis.ClosestMeetingNode.closest_meeting_node edges node1 node2 = ok r →
        r.val = min node1.val node2.val) := by
  sorry

end AegisSpec.ClosestMeetingNode
