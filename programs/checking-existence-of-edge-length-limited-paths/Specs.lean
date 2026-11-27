import Aegis.DistanceLimitedPathsExist.Code.Funs

/-!
# Specifications of `Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist`

LeetCode problem `checking-existence-of-edge-length-limited-paths`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.DistanceLimitedPathsExist

  def row (rows : List (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
    match rows[i]? with
    | some v => v.val
    | none => []

  def field (rows : List (alloc.vec.Vec Std.I64)) (i k : Nat) : Int :=
    (((row rows i)[k]?).map (fun x => x.val)).getD 0

  def answerAt (r : alloc.vec.Vec Bool) (j : Nat) : Bool := r.val.getD j false

  def VertexIn (n v : Int) : Prop := 0 ≤ v ∧ v < n

  def UnorderedPairEq (a b c d : Int) : Prop := (a = c ∧ b = d) ∨ (a = d ∧ b = c)

  def LimitedPath (edgeL : List (alloc.vec.Vec Std.I64)) (n p q L : Int) : Prop :=
    ∃ (k : Nat) (x : Nat → Int),
      x 0 = p ∧ x k = q ∧
      (∀ t, t ≤ k → VertexIn n (x t)) ∧
      (∀ t, t < k →
        ∃ i, i < edgeL.length ∧ field edgeL i 2 < L ∧
          ((field edgeL i 0 = x t ∧ field edgeL i 1 = x (t + 1)) ∨
           (field edgeL i 1 = x t ∧ field edgeL i 0 = x (t + 1))))

  def UndirectedPath (edgeL : List (alloc.vec.Vec Std.I64)) (n p q : Int) : Prop :=
    ∃ (k : Nat) (y : Nat → Int),
      y 0 = p ∧ y k = q ∧
      (∀ t, t ≤ k → VertexIn n (y t)) ∧
      (∀ t, t < k →
        ∃ i, i < edgeL.length ∧
          UnorderedPairEq (field edgeL i 0) (field edgeL i 1) (y t) (y (t + 1)))

  def SimpleLimitedPath (edgeL : List (alloc.vec.Vec Std.I64)) (n p q L : Int) : Prop :=
    ∃ (k : Nat) (x : Nat → Int),
      (k : Int) ≤ n - 1 ∧ x 0 = p ∧ x k = q ∧
      (∀ t, t ≤ k → VertexIn n (x t)) ∧
      (∀ a b, a ≤ k → b ≤ k → x a = x b → a = b) ∧
      (∀ t, t < k →
        ∃ i, i < edgeL.length ∧ field edgeL i 2 < L ∧
          ((field edgeL i 0 = x t ∧ field edgeL i 1 = x (t + 1)) ∨
           (field edgeL i 1 = x t ∧ field edgeL i 0 = x (t + 1))))

  /-- Let p_j = queries[j][0], q_j = queries[j][1], L_j = queries[j][2], u_i = edgeList[i][0], v_i = edgeList[i][1], and d_i = edgeList[i][2]. The function returns a result r such that len(r) = len(queries), and for every j with 0 <= j < len(queries): r[j] = true if and only if there exist an integer k >= 0 and vertices x_0, ..., x_k with x_0 = p_j, x_k = q_j, each x_t in {0, ..., n-1}, and for every t with 0 <= t < k there exists an edge index i with 0 <= i < len(edgeList) such that d_i < L_j and either (u_i = x_t and v_i = x_{t+1}) or (v_i = x_t and u_i = x_{t+1}).
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_1
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∃ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r ∧
        r.val.length = queries.val.length ∧
        ∀ j, j < queries.val.length →
          (answerAt r j = true ↔
            LimitedPath edgeList.val n.val
              (field queries.val j 0) (field queries.val j 1) (field queries.val j 2)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∃ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r ∧
          r.val.length = queries.val.length ∧
          ∀ j, j < queries.val.length →
            (answerAt r j = true ↔
              LimitedPath edgeList.val n.val
                (field queries.val j 0) (field queries.val j 1) (field queries.val j 2))) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(queries).
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_2
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        r.val.length = queries.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          r.val.length = queries.val.length) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on any input satisfying the preconditions.
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_3
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∃ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
        = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∃ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if there is no edge index i with 0 <= i < len(edgeList) such that edgeList[i][2] < queries[j][2] and (edgeList[i][0] = queries[j][0] or edgeList[i][1] = queries[j][0]), then r[j] = false.
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_4
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ j, j < queries.val.length →
          (¬ ∃ i, i < edgeList.val.length ∧
              field edgeList.val i 2 < field queries.val j 2 ∧
              (field edgeList.val i 0 = field queries.val j 0 ∨
               field edgeList.val i 1 = field queries.val j 0)) →
          answerAt r j = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ j, j < queries.val.length →
            (¬ ∃ i, i < edgeList.val.length ∧
                field edgeList.val i 2 < field queries.val j 2 ∧
                (field edgeList.val i 0 = field queries.val j 0 ∨
                 field edgeList.val i 1 = field queries.val j 0)) →
            answerAt r j = false) := by
    sorry

  /-- Whenever the function returns a result r, for all query indices a and b with 0 <= a < len(queries) and 0 <= b < len(queries), if {queries[a][0], queries[a][1]} = {queries[b][0], queries[b][1]} as unordered pairs and queries[a][2] = queries[b][2], then r[a] = r[b].
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_5
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ a b, a < queries.val.length → b < queries.val.length →
          UnorderedPairEq (field queries.val a 0) (field queries.val a 1)
            (field queries.val b 0) (field queries.val b 1) →
          field queries.val a 2 = field queries.val b 2 →
          answerAt r a = answerAt r b := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ a b, a < queries.val.length → b < queries.val.length →
            UnorderedPairEq (field queries.val a 0) (field queries.val a 1)
              (field queries.val b 0) (field queries.val b 1) →
            field queries.val a 2 = field queries.val b 2 →
            answerAt r a = answerAt r b) := by
    sorry

  /-- Whenever the function returns a result r, for all query indices a and b with 0 <= a < len(queries) and 0 <= b < len(queries), if queries[a][0] = queries[b][0], queries[a][1] = queries[b][1], queries[a][2] <= queries[b][2], and r[a] = true, then r[b] = true.
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_6
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ a b, a < queries.val.length → b < queries.val.length →
          field queries.val a 0 = field queries.val b 0 →
          field queries.val a 1 = field queries.val b 1 →
          field queries.val a 2 ≤ field queries.val b 2 →
          answerAt r a = true → answerAt r b = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ a b, a < queries.val.length → b < queries.val.length →
            field queries.val a 0 = field queries.val b 0 →
            field queries.val a 1 = field queries.val b 1 →
            field queries.val a 2 ≤ field queries.val b 2 →
            answerAt r a = true → answerAt r b = true) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if there do not exist an integer m >= 0 and vertices y_0, ..., y_m with y_0 = queries[j][0], y_m = queries[j][1], each y_t in {0, ..., n-1}, and for every t with 0 <= t < m an edge index i with 0 <= i < len(edgeList) such that {edgeList[i][0], edgeList[i][1]} = {y_t, y_{t+1}} as unordered pairs, then r[j] = false.
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_7
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ j, j < queries.val.length →
          (¬ UndirectedPath edgeList.val n.val
              (field queries.val j 0) (field queries.val j 1)) →
          answerAt r j = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ j, j < queries.val.length →
            (¬ UndirectedPath edgeList.val n.val
                (field queries.val j 0) (field queries.val j 1)) →
            answerAt r j = false) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if there exist an integer k >= 0 and vertices x_0, ..., x_k with x_0 = queries[j][0], x_k = queries[j][1], each x_t in {0, ..., n-1}, and for every t with 0 <= t < k there exists an edge index i with 0 <= i < len(edgeList) such that edgeList[i][2] < queries[j][2] and either (edgeList[i][0] = x_t and edgeList[i][1] = x_{t+1}) or (edgeList[i][1] = x_t and edgeList[i][0] = x_{t+1}), then r[j] = true.
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_8
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ j, j < queries.val.length →
          LimitedPath edgeList.val n.val
              (field queries.val j 0) (field queries.val j 1) (field queries.val j 2) →
          answerAt r j = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ j, j < queries.val.length →
            LimitedPath edgeList.val n.val
                (field queries.val j 0) (field queries.val j 1) (field queries.val j 2) →
            answerAt r j = true) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(queries), if r[j] = true, then there exist an integer k with 0 <= k <= n-1 and pairwise distinct vertices x_0, ..., x_k with x_0 = queries[j][0], x_k = queries[j][1], each x_t in {0, ..., n-1}, and for every t with 0 <= t < k there exists an edge index i with 0 <= i < len(edgeList) such that edgeList[i][2] < queries[j][2] and either (edgeList[i][0] = x_t and edgeList[i][1] = x_{t+1}) or (edgeList[i][1] = x_t and edgeList[i][0] = x_{t+1}).
    Preconditions: n is an integer with 2 <= n <= 100000. edgeList and queries are finite slices of integer vectors. 1 <= len(edgeList) <= 100000 and 1 <= len(queries) <= 100000. For every i with 0 <= i < len(edgeList), len(edgeList[i]) = 3, edgeList[i][0] and edgeList[i][1] are integers in [0, n-1], edgeList[i][0] != edgeList[i][1], and edgeList[i][2] is an integer in [1, 1000000000]. For every j with 0 <= j < len(queries), len(queries[j]) = 3, queries[j][0] and queries[j][1] are integers in [0, n-1], queries[j][0] != queries[j][1], and queries[j][2] is an integer in [1, 1000000000]. All indices are 0-based. -/
  theorem spec_9
      (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
      (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
      (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
      (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
      (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
      (h_edge_ne : ∀ i, i < edgeList.val.length →
        field edgeList.val i 0 ≠ field edgeList.val i 1)
      (h_edge_d : ∀ i, i < edgeList.val.length →
        1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
      (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
      (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
      (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
      (h_q_ne : ∀ j, j < queries.val.length →
        field queries.val j 0 ≠ field queries.val j 1)
      (h_q_L : ∀ j, j < queries.val.length →
        1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000) :
      ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
          = ok r →
        ∀ j, j < queries.val.length →
          answerAt r j = true →
          SimpleLimitedPath edgeList.val n.val
            (field queries.val j 0) (field queries.val j 1) (field queries.val j 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (edgeList queries : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hm_lo : 1 ≤ edgeList.val.length) (hm_hi : edgeList.val.length ≤ 100000)
        (hq_lo : 1 ≤ queries.val.length) (hq_hi : queries.val.length ≤ 100000)
        (h_edge_len : ∀ i, i < edgeList.val.length → (row edgeList.val i).length = 3)
        (h_edge_u : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 0))
        (h_edge_v : ∀ i, i < edgeList.val.length → VertexIn n.val (field edgeList.val i 1))
        (h_edge_ne : ∀ i, i < edgeList.val.length →
          field edgeList.val i 0 ≠ field edgeList.val i 1)
        (h_edge_d : ∀ i, i < edgeList.val.length →
          1 ≤ field edgeList.val i 2 ∧ field edgeList.val i 2 ≤ 1000000000)
        (h_q_len : ∀ j, j < queries.val.length → (row queries.val j).length = 3)
        (h_q_p : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 0))
        (h_q_q : ∀ j, j < queries.val.length → VertexIn n.val (field queries.val j 1))
        (h_q_ne : ∀ j, j < queries.val.length →
          field queries.val j 0 ≠ field queries.val j 1)
        (h_q_L : ∀ j, j < queries.val.length →
          1 ≤ field queries.val j 2 ∧ field queries.val j 2 ≤ 1000000000), ∀ r, Aegis.DistanceLimitedPathsExist.distance_limited_paths_exist n edgeList queries
            = ok r →
          ∀ j, j < queries.val.length →
            answerAt r j = true →
            SimpleLimitedPath edgeList.val n.val
              (field queries.val j 0) (field queries.val j 1) (field queries.val j 2)) := by
    sorry

  end AegisSpec.DistanceLimitedPathsExist
