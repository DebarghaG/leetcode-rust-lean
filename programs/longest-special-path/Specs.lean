import Aegis.LongestSpecialPath.Code.Funs

/-!
# Specifications of `Aegis.LongestSpecialPath.longest_special_path`

LeetCode problem `longest-special-path`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestSpecialPath

  open Classical

  def edgeRows (edges : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    edges.val.map fun e => e.val.map fun x => x.val

  def numValues (nums : Slice I64) : List Int :=
    nums.val.map fun x => x.val

  def Adj (edges : List (List Int)) (u v : Nat) : Prop :=
    ∃ w : Int, [((u : Int)), ((v : Int)), w] ∈ edges ∨ [((v : Int)), ((u : Int)), w] ∈ edges

  def GraphConnected (n : Nat) (edges : List (List Int)) : Prop :=
    ∀ u v : Nat, u < n → v < n → Relation.ReflTransGen (Adj edges) u v

  def GraphAcyclic (n : Nat) (edges : List (List Int)) : Prop :=
    ∀ u : Nat, u < n → ¬ Relation.TransGen (Adj edges) u u

  def EdgesWellFormed (n : Nat) (edges : List (List Int)) : Prop :=
    (∀ e ∈ edges, e.length = 3) ∧
      ∀ a b w : Int, [a, b, w] ∈ edges →
        0 ≤ a ∧ a < (n : Int) ∧ 0 ≤ b ∧ b < (n : Int) ∧ 1 ≤ w ∧ w ≤ 1000

  def ValuesInRange (nums : List Int) : Prop :=
    ∀ x ∈ nums, 0 ≤ x ∧ x ≤ 50000

  def AllValuesEqual (nums : List Int) : Prop :=
    ∀ x ∈ nums, ∀ y ∈ nums, x = y

  def EdgeWeight (edges : List (List Int)) (u v : Nat) : Option Int :=
    edges.findSome? fun e =>
      match e with
      | [a, b, w] =>
          if (a = (u : Int) ∧ b = (v : Int)) ∨ (a = (v : Int) ∧ b = (u : Int)) then some w else none
      | _ => none

  def IsSimplePath (edges : List (List Int)) (q : List Nat) : Prop :=
    q.Nodup ∧ ∀ k : Nat, k + 1 < q.length → Adj edges (q.getD k 0) (q.getD (k + 1) 0)

  def PathWeight (edges : List (List Int)) (q : List Nat) : Int :=
    ((List.range (q.length - 1)).map fun k =>
      (EdgeWeight edges (q.getD k 0) (q.getD (k + 1) 0)).getD 0).sum

  def PathValuesDistinct (nums : List Int) (q : List Nat) : Prop :=
    (q.map fun v => nums.getD v 0).Nodup

  def IsRootPath (edges : List (List Int)) (v : Nat) (q : List Nat) : Prop :=
    IsSimplePath edges q ∧ q.head? = some 0 ∧ q.getLast? = some v

  def IsAncestor (edges : List (List Int)) (a b : Nat) : Prop :=
    ∃ q : List Nat, IsRootPath edges b q ∧ a ∈ q

  def IsDownwardPath (edges : List (List Int)) (a b : Nat) (q : List Nat) : Prop :=
    IsAncestor edges a b ∧ IsSimplePath edges q ∧ q.head? = some a ∧ q.getLast? = some b

  def IsSpecialDownwardPath (edges : List (List Int)) (nums : List Int) (a b : Nat)
      (q : List Nat) : Prop :=
    IsDownwardPath edges a b q ∧ PathValuesDistinct nums q

  def TotalEdgeWeight (edges : List (List Int)) : Int :=
    (edges.map fun e => e.getD 2 0).sum

  noncomputable def rootPath (edges : List (List Int)) (v : Nat) : List Nat :=
    if h : ∃ q : List Nat, IsRootPath edges v q then h.choose else []

  noncomputable def distToRoot (edges : List (List Int)) (v : Nat) : Int :=
    PathWeight edges (rootPath edges v)

  noncomputable def depthOf (edges : List (List Int)) (v : Nat) : Nat :=
    (rootPath edges v).length - 1

  /-- Whenever the function returns a result r, len(r) = 2, and the following holds. Let T be the undirected tree on vertices {0,...,n-1} with weighted edges {edges[i][0], edges[i][1]} of weight edges[i][2], rooted at 0. For vertices a and b, call a an ancestor of b if a lies on the unique simple path from 0 to b; the downward path from a to b is the unique path from a to b directed away from the root. Its length is the sum of its edge weights, with length 0 when a = b, and its node count is the number of its vertices. It is special if the values nums at its vertices are pairwise distinct. Then r[0] is the maximum length over all special downward paths, and r[1] is the minimum node count over all special downward paths whose length equals r[0].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_1 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 ∧
            (∀ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                PathWeight (edgeRows edges) q ≤ (r.val[0]!).val) ∧
            (∃ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q ∧
                PathWeight (edgeRows edges) q = (r.val[0]!).val ∧
                (q.length : Int) = (r.val[1]!).val) ∧
            (∀ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                PathWeight (edgeRows edges) q = (r.val[0]!).val →
                  (r.val[1]!).val ≤ (q.length : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 ∧
              (∀ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                  PathWeight (edgeRows edges) q ≤ (r.val[0]!).val) ∧
              (∃ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q ∧
                  PathWeight (edgeRows edges) q = (r.val[0]!).val ∧
                  (q.length : Int) = (r.val[1]!).val) ∧
              (∀ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                  PathWeight (edgeRows edges) q = (r.val[0]!).val →
                    (r.val[1]!).val ≤ (q.length : Int))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail by out-of-bounds access, arithmetic overflow, or panic.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_2 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∃ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r) := by
    sorry

  /-- Let T be the tree on {0,...,n-1} with weighted edges {edges[i][0], edges[i][1]} of weight edges[i][2], rooted at 0. Whenever the function returns a result r of length 2, there exists an ancestor-descendant path P in T whose vertex values nums are pairwise distinct, whose edge-weight sum is r[0], and whose number of vertices is r[1].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_3 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 →
            ∃ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q ∧
                PathWeight (edgeRows edges) q = (r.val[0]!).val ∧
                (q.length : Int) = (r.val[1]!).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 →
              ∃ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q ∧
                  PathWeight (edgeRows edges) q = (r.val[0]!).val ∧
                  (q.length : Int) = (r.val[1]!).val) := by
    sorry

  /-- Let T be the tree on {0,...,n-1} with weighted edges {edges[i][0], edges[i][1]} of weight edges[i][2], rooted at 0. Whenever the function returns a result r of length 2, for every ancestor-descendant path P in T whose vertex values nums are pairwise distinct, the sum of edge weights along P is at most r[0].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_4 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 →
            ∀ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                PathWeight (edgeRows edges) q ≤ (r.val[0]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 →
              ∀ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                  PathWeight (edgeRows edges) q ≤ (r.val[0]!).val) := by
    sorry

  /-- Let T be the tree on {0,...,n-1} with weighted edges {edges[i][0], edges[i][1]} of weight edges[i][2], rooted at 0. Whenever the function returns a result r of length 2, for every ancestor-descendant path P in T whose vertex values nums are pairwise distinct and whose edge-weight sum equals r[0], the number of vertices of P is at least r[1].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_5 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 →
            ∀ (a b : Nat) (q : List Nat),
              IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                PathWeight (edgeRows edges) q = (r.val[0]!).val →
                  (r.val[1]!).val ≤ (q.length : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 →
              ∀ (a b : Nat) (q : List Nat),
                IsSpecialDownwardPath (edgeRows edges) (numValues nums) a b q →
                  PathWeight (edgeRows edges) q = (r.val[0]!).val →
                    (r.val[1]!).val ≤ (q.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r of length 2, r[0] is at most the sum of edges[i][2] over all i with 0 <= i < len(edges).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_6 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 → (r.val[0]!).val ≤ TotalEdgeWeight (edgeRows edges) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 → (r.val[0]!).val ≤ TotalEdgeWeight (edgeRows edges)) := by
    sorry

  /-- Whenever the function returns a result r of length 2, r[0] = 0 if and only if r[1] = 1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_7 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 → ((r.val[0]!).val = 0 ↔ (r.val[1]!).val = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 → ((r.val[0]!).val = 0 ↔ (r.val[1]!).val = 1)) := by
    sorry

  /-- If all entries of nums are equal, then whenever the function returns a result r of length 2, r[0] = 0 and r[1] = 1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_8 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
      (hall : AllValuesEqual (numValues nums)) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 → (r.val[0]!).val = 0 ∧ (r.val[1]!).val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
        (hall : AllValuesEqual (numValues nums)), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 → (r.val[0]!).val = 0 ∧ (r.val[1]!).val = 1) := by
    sorry

  /-- If n = 2 and nums[0] != nums[1], let w = edges[0][2]. Then whenever the function returns a result r of length 2, r[0] = w and r[1] = 2.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_9 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
      (hn : nums.val.length = 2)
      (hne : (numValues nums)[0]! ≠ (numValues nums)[1]!) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 →
            (r.val[0]!).val = ((edgeRows edges)[0]!)[2]! ∧ (r.val[1]!).val = 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
        (hn : nums.val.length = 2)
        (hne : (numValues nums)[0]! ≠ (numValues nums)[1]!), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 →
              (r.val[0]!).val = ((edgeRows edges)[0]!)[2]! ∧ (r.val[1]!).val = 2) := by
    sorry

  /-- Let T be the tree on {0,...,n-1} with weighted edges {edges[i][0], edges[i][1]} of weight edges[i][2], rooted at 0. For each vertex v, let dist(v) be the sum of edge weights on the unique simple path from 0 to v, and let depth(v) be the number of edges on that path. If the entries of nums are pairwise distinct, meaning nums[i] != nums[j] for all i != j, then whenever the function returns a result r of length 2, r[0] = max_{0 <= v < n} dist(v) and r[1] = min{ depth(v) + 1 : 0 <= v < n and dist(v) = r[0] }.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 50000, len(edges) = n - 1, every edges[i] has length 3, for every i with 0 <= i < len(edges) the endpoints edges[i][0] and edges[i][1] lie in [0, n-1] and 1 <= edges[i][2] <= 1000, for every j with 0 <= j < n we have 0 <= nums[j] <= 50000, and the undirected graph on vertices {0,...,n-1} with edges (edges[i][0], edges[i][1]) is connected and acyclic, hence a tree. -/
  theorem spec_10 (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
      (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
      (hedges_len : edges.val.length = nums.val.length - 1)
      (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
      (hnums : ValuesInRange (numValues nums))
      (hconn : GraphConnected nums.val.length (edgeRows edges))
      (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
      (hnd : (numValues nums).Nodup) :
      ∀ r : alloc.vec.Vec I64,
        Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
          r.val.length = 2 →
            (∀ v : Nat, v < nums.val.length → distToRoot (edgeRows edges) v ≤ (r.val[0]!).val) ∧
              (∃ v : Nat,
                v < nums.val.length ∧ distToRoot (edgeRows edges) v = (r.val[0]!).val) ∧
              (∀ v : Nat,
                v < nums.val.length → distToRoot (edgeRows edges) v = (r.val[0]!).val →
                  (r.val[1]!).val ≤ ((depthOf (edgeRows edges) v + 1 : Nat) : Int)) ∧
              (∃ v : Nat,
                v < nums.val.length ∧ distToRoot (edgeRows edges) v = (r.val[0]!).val ∧
                  ((depthOf (edgeRows edges) v + 1 : Nat) : Int) = (r.val[1]!).val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (edges : Slice (alloc.vec.Vec I64)) (nums : Slice I64)
        (hn_ge : 2 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50000)
        (hedges_len : edges.val.length = nums.val.length - 1)
        (hedges_wf : EdgesWellFormed nums.val.length (edgeRows edges))
        (hnums : ValuesInRange (numValues nums))
        (hconn : GraphConnected nums.val.length (edgeRows edges))
        (hacyc : GraphAcyclic nums.val.length (edgeRows edges))
        (hnd : (numValues nums).Nodup), ∀ r : alloc.vec.Vec I64,
          Aegis.LongestSpecialPath.longest_special_path edges nums = ok r →
            r.val.length = 2 →
              (∀ v : Nat, v < nums.val.length → distToRoot (edgeRows edges) v ≤ (r.val[0]!).val) ∧
                (∃ v : Nat,
                  v < nums.val.length ∧ distToRoot (edgeRows edges) v = (r.val[0]!).val) ∧
                (∀ v : Nat,
                  v < nums.val.length → distToRoot (edgeRows edges) v = (r.val[0]!).val →
                    (r.val[1]!).val ≤ ((depthOf (edgeRows edges) v + 1 : Nat) : Int)) ∧
                (∃ v : Nat,
                  v < nums.val.length ∧ distToRoot (edgeRows edges) v = (r.val[0]!).val ∧
                    ((depthOf (edgeRows edges) v + 1 : Nat) : Int) = (r.val[1]!).val)) := by
    sorry

  end AegisSpec.LongestSpecialPath
