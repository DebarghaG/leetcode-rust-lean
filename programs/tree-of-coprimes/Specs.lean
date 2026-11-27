import Aegis.GetCoprimes.Code.Funs

/-!
# Specifications of `Aegis.GetCoprimes.get_coprimes`

LeetCode problem `tree-of-coprimes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetCoprimes

  open Aegis.GetCoprimes

  def atI (l : List I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def Adj (edges : Slice (alloc.vec.Vec I64)) (a b : Nat) : Prop :=
    ∃ e ∈ edges.val, ∃ u v : I64, e.val = [u, v] ∧ u.val = (a : Int) ∧ v.val = (b : Int)

  def Walk (edges : Slice (alloc.vec.Vec I64)) : List Nat → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => Adj edges a b ∧ Walk edges (b :: rest)

  def IsPath (edges : Slice (alloc.vec.Vec I64)) (a b : Nat) (l : List Nat) : Prop :=
    Walk edges l ∧ l.head? = some a ∧ l.getLast? = some b

  def IsSimplePath (edges : Slice (alloc.vec.Vec I64)) (a b : Nat) (l : List Nat) : Prop :=
    IsPath edges a b l ∧ l.Nodup

  def Connected (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    ∀ a, a < n → ∃ l : List Nat, IsPath edges a 0 l

  def Acyclic (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    ∀ (a : Nat) (l : List Nat), a < n → IsPath edges a a l → 3 ≤ (l.dropLast).length →
      (l.dropLast).Nodup → False

  def IsTree (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    Connected edges n ∧ Acyclic edges n

  noncomputable def graphDist (edges : Slice (alloc.vec.Vec I64)) (a b : Nat) : Nat :=
    sInf {d : Nat | ∃ l : List Nat, IsPath edges a b l ∧ l.length = d + 1}

  def Ancestor (edges : Slice (alloc.vec.Vec I64)) (j i : Nat) : Prop :=
    j ≠ i ∧ ∃ l : List Nat, IsSimplePath edges i 0 l ∧ j ∈ l

  def Parent (edges : Slice (alloc.vec.Vec I64)) (i p : Nat) : Prop :=
    Adj edges i p ∧ Ancestor edges p i

  def NumsWF (nums : Slice I64) : Prop :=
    ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 50

  def EdgesWF (edges : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    edges.val.length = n - 1 ∧
      ∀ e ∈ edges.val, ∃ u v : I64,
        e.val = [u, v] ∧ u.val ≠ v.val ∧ 0 ≤ u.val ∧ u.val < (n : Int) ∧
          0 ≤ v.val ∧ v.val < (n : Int)

  def firstCoprime (nums : Slice I64) (v : Int) : List Nat → Option Nat
    | [] => none
    | x :: xs => if Int.gcd v (atI nums.val x) = 1 then some x else firstCoprime nums v xs

  /-- Whenever get_coprimes(nums, edges) returns a result r, len(r) = n, and for every i with 0 <= i < n the following holds. Let (v_0, v_1, ..., v_k) be the unique simple path in the tree from i to 0, with v_0 = i and v_k = 0. If there exists t with 1 <= t <= k such that gcd(nums[i], nums[v_t]) = 1, then r[i] = v_{t_i}, where t_i is the least such t; otherwise r[i] = -1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. An ancestor of node i means any node j != i lying on the unique simple path from i to 0; node 0 has no ancestors. gcd is the greatest common divisor of positive integers. -/
  theorem spec_1
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      r.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → ∀ l : List Nat,
          IsSimplePath edges i 0 l →
            (match firstCoprime nums (atI nums.val i) l.tail with
              | some v => atI r.val i = (v : Int)
              | none => atI r.val i = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), r.val.length = nums.val.length ∧
          ∀ i, i < nums.val.length → ∀ l : List Nat,
            IsSimplePath edges i 0 l →
              (match firstCoprime nums (atI nums.val i) l.tail with
                | some v => atI r.val i = (v : Int)
                | none => atI r.val i = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, get_coprimes(nums, edges) returns a result r; it never fails due to integer overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. -/
  theorem spec_2
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length) :
      ∃ r : alloc.vec.Vec I64, get_coprimes nums edges = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length), ∃ r : alloc.vec.Vec I64, get_coprimes nums edges = ok r) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, len(r) = len(nums).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. -/
  theorem spec_3
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), r.val.length = nums.val.length) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n, either r[i] = -1 or 0 <= r[i] < n.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. -/
  theorem spec_4
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length →
        atI r.val i = -1 ∨ (0 ≤ atI r.val i ∧ atI r.val i < (nums.val.length : Int)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length →
          atI r.val i = -1 ∨ (0 ≤ atI r.val i ∧ atI r.val i < (nums.val.length : Int))) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, r[0] = -1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. -/
  theorem spec_5
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      atI r.val 0 = -1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), atI r.val 0 = -1) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n, if r[i] >= 0 then r[i] is an ancestor of i (that is, r[i] != i and r[i] lies on the unique simple path from i to 0).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. An ancestor of node i means any node j != i lying on the unique simple path from i to 0. -/
  theorem spec_6
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length → 0 ≤ atI r.val i →
        Ancestor edges (atI r.val i).toNat i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length → 0 ≤ atI r.val i →
          Ancestor edges (atI r.val i).toNat i) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n, if r[i] >= 0 then gcd(nums[i], nums[r[i]]) = 1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_7
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length → 0 ≤ atI r.val i →
        Int.gcd (atI nums.val i) (atI nums.val (atI r.val i).toNat) = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length → 0 ≤ atI r.val i →
          Int.gcd (atI nums.val i) (atI nums.val (atI r.val i).toNat) = 1) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n, if r[i] = -1 then there is no node j with 0 <= j < n such that j is an ancestor of i and gcd(nums[i], nums[j]) = 1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. An ancestor of node i means any node j != i lying on the unique simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_8
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length → atI r.val i = -1 → ∀ j, j < nums.val.length →
        ¬ (Ancestor edges j i ∧ Int.gcd (atI nums.val i) (atI nums.val j) = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length → atI r.val i = -1 → ∀ j, j < nums.val.length →
          ¬ (Ancestor edges j i ∧ Int.gcd (atI nums.val i) (atI nums.val j) = 1)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n and r[i] >= 0, every ancestor j of i with distance(i,j) < distance(i,r[i]) satisfies gcd(nums[i], nums[j]) != 1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For two nodes a and b, distance(a,b) is the number of edges on the unique simple path between them. An ancestor of node i means any node j != i lying on the unique simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_9
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length → 0 ≤ atI r.val i → ∀ j,
        Ancestor edges j i →
          graphDist edges i j < graphDist edges i (atI r.val i).toNat →
            Int.gcd (atI nums.val i) (atI nums.val j) ≠ 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length → 0 ≤ atI r.val i → ∀ j,
          Ancestor edges j i →
            graphDist edges i j < graphDist edges i (atI r.val i).toNat →
              Int.gcd (atI nums.val i) (atI nums.val j) ≠ 1) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 1 <= i < n such that nums[i] = 1, r[i] = parent(i).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For i != 0, parent(i) is the unique neighbor of i on the simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_10
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, 1 ≤ i → i < nums.val.length → atI nums.val i = 1 → ∀ p,
        Parent edges i p → atI r.val i = (p : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, 1 ≤ i → i < nums.val.length → atI nums.val i = 1 → ∀ p,
          Parent edges i p → atI r.val i = (p : Int)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 1 <= i < n such that nums[parent(i)] = 1, r[i] = parent(i).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For i != 0, parent(i) is the unique neighbor of i on the simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_11
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
        Parent edges i p → atI nums.val p = 1 → atI r.val i = (p : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
          Parent edges i p → atI nums.val p = 1 → atI r.val i = (p : Int)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 1 <= i < n, r[i] = parent(i).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For i != 0, parent(i) is the unique neighbor of i on the simple path from i to 0. Additionally, for every i and j with 0 <= i < n, 0 <= j < n, and i != j, gcd(nums[i], nums[j]) = 1. -/
  theorem spec_12
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (hcop : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
        Int.gcd (atI nums.val i) (atI nums.val j) = 1)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
        Parent edges i p → atI r.val i = (p : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (hcop : ∀ i j, i < nums.val.length → j < nums.val.length → i ≠ j →
          Int.gcd (atI nums.val i) (atI nums.val j) = 1)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
          Parent edges i p → atI r.val i = (p : Int)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r and get_coprimes(nums, edges') returns a result r', we have len(r) = len(r') = n and r[i] = r'[i] for every i with 0 <= i < n.
    Preconditions: Let n = len(nums). n >= 1; every nums[i] satisfies 1 <= nums[i] <= 50. Let edges and edges' be two edge lists of length n - 1 each; every edge has two distinct endpoints in [0,n); and edges and edges' describe the same connected acyclic undirected graph on vertices 0,...,n-1, i.e. they have the same set of unordered edges, possibly in a different order or with the two endpoints of an edge swapped. -/
  theorem spec_13
      (nums : Slice I64) (edges edges' : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hedges' : EdgesWF edges' nums.val.length)
      (hnums : NumsWF nums)
      (hsame : ∀ a b, Adj edges a b ↔ Adj edges' a b)
      (htree : IsTree edges nums.val.length)
      (r r' : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r)
      (hr' : get_coprimes nums edges' = ok r') :
      r.val.length = nums.val.length ∧ r'.val.length = nums.val.length ∧
        ∀ i, i < nums.val.length → atI r.val i = atI r'.val i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64) (edges edges' : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hedges' : EdgesWF edges' nums.val.length)
        (hnums : NumsWF nums)
        (hsame : ∀ a b, Adj edges a b ↔ Adj edges' a b)
        (htree : IsTree edges nums.val.length)
        (r r' : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r)
        (hr' : get_coprimes nums edges' = ok r'), r.val.length = nums.val.length ∧ r'.val.length = nums.val.length ∧
          ∀ i, i < nums.val.length → atI r.val i = atI r'.val i) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 1 <= i < n such that parent(i) = 0, we have r[i] = 0 if gcd(nums[i], nums[0]) = 1, and r[i] = -1 if gcd(nums[i], nums[0]) != 1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For i != 0, parent(i) is the unique neighbor of i on the simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_14
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, 1 ≤ i → i < nums.val.length → ∀ p, Parent edges i p → p = 0 →
        (Int.gcd (atI nums.val i) (atI nums.val 0) = 1 ∧ atI r.val i = 0) ∨
          (Int.gcd (atI nums.val i) (atI nums.val 0) ≠ 1 ∧ atI r.val i = -1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, 1 ≤ i → i < nums.val.length → ∀ p, Parent edges i p → p = 0 →
          (Int.gcd (atI nums.val i) (atI nums.val 0) = 1 ∧ atI r.val i = 0) ∨
            (Int.gcd (atI nums.val i) (atI nums.val 0) ≠ 1 ∧ atI r.val i = -1)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 1 <= i < n: r[i] = parent(i) if and only if gcd(nums[i], nums[parent(i)]) = 1.
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For i != 0, parent(i) is the unique neighbor of i on the simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_15
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
        Parent edges i p →
          (atI r.val i = (p : Int) ↔ Int.gcd (atI nums.val i) (atI nums.val p) = 1) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, 1 ≤ i → i < nums.val.length → ∀ p,
          Parent edges i p →
            (atI r.val i = (p : Int) ↔ Int.gcd (atI nums.val i) (atI nums.val p) = 1)) := by
    sorry

  /-- Whenever get_coprimes(nums, edges) returns a result r, for every i with 0 <= i < n such that r[i] >= 0, and every ancestor j of i, if gcd(nums[i], nums[j]) = 1 then distance(i, r[i]) <= distance(i, j).
    Preconditions: Let n = len(nums). n >= 1; len(edges) = n - 1; every edges[j] has length 2 with two distinct endpoints in [0,n); every nums[i] satisfies 1 <= nums[i] <= 50; the undirected graph with vertices 0,...,n-1 and edges {edges[j][0],edges[j][1]} is connected and acyclic (a tree), rooted at 0. For two nodes a and b, distance(a,b) is the number of edges on the unique simple path between them. An ancestor of node i means any node j != i lying on the unique simple path from i to 0. gcd is the greatest common divisor of positive integers. -/
  theorem spec_16
      (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
      (hn : 1 ≤ nums.val.length)
      (hedges : EdgesWF edges nums.val.length)
      (hnums : NumsWF nums)
      (htree : IsTree edges nums.val.length)
      (r : alloc.vec.Vec I64)
      (hr : get_coprimes nums edges = ok r) :
      ∀ i, i < nums.val.length → 0 ≤ atI r.val i → ∀ j,
        Ancestor edges j i →
          Int.gcd (atI nums.val i) (atI nums.val j) = 1 →
            graphDist edges i (atI r.val i).toNat ≤ graphDist edges i j := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice I64) (edges : Slice (alloc.vec.Vec I64))
        (hn : 1 ≤ nums.val.length)
        (hedges : EdgesWF edges nums.val.length)
        (hnums : NumsWF nums)
        (htree : IsTree edges nums.val.length)
        (r : alloc.vec.Vec I64)
        (hr : get_coprimes nums edges = ok r), ∀ i, i < nums.val.length → 0 ≤ atI r.val i → ∀ j,
          Ancestor edges j i →
            Int.gcd (atI nums.val i) (atI nums.val j) = 1 →
              graphDist edges i (atI r.val i).toNat ≤ graphDist edges i j) := by
    sorry

  end AegisSpec.GetCoprimes
