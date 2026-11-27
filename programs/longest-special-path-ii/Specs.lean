import Aegis.LongestSpecialPath.Code.Funs

/-!
# Specifications of `Aegis.LongestSpecialPath.longest_special_path`

LeetCode problem `longest-special-path-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestSpecialPath
open Classical

namespace AegisSpec.LongestSpecialPath

abbrev EdgeVec : Type := alloc.vec.Vec I64

def vecValues (v : EdgeVec) : List ℤ := v.val.map (fun x => x.val)

def values (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def numAt (nums : Slice I64) (i : Nat) : ℤ := (values nums).getD i 0

def decodeEdge (e : EdgeVec) : Option (ℤ × ℤ × ℤ) :=
  match vecValues e with
  | [u, v, w] => some (u, v, w)
  | _ => none

def decodeUndirected (e : EdgeVec) : Option (ℤ × ℤ × ℤ) :=
  match vecValues e with
  | [u, v, w] => some (min u v, max u v, w)
  | _ => none

def edgeTriples (edges : Slice EdgeVec) : List (ℤ × ℤ × ℤ) := edges.val.filterMap decodeEdge

def undirectedEdges (edges : Slice EdgeVec) : List (ℤ × ℤ × ℤ) :=
  edges.val.filterMap decodeUndirected

def edgeAt (edges : Slice EdgeVec) (i : Nat) : Option (ℤ × ℤ × ℤ) :=
  (edges.val[i]?).bind decodeEdge

def edgeWeightAt (edges : Slice EdgeVec) (i : Nat) : ℤ :=
  ((edgeAt edges i).map (fun p : ℤ × ℤ × ℤ => p.2.2)).getD 0

def Wsum (edges : Slice EdgeVec) : ℤ :=
  ((edgeTriples edges).map (fun p : ℤ × ℤ × ℤ => p.2.2)).sum

def Wmax (edges : Slice EdgeVec) : ℤ :=
  ((edgeTriples edges).map (fun p : ℤ × ℤ × ℤ => p.2.2)).foldr max 0

def Adj (edges : Slice EdgeVec) (u v : Nat) (w : ℤ) : Prop :=
  ∃ p ∈ edgeTriples edges,
    ((p.1 = (u : ℤ) ∧ p.2.1 = (v : ℤ)) ∨ (p.1 = (v : ℤ) ∧ p.2.1 = (u : ℤ))) ∧ p.2.2 = w

def IsWalk (edges : Slice EdgeVec) (p : List Nat) : Prop :=
  ∀ (i : Nat) (u v : Nat), p[i]? = some u → p[i + 1]? = some v → ∃ w : ℤ, Adj edges u v w

def IsSimplePath (edges : Slice EdgeVec) (a b : Nat) (p : List Nat) : Prop :=
  IsWalk edges p ∧ p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup

def IsTree (edges : Slice EdgeVec) (n : Nat) : Prop :=
  (∀ u v : Nat, u < n → v < n →
      ∃ p : List Nat, IsWalk edges p ∧ p.head? = some u ∧ p.getLast? = some v) ∧
    (∀ (p : List Nat) (u : Nat), u < n → IsWalk edges p → p.head? = some u →
      p.getLast? = some u → p.Nodup → p.length ≤ 1)

noncomputable def pathVerts (edges : Slice EdgeVec) (a b : Nat) : List Nat :=
  if h : ∃ p : List Nat, IsSimplePath edges a b p then Classical.choose h else []

noncomputable def stepWeight (edges : Slice EdgeVec) (u v : Nat) : ℤ :=
  if h : ∃ w : ℤ, Adj edges u v w then Classical.choose h else 0

noncomputable def pathWeight (edges : Slice EdgeVec) : List Nat → ℤ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => stepWeight edges u v + pathWeight edges (v :: rest)

noncomputable def wt (edges : Slice EdgeVec) (a b : Nat) : ℤ :=
  pathWeight edges (pathVerts edges a b)

noncomputable def sz (edges : Slice EdgeVec) (a b : Nat) : ℤ :=
  ((pathVerts edges a b).length : ℤ)

noncomputable def Ancestor (edges : Slice EdgeVec) (a b : Nat) : Prop :=
  a ∈ pathVerts edges 0 b

def pathValues (nums : Slice I64) (p : List Nat) : List ℤ := p.map (numAt nums)

def Special (nums : Slice I64) (p : List Nat) : Prop :=
  (∀ c : ℤ, (pathValues nums p).count c ≤ 2) ∧
    ((pathValues nums p).dedup.filter (fun c => (pathValues nums p).count c = 2)).length ≤ 1

noncomputable def Admissible (edges : Slice EdgeVec) (nums : Slice I64) (a b : Nat) : Prop :=
  Ancestor edges a b ∧ Special nums (pathVerts edges a b)

noncomputable def IsMaxWt (edges : Slice EdgeVec) (nums : Slice I64) (L : ℤ) : Prop :=
  (∀ a b : Nat, Admissible edges nums a b → wt edges a b ≤ L) ∧
    ∃ a b : Nat, Admissible edges nums a b ∧ wt edges a b = L

noncomputable def IsMinSz (edges : Slice EdgeVec) (nums : Slice I64) (L M : ℤ) : Prop :=
  (∀ a b : Nat, Admissible edges nums a b → wt edges a b = L → M ≤ sz edges a b) ∧
    ∃ a b : Nat, Admissible edges nums a b ∧ wt edges a b = L ∧ sz edges a b = M

noncomputable def dist (edges : Slice EdgeVec) (v : Nat) : ℤ := wt edges 0 v

noncomputable def depth (edges : Slice EdgeVec) (v : Nat) : ℤ :=
  (((pathVerts edges 0 v).length - 1 : Nat) : ℤ)

noncomputable def IsMaxDist (edges : Slice EdgeVec) (n : Nat) (L : ℤ) : Prop :=
  (∀ v : Nat, v < n → dist edges v ≤ L) ∧ ∃ v : Nat, v < n ∧ dist edges v = L

noncomputable def IsMinDepth (edges : Slice EdgeVec) (n : Nat) (L M : ℤ) : Prop :=
  (∀ v : Nat, v < n → dist edges v = L → M ≤ depth edges v + 1) ∧
    ∃ v : Nat, v < n ∧ dist edges v = L ∧ depth edges v + 1 = M

/-- Whenever longest_special_path(edges, nums) returns a result r, r is a vector of length 2 and r[0] = L and r[1] = M, where: root the tree at node 0; a node a is an ancestor of b when a lies on the unique simple path from 0 to b (allowing a=b); for such a,b, P(a,b) is the vertex sequence on the unique simple path from a to b, wt(a,b) is the sum of the edge lengths between consecutive vertices of P(a,b), and sz(a,b) is the number of vertices in P(a,b); P(a,b) is special when every value occurs at most twice among nums on P(a,b) and at most one value occurs exactly twice; S is the set of all pairs (a,b) such that a is an ancestor of b and P(a,b) is special; L = max over (a,b) in S of wt(a,b), and M = min over (a,b) in S with wt(a,b)=L of sz(a,b).
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_1 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ r, longest_special_path edges nums = ok r →
      ∃ x y : I64, r.val = [x, y] ∧
        IsMaxWt edges nums x.val ∧ IsMinSz edges nums x.val y.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ r, longest_special_path edges nums = ok r →
      ∃ x y : I64, r.val = [x, y] ∧
        IsMaxWt edges nums x.val ∧ IsMinSz edges nums x.val y.val) := by
  sorry

/-- The call longest_special_path(edges, nums) returns a result r for some vector r; it does not return Err, overflow, go out of bounds, or panic.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_2 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∃ r : EdgeVec, longest_special_path edges nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∃ r : EdgeVec, longest_special_path edges nums = ok r) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, len(r) = 2.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_3 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ r, longest_special_path edges nums = ok r → r.val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ r, longest_special_path edges nums = ok r → r.val.length = 2) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, for every pair of nodes a,b such that a is an ancestor of b and the downward path P(a,b) is special, the sum wt(a,b) of edge lengths on P(a,b) satisfies wt(a,b) <= r[0]. Here P(a,b) is the unique simple path from a to b, and special means that every node value occurs at most twice on P(a,b) and at most one value occurs exactly twice.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_4 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x →
      ∀ a b : Nat, Ancestor edges a b → Special nums (pathVerts edges a b) →
        wt edges a b ≤ x.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x →
      ∀ a b : Nat, Ancestor edges a b → Special nums (pathVerts edges a b) →
        wt edges a b ≤ x.val) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, there exist nodes a,b such that a is an ancestor of b, the downward path P(a,b) is special (every value occurs at most twice on P(a,b), and at most one value occurs exactly twice), and the edge-length sum wt(a,b) equals r[0].
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_5 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x →
      ∃ a b : Nat, Ancestor edges a b ∧ Special nums (pathVerts edges a b) ∧
        wt edges a b = x.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x →
      ∃ a b : Nat, Ancestor edges a b ∧ Special nums (pathVerts edges a b) ∧
        wt edges a b = x.val) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, for every pair of nodes a,b such that a is an ancestor of b, P(a,b) is special, and wt(a,b) = r[0], the number of vertices sz(a,b) on P(a,b) satisfies sz(a,b) >= r[1].
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_6 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      ∀ a b : Nat, Ancestor edges a b → Special nums (pathVerts edges a b) →
        wt edges a b = x.val → y.val ≤ sz edges a b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      ∀ a b : Nat, Ancestor edges a b → Special nums (pathVerts edges a b) →
        wt edges a b = x.val → y.val ≤ sz edges a b) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, there exist nodes a,b such that a is an ancestor of b, P(a,b) is special, wt(a,b) = r[0], and sz(a,b) = r[1], where wt(a,b) is the sum of edge lengths on P(a,b) and sz(a,b) is the number of vertices on P(a,b).
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_7 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      ∃ a b : Nat, Ancestor edges a b ∧ Special nums (pathVerts edges a b) ∧
        wt edges a b = x.val ∧ sz edges a b = y.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      ∃ a b : Nat, Ancestor edges a b ∧ Special nums (pathVerts edges a b) ∧
        wt edges a b = x.val ∧ sz edges a b = y.val) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, let Wmax = max over 0 <= i < len(edges) of edges[i][2] and Wsum = sum over 0 <= i < len(edges) of edges[i][2]. Then Wmax <= r[0] <= Wsum.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_8 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → Wmax edges ≤ x.val ∧ x.val ≤ Wsum edges := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → Wmax edges ≤ x.val ∧ x.val ≤ Wsum edges) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, 2 <= r[1] <= n.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_9 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (y : I64), longest_special_path edges nums = ok r →
      r.val[1]? = some y → 2 ≤ y.val ∧ y.val ≤ (n : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (y : I64), longest_special_path edges nums = ok r →
      r.val[1]? = some y → 2 ≤ y.val ∧ y.val ≤ (n : ℤ)) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, r[0] = edges[0][2] and r[1] = 2.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. In addition, n = 2, so len(edges) = 1 and the unique edge joins nodes 0 and 1. -/
theorem spec_10 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (htwo : n = 2) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      x.val = edgeWeightAt edges 0 ∧ y.val = 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (htwo : n = 2), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      x.val = edgeWeightAt edges 0 ∧ y.val = 2) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, r[0] = max over 0 <= i < len(edges) of edges[i][2] and r[1] = 2.
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. In addition, there exists a value c such that nums[j] = c for every 0 <= j < n. -/
theorem spec_11 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hconst : ∃ c : ℤ, ∀ v ∈ values nums, v = c) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      x.val = Wmax edges ∧ y.val = 2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hconst : ∃ c : ℤ, ∀ v ∈ values nums, v = c), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      x.val = Wmax edges ∧ y.val = 2) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, let dist(v) be the sum of edge lengths on the unique path from root 0 to v, and let depth(v) be the number of edges on that path. Then r[0] = max over 0 <= v < n of dist(v), and r[1] = min of depth(v)+1 over all v with 0 <= v < n and dist(v) = max over 0 <= u < n of dist(u).
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. In addition, nums[i] != nums[j] for all 0 <= i < j < n. -/
theorem spec_12 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hdistinct : (values nums).Pairwise (fun a b => a ≠ b)) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      IsMaxDist edges n x.val ∧ IsMinDepth edges n x.val y.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hdistinct : (values nums).Pairwise (fun a b => a ≠ b)), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      IsMaxDist edges n x.val ∧ IsMinDepth edges n x.val y.val) := by
  sorry

/-- If longest_special_path(edges, nums) returns a result r and longest_special_path(edges', nums) returns a result r', then r = r'.
  Preconditions: Let n = len(nums). The inputs (edges, nums) satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. Let edges' be any other edge list of length len(edges) whose multiset of undirected weighted edges is the same as that of edges, allowing permutations of entries and swapping the two endpoints inside any entry, and suppose edges' also satisfies the same tree and weight constraints. -/
theorem spec_13 (edges edges' : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (he'_len : edges'.val.length = n - 1)
    (he'_len3 : ∀ e ∈ edges'.val, (vecValues e).length = 3)
    (he'_rng : ∀ p ∈ edgeTriples edges', 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree' : IsTree edges' n)
    (hsame : List.Perm (undirectedEdges edges) (undirectedEdges edges')) :
    ∀ r r' : EdgeVec, longest_special_path edges nums = ok r →
      longest_special_path edges' nums = ok r' → r = r' := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (edges edges' : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (he'_len : edges'.val.length = n - 1)
    (he'_len3 : ∀ e ∈ edges'.val, (vecValues e).length = 3)
    (he'_rng : ∀ p ∈ edgeTriples edges', 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree' : IsTree edges' n)
    (hsame : List.Perm (undirectedEdges edges) (undirectedEdges edges')), ∀ r r' : EdgeVec, longest_special_path edges nums = ok r →
      longest_special_path edges' nums = ok r' → r = r') := by
  sorry

/-- If longest_special_path(edges, nums) returns a result r and longest_special_path(edges, nums') returns a result r', then r = r'.
  Preconditions: Let n = len(nums). The inputs (edges, nums) satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. Let nums' be any array of length n with 0 <= nums'[j] <= 50000 for every j and with the same equality pattern as nums, meaning nums[i] = nums[j] if and only if nums'[i] = nums'[j] for all 0 <= i,j < n. -/
theorem spec_14 (edges : Slice EdgeVec) (nums nums' : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hn'_len : nums'.val.length = n)
    (hn'_rng : ∀ c ∈ values nums', 0 ≤ c ∧ c ≤ 50000)
    (hsame : ∀ i j : Nat, i < n → j < n →
      (numAt nums i = numAt nums j ↔ numAt nums' i = numAt nums' j)) :
    ∀ r r' : EdgeVec, longest_special_path edges nums = ok r →
      longest_special_path edges nums' = ok r' → r = r' := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums nums' : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000)
    (hn'_len : nums'.val.length = n)
    (hn'_rng : ∀ c ∈ values nums', 0 ≤ c ∧ c ≤ 50000)
    (hsame : ∀ i j : Nat, i < n → j < n →
      (numAt nums i = numAt nums j ↔ numAt nums' i = numAt nums' j)), ∀ r r' : EdgeVec, longest_special_path edges nums = ok r →
      longest_special_path edges nums' = ok r' → r = r') := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, r[1] = 2 if and only if r[0] = max over 0 <= i < len(edges) of edges[i][2].
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_15 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      (y.val = 2 ↔ x.val = Wmax edges) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      (y.val = 2 ↔ x.val = Wmax edges)) := by
  sorry

/-- Whenever longest_special_path(edges, nums) returns a result r, r[1] = n if and only if r[0] = sum over 0 <= i < len(edges) of edges[i][2].
  Preconditions: Let n = len(nums). The inputs satisfy the problem constraints: 2 <= n <= 50000; len(edges) = n - 1; each edges[i] has length 3 and, writing edges[i] = [u,v,w], we have 0 <= u < n, 0 <= v < n, and 1 <= w <= 1000; the undirected graph on vertices 0,...,n-1 with these n-1 weighted edges is a tree; and 0 <= nums[j] <= 50000 for every 0 <= j < n. -/
theorem spec_16 (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000) :
    ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      (y.val = (n : ℤ) ↔ x.val = Wsum edges) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (edges : Slice EdgeVec) (nums : Slice I64) (n : Nat)
    (hn : n = nums.val.length) (hn_ge : 2 ≤ n) (hn_le : n ≤ 50000)
    (he_len : edges.val.length = n - 1)
    (he_len3 : ∀ e ∈ edges.val, (vecValues e).length = 3)
    (he_rng : ∀ p ∈ edgeTriples edges, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2.1 ∧
      p.2.1 < (n : ℤ) ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 1000)
    (htree : IsTree edges n)
    (hnum : ∀ c ∈ values nums, 0 ≤ c ∧ c ≤ 50000), ∀ (r : EdgeVec) (x y : I64), longest_special_path edges nums = ok r →
      r.val[0]? = some x → r.val[1]? = some y →
      (y.val = (n : ℤ) ↔ x.val = Wsum edges)) := by
  sorry

end AegisSpec.LongestSpecialPath
