import Aegis.LevelOrder.Code.Funs

/-!
# Specifications of `Aegis.LevelOrder.level_order`

LeetCode problem `binary-tree-level-order-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LevelOrder

  namespace AegisSpec.LevelOrder

  abbrev Levels := alloc.vec.Vec (alloc.vec.Vec Std.I64)

  def H : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + max (H l) (H r)

  def N : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + N l + N r

  def L : Tree → Nat → List Int
    | .Null, _ => []
    | .Node v _ _, 0 => [v.val]
    | .Node _ l r, (k + 1) => L l k ++ L r k

  def ValuesInRange : Tree → Prop
    | .Null => True
    | .Node v l r => -1000 ≤ v.val ∧ v.val ≤ 1000 ∧ ValuesInRange l ∧ ValuesInRange r

  def nodesAtDepth : Tree → Nat → List Tree
    | .Null, _ => []
    | t@(.Node _ _ _), 0 => [t]
    | .Node _ l r, (k + 1) => nodesAtDepth l k ++ nodesAtDepth r k

  def nodeVal? : Tree → Option Int
    | .Null => none
    | .Node v _ _ => some v.val

  def leftChildVal? : Tree → Option Int
    | .Null => none
    | .Node _ l _ => match l with
      | .Null => none
      | .Node v _ _ => some v.val

  def rightChildVal? : Tree → Option Int
    | .Null => none
    | .Node _ _ r => match r with
      | .Null => none
      | .Node v _ _ => some v.val

  def rowVals (res : Levels) (k : Nat) : List Int :=
    (res.val[k]?.map (fun row => row.val.map IScalar.val)).getD []

  def totalEntries (res : Levels) : Nat :=
    (res.val.map (fun row => row.val.length)).sum

  inductive Dir where
    | L
    | R
    deriving DecidableEq

  def pathLt : List Dir → List Dir → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: ta, b :: tb =>
      match a, b with
      | .L, .L => pathLt ta tb
      | .L, .R => true
      | .R, .L => false
      | .R, .R => pathLt ta tb

  def nodePathsAtDepth : Tree → Nat → List (List Dir × Int)
    | .Null, _ => []
    | .Node v _ _, 0 => [([], v.val)]
    | .Node _ l r, (k + 1) =>
      (nodePathsAtDepth l k).map (fun p => (Dir.L :: p.1, p.2)) ++
        (nodePathsAtDepth r k).map (fun p => (Dir.R :: p.1, p.2))

  def levelByPaths (t : Tree) (k : Nat) : List Int :=
    ((nodePathsAtDepth t k).mergeSort (fun p q => pathLt p.1 q.1)).map (fun p => p.2)

  /-- The function returns a result res and: (1) len(res) = H(root), where H(Null) = 0 and H(Node(_, l, rt)) = 1 + max(H(l), H(rt)); (2) for every k with 0 <= k < len(res), res[k] = L(root, k), where L(Null, k) = [] for every k >= 0, L(Node(v, l, rt), 0) = [v], and L(Node(v, l, rt), k+1) = L(l, k) ++ L(rt, k) for every k >= 0, with ++ denoting list concatenation. Thus res is exactly the level-order traversal: levels from top to bottom, and each level from left to right.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_1 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root) :
      ∃ res : Levels,
        level_order root = ok res ∧
          res.val.length = H root ∧
            ∀ k (hk : k < res.val.length), (res.val[k]).val.map IScalar.val = L root k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root), ∃ res : Levels,
          level_order root = ok res ∧
            res.val.length = H root ∧
              ∀ k (hk : k < res.val.length), (res.val[k]).val.map IScalar.val = L root k) := by
    sorry

  /-- The function returns a result r (it does not fail) for every root satisfying the preconditions.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_2 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root) :
      ∃ r : Levels, level_order root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root), ∃ r : Levels, level_order root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every inner list is non-empty: for every k with 0 <= k < len(r), len(r[k]) >= 1.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_3 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ k (hk : k < r.val.length), 1 ≤ (r.val[k]).val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ k (hk : k < r.val.length), 1 ≤ (r.val[k]).val.length) := by
    sorry

  /-- Whenever the function returns a result res, the total number of entries in all inner lists equals the number of nodes of root: sum over k from 0 to len(res)-1 of len(res[k]) = N(root), where N(Null) = 0 and N(Node(_, l, rt)) = 1 + N(l) + N(rt).
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_4 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (res : Levels) (hres : level_order root = ok res) :
      totalEntries res = N root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (res : Levels) (hres : level_order root = ok res), totalEntries res = N root) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), len(r[k]) <= 2^k.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_5 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ k (hk : k < r.val.length), (r.val[k]).val.length ≤ 2 ^ k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ k (hk : k < r.val.length), (r.val[k]).val.length ≤ 2 ^ k) := by
    sorry

  /-- Whenever the function returns a result res, len(res) <= N(root), where N(Null) = 0 and N(Node(_, l, rt)) = 1 + N(l) + N(rt). In particular, under the precondition len(res) <= 2000.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_6 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (res : Levels) (hres : level_order root = ok res) :
      res.val.length ≤ N root ∧ res.val.length ≤ 2000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (res : Levels) (hres : level_order root = ok res), res.val.length ≤ N root ∧ res.val.length ≤ 2000) := by
    sorry

  /-- Whenever the function returns a result res, len(res) > 0, len(res[0]) = 1, and res[0][0] = v.
    Preconditions: root = Node(v, l, rt) for some integer v and subtrees l and rt, with at most 2000 total nodes and every node value between -1000 and 1000 inclusive. -/
  theorem spec_7 (v : Std.I64) (l rt : Tree) (hnodes : N (.Node v l rt) ≤ 2000)
      (hvalues : ValuesInRange (.Node v l rt)) (res : Levels)
      (hres : level_order (.Node v l rt) = ok res) :
      0 < res.val.length ∧ (rowVals res 0).length = 1 ∧ (rowVals res 0).head? = some v.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (v : Std.I64) (l rt : Tree) (hnodes : N (.Node v l rt) ≤ 2000)
        (hvalues : ValuesInRange (.Node v l rt)) (res : Levels)
        (hres : level_order (.Node v l rt) = ok res), 0 < res.val.length ∧ (rowVals res 0).length = 1 ∧ (rowVals res 0).head? = some v.val) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k+1 < len(r) and every integer x, the number of indices j with 0 <= j < len(r[k+1]) and r[k+1][j] = x equals the number of nodes u at depth k of root such that u has a left child with value x plus the number of nodes u at depth k of root such that u has a right child with value x.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_8 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ k (hk : k + 1 < r.val.length) (x : Int),
        ((r.val[k + 1]).val.map IScalar.val).countP (fun y => decide (y = x)) =
          (nodesAtDepth root k).countP (fun u => decide (leftChildVal? u = some x)) +
            (nodesAtDepth root k).countP (fun u => decide (rightChildVal? u = some x)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ k (hk : k + 1 < r.val.length) (x : Int),
          ((r.val[k + 1]).val.map IScalar.val).countP (fun y => decide (y = x)) =
            (nodesAtDepth root k).countP (fun u => decide (leftChildVal? u = some x)) +
              (nodesAtDepth root k).countP (fun u => decide (rightChildVal? u = some x))) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r) and every j with 0 <= j < len(r[k]), there exists a node u of root at depth k such that value(u) = r[k][j], where value(u) denotes the integer stored at node u.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_9 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ k (hk : k < r.val.length) (j : Nat),
        j < (rowVals r k).length →
          ∃ u : Tree, u ∈ nodesAtDepth root k ∧ nodeVal? u = (rowVals r k)[j]? := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ k (hk : k < r.val.length) (j : Nat),
          j < (rowVals r k).length →
            ∃ u : Tree, u ∈ nodesAtDepth root k ∧ nodeVal? u = (rowVals r k)[j]?) := by
    sorry

  /-- Whenever the function returns a result r, for every node u of root, if u has depth k, then k < len(r) and there exists an index j with 0 <= j < len(r[k]) such that r[k][j] = value(u), where value(u) denotes the integer stored at node u.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_10 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ (k : Nat) (u : Tree), u ∈ nodesAtDepth root k →
        k < r.val.length ∧ ∃ j, j < (rowVals r k).length ∧ (rowVals r k)[j]? = nodeVal? u := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ (k : Nat) (u : Tree), u ∈ nodesAtDepth root k →
          k < r.val.length ∧ ∃ j, j < (rowVals r k).length ∧ (rowVals r k)[j]? = nodeVal? u) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), if all nodes of root at depth k are ordered by their root-to-node paths (a path is a word over L and R, empty at the root, L for a left edge and R for a right edge; words have equal length at fixed k and are compared lexicographically with L < R), and W is the list of their values in that order, then r[k] = W.
    Preconditions: root is a Tree with at most 2000 nodes, and every node value v of root satisfies -1000 <= v <= 1000. -/
  theorem spec_11 (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
      (r : Levels) (hres : level_order root = ok r) :
      ∀ k (hk : k < r.val.length), (r.val[k]).val.map IScalar.val = levelByPaths root k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hnodes : N root ≤ 2000) (hvalues : ValuesInRange root)
        (r : Levels) (hres : level_order root = ok r), ∀ k (hk : k < r.val.length), (r.val[k]).val.map IScalar.val = levelByPaths root k) := by
    sorry

  /-- For any integer k >= 0, if k < H(root1), k < H(root2), and L(root1, k) = L(root2, k), where H(Null) = 0, H(Node(_, l, r)) = 1 + max(H(l), H(r)), L(Null, k) = [], L(Node(v, l, r), 0) = [v], and L(Node(v, l, r), k+1) = L(l, k) ++ L(r, k), then whenever level_order(root1) returns r1 and level_order(root2) returns r2, r1[k] = r2[k].
    Preconditions: root1 and root2 are Trees, each with at most 2000 nodes and every node value between -1000 and 1000 inclusive. -/
  theorem spec_12 (root1 root2 : Tree) (hnodes1 : N root1 ≤ 2000)
      (hvalues1 : ValuesInRange root1) (hnodes2 : N root2 ≤ 2000)
      (hvalues2 : ValuesInRange root2) (k : Nat) (hk1 : k < H root1) (hk2 : k < H root2)
      (hL : L root1 k = L root2 k) (r1 r2 : Levels)
      (h1 : level_order root1 = ok r1) (h2 : level_order root2 = ok r2) :
      rowVals r1 k = rowVals r2 k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root1 root2 : Tree) (hnodes1 : N root1 ≤ 2000)
        (hvalues1 : ValuesInRange root1) (hnodes2 : N root2 ≤ 2000)
        (hvalues2 : ValuesInRange root2) (k : Nat) (hk1 : k < H root1) (hk2 : k < H root2)
        (hL : L root1 k = L root2 k) (r1 r2 : Levels)
        (h1 : level_order root1 = ok r1) (h2 : level_order root2 = ok r2), rowVals r1 k = rowVals r2 k) := by
    sorry

  end AegisSpec.LevelOrder
