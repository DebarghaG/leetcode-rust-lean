import Aegis.FindTilt.Code.Funs

/-!
# Specifications of `Aegis.FindTilt.find_tilt`

LeetCode problem `binary-tree-tilt`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTilt

  open _root_.Aegis.FindTilt

  def subtree_sum : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r => v.val + subtree_sum l + subtree_sum r

  def node_count : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + node_count l + node_count r

  def tilt : Tree → Int
    | Tree.Null => 0
    | Tree.Node _ l r => |subtree_sum l - subtree_sum r|

  def total_tilt : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r => tilt (Tree.Node v l r) + total_tilt l + total_tilt r

  def ForallNodes (p : Int → Prop) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => p v.val ∧ ForallNodes p l ∧ ForallNodes p r

  def values_bounded (t : Tree) : Prop := ForallNodes (fun x => -1000 ≤ x ∧ x ≤ 1000) t

  def values_nonneg (t : Tree) : Prop := ForallNodes (fun x => 0 ≤ x) t

  def values_zero (t : Tree) : Prop := ForallNodes (fun x => x = 0) t

  def at_most_one_child : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r =>
      (l = Tree.Null ∨ r = Tree.Null) ∧ at_most_one_child l ∧ at_most_one_child r

  def depth : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (depth l) (depth r)

  def value_depth_sum_from (d : Int) : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r =>
      v.val * d + value_depth_sum_from (d + 1) l + value_depth_sum_from (d + 1) r

  def value_depth_sum (t : Tree) : Int := value_depth_sum_from 0 t

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def negI64 (v : Std.I64) : Std.I64 := IScalar.mk (-v.bv)

  def negate : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node (negI64 v) (negate l) (negate r)

  /-- Define subtree_sum(t) by subtree_sum(Null) = 0 and subtree_sum(Node(v,l,r)) = v + subtree_sum(l) + subtree_sum(r). Define tilt(t) by tilt(Null) = 0 and tilt(Node(v,l,r)) = |subtree_sum(l) - subtree_sum(r)|. Define total_tilt(t) by total_tilt(Null) = 0 and total_tilt(Node(v,l,r)) = tilt(Node(v,l,r)) + total_tilt(l) + total_tilt(r); equivalently, total_tilt(t) is the sum of tilt(u) over all nodes u of t. Then find_tilt(root) returns a result ans and ans = total_tilt(root).
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_1 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = total_tilt root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = total_tilt root) := by
    sorry

  /-- There exists an i64 ans such that find_tilt(root) returns ans; the call does not fail by arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_2 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∃ ans : Std.I64, find_tilt root = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∃ ans : Std.I64, find_tilt root = ok ans) := by
    sorry

  /-- Whenever find_tilt(root) returns an i64 ans, 0 <= ans.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_3 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∀ ans : Std.I64, find_tilt root = ok ans → 0 ≤ ans.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∀ ans : Std.I64, find_tilt root = ok ans → 0 ≤ ans.val) := by
    sorry

  /-- Let n be the number of nodes in root. Whenever find_tilt(root) returns an i64 ans, ans <= 2000 * n * n.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_4 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∀ ans : Std.I64, find_tilt root = ok ans →
        ans.val ≤ 2000 * (node_count root : Int) * (node_count root : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∀ ans : Std.I64, find_tilt root = ok ans →
          ans.val ≤ 2000 * (node_count root : Int) * (node_count root : Int)) := by
    sorry

  /-- If root = Null, then find_tilt(root) returns 0.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_5 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000)
      (hroot : root = Tree.Null) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000)
        (hroot : root = Tree.Null), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0) := by
    sorry

  /-- If root = Node(v, Null, Null) and -1000 <= v <= 1000, then find_tilt(root) returns 0.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_6 (root : Tree) (v : Std.I64) (hb : values_bounded root)
      (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v Tree.Null Tree.Null)
      (hv : -1000 ≤ v.val ∧ v.val ≤ 1000) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (hb : values_bounded root)
        (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v Tree.Null Tree.Null)
        (hv : -1000 ≤ v.val ∧ v.val ≤ 1000), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0) := by
    sorry

  /-- If root = Node(v, Node(c, Null, Null), Null) or root = Node(v, Null, Node(c, Null, Null)), then find_tilt(root) returns |c|.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_7 (root : Tree) (v c : Std.I64) (hb : values_bounded root)
      (hn : node_count root ≤ 10000)
      (hroot : root = Tree.Node v (Tree.Node c Tree.Null Tree.Null) Tree.Null ∨
        root = Tree.Node v Tree.Null (Tree.Node c Tree.Null Tree.Null)) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = |c.val| := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (v c : Std.I64) (hb : values_bounded root)
        (hn : node_count root ≤ 10000)
        (hroot : root = Tree.Node v (Tree.Node c Tree.Null Tree.Null) Tree.Null ∨
          root = Tree.Node v Tree.Null (Tree.Node c Tree.Null Tree.Null)), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = |c.val|) := by
    sorry

  /-- For every root of the form Node(v,l,r), whenever find_tilt(root) returns an i64 ans, ans >= |subtree_sum(l) - subtree_sum(r)|, where subtree_sum(l) is the sum of all node values in l (with subtree_sum(Null)=0).
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_8 (root : Tree) (v : Std.I64) (l r : Tree) (hb : values_bounded root)
      (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v l r) :
      ∀ ans : Std.I64, find_tilt root = ok ans →
        |subtree_sum l - subtree_sum r| ≤ ans.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (l r : Tree) (hb : values_bounded root)
        (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v l r), ∀ ans : Std.I64, find_tilt root = ok ans →
          |subtree_sum l - subtree_sum r| ≤ ans.val) := by
    sorry

  /-- For every root of the form Node(v,l,r), whenever find_tilt(root) returns an i64 ans, ans = |subtree_sum(l) - subtree_sum(r)| + total_tilt(l) + total_tilt(r), where subtree_sum(Null)=0 and subtree_sum(Node(x,a,b))=x+subtree_sum(a)+subtree_sum(b), and total_tilt is the sum of tilts over all nodes as defined in spec_1.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_9 (root : Tree) (v : Std.I64) (l r : Tree) (hb : values_bounded root)
      (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v l r) :
      ∀ ans : Std.I64, find_tilt root = ok ans →
        ans.val = |subtree_sum l - subtree_sum r| + total_tilt l + total_tilt r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (l r : Tree) (hb : values_bounded root)
        (hn : node_count root ≤ 10000) (hroot : root = Tree.Node v l r), ∀ ans : Std.I64, find_tilt root = ok ans →
          ans.val = |subtree_sum l - subtree_sum r| + total_tilt l + total_tilt r) := by
    sorry

  /-- Define mirror(t) by mirror(Null)=Null and mirror(Node(v,l,r))=Node(v,mirror(r),mirror(l)). Then find_tilt(root) and find_tilt(mirror(root)) both return results, and those two results are equal.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_10 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∃ ans ans' : Std.I64,
        find_tilt root = ok ans ∧ find_tilt (mirror root) = ok ans' ∧ ans = ans' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∃ ans ans' : Std.I64,
          find_tilt root = ok ans ∧ find_tilt (mirror root) = ok ans' ∧ ans = ans') := by
    sorry

  /-- Define negate(t) by negate(Null)=Null and negate(Node(v,l,r))=Node(-v,negate(l),negate(r)). Then find_tilt(root) and find_tilt(negate(root)) both return results, and those two results are equal.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_11 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      ∃ ans ans' : Std.I64,
        find_tilt root = ok ans ∧ find_tilt (negate root) = ok ans' ∧ ans = ans' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), ∃ ans ans' : Std.I64,
          find_tilt root = ok ans ∧ find_tilt (negate root) = ok ans' ∧ ans = ans') := by
    sorry

  /-- If root = Node(v,l,r) and root' = Node(v',l,r) where v' is any integer with -1000 <= v' <= 1000, then find_tilt(root) and find_tilt(root') both return results, and those two results are equal.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_12 (root root' : Tree) (v v' : Std.I64) (l r : Tree)
      (hb : values_bounded root) (hn : node_count root ≤ 10000)
      (hroot : root = Tree.Node v l r) (hroot' : root' = Tree.Node v' l r)
      (hv' : -1000 ≤ v'.val ∧ v'.val ≤ 1000) :
      ∃ ans ans' : Std.I64,
        find_tilt root = ok ans ∧ find_tilt root' = ok ans' ∧ ans = ans' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root' : Tree) (v v' : Std.I64) (l r : Tree)
        (hb : values_bounded root) (hn : node_count root ≤ 10000)
        (hroot : root = Tree.Node v l r) (hroot' : root' = Tree.Node v' l r)
        (hv' : -1000 ≤ v'.val ∧ v'.val ≤ 1000), ∃ ans ans' : Std.I64,
          find_tilt root = ok ans ∧ find_tilt root' = ok ans' ∧ ans = ans') := by
    sorry

  /-- If every node value in root is 0, then find_tilt(root) returns 0.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_13 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000)
      (hzero : values_zero root) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000)
        (hzero : values_zero root), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0) := by
    sorry

  /-- If root = Null, then find_tilt(root) returns 0. If root is nonempty, every node of root has at most one child, and every node value in root is nonnegative, then letting depth(root)=0 and depth(c)=depth(u)+1 for every child c of a node u, find_tilt(root) returns the sum over all nodes x of root of (value(x) * depth(x)).
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_14 (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000) :
      (root = Tree.Null →
          ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0) ∧
      (∀ (v : Std.I64) (l r : Tree), root = Tree.Node v l r → at_most_one_child root →
          values_nonneg root →
          ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = value_depth_sum root) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (hb : values_bounded root) (hn : node_count root ≤ 10000), (root = Tree.Null →
            ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = 0) ∧
        (∀ (v : Std.I64) (l r : Tree), root = Tree.Node v l r → at_most_one_child root →
            values_nonneg root →
            ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = value_depth_sum root)) := by
    sorry

  /-- If root = Node(v, Node(a, Null, Null), Node(b, Null, Null)), then find_tilt(root) returns |a - b|.
    Preconditions: Every node value v in root satisfies -1000 <= v <= 1000, and the number of nodes (Node constructors) in root is at most 10000; the tree may be empty. -/
  theorem spec_15 (root : Tree) (v a b : Std.I64) (hb : values_bounded root)
      (hn : node_count root ≤ 10000)
      (hroot : root =
        Tree.Node v (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null)) :
      ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = |a.val - b.val| := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (root : Tree) (v a b : Std.I64) (hb : values_bounded root)
        (hn : node_count root ≤ 10000)
        (hroot : root =
          Tree.Node v (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null)), ∃ ans : Std.I64, find_tilt root = ok ans ∧ ans.val = |a.val - b.val|) := by
    sorry

  end AegisSpec.FindTilt
