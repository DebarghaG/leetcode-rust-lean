import Aegis.CountNodes.Code.Funs

/-!
# Specifications of `Aegis.CountNodes.count_nodes`

LeetCode problem `count-complete-tree-nodes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountNodes

open Aegis.CountNodes

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def treeHeight : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (treeHeight l) (treeHeight r)

def IsPerfect : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => IsPerfect l ∧ IsPerfect r ∧ treeHeight l = treeHeight r

def IsComplete : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r =>
    (IsPerfect l ∧ IsComplete r ∧ treeHeight l = treeHeight r) ∨
    (IsComplete l ∧ IsPerfect r ∧ treeHeight l = treeHeight r + 1)

def ValuesInRange : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => 0 ≤ v.val ∧ v.val ≤ 50000 ∧ ValuesInRange l ∧ ValuesInRange r

/-- Whenever count_nodes(root) returns a result r, r = N(root), i.e. the returned integer equals the number of Node constructors in root (the number of nodes in the tree).
  Preconditions: Let N(t) be the number of Node constructors in t, defined by N(Null)=0 and N(Node(v,l,r))=1+N(l)+N(r). Assume root is a complete binary tree (the empty tree Null is complete; otherwise every level except possibly the last is completely filled, and all nodes in the last level are as far left as possible), 0 <= N(root) <= 50000, and every node value v satisfies 0 <= v <= 50000. -/
theorem spec_1 (root : Tree)
    (hcomplete : IsComplete root)
    (hsize : 0 ≤ nodeCount root ∧ nodeCount root ≤ 50000)
    (hvalues : ValuesInRange root)
    (r : Std.I64)
    (hres : count_nodes root = ok r) :
    r.val = (nodeCount root : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hcomplete : IsComplete root)
    (hsize : 0 ≤ nodeCount root ∧ nodeCount root ≤ 50000)
    (hvalues : ValuesInRange root)
    (r : Std.I64)
    (hres : count_nodes root = ok r), r.val = (nodeCount root : Int)) := by
  sorry

/-- count_nodes(root) returns a result r (it does not fail: no overflow, out-of-bounds access, panic, or other Lean Result error occurs).
  Preconditions: Let N(t) be the number of Node constructors in t, defined by N(Null)=0 and N(Node(v,l,r))=1+N(l)+N(r). Assume root is a complete binary tree (the empty tree Null is complete; otherwise every level except possibly the last is completely filled, and all nodes in the last level are as far left as possible), 0 <= N(root) <= 50000, and every node value v satisfies 0 <= v <= 50000. -/
theorem spec_2 (root : Tree)
    (hcomplete : IsComplete root)
    (hsize : 0 ≤ nodeCount root ∧ nodeCount root ≤ 50000)
    (hvalues : ValuesInRange root) :
    ∃ r : Std.I64, count_nodes root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hcomplete : IsComplete root)
    (hsize : 0 ≤ nodeCount root ∧ nodeCount root ≤ 50000)
    (hvalues : ValuesInRange root), ∃ r : Std.I64, count_nodes root = ok r) := by
  sorry

end AegisSpec.CountNodes
