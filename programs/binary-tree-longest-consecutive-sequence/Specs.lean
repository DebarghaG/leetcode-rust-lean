import Aegis.LongestConsecutive.Code.Funs

/-!
# Specifications of `Aegis.LongestConsecutive.longest_consecutive`

LeetCode problem `binary-tree-longest-consecutive-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestConsecutive

open Aegis.LongestConsecutive

def nodeVal : Tree → Option Int
  | Tree.Null => none
  | Tree.Node v _ _ => some v.val

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + nodeCount r + 1

def treeHeight : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (treeHeight l) (treeHeight r)

def nodeList : Tree → List Tree
  | Tree.Null => []
  | Tree.Node v l r => Tree.Node v l r :: (nodeList l ++ nodeList r)

def valueList : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (valueList l ++ valueList r)

def ValuesInRange (t : Tree) : Prop := ∀ x ∈ valueList t, -30000 ≤ x ∧ x ≤ 30000

def leftChild : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node _ l _ => l

def rightChild : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node _ _ r => r

def IsChild (p c : Tree) : Prop :=
  match p with
  | Tree.Null => False
  | Tree.Node _ l r => (c = l ∨ c = r) ∧ c ≠ Tree.Null

def ConsecStep (p c : Tree) : Prop :=
  IsChild p c ∧ ∃ a : Int, nodeVal p = some a ∧ nodeVal c = some (a + 1)

def AtMostOneChild : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ Tree.Null _ => True
  | Tree.Node _ _ Tree.Null => True
  | Tree.Node _ _ _ => False

def ChainStep : List Tree → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ConsecStep a b ∧ ChainStep (b :: rest)

def IsConsecPath (root : Tree) (path : List Tree) : Prop :=
  path ≠ [] ∧ (∀ u, path.head? = some u → u ∈ nodeList root) ∧ ChainStep path

def extendDown (w : Int) : Tree → Nat
  | Tree.Null => 0
  | Tree.Node a l r =>
      if a.val = w + 1 then 1 + max (extendDown a.val l) (extendDown a.val r) else 0

def maxFromRoot : Tree → Nat
  | Tree.Null => 0
  | Tree.Node v l r => 1 + max (extendDown v.val l) (extendDown v.val r)

def maxDown : Tree → Nat
  | Tree.Null => 0
  | Tree.Node v l r => max (maxDown l) (max (maxDown r) (maxFromRoot (Tree.Node v l r)))

inductive InsertLeaf : Tree → Tree → Prop where
  | left (v w : Std.I64) (rest : Tree) :
      InsertLeaf (Tree.Node v Tree.Null rest)
        (Tree.Node v (Tree.Node w Tree.Null Tree.Null) rest)
  | right (v w : Std.I64) (l : Tree) :
      InsertLeaf (Tree.Node v l Tree.Null)
        (Tree.Node v l (Tree.Node w Tree.Null Tree.Null))
  | node_left {v : Std.I64} {l r l' : Tree} (h : InsertLeaf l l') :
      InsertLeaf (Tree.Node v l r) (Tree.Node v l' r)
  | node_right {v : Std.I64} {l r r' : Tree} (h : InsertLeaf r r') :
      InsertLeaf (Tree.Node v l r) (Tree.Node v l r')

inductive SwapsChildren : Tree → Tree → Prop where
  | null : SwapsChildren Tree.Null Tree.Null
  | keep {v : Std.I64} {l r l' r' : Tree} (hl : SwapsChildren l l')
      (hr : SwapsChildren r r') :
      SwapsChildren (Tree.Node v l r) (Tree.Node v l' r')
  | swap {v : Std.I64} {l r l' r' : Tree} (hl : SwapsChildren l l')
      (hr : SwapsChildren r r') :
      SwapsChildren (Tree.Node v l r) (Tree.Node v r' l')

/-- The function returns a result r and r is the maximum length of a consecutive downward path in root. That is: (1) there exists a downward path n0, n1, ..., n_{r-1} in root (a sequence of r nodes where each n_{i+1} is the left or right child of n_i) such that for every i with 0 <= i < r-1, val(n_{i+1}) = val(n_i) + 1; and (2) for every consecutive downward path in root of length k, k <= r.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_1 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        (∃ path : List Tree,
          IsConsecPath root path ∧ res.val = (path.length : Int)) ∧
        (∀ path : List Tree,
          IsConsecPath root path → (path.length : Int) ≤ res.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        (∃ path : List Tree,
          IsConsecPath root path ∧ res.val = (path.length : Int)) ∧
        (∀ path : List Tree,
          IsConsecPath root path → (path.length : Int) ≤ res.val)) := by
  sorry

/-- The function returns a result r and 1 <= r <= n, where n is the total number of nodes in root.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_2 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        1 ≤ res.val ∧ res.val ≤ (nodeCount root : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        1 ≤ res.val ∧ res.val ≤ (nodeCount root : Int)) := by
  sorry

/-- The function returns r = 1.
  Preconditions: root = Node(v, Null, Null) for some i64 v with -30000 <= v <= 30000. -/
theorem spec_3 (root : Tree) (v : Std.I64)
    (hroot : root = Tree.Node v Tree.Null Tree.Null)
    (hvlo : -30000 ≤ v.val) (hvhi : v.val ≤ 30000) :
    ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (v : Std.I64)
    (hroot : root = Tree.Node v Tree.Null Tree.Null)
    (hvlo : -30000 ≤ v.val) (hvhi : v.val ≤ 30000), ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 1) := by
  sorry

/-- The function returns r = 2.
  Preconditions: root is either Node(v, Node(v+1, Null, Null), Null) or Node(v, Null, Node(v+1, Null, Null)), with -30000 <= v <= 29999. -/
theorem spec_4 (root : Tree) (v w : Std.I64)
    (hroot : root = Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null ∨
      root = Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null))
    (hvlo : -30000 ≤ v.val) (hvhi : v.val ≤ 29999)
    (hw : w.val = v.val + 1) :
    ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (v w : Std.I64)
    (hroot : root = Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null ∨
      root = Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null))
    (hvlo : -30000 ≤ v.val) (hvhi : v.val ≤ 29999)
    (hw : w.val = v.val + 1), ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 2) := by
  sorry

/-- The function returns a result r and there exists a consecutive downward path in root of length r.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_5 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        ∃ path : List Tree,
          IsConsecPath root path ∧ res.val = (path.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        ∃ path : List Tree,
          IsConsecPath root path ∧ res.val = (path.length : Int)) := by
  sorry

/-- The function returns a result r and for every consecutive downward path in root of length k, k <= r.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_6 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        ∀ path : List Tree,
          IsConsecPath root path → (path.length : Int) ≤ res.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        ∀ path : List Tree,
          IsConsecPath root path → (path.length : Int) ≤ res.val) := by
  sorry

/-- Let r be the result of longest_consecutive(root) and r' be the result of longest_consecutive(root'). If both functions return results, then r' >= r.
  Preconditions: root is not Null and satisfies the node count and value range constraints; root' is obtained from root by attaching one new leaf node (with any value in [-30000, 30000]) to an empty left or right child of some node in root, and root' also satisfies the node count and value range constraints. -/
theorem spec_7 (root root' : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hins : InsertLeaf root root')
    (hlo' : 1 ≤ nodeCount root') (hhi' : nodeCount root' ≤ 30000)
    (hval' : ValuesInRange root')
    (res res' : Std.I64)
    (hres : longest_consecutive root = ok res)
    (hres' : longest_consecutive root' = ok res') :
    res.val ≤ res'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root root' : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hins : InsertLeaf root root')
    (hlo' : 1 ≤ nodeCount root') (hhi' : nodeCount root' ≤ 30000)
    (hval' : ValuesInRange root')
    (res res' : Std.I64)
    (hres : longest_consecutive root = ok res)
    (hres' : longest_consecutive root' = ok res'), res.val ≤ res'.val) := by
  sorry

/-- Let r be the result of longest_consecutive(root) and r' be the result of longest_consecutive(root'). If both functions return results, then r' = r.
  Preconditions: root is not Null and satisfies the node count and value range constraints; root' is obtained from root by swapping the left and right subtrees at any set of nodes (i.e., replacing some Node(v, l, r) with Node(v, r, l)). -/
theorem spec_8 (root root' : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hswap : SwapsChildren root root')
    (res res' : Std.I64)
    (hres : longest_consecutive root = ok res)
    (hres' : longest_consecutive root' = ok res') :
    res'.val = res.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root' : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hswap : SwapsChildren root root')
    (res res' : Std.I64)
    (hres : longest_consecutive root = ok res)
    (hres' : longest_consecutive root' = ok res'), res'.val = res.val) := by
  sorry

/-- The function returns r = n, where n is the number of nodes in root.
  Preconditions: root is not Null; the tree is a single downward path (each node has at most one child); for every edge from a parent node to a child node, the child's value is exactly the parent's value + 1; all values are in [-30000, 30000]. -/
theorem spec_9 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hchain : ∀ u ∈ nodeList root, AtMostOneChild u)
    (hinc : ∀ u ∈ nodeList root, ∀ c : Tree, IsChild u c →
      ∃ a : Int, nodeVal u = some a ∧ nodeVal c = some (a + 1))
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧ res.val = (nodeCount root : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hchain : ∀ u ∈ nodeList root, AtMostOneChild u)
    (hinc : ∀ u ∈ nodeList root, ∀ c : Tree, IsChild u c →
      ∃ a : Int, nodeVal u = some a ∧ nodeVal c = some (a + 1))
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧ res.val = (nodeCount root : Int)) := by
  sorry

/-- The function returns a result r and r = max(L, R, S), where: L is the maximum length of a consecutive downward path in the left subtree (0 if the left child is Null); R is the maximum length of a consecutive downward path in the right subtree (0 if the right child is Null); and S is the maximum length of a consecutive downward path in root that starts at the root.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_10 (root : Tree) (v : Std.I64) (l r : Tree)
    (hroot : root = Tree.Node v l r)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        res.val =
          ((max (max (maxDown l) (maxDown r)) (maxFromRoot root) : Nat) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (v : Std.I64) (l r : Tree)
    (hroot : root = Tree.Node v l r)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧
        res.val =
          ((max (max (maxDown l) (maxDown r)) (maxFromRoot root) : Nat) : Int)) := by
  sorry

/-- The function returns a result r and r <= h, where h is the maximum number of nodes on any downward path in root (the height of the tree in nodes).
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_11 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64,
      longest_consecutive root = ok res ∧ res.val ≤ (treeHeight root : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64,
      longest_consecutive root = ok res ∧ res.val ≤ (treeHeight root : Int)) := by
  sorry

/-- The function returns a result r and r >= 2.
  Preconditions: root is not Null and satisfies the node count and value range constraints; there exists a node u in root with a child c such that val(c) = val(u) + 1. -/
theorem spec_12 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hedge : ∃ u ∈ nodeList root, ∃ c : Tree, ConsecStep u c) :
    ∃ res : Std.I64, longest_consecutive root = ok res ∧ 2 ≤ res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hedge : ∃ u ∈ nodeList root, ∃ c : Tree, ConsecStep u c), ∃ res : Std.I64, longest_consecutive root = ok res ∧ 2 ≤ res.val) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive. -/
theorem spec_13 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root) :
    ∃ res : Std.I64, longest_consecutive root = ok res := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root), ∃ res : Std.I64, longest_consecutive root = ok res) := by
  sorry

/-- The function returns a result r and r = 1.
  Preconditions: root is not Null; the number of nodes in root is between 1 and 30000 inclusive; every node's value is between -30000 and 30000 inclusive; for every node u in root and every child c of u, val(c) != val(u)+1. -/
theorem spec_14 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hnone : ∀ u ∈ nodeList root, ∀ c : Tree, ¬ ConsecStep u c) :
    ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hlo : 1 ≤ nodeCount root) (hhi : nodeCount root ≤ 30000)
    (hval : ValuesInRange root)
    (hnone : ∀ u ∈ nodeList root, ∀ c : Tree, ¬ ConsecStep u c), ∃ res : Std.I64, longest_consecutive root = ok res ∧ res.val = 1) := by
  sorry

end AegisSpec.LongestConsecutive
