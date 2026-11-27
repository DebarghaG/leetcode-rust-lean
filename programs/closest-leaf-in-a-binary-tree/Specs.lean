import Aegis.FindClosestLeaf.Code.Funs

/-!
# Specifications of `Aegis.FindClosestLeaf.find_closest_leaf`

LeetCode problem `closest-leaf-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindClosestLeaf

open Aegis.FindClosestLeaf (Tree)

def values : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (values l ++ values r)

def occurs (v : Int) (t : Tree) : Prop := v ∈ values t

def leafValue (v : Int) : Tree → Prop
  | Tree.Null => False
  | Tree.Node w l r =>
      (w.val = v ∧ l = Tree.Null ∧ r = Tree.Null) ∨ leafValue v l ∨ leafValue v r

def isLeafNode : Tree → Prop
  | Tree.Null => False
  | Tree.Node _ l r => l = Tree.Null ∧ r = Tree.Null

def hasChild (v : Int) : Tree → Prop
  | Tree.Null => False
  | Tree.Node w l r =>
      (w.val = v ∧ (l ≠ Tree.Null ∨ r ≠ Tree.Null)) ∨ hasChild v l ∨ hasChild v r

def hasLeafChild (v : Int) : Tree → Prop
  | Tree.Null => False
  | Tree.Node w l r =>
      (w.val = v ∧ (isLeafNode l ∨ isLeafNode r)) ∨ hasLeafChild v l ∨ hasLeafChild v r

def pathTo (v : Int) : Tree → Option (List Int)
  | Tree.Null => none
  | Tree.Node w l r =>
      if w.val = v then some [v]
      else
        match pathTo v l with
        | some p => some (w.val :: p)
        | none => (pathTo v r).map (fun p => w.val :: p)

def path (t : Tree) (v : Int) : List Int := (pathTo v t).getD []

def depth (t : Tree) (v : Int) : Nat := (path t v).length - 1

def commonPrefixLen : List Int → List Int → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: xs, b :: ys => if a = b then commonPrefixLen xs ys + 1 else 0

def dist (t : Tree) (a b : Int) : Nat :=
  depth t a + depth t b - 2 * (commonPrefixLen (path t a) (path t b) - 1)

def uniqueLeafValue (t : Tree) : Prop :=
  ∃ l : Int, leafValue l t ∧ ∀ l' : Int, leafValue l' t → l' = l

/-- For a value v occurring in root, let node(v) be the unique node with value v. For values a,b occurring in root, let d(a,b) be the number of edges on the unique simple path between node(a) and node(b) in the underlying undirected tree. A leaf value is a value l such that node(l) has no children, i.e. Node(l, Null, Null) occurs in root. The function returns a result r, r is a leaf value of root, and for every leaf value l of root, d(k,l) >= d(k,r).
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k (hence k is one of the node values). -/
theorem spec_1 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root) :
    ∃ r : Std.I64,
      Aegis.FindClosestLeaf.find_closest_leaf root k = ok r ∧
        leafValue r.val root ∧
        ∀ l : Int, leafValue l root → dist root k.val l ≥ dist root k.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root), ∃ r : Std.I64,
      Aegis.FindClosestLeaf.find_closest_leaf root k = ok r ∧
        leafValue r.val root ∧
        ∀ l : Int, leafValue l root → dist root k.val l ≥ dist root k.val r.val) := by
  sorry

/-- The function returns a result r; in particular it does not fail, panic, overflow, or go out of bounds.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_2 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root) :
    ∃ r : Std.I64, Aegis.FindClosestLeaf.find_closest_leaf root k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root), ∃ r : Std.I64, Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) := by
  sorry

/-- Whenever the function returns a result r, the node Node(r, Null, Null) occurs in root; equivalently, r is the value of a leaf node of root.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_3 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) :
    leafValue r.val root := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r), leafValue r.val root) := by
  sorry

/-- Whenever the function returns a result r, for every leaf value l of root, d(k,l) >= d(k,r), where d(a,b) is the number of edges on the unique simple path between the unique nodes with values a and b.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_4 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) :
    ∀ l : Int, leafValue l root → dist root k.val l ≥ dist root k.val r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r), ∀ l : Int, leafValue l root → dist root k.val l ≥ dist root k.val r.val) := by
  sorry

/-- Whenever the function returns a result r, if the node with value k is a leaf of root, then r = k.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_5 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkleaf : leafValue k.val root) :
    r.val = k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkleaf : leafValue k.val root), r.val = k.val) := by
  sorry

/-- Whenever the function returns a result r, if the node with value k has at least one child that is a leaf, then the node with value r is a leaf child of the node with value k; equivalently, d(k,r) = 1 and r is a leaf value.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_6 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkchild : hasLeafChild k.val root) :
    dist root k.val r.val = 1 ∧ leafValue r.val root := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkchild : hasLeafChild k.val root), dist root k.val r.val = 1 ∧ leafValue r.val root) := by
  sorry

/-- Whenever the function returns a result r, if the root node itself has value k, then r is a leaf value and for every leaf value l of root, depth(l) >= depth(r), where depth(x) is the number of edges from the root to the node with value x.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_7 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hrootk : ∃ tl tr : Tree, root = Tree.Node k tl tr) :
    leafValue r.val root ∧ ∀ l : Int, leafValue l root → depth root l ≥ depth root r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hrootk : ∃ tl tr : Tree, root = Tree.Node k tl tr), leafValue r.val root ∧ ∀ l : Int, leafValue l root → depth root l ≥ depth root r.val) := by
  sorry

/-- Whenever the function returns a result r, if N is the number of nodes of root, then d(k,r) <= N - 1, where d(a,b) is the number of edges on the unique simple path between the unique nodes with values a and b.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_8 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) :
    dist root k.val r.val ≤ (values root).length - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r), dist root k.val r.val ≤ (values root).length - 1) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= 1000.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_9 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) :
    1 ≤ r.val ∧ r.val ≤ 1000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r), 1 ≤ r.val ∧ r.val ≤ 1000) := by
  sorry

/-- Whenever the function returns a result r, if the node with value k has at least one child (that is, k is not a leaf), then r != k and d(k,r) >= 1, where d(a,b) is the number of edges on the unique simple path between the unique nodes with values a and b.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_10 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkchild : hasChild k.val root) :
    r.val ≠ k.val ∧ dist root k.val r.val ≥ 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (hkchild : hasChild k.val root), r.val ≠ k.val ∧ dist root k.val r.val ≥ 1) := by
  sorry

/-- Whenever the function returns a result r, d(k,r) = 0 if and only if the node with value k is a leaf of root and r = k, where d(a,b) is the number of edges on the unique simple path between the unique nodes with values a and b.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_11 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r) :
    dist root k.val r.val = 0 ↔ leafValue k.val root ∧ r.val = k.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r), dist root k.val r.val = 0 ↔ leafValue k.val root ∧ r.val = k.val) := by
  sorry

/-- Whenever the function returns a result r, if there is exactly one value l such that Node(l, Null, Null) occurs in root, then r = l.
  Preconditions: root is a finite nonempty binary tree (root != Null); every node value is an integer v with 1 <= v <= 1000; all node values are distinct; the number of nodes is between 1 and 1000; and there is a node in root whose value equals k. -/
theorem spec_12 (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (huniq : uniqueLeafValue root) :
    ∃ l : Int, leafValue l root ∧ (∀ l' : Int, leafValue l' root → l' = l) ∧ r.val = l := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (r : Std.I64)
    (hroot : root ≠ Tree.Null)
    (hval : ∀ v : Int, occurs v root → 1 ≤ v ∧ v ≤ 1000)
    (hnd : (values root).Nodup)
    (hsize : 1 ≤ (values root).length ∧ (values root).length ≤ 1000)
    (hk : occurs k.val root)
    (hres : Aegis.FindClosestLeaf.find_closest_leaf root k = ok r)
    (huniq : uniqueLeafValue root), ∃ l : Int, leafValue l root ∧ (∀ l' : Int, leafValue l' root → l' = l) ∧ r.val = l) := by
  sorry

end AegisSpec.FindClosestLeaf
