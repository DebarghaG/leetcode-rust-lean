import Aegis.IncreasingBst.Code.Funs

/-!
# Specifications of `Aegis.IncreasingBst.increasing_bst`

LeetCode problem `increasing-order-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IncreasingBst

  open Aegis.IncreasingBst

  def nodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodes l + nodes r

  def inorder : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => inorder l ++ [v.val] ++ inorder r

  def values : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def countValue : Tree → Int → Nat
    | Tree.Null, _ => 0
    | Tree.Node v l r, x => (if v.val = x then 1 else 0) + countValue l x + countValue r x

  def spine : Tree → List Int
    | Tree.Null => []
    | Tree.Node v _ r => v.val :: spine r

  def nondecreasing (l : List Int) : Prop :=
    ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i < j → l[i]'hi ≤ l[j]'hj

  def isBst (t : Tree) : Prop := nondecreasing (inorder t)

  def hasNoLeftChild : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => l = Tree.Null ∧ hasNoLeftChild r

  def countRightNull : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r =>
      (match r with
        | Tree.Null => 1
        | Tree.Node _ _ _ => 0) + countRightNull l + countRightNull r

  def heightNodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + Nat.max (heightNodes l) (heightNodes r)

  def height (t : Tree) : Nat := heightNodes t - 1

  def toI64 (x : Int) : Std.I64 :=
    if h : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 ≤ x ∧
        x ≤ Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64
    then Aeneas.Std.IScalar.ofInt x h
    else 0#i64

  def chain : List Int → Tree
    | [] => Tree.Null
    | x :: xs => Tree.Node (toI64 x) Tree.Null (chain xs)

  def Pre (root : Tree) : Prop :=
    1 ≤ nodes root ∧ nodes root ≤ 100 ∧
      (∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) ∧
      isBst root

  /-- For every root satisfying the preconditions, increasing_bst(root) returns a result r (it does not fail) and r = chain(inorder(root)), where chain([]) = Null and, for n >= 1 and a sequence s = [s0, s1, ..., s_{n-1}], chain(s) = Node(s0, Null, chain([s1, ..., s_{n-1}])). Equivalently, if n = len(inorder(root)), then r has exactly n nodes and for every k with 0 <= k < n, the k-th node on the right spine from the root (0-indexed) has value inorder(root)[k], left child Null, and right child equal to the (k+1)-th spine node when k < n-1 and Null when k = n-1.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_1 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∃ r : Tree, increasing_bst root = ok r ∧ r = chain (inorder root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∃ r : Tree, increasing_bst root = ok r ∧ r = chain (inorder root)) := by
    sorry

  /-- For every root satisfying the preconditions, increasing_bst(root) does not fail: there exists a Tree r such that increasing_bst(root) returns the successful result r. In particular, no overflow, out-of-bounds access, panic, or other error result occurs.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_2 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∃ r : Tree, increasing_bst root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∃ r : Tree, increasing_bst root = ok r) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, every node occurrence of the form Node(v,L,R) in r has L = Null; equivalently, the output tree has no left child anywhere.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_3 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → hasNoLeftChild r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → hasNoLeftChild r) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, r has exactly one node whose right child is Null, and every other node of r has a right child that is a Node. Equivalently, following right children from the root of r visits every node of r exactly once and ends at a single node with no right child.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_4 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r →
        countRightNull r = 1 ∧ (spine r).length = nodes r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r →
          countRightNull r = 1 ∧ (spine r).length = nodes r) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, nodes(r) = nodes(root), where nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R).
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_5 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → nodes r = nodes root := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → nodes r = nodes root) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, inorder(r) = inorder(root), where inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R).
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_6 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → inorder r = inorder root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → inorder r = inorder root) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, for every integer x, the number of nodes in r whose value is x equals the number of nodes in root whose value is x. Equivalently, the multiset of values in r equals the multiset of values in root.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_7 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r →
        ∀ x : Int, countValue r x = countValue root x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r →
          ∀ x : Int, countValue r x = countValue root x) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r and r = Node(v,L,R), the root value v equals inorder(root)[0], the first element of the in-order sequence of root.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_8 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r →
        ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
          (inorder root).head? = some v.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r →
          ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
            (inorder root).head? = some v.val) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, let w be the value of the unique node on the right spine of r whose right child is Null (the last node on the right spine). Then w = inorder(root)[len(inorder(root))-1], the last element of the in-order sequence of root.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_9 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r →
        ∀ w : Int, (spine r).getLast? = some w → (inorder root).getLast? = some w := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r →
          ∀ w : Int, (spine r).getLast? = some w → (inorder root).getLast? = some w) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, if w0, w1, ..., w_{n-1} are the values along the right spine of r in order from the root, then for every i,j with 0 <= i < j < n, wi <= wj. In particular, the spine values are nondecreasing.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_10 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → nondecreasing (spine r) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → nondecreasing (spine r)) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, every value v stored in r satisfies 0 <= v <= 1000.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_11 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → ∀ v ∈ values r, 0 ≤ v ∧ v ≤ 1000 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → ∀ v ∈ values r, 0 ≤ v ∧ v ≤ 1000) := by
    sorry

  /-- Whenever increasing_bst(root) returns a result r, if n = nodes(root) >= 1, then the height of r, defined as the maximum number of edges on a path from the root of r to a leaf of r (a node with no children), is n-1. Equivalently, r contains nodes at depths 0,1,...,n-1 and no node at depth n.
    Preconditions: root is a Tree with 1 <= nodes(root) <= 100, every value stored in root lies in the interval [0,1000], and root is a binary search tree, formalized as: inorder(root) is nondecreasing (for every i,j with 0 <= i < j < len(inorder(root)), inorder(root)[i] <= inorder(root)[j]). Here nodes(Null)=0 and nodes(Node(v,L,R))=1+nodes(L)+nodes(R); inorder(Null)=[] and inorder(Node(v,L,R))=inorder(L) ++ [v] ++ inorder(R), with ++ denoting sequence concatenation and sequences 0-indexed. -/
  theorem spec_12 (root : Tree)
      (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
      (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root) :
      ∀ r : Tree, increasing_bst root = ok r → height r = nodes root - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree)
        (hnodes_pos : 1 ≤ nodes root) (hnodes_le : nodes root ≤ 100)
        (hvals : ∀ x ∈ values root, 0 ≤ x ∧ x ≤ 1000) (hbst : isBst root), ∀ r : Tree, increasing_bst root = ok r → height r = nodes root - 1) := by
    sorry

  end AegisSpec.IncreasingBst
