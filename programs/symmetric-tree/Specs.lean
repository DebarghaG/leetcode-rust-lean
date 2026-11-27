import Aegis.IsSymmetric.Code.Funs

/-!
# Specifications of `Aegis.IsSymmetric.is_symmetric`

LeetCode problem `symmetric-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsSymmetric

  open Aegis.IsSymmetric (Tree)

  def size : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + size l + size r

  def nodeValuesInRange : Tree → Prop
    | .Null => True
    | .Node v l r =>
      -100 ≤ v.val ∧ v.val ≤ 100 ∧ nodeValuesInRange l ∧ nodeValuesInRange r

  def WellFormed (t : Tree) : Prop :=
    1 ≤ size t ∧ size t ≤ 1000 ∧ nodeValuesInRange t

  def Mirror : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node va la ra, .Node vb lb rb =>
      va = vb ∧ Mirror la rb ∧ Mirror ra lb
    | .Node _ _ _, .Null => False
    | .Null, .Node _ _ _ => False

  def Symmetric : Tree → Prop
    | .Null => True
    | .Node _ l r => Mirror l r

  def mirrorTree : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirrorTree r) (mirrorTree l)

  def inorder : Tree → List Int
    | .Null => []
    | .Node v l r => inorder l ++ [v.val] ++ inorder r

  def countNodes (x : Int) : Tree → Nat
    | .Null => 0
    | .Node u l r => (if u.val = x then 1 else 0) + countNodes x l + countNodes x r

  def nodesAtDepth : Nat → Tree → Nat
    | 0, .Null => 0
    | 0, .Node _ _ _ => 1
    | _ + 1, .Null => 0
    | d + 1, .Node _ l r => nodesAtDepth d l + nodesAtDepth d r

  def shift (c : Int) : Tree → Tree
    | .Null => .Null
    | .Node v l r =>
      .Node ⟨BitVec.ofInt 64 (v.val + c)⟩ (shift c l) (shift c r)

  def shiftStaysInRange (c : Int) : Tree → Prop
    | .Null => True
    | .Node v l r =>
      -100 ≤ v.val + c ∧ v.val + c ≤ 100 ∧ shiftStaysInRange c l ∧ shiftStaysInRange c r

  /-- Whenever is_symmetric(root) returns a result r, r = true if and only if Symmetric(root). Here Symmetric(t) holds iff either t = Null, or t = Node(v,l,r) and Mirror(l,r). The relation Mirror(a,b) holds iff either (a = Null and b = Null), or (a = Node(va,la,ra) and b = Node(vb,lb,rb) and va = vb and Mirror(la,rb) and Mirror(ra,lb)); in all other cases Mirror(a,b) is false.
    Preconditions: root is a finite binary tree (a value of type Tree) with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_1 (root : Tree) (hroot : WellFormed root) :
      ∀ r, Aegis.IsSymmetric.is_symmetric root = ok r → (r = true ↔ Symmetric root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ r, Aegis.IsSymmetric.is_symmetric root = ok r → (r = true ↔ Symmetric root)) := by
    sorry

  /-- For every root satisfying the preconditions, is_symmetric(root) returns a result; it does not fail, overflow, access out of bounds, or panic.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_2 (root : Tree) (hroot : WellFormed root) :
      ∃ r, Aegis.IsSymmetric.is_symmetric root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∃ r, Aegis.IsSymmetric.is_symmetric root = ok r) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, if b = true then size(root) is odd.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_3 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true → Odd (size root) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true → Odd (size root)) := by
    sorry

  /-- Whenever is_symmetric(Node(v, Null, Null)) returns a result b, b = true.
    Preconditions: v is an integer with -100 <= v <= 100. -/
  theorem spec_4 (v : Std.I64) (hv1 : -100 ≤ v.val) (hv2 : v.val ≤ 100) :
      ∀ b, Aegis.IsSymmetric.is_symmetric (.Node v .Null .Null) = ok b → b = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (v : Std.I64) (hv1 : -100 ≤ v.val) (hv2 : v.val ≤ 100), ∀ b, Aegis.IsSymmetric.is_symmetric (.Node v .Null .Null) = ok b → b = true) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, b = false.
    Preconditions: root is exactly Node(v, l, Null) with l != Null, or exactly Node(v, Null, r) with r != Null; every node value is in [-100,100] and size(root) <= 1000, where size counts Node constructors. -/
  theorem spec_5 (root : Tree)
      (hshape : (∃ (v : Std.I64) (l : Tree), root = .Node v l .Null ∧ l ≠ .Null) ∨
        (∃ (v : Std.I64) (r : Tree), root = .Node v .Null r ∧ r ≠ .Null))
      (hvals : nodeValuesInRange root) (hsize : size root ≤ 1000) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hshape : (∃ (v : Std.I64) (l : Tree), root = .Node v l .Null ∧ l ≠ .Null) ∨
          (∃ (v : Std.I64) (r : Tree), root = .Node v .Null r ∧ r ≠ .Null))
        (hvals : nodeValuesInRange root) (hsize : size root ≤ 1000), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = false) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result bres, bres = true if and only if a = b.
    Preconditions: root = Node(v, Node(a, Null, Null), Node(b, Null, Null)) with -100 <= v <= 100, -100 <= a <= 100, and -100 <= b <= 100. -/
  theorem spec_6 (v a b : Std.I64)
      (hv1 : -100 ≤ v.val) (hv2 : v.val ≤ 100)
      (ha1 : -100 ≤ a.val) (ha2 : a.val ≤ 100)
      (hb1 : -100 ≤ b.val) (hb2 : b.val ≤ 100) :
      ∀ bres,
        Aegis.IsSymmetric.is_symmetric
            (.Node v (.Node a .Null .Null) (.Node b .Null .Null)) = ok bres →
          (bres = true ↔ a = b) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (v a b : Std.I64)
        (hv1 : -100 ≤ v.val) (hv2 : v.val ≤ 100)
        (ha1 : -100 ≤ a.val) (ha2 : a.val ≤ 100)
        (hb1 : -100 ≤ b.val) (hb2 : b.val ≤ 100), ∀ bres,
          Aegis.IsSymmetric.is_symmetric
              (.Node v (.Node a .Null .Null) (.Node b .Null .Null)) = ok bres →
            (bres = true ↔ a = b)) := by
    sorry

  /-- Whenever is_symmetric(Node(v,l,r)) returns a result b1 and is_symmetric(Node(v',l,r)) returns a result b2, b1 = b2.
    Preconditions: l and r are finite trees, v and v' are integers, all node values in Node(v,l,r) and Node(v',l,r) are in [-100,100], and both trees have size at most 1000. -/
  theorem spec_7 (l r : Tree) (v v' : Std.I64)
      (h1 : nodeValuesInRange (.Node v l r))
      (h2 : nodeValuesInRange (.Node v' l r))
      (hs1 : size (.Node v l r) ≤ 1000) (hs2 : size (.Node v' l r) ≤ 1000) :
      ∀ b1 b2,
        Aegis.IsSymmetric.is_symmetric (.Node v l r) = ok b1 →
          Aegis.IsSymmetric.is_symmetric (.Node v' l r) = ok b2 → b1 = b2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (l r : Tree) (v v' : Std.I64)
        (h1 : nodeValuesInRange (.Node v l r))
        (h2 : nodeValuesInRange (.Node v' l r))
        (hs1 : size (.Node v l r) ≤ 1000) (hs2 : size (.Node v' l r) ≤ 1000), ∀ b1 b2,
          Aegis.IsSymmetric.is_symmetric (.Node v l r) = ok b1 →
            Aegis.IsSymmetric.is_symmetric (.Node v' l r) = ok b2 → b1 = b2) := by
    sorry

  /-- Define mirrorTree(Null)=Null and mirrorTree(Node(v,l,r))=Node(v,mirrorTree(r),mirrorTree(l)). Whenever is_symmetric(root) returns a result b1 and is_symmetric(mirrorTree(root)) returns a result b2, b1 = b2.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000 and every node value in [-100,100]. -/
  theorem spec_8 (root : Tree) (hroot : WellFormed root) :
      ∀ b1 b2,
        Aegis.IsSymmetric.is_symmetric root = ok b1 →
          Aegis.IsSymmetric.is_symmetric (mirrorTree root) = ok b2 → b1 = b2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b1 b2,
          Aegis.IsSymmetric.is_symmetric root = ok b1 →
            Aegis.IsSymmetric.is_symmetric (mirrorTree root) = ok b2 → b1 = b2) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, if b = true and root = Node(v,left,right), then size(left) = size(right), where size(Null)=0 and size(Node(u,l,r))=1+size(l)+size(r).
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000 and every node value in [-100,100]. -/
  theorem spec_9 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
        ∀ (v : Std.I64) (left right : Tree), root = .Node v left right →
          size left = size right := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
          ∀ (v : Std.I64) (left right : Tree), root = .Node v left right →
            size left = size right) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, if b = true and root = Node(v,left,right), then for every integer x, count(x,left) = count(x,right), where count(x,Null)=0 and count(x,Node(u,l,r)) = (if u=x then 1 else 0) + count(x,l) + count(x,r).
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000 and every node value in [-100,100]. -/
  theorem spec_10 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
        ∀ (v : Std.I64) (left right : Tree), root = .Node v left right →
          ∀ x : Int, countNodes x left = countNodes x right := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
          ∀ (v : Std.I64) (left right : Tree), root = .Node v left right →
            ∀ x : Int, countNodes x left = countNodes x right) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, if b = true then x = y.
    Preconditions: root = Node(v, Node(x,lx,rx), Node(y,ly,ry)), all node values are in [-100,100], and size(root) <= 1000. -/
  theorem spec_11 (v x y : Std.I64) (lx rx ly ry : Tree)
      (hvals : nodeValuesInRange (.Node v (.Node x lx rx) (.Node y ly ry)))
      (hsize : size (.Node v (.Node x lx rx) (.Node y ly ry)) ≤ 1000) :
      ∀ b, Aegis.IsSymmetric.is_symmetric (.Node v (.Node x lx rx) (.Node y ly ry)) = ok b →
        b = true → x = y := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (v x y : Std.I64) (lx rx ly ry : Tree)
        (hvals : nodeValuesInRange (.Node v (.Node x lx rx) (.Node y ly ry)))
        (hsize : size (.Node v (.Node x lx rx) (.Node y ly ry)) ≤ 1000), ∀ b, Aegis.IsSymmetric.is_symmetric (.Node v (.Node x lx rx) (.Node y ly ry)) = ok b →
          b = true → x = y) := by
    sorry

  /-- Define shift(c,Null)=Null and shift(c,Node(v,l,r))=Node(v+c,shift(c,l),shift(c,r)). Whenever is_symmetric(root) returns a result b1 and is_symmetric(shift(c,root)) returns a result b2, b1 = b2.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100; c is an integer such that v+c is in [-100,100] for every node value v of root. -/
  theorem spec_12 (root : Tree) (c : Int) (hroot : WellFormed root)
      (hc : shiftStaysInRange c root) :
      ∀ b1 b2,
        Aegis.IsSymmetric.is_symmetric root = ok b1 →
          Aegis.IsSymmetric.is_symmetric (shift c root) = ok b2 → b1 = b2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (c : Int) (hroot : WellFormed root)
        (hc : shiftStaysInRange c root), ∀ b1 b2,
          Aegis.IsSymmetric.is_symmetric root = ok b1 →
            Aegis.IsSymmetric.is_symmetric (shift c root) = ok b2 → b1 = b2) := by
    sorry

  /-- Define mirrorTree(Null)=Null and mirrorTree(Node(v,l,r))=Node(v,mirrorTree(r),mirrorTree(l)). Whenever is_symmetric(root) returns a result b, b = true if and only if root = mirrorTree(root).
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_13 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → (b = true ↔ root = mirrorTree root) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → (b = true ↔ root = mirrorTree root)) := by
    sorry

  /-- Define inorder(Null)=[] and inorder(Node(v,l,r))=inorder(l) ++ [v] ++ inorder(r). Whenever is_symmetric(root) returns a result b, if b = true then inorder(root) = reverse(inorder(root)).
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_14 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
        inorder root = (inorder root).reverse := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
          inorder root = (inorder root).reverse) := by
    sorry

  /-- Whenever is_symmetric(root) returns a result b, if b = true then for every depth d >= 1, the number of nodes at depth d in root is even, where the root has depth 0 and the children of a node at depth d have depth d+1.
    Preconditions: root is a finite binary tree with 1 <= size(root) <= 1000, where size(Null)=0 and size(Node(v,l,r))=1+size(l)+size(r), and every node value v satisfies -100 <= v <= 100. -/
  theorem spec_15 (root : Tree) (hroot : WellFormed root) :
      ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
        ∀ d : Nat, 1 ≤ d → Even (nodesAtDepth d root) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (root : Tree) (hroot : WellFormed root), ∀ b, Aegis.IsSymmetric.is_symmetric root = ok b → b = true →
          ∀ d : Nat, 1 ≤ d → Even (nodesAtDepth d root)) := by
    sorry

  end AegisSpec.IsSymmetric
