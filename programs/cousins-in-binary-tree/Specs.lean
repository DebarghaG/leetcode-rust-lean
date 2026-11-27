import Aegis.IsCousins.Code.Funs

/-!
# Specifications of `Aegis.IsCousins.is_cousins`

LeetCode problem `cousins-in-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsCousins

  namespace AegisSpec.IsCousins

  def values : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def ValuesInRange : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => 1 ≤ v.val ∧ v.val ≤ 100 ∧ ValuesInRange l ∧ ValuesInRange r

  def Distinct (t : Tree) : Prop := (values t).Nodup

  def OccursOnce (t : Tree) (v : Int) : Prop := (values t).count v = 1

  def HasValue (t : Tree) (v : Int) : Prop := v ∈ values t

  def pathTo : Tree → Int → Option (List Int)
    | Tree.Null, _ => none
    | Tree.Node v l r, target =>
        if v.val = target then some [v.val]
        else
          match pathTo l target with
          | some p => some (v.val :: p)
          | none => (pathTo r target).map (fun p => v.val :: p)

  def depthOf (t : Tree) (v : Int) : Option Nat :=
    (pathTo t v).map (fun p => p.length - 1)

  def parentOf (t : Tree) (v : Int) : Option Int :=
    (pathTo t v).bind (fun p => p.dropLast.getLast?)

  /-- Whenever is_cousins(root,x,y) returns a result r, r is true if and only if depth(root,x) = depth(root,y), this common depth is at least 1, and the parent of the node with value x in root is a different node from the parent of the node with value y in root. Here depth(root,v) is the number of edges on the path from the root node (which has depth 0) to the unique node with value v, and the parent of a non-root node is the immediate predecessor of that node on this path. In all other cases, including when either node has no parent, r is false.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_1 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∀ r : Bool, is_cousins root x y = ok r →
        (r = true ↔
          ∃ d : Nat,
            depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 1 ≤ d ∧
              ∃ px py : Int,
                parentOf root x.val = some px ∧ parentOf root y.val = some py ∧ px ≠ py) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∀ r : Bool, is_cousins root x y = ok r →
          (r = true ↔
            ∃ d : Nat,
              depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 1 ≤ d ∧
                ∃ px py : Int,
                  parentOf root x.val = some px ∧ parentOf root y.val = some py ∧ px ≠ py)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_2 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∃ r : Bool, is_cousins root x y = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∃ r : Bool, is_cousins root x y = ok r) := by
    sorry

  /-- If the nodes with values x and y have the same parent in root, then whenever is_cousins(root,x,y) returns a result r, r = false.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_3 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
      (hsame_parent : ∃ p : Int, parentOf root x.val = some p ∧ parentOf root y.val = some p) :
      ∀ r : Bool, is_cousins root x y = ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
        (hsame_parent : ∃ p : Int, parentOf root x.val = some p ∧ parentOf root y.val = some p), ∀ r : Bool, is_cousins root x y = ok r → r = false) := by
    sorry

  /-- If depth(root,x) != depth(root,y), then whenever is_cousins(root,x,y) returns a result r, r = false. Here depth(root,v) is the number of edges from the root node (which has depth 0) to the unique node with value v.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_4 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
      (hdepth_ne : depthOf root x.val ≠ depthOf root y.val) :
      ∀ r : Bool, is_cousins root x y = ok r → r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
        (hdepth_ne : depthOf root x.val ≠ depthOf root y.val), ∀ r : Bool, is_cousins root x y = ok r → r = false) := by
    sorry

  /-- If depth(root,x) = depth(root,y), this common depth is at least 1, and the parent node of x is different from the parent node of y, then whenever is_cousins(root,x,y) returns a result r, r = true. Here depth(root,v) is the number of edges from the root node (which has depth 0) to the unique node with value v, and parent means the immediate predecessor on that path.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_5 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
      (hdepth : ∃ d : Nat,
        depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 1 ≤ d)
      (hparent : ∃ px py : Int,
        parentOf root x.val = some px ∧ parentOf root y.val = some py ∧ px ≠ py) :
      ∀ r : Bool, is_cousins root x y = ok r → r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
        (hdepth : ∃ d : Nat,
          depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 1 ≤ d)
        (hparent : ∃ px py : Int,
          parentOf root x.val = some px ∧ parentOf root y.val = some py ∧ px ≠ py), ∀ r : Bool, is_cousins root x y = ok r → r = true) := by
    sorry

  /-- If is_cousins(root,x,y) returns true, then 2 <= depth(root,x) = depth(root,y) <= 99. Here depth(root,v) is the number of edges from the root node (which has depth 0) to the unique node with value v.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_6 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∀ r : Bool, is_cousins root x y = ok r → r = true →
        ∃ d : Nat,
          depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 2 ≤ d ∧ d ≤ 99 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∀ r : Bool, is_cousins root x y = ok r → r = true →
          ∃ d : Nat,
            depthOf root x.val = some d ∧ depthOf root y.val = some d ∧ 2 ≤ d ∧ d ≤ 99) := by
    sorry

  /-- If root has at most 4 Node constructors, then whenever is_cousins(root,x,y) returns a result r, r = false.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_7 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
      (hsmall : nodeCount root ≤ 4) :
      ∀ r : Bool, is_cousins root x y = ok r → r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
        (hsmall : nodeCount root ≤ 4), ∀ r : Bool, is_cousins root x y = ok r → r = false) := by
    sorry

  /-- For every input satisfying the preconditions, if is_cousins(root,x,y) returns r1 and is_cousins(root,y,x) returns r2, then r1 = r2.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_8 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∀ r1 r2 : Bool,
        is_cousins root x y = ok r1 → is_cousins root y x = ok r2 → r1 = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∀ r1 r2 : Bool,
          is_cousins root x y = ok r1 → is_cousins root y x = ok r2 → r1 = r2) := by
    sorry

  /-- Under these preconditions, if is_cousins(root,x,y) returns r and is_cousins(root2,x,y) returns r2, then r = r2.
    Preconditions: root and root2 are Trees each with between 2 and 100 Node constructors inclusive; every node value in each tree lies in the integer interval [1,100]; all node values in each tree are distinct; x and y are two distinct values occurring exactly once in both root and root2; the sequence of node values on the path from the root of root to x equals the sequence on the path from the root of root2 to x, and the same holds for y. -/
  theorem spec_9 (root root2 : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hnode2_lo : 2 ≤ nodeCount root2) (hnode2_hi : nodeCount root2 ≤ 100)
      (hrange : ValuesInRange root) (hrange2 : ValuesInRange root2)
      (hdistinct : Distinct root) (hdistinct2 : Distinct root2)
      (hxy : x.val ≠ y.val)
      (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
      (hx2 : OccursOnce root2 x.val) (hy2 : OccursOnce root2 y.val)
      (hpath_x : pathTo root x.val = pathTo root2 x.val)
      (hpath_y : pathTo root y.val = pathTo root2 y.val) :
      ∀ r1 r2 : Bool,
        is_cousins root x y = ok r1 → is_cousins root2 x y = ok r2 → r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root root2 : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hnode2_lo : 2 ≤ nodeCount root2) (hnode2_hi : nodeCount root2 ≤ 100)
        (hrange : ValuesInRange root) (hrange2 : ValuesInRange root2)
        (hdistinct : Distinct root) (hdistinct2 : Distinct root2)
        (hxy : x.val ≠ y.val)
        (hx : OccursOnce root x.val) (hy : OccursOnce root y.val)
        (hx2 : OccursOnce root2 x.val) (hy2 : OccursOnce root2 y.val)
        (hpath_x : pathTo root x.val = pathTo root2 x.val)
        (hpath_y : pathTo root y.val = pathTo root2 y.val), ∀ r1 r2 : Bool,
          is_cousins root x y = ok r1 → is_cousins root2 x y = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever is_cousins(root,x,y) returns true, there exist two distinct nodes p and q in root such that the node with value x is a child of p, the node with value y is a child of q, and depth(root,p) = depth(root,q). Here depth(root,v) is the number of edges from the root node (which has depth 0) to the unique node with value v.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_10 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∀ r : Bool, is_cousins root x y = ok r → r = true →
        ∃ px py : Int,
          HasValue root px ∧ HasValue root py ∧
            parentOf root x.val = some px ∧ parentOf root y.val = some py ∧
              px ≠ py ∧ depthOf root px = depthOf root py := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∀ r : Bool, is_cousins root x y = ok r → r = true →
          ∃ px py : Int,
            HasValue root px ∧ HasValue root py ∧
              parentOf root x.val = some px ∧ parentOf root y.val = some py ∧
                px ≠ py ∧ depthOf root px = depthOf root py) := by
    sorry

  /-- Whenever is_cousins(root,x,y) returns false and depth(root,x) = depth(root,y), the nodes with values x and y have the same parent in root. Here depth(root,v) is the number of edges from the root node (which has depth 0) to the unique node with value v.
    Preconditions: root is a Tree with between 2 and 100 Node constructors inclusive; every node value lies in the integer interval [1,100]; all node values in root are distinct; x and y are distinct values and each occurs exactly once in root. -/
  theorem spec_11 (root : Tree) (x y : Std.I64)
      (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
      (hrange : ValuesInRange root) (hdistinct : Distinct root)
      (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val) :
      ∀ r : Bool, is_cousins root x y = ok r → r = false →
        (∃ d : Nat, depthOf root x.val = some d ∧ depthOf root y.val = some d) →
          ∃ p : Int, parentOf root x.val = some p ∧ parentOf root y.val = some p := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (x y : Std.I64)
        (hnode_lo : 2 ≤ nodeCount root) (hnode_hi : nodeCount root ≤ 100)
        (hrange : ValuesInRange root) (hdistinct : Distinct root)
        (hxy : x.val ≠ y.val) (hx : OccursOnce root x.val) (hy : OccursOnce root y.val), ∀ r : Bool, is_cousins root x y = ok r → r = false →
          (∃ d : Nat, depthOf root x.val = some d ∧ depthOf root y.val = some d) →
            ∃ p : Int, parentOf root x.val = some p ∧ parentOf root y.val = some p) := by
    sorry

  end AegisSpec.IsCousins
