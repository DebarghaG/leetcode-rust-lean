import Aegis.InsertIntoMaxTree.Code.Funs

/-!
# Specifications of `Aegis.InsertIntoMaxTree.insert_into_max_tree`

LeetCode problem `maximum-binary-tree-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.InsertIntoMaxTree

  open Aegis.InsertIntoMaxTree

  def toI64 (x : Int) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

  def inorder : Tree → List Int
    | .Null => []
    | .Node v l r => inorder l ++ [v.val] ++ inorder r

  def numNodes : Tree → Nat
    | .Null => 0
    | .Node _ l r => numNodes l + 1 + numNodes r

  def rootVal? : Tree → Option Int
    | .Null => none
    | .Node v _ _ => some v.val

  def IsMaxTree : Tree → Prop
    | .Null => True
    | .Node v l r =>
        IsMaxTree l ∧ IsMaxTree r ∧
        (∀ x ∈ inorder l, x < v.val) ∧ (∀ x ∈ inorder r, x < v.val)

  def rightSpine : Tree → List Int
    | .Null => []
    | .Node v _ r => v.val :: rightSpine r

  def spineNode? : Tree → Int → Option Tree
    | .Null, _ => none
    | .Node v l r, x => if v.val = x then some (.Node v l r) else spineNode? r x

  def findNode? : Tree → Int → Option Tree
    | .Null, _ => none
    | .Node v l r, x =>
        if v.val = x then some (.Node v l r)
        else match findNode? l x with
             | some u => some u
             | none => findNode? r x

  def parentOf? : Tree → Int → Option Tree
    | .Null, _ => none
    | .Node v l r, x =>
        if rootVal? l = some x ∨ rootVal? r = some x then some (.Node v l r)
        else match parentOf? l x with
             | some p => some p
             | none => parentOf? r x

  def HasNullRightChild : Tree → Prop
    | .Null => True
    | .Node _ _ r => r = .Null

  def removeVal : Tree → Int → Tree
    | .Null, _ => .Null
    | .Node v l r, x =>
        if v.val = x then l
        else if x ∈ inorder l then .Node v (removeVal l x) r
        else .Node v l (removeVal r x)

  def splitMax : List Int → Option (List Int × Int × List Int)
    | [] => none
    | x :: xs =>
        match splitMax xs with
        | none => some ([], x, [])
        | some (l, m, r) => if x < m then some (x :: l, m, r) else some ([], x, xs)

  def ConstructAux : Nat → List Int → Tree
    | 0, _ => .Null
    | n + 1, s =>
        match splitMax s with
        | none => .Null
        | some (l, m, r) => .Node (toI64 m) (ConstructAux n l) (ConstructAux n r)

  def Construct (s : List Int) : Tree := ConstructAux s.length s

  /-- Let a = inorder(root), the list of node values obtained by traversing root in inorder (left subtree, then node, then right subtree). Let b = a with val appended as a new final element. Let Construct be the recursive constructor from the problem statement: Construct(empty) = Null, and for a nonempty sequence with unique values, Construct(s) has as its root the unique maximum element of s, its left child is Construct(elements of s before that maximum), and its right child is Construct(elements of s after that maximum). The function returns a result t (it does not fail) such that t = Construct(b).
    Preconditions: root is a non-null maximum binary tree: every node's value is strictly greater than every value in its proper left and right subtrees; its node values are pairwise distinct and lie in [1,100]; root has between 1 and 100 nodes. val is in [1,100] and does not occur as a node value of root, so the values of root together with val are distinct. -/
  theorem spec_1 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∃ t : Tree,
        insert_into_max_tree root val = Result.ok t ∧
          t = Construct (inorder root ++ [val.val]) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∃ t : Tree,
          insert_into_max_tree root val = Result.ok t ∧
            t = Construct (inorder root ++ [val.val])) := by
    sorry

  /-- Whenever the function returns a result t, the inorder traversal of t is inorder(root) with val appended as the last element: inorder(t) = inorder(root) ++ [val].
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_2 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          inorder t = inorder root ++ [val.val] := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            inorder t = inorder root ++ [val.val]) := by
    sorry

  /-- Whenever the function returns a result t, t is a maximum binary tree: for every node x of t, the value stored at x is strictly greater than the value of every node in the proper left subtree of x and strictly greater than the value of every node in the proper right subtree of x.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_3 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree, insert_into_max_tree root val = Result.ok t → IsMaxTree t := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree, insert_into_max_tree root val = Result.ok t → IsMaxTree t) := by
    sorry

  /-- Whenever the function returns a result t, for every integer x, x occurs as a node value in t if and only if either x occurs as a node value in root or x = val; moreover, every such value occurs exactly once in t.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_4 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          (∀ x : Int, x ∈ inorder t ↔ x ∈ inorder root ∨ x = val.val) ∧
            (inorder t).Nodup := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            (∀ x : Int, x ∈ inorder t ↔ x ∈ inorder root ∨ x = val.val) ∧
              (inorder t).Nodup) := by
    sorry

  /-- Whenever the function returns a result t, the value at the root of t is max(value(root), val), the larger of the original root value and val.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_5 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          ∀ x : Int, rootVal? root = some x → rootVal? t = some (max x val.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            ∀ x : Int, rootVal? root = some x → rootVal? t = some (max x val.val)) := by
    sorry

  /-- Whenever these additional conditions hold and the function returns a result t, let L and R be the left and right children of root, where inorder(Null) = [] for the empty tree, and let r' = Construct(inorder(R) ++ [val]), where Construct is the recursive maximum-tree constructor defined in spec_1. Then t = Node(value(root), L, r'). In particular, the root value of t equals the root value of root, and the left subtree of t is exactly L.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root; additionally, val < value(root). -/
  theorem spec_6 {root : Tree} {val : Std.I64} {v0 : Std.I64} {L0 R0 : Tree}
      (hroot : root = Tree.Node v0 L0 R0)
      (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root)
      (hlt : val.val < v0.val) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          t = Tree.Node v0 L0 (Construct (inorder R0 ++ [val.val])) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ {root : Tree} {val : Std.I64} {v0 : Std.I64} {L0 R0 : Tree}
        (hroot : root = Tree.Node v0 L0 R0)
        (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root)
        (hlt : val.val < v0.val), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            t = Tree.Node v0 L0 (Construct (inorder R0 ++ [val.val]))) := by
    sorry

  /-- Whenever the function returns a result t, let u be the unique node of t whose value is val. Removing u by splicing its left child into its parent's position (or taking its left child as the whole tree if u is the root) yields exactly the original tree root.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_7 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t → removeVal t val.val = root := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t → removeVal t val.val = root) := by
    sorry

  /-- Whenever the function returns a result t, there exists exactly one node u in t whose stored value is val.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_8 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t → (inorder t).count val.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t → (inorder t).count val.val = 1) := by
    sorry

  /-- Whenever the function returns a result t, let u be the unique node of t whose value is val. The right child of u is Null.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_9 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          ∀ u : Tree, findNode? t val.val = some u → HasNullRightChild u := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            ∀ u : Tree, findNode? t val.val = some u → HasNullRightChild u) := by
    sorry

  /-- For every root and val satisfying the preconditions, the function returns a result t; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_10 {root : Tree} {val : Std.I64}
      (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∃ t : Tree, insert_into_max_tree root val = Result.ok t := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ {root : Tree} {val : Std.I64}
        (hne : root ≠ Tree.Null) (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∃ t : Tree, insert_into_max_tree root val = Result.ok t) := by
    sorry

  /-- Whenever the function returns a result t, let u be the unique node of t whose value is val. If val > value(root), then u is the root of t, its left child is root, and its right child is Null. If val < value(root), then u lies on the right spine of t, its right child is Null, and if p is the parent of u, then p is the deepest node on the right spine of root whose value is greater than val, and the left child of u is the right child that p has in root (which may be Null).
    Preconditions: root is a non-null maximum binary tree with distinct node values in [1,100] and between 1 and 100 nodes; val is in [1,100] and does not occur as a node value of root. -/
  theorem spec_11 {root : Tree} {val : Std.I64} {v0 : Std.I64} {L0 R0 : Tree}
      (hroot : root = Tree.Node v0 L0 R0)
      (hmax : IsMaxTree root)
      (hnd : (inorder root).Nodup)
      (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
      (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
      (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
      (hnoval : val.val ∉ inorder root) :
      ∀ t : Tree,
        insert_into_max_tree root val = Result.ok t →
          (v0.val < val.val → t = Tree.Node val root Tree.Null) ∧
            (val.val < v0.val →
              val.val ∈ rightSpine t ∧
                ∃ (p u : Tree) (vp : Std.I64) (Lp Rp : Tree),
                  parentOf? t val.val = some p ∧
                    findNode? t val.val = some u ∧
                    p = Tree.Node vp Lp u ∧
                    u = Tree.Node val Rp Tree.Null ∧
                    vp.val ∈ rightSpine root ∧
                    spineNode? root vp.val = some (Tree.Node vp Lp Rp) ∧
                    val.val < vp.val ∧
                    (∀ y ∈ rightSpine root, val.val < y → vp.val ≤ y)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ {root : Tree} {val : Std.I64} {v0 : Std.I64} {L0 R0 : Tree}
        (hroot : root = Tree.Node v0 L0 R0)
        (hmax : IsMaxTree root)
        (hnd : (inorder root).Nodup)
        (hrange : ∀ x ∈ inorder root, 1 ≤ x ∧ x ≤ 100)
        (hsize1 : 1 ≤ numNodes root) (hsize2 : numNodes root ≤ 100)
        (hval1 : 1 ≤ val.val) (hval2 : val.val ≤ 100)
        (hnoval : val.val ∉ inorder root), ∀ t : Tree,
          insert_into_max_tree root val = Result.ok t →
            (v0.val < val.val → t = Tree.Node val root Tree.Null) ∧
              (val.val < v0.val →
                val.val ∈ rightSpine t ∧
                  ∃ (p u : Tree) (vp : Std.I64) (Lp Rp : Tree),
                    parentOf? t val.val = some p ∧
                      findNode? t val.val = some u ∧
                      p = Tree.Node vp Lp u ∧
                      u = Tree.Node val Rp Tree.Null ∧
                      vp.val ∈ rightSpine root ∧
                      spineNode? root vp.val = some (Tree.Node vp Lp Rp) ∧
                      val.val < vp.val ∧
                      (∀ y ∈ rightSpine root, val.val < y → vp.val ≤ y))) := by
    sorry

  end AegisSpec.InsertIntoMaxTree
