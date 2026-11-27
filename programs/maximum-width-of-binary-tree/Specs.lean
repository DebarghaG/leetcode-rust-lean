import Aegis.WidthOfBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.WidthOfBinaryTree.width_of_binary_tree`

LeetCode problem `maximum-width-of-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.WidthOfBinaryTree

  open Aegis.WidthOfBinaryTree (Tree width_of_binary_tree)
  open Aeneas.Std (I64)
  open Aeneas.Std.Result (ok)

  def nodeCount : Tree → Nat
    | .Null => 0
    | .Node _ l r => nodeCount l + nodeCount r + 1

  def payloads : Tree → List Int
    | .Null => []
    | .Node v l r => v.val :: (payloads l ++ payloads r)

  def payloadsInRange (t : Tree) : Prop :=
    ∀ x ∈ payloads t, -100 ≤ x ∧ x ≤ 100

  mutual

    def height : Tree → Nat
      | .Null => 0
      | .Node _ l r => max (childHeight l) (childHeight r)

    def childHeight : Tree → Nat
      | .Null => 0
      | .Node _ l r => max (childHeight l) (childHeight r) + 1
  end

  def levelPositions : Nat → Nat → Tree → List Nat
    | 0, _p, .Null => []
    | 0, p, .Node _ _ _ => [p]
    | _d + 1, _p, .Null => []
    | d + 1, p, .Node _ l r =>
        levelPositions d (2 * p) l ++ levelPositions d (2 * p + 1) r

  def levelWidth (d : Nat) (t : Tree) : Option Nat :=
    match levelPositions d 1 t with
    | [] => none
    | p :: ps => some (ps.foldr max p - ps.foldr min p + 1)

  def maxWidth (t : Tree) : Nat :=
    ((List.range (height t + 1)).filterMap (fun d => levelWidth d t)).foldr max 0

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def sameShape : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node _ l₁ r₁, .Node _ l₂ r₂ => sameShape l₁ l₂ ∧ sameShape r₁ r₂
    | _, _ => False

  def isPath : Tree → Prop
    | .Null => True
    | .Node _ l r => (l = .Null ∨ r = .Null) ∧ isPath l ∧ isPath r

  def perfect : Nat → Tree → Prop
    | 0, t => ∃ v : I64, t = .Node v .Null .Null
    | h + 1, t =>
        ∃ (v : I64) (l r : Tree), t = .Node v l r ∧ perfect h l ∧ perfect h r

  inductive Extends : Tree → Tree → Prop where
    | node (v : I64) (l₁ r₁ l₂ r₂ : Tree) :
        Extends l₁ l₂ → Extends r₁ r₂ →
        Extends (.Node v l₁ r₁) (.Node v l₂ r₂)
    | nullNull : Extends .Null .Null
    | nullFill (t : Tree) (h : t ≠ .Null) : Extends .Null t

  /-- Whenever width_of_binary_tree(root) returns a result r, r = W(root), where: the root has depth 0 and position 1; for a node at position p, its left child (if present) has position 2p and its right child (if present) has position 2p+1; for each depth d that contains at least one node, LevelWidth(d) = (maximum position among nodes at depth d) - (minimum position among nodes at depth d) + 1; and W(root) = the maximum of LevelWidth(d) over all depths d that contain at least one node.
    Preconditions: root is a non-null Tree (it contains at least one Node constructor); the number of Node constructors in root is between 1 and 3000 inclusive; every Node payload is in [-100,100]; the mathematical maximum width W(root) defined in the statement is at most 2^31 - 1. -/
  theorem spec_1 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root)
      (hwidth : maxWidth root ≤ 2 ^ 31 - 1) :
      ∀ r : I64, width_of_binary_tree root = ok r → r.val = (maxWidth root : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root)
        (hwidth : maxWidth root ≤ 2 ^ 31 - 1), ∀ r : I64, width_of_binary_tree root = ok r → r.val = (maxWidth root : Int)) := by
    sorry

  /-- For every such root, width_of_binary_tree(root) returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: root is a non-null Tree (it contains at least one Node constructor); the number of Node constructors in root is between 1 and 3000 inclusive; every Node payload is in [-100,100]; the mathematical maximum width W(root) defined in S1 is at most 2^31 - 1; and the height H of root (the largest depth of any node, with the root at depth 0) is at most 62, so every position defined by root position 1 and children at 2p and 2p+1 fits in a signed 64-bit integer. -/
  theorem spec_2 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root)
      (hwidth : maxWidth root ≤ 2 ^ 31 - 1)
      (hheight : height root ≤ 62) :
      ∃ r : I64, width_of_binary_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root)
        (hwidth : maxWidth root ≤ 2 ^ 31 - 1)
        (hheight : height root ≤ 62), ∃ r : I64, width_of_binary_tree root = ok r) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, there exists a depth d >= 0 such that root has at least one node at depth d and, using root position 1 and children of position p at positions 2p and 2p+1, r = (maximum position among nodes of root at depth d) - (minimum position among nodes of root at depth d) + 1.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]. -/
  theorem spec_3 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root) :
      ∀ r : I64, width_of_binary_tree root = ok r →
        ∃ (d : Nat) (w : Nat), levelWidth d root = some w ∧ r.val = (w : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root), ∀ r : I64, width_of_binary_tree root = ok r →
          ∃ (d : Nat) (w : Nat), levelWidth d root = some w ∧ r.val = (w : Int)) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, for every depth d >= 0 that contains at least one node of root, (maximum position among nodes of root at depth d) - (minimum position among nodes of root at depth d) + 1 <= r, using root position 1 and children of position p at positions 2p and 2p+1.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]. -/
  theorem spec_4 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root) :
      ∀ r : I64, width_of_binary_tree root = ok r →
        ∀ (d : Nat) (w : Nat), levelWidth d root = some w → (w : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root), ∀ r : I64, width_of_binary_tree root = ok r →
          ∀ (d : Nat) (w : Nat), levelWidth d root = some w → (w : Int) ≤ r.val) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, r >= 1.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]. -/
  theorem spec_5 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root) :
      ∀ r : I64, width_of_binary_tree root = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root), ∀ r : I64, width_of_binary_tree root = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, r <= 2^H.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]. Let H be the largest depth of any node in root, with the root at depth 0. -/
  theorem spec_6 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root) :
      ∀ r : I64, width_of_binary_tree root = ok r → r.val ≤ (2 : Int) ^ height root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root), ∀ r : I64, width_of_binary_tree root = ok r → r.val ≤ (2 : Int) ^ height root) := by
    sorry

  /-- width_of_binary_tree(root) returns a result r and r = 1.
    Preconditions: root = Node(v, Null, Null) for some i64 v with -100 <= v <= 100. -/
  theorem spec_7 (v : I64)
      (hv_lo : -100 ≤ v.val) (hv_hi : v.val ≤ 100) :
      ∃ r : I64, width_of_binary_tree (.Node v .Null .Null) = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (v : I64)
        (hv_lo : -100 ≤ v.val) (hv_hi : v.val ≤ 100), ∃ r : I64, width_of_binary_tree (.Node v .Null .Null) = ok r ∧ r.val = 1) := by
    sorry

  /-- width_of_binary_tree(root) returns a result r and r = 2.
    Preconditions: root = Node(v, Node(lv, Null, Null), Node(rv, Null, Null)) with v, lv, rv in [-100,100]. -/
  theorem spec_8 (v lv rv : I64)
      (hv_lo : -100 ≤ v.val) (hv_hi : v.val ≤ 100)
      (hlv_lo : -100 ≤ lv.val) (hlv_hi : lv.val ≤ 100)
      (hrv_lo : -100 ≤ rv.val) (hrv_hi : rv.val ≤ 100) :
      ∃ r : I64,
        width_of_binary_tree (.Node v (.Node lv .Null .Null) (.Node rv .Null .Null)) = ok r ∧
          r.val = 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v lv rv : I64)
        (hv_lo : -100 ≤ v.val) (hv_hi : v.val ≤ 100)
        (hlv_lo : -100 ≤ lv.val) (hlv_hi : lv.val ≤ 100)
        (hrv_lo : -100 ≤ rv.val) (hrv_hi : rv.val ≤ 100), ∃ r : I64,
          width_of_binary_tree (.Node v (.Node lv .Null .Null) (.Node rv .Null .Null)) = ok r ∧
            r.val = 2) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, r = 1.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]; and every Node in root has at most one non-null child (the tree is a single path). -/
  theorem spec_9 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root)
      (hpath : isPath root) :
      ∀ r : I64, width_of_binary_tree root = ok r → r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root)
        (hpath : isPath root), ∀ r : I64, width_of_binary_tree root = ok r → r.val = 1) := by
    sorry

  /-- width_of_binary_tree(root) returns a result r and r = 2^h.
    Preconditions: root is a perfect binary tree of height h >= 0, meaning all levels 0 through h are full; the number of nodes is 2^{h+1}-1 <= 3000; all node payloads are in [-100,100]. -/
  theorem spec_10 (h : Nat) (root : Tree)
      (hperfect : perfect h root)
      (hpayloads : payloadsInRange root)
      (hcount : 2 ^ (h + 1) - 1 ≤ 3000) :
      ∃ r : I64, width_of_binary_tree root = ok r ∧ r.val = (2 : Int) ^ h := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (h : Nat) (root : Tree)
        (hperfect : perfect h root)
        (hpayloads : payloadsInRange root)
        (hcount : 2 ^ (h + 1) - 1 ≤ 3000), ∃ r : I64, width_of_binary_tree root = ok r ∧ r.val = (2 : Int) ^ h) := by
    sorry

  /-- If width_of_binary_tree(root) returns r and width_of_binary_tree(mirror(root)) returns r', then r = r'.
    Preconditions: root is a non-null Tree with between 1 and 3000 Node constructors; every Node payload is in [-100,100]; mirror(root) is obtained by recursively swapping the left and right subtrees at every Node. -/
  theorem spec_11 (root : Tree)
      (hnonnull : root ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hpayloads : payloadsInRange root) :
      ∀ r r' : I64,
        width_of_binary_tree root = ok r →
        width_of_binary_tree (mirror root) = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hnonnull : root ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hpayloads : payloadsInRange root), ∀ r r' : I64,
          width_of_binary_tree root = ok r →
          width_of_binary_tree (mirror root) = ok r' →
          r.val = r'.val) := by
    sorry

  /-- If width_of_binary_tree(root) returns r and width_of_binary_tree(root') returns r', then r = r'.
    Preconditions: root and root' are non-null trees with the same shape (the same pattern of Null and Node constructors, so corresponding nodes have the same depths and positions) and with between 1 and 3000 Node constructors each; all node payloads in both trees are in [-100,100]. -/
  theorem spec_12 (root root' : Tree)
      (hnonnull : root ≠ .Null) (hnonnull' : root' ≠ .Null)
      (hshape : sameShape root root')
      (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
      (hcount_lo' : 1 ≤ nodeCount root') (hcount_hi' : nodeCount root' ≤ 3000)
      (hpayloads : payloadsInRange root) (hpayloads' : payloadsInRange root') :
      ∀ r r' : I64,
        width_of_binary_tree root = ok r →
        width_of_binary_tree root' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root' : Tree)
        (hnonnull : root ≠ .Null) (hnonnull' : root' ≠ .Null)
        (hshape : sameShape root root')
        (hcount_lo : 1 ≤ nodeCount root) (hcount_hi : nodeCount root ≤ 3000)
        (hcount_lo' : 1 ≤ nodeCount root') (hcount_hi' : nodeCount root' ≤ 3000)
        (hpayloads : payloadsInRange root) (hpayloads' : payloadsInRange root'), ∀ r r' : I64,
          width_of_binary_tree root = ok r →
          width_of_binary_tree root' = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever width_of_binary_tree(root) returns a result r, r >= 2.
    Preconditions: root = Node(v, L, R) with both L and R non-null; the tree has between 1 and 3000 Node constructors; all node payloads are in [-100,100]. -/
  theorem spec_13 (v : I64) (L R : Tree)
      (hL : L ≠ .Null) (hR : R ≠ .Null)
      (hcount_lo : 1 ≤ nodeCount (.Node v L R))
      (hcount_hi : nodeCount (.Node v L R) ≤ 3000)
      (hpayloads : payloadsInRange (.Node v L R)) :
      ∀ r : I64, width_of_binary_tree (.Node v L R) = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (v : I64) (L R : Tree)
        (hL : L ≠ .Null) (hR : R ≠ .Null)
        (hcount_lo : 1 ≤ nodeCount (.Node v L R))
        (hcount_hi : nodeCount (.Node v L R) ≤ 3000)
        (hpayloads : payloadsInRange (.Node v L R)), ∀ r : I64, width_of_binary_tree (.Node v L R) = ok r → 2 ≤ r.val) := by
    sorry

  /-- If width_of_binary_tree(root1) returns r1 and width_of_binary_tree(root2) returns r2, then r2 >= r1.
    Preconditions: root1 and root2 are non-null trees with between 1 and 3000 Node constructors each; all node payloads are in [-100,100]; root2 is obtained from root1 by replacing zero or more Null subtrees of root1 by arbitrary non-null trees, so every Node of root1 remains at the same depth and position in root2. -/
  theorem spec_14 (root₁ root₂ : Tree)
      (hnonnull₁ : root₁ ≠ .Null) (hnonnull₂ : root₂ ≠ .Null)
      (hext : Extends root₁ root₂)
      (hcount_lo₁ : 1 ≤ nodeCount root₁) (hcount_hi₁ : nodeCount root₁ ≤ 3000)
      (hcount_lo₂ : 1 ≤ nodeCount root₂) (hcount_hi₂ : nodeCount root₂ ≤ 3000)
      (hpayloads₁ : payloadsInRange root₁) (hpayloads₂ : payloadsInRange root₂) :
      ∀ r₁ r₂ : I64,
        width_of_binary_tree root₁ = ok r₁ →
        width_of_binary_tree root₂ = ok r₂ →
        r₁.val ≤ r₂.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root₁ root₂ : Tree)
        (hnonnull₁ : root₁ ≠ .Null) (hnonnull₂ : root₂ ≠ .Null)
        (hext : Extends root₁ root₂)
        (hcount_lo₁ : 1 ≤ nodeCount root₁) (hcount_hi₁ : nodeCount root₁ ≤ 3000)
        (hcount_lo₂ : 1 ≤ nodeCount root₂) (hcount_hi₂ : nodeCount root₂ ≤ 3000)
        (hpayloads₁ : payloadsInRange root₁) (hpayloads₂ : payloadsInRange root₂), ∀ r₁ r₂ : I64,
          width_of_binary_tree root₁ = ok r₁ →
          width_of_binary_tree root₂ = ok r₂ →
          r₁.val ≤ r₂.val) := by
    sorry

  end AegisSpec.WidthOfBinaryTree
