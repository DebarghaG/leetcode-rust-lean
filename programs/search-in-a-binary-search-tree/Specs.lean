import Aegis.SearchBst.Code.Funs

/-!
# Specifications of `Aegis.SearchBst.search_bst`

LeetCode problem `search-in-a-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SearchBst

  namespace AegisSpec.SearchBst

  inductive Subtree : Tree → Tree → Prop where
    | refl (t : Tree) : Subtree t t
    | left {p : Tree} {v : Std.I64} {l r : Tree} : Subtree p l → Subtree p (Tree.Node v l r)
    | right {p : Tree} {v : Std.I64} {l r : Tree} : Subtree p r → Subtree p (Tree.Node v l r)

  def nodeValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

  def numNodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + numNodes l + numNodes r

  def IsStrictBst (t : Tree) : Prop :=
    ∀ p, Subtree p t → ∀ v l r, p = Tree.Node v l r →
      (∀ x ∈ nodeValues l, x < v.val) ∧ (∀ x ∈ nodeValues r, v.val < x)

  def HasVal (t : Tree) (x : Std.I64) : Prop :=
    ∃ v l r, Subtree (Tree.Node v l r) t ∧ v.val = x.val

  /-- The function returns a result r and: if root contains a node p with p.value equal to val, then r is exactly the subtree of root rooted at p (same node structure, same child positions, and same values); if root contains no node with value equal to val, then r = Null.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_1 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∃ r, search_bst root val = ok r ∧
        (HasVal root val →
          ∃ v l r', Subtree (Tree.Node v l r') root ∧ v.val = val.val ∧
            r = Tree.Node v l r') ∧
        (¬ HasVal root val → r = Tree.Null) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∃ r, search_bst root val = ok r ∧
          (HasVal root val →
            ∃ v l r', Subtree (Tree.Node v l r') root ∧ v.val = val.val ∧
              r = Tree.Node v l r') ∧
          (¬ HasVal root val → r = Tree.Null)) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, perform an out-of-bounds access, or overflow.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_2 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∃ r, search_bst root val = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∃ r, search_bst root val = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = Null if and only if no node occurring in root has value equal to val.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_3 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → (r = Tree.Null ↔ ¬ HasVal root val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → (r = Tree.Null ↔ ¬ HasVal root val)) := by
    sorry

  /-- Whenever the function returns a result r of the form Node(v, l, rr), the integer v is equal to the integer value of val.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_4 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → ∀ (v : Std.I64) (l rr : Tree),
        r = Tree.Node v l rr → v.val = val.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → ∀ (v : Std.I64) (l rr : Tree),
          r = Tree.Node v l rr → v.val = val.val) := by
    sorry

  /-- For every input satisfying the preconditions in which some node occurring in root has value equal to val, the function returns a result r with r != Null.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_5 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7)
      (hex : HasVal root val) :
      ∃ r, search_bst root val = ok r ∧ r ≠ Tree.Null := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7)
        (hex : HasVal root val), ∃ r, search_bst root val = ok r ∧ r ≠ Tree.Null) := by
    sorry

  /-- Whenever the function returns a result r with r != Null, there exists a node p occurring in root such that r is exactly the subtree rooted at p.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_6 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r root) := by
    sorry

  /-- Whenever the function returns a result r with r != Null, r is a strict binary search tree: for every node q occurring in r, every value in the left subtree of q is less than q.value and every value in the right subtree of q is greater than q.value.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_7 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → r ≠ Tree.Null → IsStrictBst r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → r ≠ Tree.Null → IsStrictBst r) := by
    sorry

  /-- Whenever the function returns a result r, the number of Node constructors in r is at most the number of Node constructors in root.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_8 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → numNodes r ≤ numNodes root := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → numNodes r ≤ numNodes root) := by
    sorry

  /-- Whenever the function returns a result r with r != Null, r is a subtree of l: there exists a node p occurring in l such that r is exactly the subtree rooted at p.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; the integer value of val is in [1, 10^7]; and root = Node(x, l, rr) for some integer x and trees l and rr, with the integer value of val less than x. -/
  theorem spec_9 (root l rr : Tree) (x val : Std.I64)
      (hroot : root = Tree.Node x l rr)
      (hlt : val.val < x.val)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ y ∈ nodeValues root, 1 ≤ y ∧ y ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r l := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root l rr : Tree) (x val : Std.I64)
        (hroot : root = Tree.Node x l rr)
        (hlt : val.val < x.val)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ y ∈ nodeValues root, 1 ≤ y ∧ y ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r l) := by
    sorry

  /-- Whenever the function returns a result r with r != Null, r is a subtree of rr: there exists a node p occurring in rr such that r is exactly the subtree rooted at p.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; the integer value of val is in [1, 10^7]; and root = Node(x, l, rr) for some integer x and trees l and rr, with the integer value of val greater than x. -/
  theorem spec_10 (root l rr : Tree) (x val : Std.I64)
      (hroot : root = Tree.Node x l rr)
      (hlt : x.val < val.val)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ y ∈ nodeValues root, 1 ≤ y ∧ y ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r rr := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root l rr : Tree) (x val : Std.I64)
        (hroot : root = Tree.Node x l rr)
        (hlt : x.val < val.val)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ y ∈ nodeValues root, 1 ≤ y ∧ y ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → r ≠ Tree.Null → Subtree r rr) := by
    sorry

  /-- Whenever the function returns a result r, r is exactly equal to the input tree root if and only if root = Node(val, l, rr) for some trees l and rr.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_11 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r →
        (r = root ↔ ∃ (l rr : Tree), root = Tree.Node val l rr) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r →
          (r = root ↔ ∃ (l rr : Tree), root = Tree.Node val l rr)) := by
    sorry

  /-- Whenever the function returns a result r with r != Null, there exists a node p occurring in root such that p.value equals val and r is exactly the subtree rooted at p.
    Preconditions: root is a strict binary search tree: for every node p occurring in root, every value in the left subtree of p is less than p.value and every value in the right subtree of p is greater than p.value. The tree has between 1 and 5000 nodes; every node value is in [1, 10^7]; and the integer value of val is in [1, 10^7]. -/
  theorem spec_12 (root : Tree) (val : Std.I64)
      (hbst : IsStrictBst root)
      (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
      (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
      (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7) :
      ∀ r, search_bst root val = ok r → r ≠ Tree.Null →
        ∃ v l rr, Subtree (Tree.Node v l rr) root ∧ v.val = val.val ∧
          r = Tree.Node v l rr := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (val : Std.I64)
        (hbst : IsStrictBst root)
        (hsize_lo : 1 ≤ numNodes root) (hsize_hi : numNodes root ≤ 5000)
        (hvals : ∀ x ∈ nodeValues root, 1 ≤ x ∧ x ≤ 10 ^ 7)
        (hval : 1 ≤ val.val ∧ val.val ≤ 10 ^ 7), ∀ r, search_bst root val = ok r → r ≠ Tree.Null →
          ∃ v l rr, Subtree (Tree.Node v l rr) root ∧ v.val = val.val ∧
            r = Tree.Node v l rr) := by
    sorry

  end AegisSpec.SearchBst
