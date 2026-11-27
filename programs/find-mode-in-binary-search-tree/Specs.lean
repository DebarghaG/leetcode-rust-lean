import Aegis.FindMode.Code.Funs

/-!
# Specifications of `Aegis.FindMode.find_mode`

LeetCode problem `find-mode-in-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMode

  open Aegis.FindMode

  def keys : Tree → List ℤ
    | .Null => []
    | .Node k l r => keys l ++ [k.val] ++ keys r

  def size : Tree → ℕ
    | .Null => 0
    | .Node _ l r => size l + 1 + size r

  def count (t : Tree) (v : ℤ) : ℕ := (keys t).countP (fun x => decide (x = v))

  def occurs (t : Tree) (v : ℤ) : Prop := v ∈ keys t

  def BST : Tree → Prop
    | .Null => True
    | .Node k l r => BST l ∧ BST r ∧ (∀ x ∈ keys l, x ≤ k.val) ∧ (∀ x ∈ keys r, k.val ≤ x)

  def keyBounds (lo hi : ℤ) (t : Tree) : Prop := ∀ x ∈ keys t, lo ≤ x ∧ x ≤ hi

  def maxCount (t : Tree) : ℕ := (keys t).foldr (fun v m => max (count t v) m) 0

  def modesSet (t : Tree) : Finset ℤ := (keys t).toFinset.filter (fun v => count t v = maxCount t)

  def minKey? : Tree → Option ℤ
    | .Null => none
    | .Node k l r => some (min k.val (min ((minKey? l).getD k.val) ((minKey? r).getD k.val)))

  def maxKey? : Tree → Option ℤ
    | .Null => none
    | .Node k l r => some (max k.val (max ((maxKey? l).getD k.val) ((maxKey? r).getD k.val)))

  def minKey (t : Tree) : ℤ := (minKey? t).getD 0

  def maxKey (t : Tree) : ℤ := (maxKey? t).getD 0

  /-- Whenever find_mode(root) returns a result r, let M = max { count(root, v) | v occurs as a key in root }, where count(root, v) is the number of nodes of root whose key equals v. Then r contains exactly the distinct modes of root, in some order: (1) for every i with 0 <= i < len(r), r[i] occurs as a key in root and count(root, r[i]) = M; (2) for every value v that occurs as a key in root, if count(root, v) = M then there is exactly one index i with 0 <= i < len(r) such that r[i] = v; (3) for every i, j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_1 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      (∀ i : Fin r.val.length,
          occurs root (r.val.get i).val ∧ count root (r.val.get i).val = maxCount root) ∧
      (∀ v : ℤ, occurs root v → count root v = maxCount root →
          ∃! i : Fin r.val.length, (r.val.get i).val = v) ∧
      (∀ i j : Fin r.val.length, i < j → (r.val.get i).val ≠ (r.val.get j).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), (∀ i : Fin r.val.length,
            occurs root (r.val.get i).val ∧ count root (r.val.get i).val = maxCount root) ∧
        (∀ v : ℤ, occurs root v → count root v = maxCount root →
            ∃! i : Fin r.val.length, (r.val.get i).val = v) ∧
        (∀ i j : Fin r.val.length, i < j → (r.val.get i).val ≠ (r.val.get j).val)) := by
    sorry

  /-- For every such root, find_mode(root) returns a result r; it does not fail.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_2 (root : Tree)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root) :
      ∃ r : alloc.vec.Vec I64, find_mode root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root), ∃ r : alloc.vec.Vec I64, find_mode root = ok r) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, for every i with 0 <= i < len(r), the value r[i] occurs as a key of some node of root.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_3 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      ∀ i : Fin r.val.length, occurs root (r.val.get i).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), ∀ i : Fin r.val.length, occurs root (r.val.get i).val) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, let M = max { count(root, v) | v occurs as a key in root }, where count(root, v) is the number of nodes of root whose key equals v. For every i with 0 <= i < len(r), count(root, r[i]) = M.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_4 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      ∀ i : Fin r.val.length, count root (r.val.get i).val = maxCount root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), ∀ i : Fin r.val.length, count root (r.val.get i).val = maxCount root) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, let M = max { count(root, v) | v occurs as a key in root }, where count(root, v) is the number of nodes of root whose key equals v. For every value v that occurs as a key in root, if count(root, v) = M then there exists an index i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_5 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      ∀ v : ℤ, occurs root v → count root v = maxCount root →
        ∃ i : Fin r.val.length, (r.val.get i).val = v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), ∀ v : ℤ, occurs root v → count root v = maxCount root →
          ∃ i : Fin r.val.length, (r.val.get i).val = v) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, for every i, j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_6 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      ∀ i j : Fin r.val.length, i < j → (r.val.get i).val ≠ (r.val.get j).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), ∀ i j : Fin r.val.length, i < j → (r.val.get i).val ≠ (r.val.get j).val) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, let M = max { count(root, v) | v occurs as a key in root }, where count(root, v) is the number of nodes of root whose key equals v. Then len(r) equals the number of distinct values v such that v occurs as a key in root and count(root, v) = M.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_7 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      r.val.length = (modesSet root).card := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), r.val.length = (modesSet root).card) := by
    sorry

  /-- Whenever find_mode(root) returns a result r, for every i with 0 <= i < len(r), min_key(root) <= r[i] <= max_key(root), where min_key(root) is the minimum key among all nodes of root and max_key(root) is the maximum key among all nodes of root.
    Preconditions: root is a nonempty binary search tree with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. The number of nodes in root is between 1 and 10^4 inclusive, and every node key lies in [-10^5, 10^5]. -/
  theorem spec_8 (root : Tree) (r : alloc.vec.Vec I64)
      (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
      (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
      (hres : find_mode root = ok r) :
      ∀ i : Fin r.val.length, minKey root ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ maxKey root := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (r : alloc.vec.Vec I64)
        (hbst : BST root) (hne : 1 ≤ size root) (hbound : size root ≤ 10 ^ 4)
        (hkeys : keyBounds (-(10 ^ 5)) (10 ^ 5) root)
        (hres : find_mode root = ok r), ∀ i : Fin r.val.length, minKey root ≤ (r.val.get i).val ∧ (r.val.get i).val ≤ maxKey root) := by
    sorry

  /-- Whenever find_mode(root1) returns a result r1 and find_mode(root2) returns a result r2, the set of values occurring in r1 equals the set of values occurring in r2; that is, { r1[i] | 0 <= i < len(r1) } = { r2[j] | 0 <= j < len(r2) }.
    Preconditions: root1 and root2 are each nonempty binary search trees with duplicates as defined in the problem: for every node with key k, all keys in its left subtree are <= k and all keys in its right subtree are >= k, and both subtrees are binary search trees. Each has between 1 and 10^4 nodes inclusive, every node key lies in [-10^5, 10^5], and root1 and root2 have the same multiset of node keys. -/
  theorem spec_9 (root1 root2 : Tree) (r1 r2 : alloc.vec.Vec I64)
      (hbst1 : BST root1) (hne1 : 1 ≤ size root1) (hbound1 : size root1 ≤ 10 ^ 4)
      (hkeys1 : keyBounds (-(10 ^ 5)) (10 ^ 5) root1)
      (hbst2 : BST root2) (hne2 : 1 ≤ size root2) (hbound2 : size root2 ≤ 10 ^ 4)
      (hkeys2 : keyBounds (-(10 ^ 5)) (10 ^ 5) root2)
      (hmult : (keys root1).Perm (keys root2))
      (hres1 : find_mode root1 = ok r1) (hres2 : find_mode root2 = ok r2) :
      (r1.val.map (fun x => x.val)).toFinset = (r2.val.map (fun x => x.val)).toFinset := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root1 root2 : Tree) (r1 r2 : alloc.vec.Vec I64)
        (hbst1 : BST root1) (hne1 : 1 ≤ size root1) (hbound1 : size root1 ≤ 10 ^ 4)
        (hkeys1 : keyBounds (-(10 ^ 5)) (10 ^ 5) root1)
        (hbst2 : BST root2) (hne2 : 1 ≤ size root2) (hbound2 : size root2 ≤ 10 ^ 4)
        (hkeys2 : keyBounds (-(10 ^ 5)) (10 ^ 5) root2)
        (hmult : (keys root1).Perm (keys root2))
        (hres1 : find_mode root1 = ok r1) (hres2 : find_mode root2 = ok r2), (r1.val.map (fun x => x.val)).toFinset = (r2.val.map (fun x => x.val)).toFinset) := by
    sorry

  end AegisSpec.FindMode
