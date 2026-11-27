import Aegis.MaxProduct.Code.Funs

/-!
# Specifications of `Aegis.MaxProduct.max_product`

LeetCode problem `maximum-product-of-splitted-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxProduct

  open Aegis.MaxProduct (Tree)

  def MOD : Int := 1000000007

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + size l + size r

  def totalSum : Tree → Int
    | Tree.Null => 0
    | Tree.Node v l r => v.val + totalSum l + totalSum r

  def nodeSums : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => (v.val + totalSum l + totalSum r) :: (nodeSums l ++ nodeSums r)

  def nonrootSums : Tree → List Int
    | Tree.Null => []
    | Tree.Node _ l r => nodeSums l ++ nodeSums r

  def maxProd (t : Tree) : Int :=
    ((nonrootSums t).map (fun s => s * (totalSum t - s))).foldr max 0

  def inRange (lo hi : Int) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => lo ≤ v.val ∧ v.val ≤ hi ∧ inRange lo hi l ∧ inRange lo hi r

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  /-- Let MOD = 1000000007. Let T be the sum of all node values in root. For each node v of root other than the root node, let s(v) be the sum of values in the subtree rooted at v (v together with all its descendants). Let M = max { s(v) * (T - s(v)) : v is a non-root node of root }. The function returns a result r and r = M mod MOD, where M mod MOD is the unique integer in [0, MOD-1] congruent to M modulo MOD. In particular, M is maximized before taking the remainder.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_1 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∃ r : Std.I64, Aegis.MaxProduct.max_product root = ok r ∧ r.val = maxProd root % MOD := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∃ r : Std.I64, Aegis.MaxProduct.max_product root = ok r ∧ r.val = maxProd root % MOD) := by
    sorry

  /-- On every input satisfying the preconditions, the function does not fail; it returns a Std.I64 result r, with no panic, out-of-bounds access, or arithmetic overflow.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_2 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∃ r : Std.I64, Aegis.MaxProduct.max_product root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∃ r : Std.I64, Aegis.MaxProduct.max_product root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r satisfies 0 <= r <= 1000000006, equivalently 0 <= r < MOD with MOD = 1000000007.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_3 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r → 0 ≤ r.val ∧ r.val < MOD := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r → 0 ≤ r.val ∧ r.val < MOD) := by
    sorry

  /-- Let MOD = 1000000007. Let T be the total sum of node values, and for each non-root node v let s(v) be the sum of the subtree rooted at v. Whenever the function returns r, there exists a non-root node v* such that: (i) for every non-root node v, s(v) * (T - s(v)) <= s(v*) * (T - s(v*)); and (ii) r = (s(v*) * (T - s(v*))) mod MOD.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_4 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        ∃ v : Int, v ∈ nonrootSums root ∧
          (∀ w : Int, w ∈ nonrootSums root →
            w * (totalSum root - w) ≤ v * (totalSum root - v)) ∧
          r.val = (v * (totalSum root - v)) % MOD := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          ∃ v : Int, v ∈ nonrootSums root ∧
            (∀ w : Int, w ∈ nonrootSums root →
              w * (totalSum root - w) ≤ v * (totalSum root - v)) ∧
            r.val = (v * (totalSum root - v)) % MOD) := by
    sorry

  /-- Suppose root is Node(a, Node(b, Null, Null), Null) or Node(a, Null, Node(b, Null, Null)), so a is the root value and b is the only other node value. Whenever the function returns r, r = (a * b) mod MOD, where MOD = 1000000007.
    Preconditions: root is a finite binary tree with exactly 2 nodes, and every node value is in [1, 10000]. -/
  theorem spec_5 (root : Tree) (a b : Std.I64) (hsize : size root = 2)
      (hval : inRange 1 10000 root) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
      (hb : 1 ≤ b.val ∧ b.val ≤ 10000)
      (hshape : root = Tree.Node a (Tree.Node b Tree.Null Tree.Null) Tree.Null ∨
        root = Tree.Node a Tree.Null (Tree.Node b Tree.Null Tree.Null)) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        r.val = (a.val * b.val) % MOD := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (a b : Std.I64) (hsize : size root = 2)
        (hval : inRange 1 10000 root) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
        (hb : 1 ≤ b.val ∧ b.val ≤ 10000)
        (hshape : root = Tree.Node a (Tree.Node b Tree.Null Tree.Null) Tree.Null ∨
          root = Tree.Node a Tree.Null (Tree.Node b Tree.Null Tree.Null)), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          r.val = (a.val * b.val) % MOD) := by
    sorry

  /-- For this three-node tree with root value a and two leaf children with values b and c, the two possible edge removals yield products b * (a + c) and c * (a + b). Whenever the function returns r, r = (max(b * (a + c), c * (a + b))) mod MOD, where MOD = 1000000007.
    Preconditions: root = Node(a, Node(b, Null, Null), Node(c, Null, Null)), and a, b, c are integers in [1, 10000]. -/
  theorem spec_6 (a b c : Std.I64) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
      (hb : 1 ≤ b.val ∧ b.val ≤ 10000) (hc : 1 ≤ c.val ∧ c.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.MaxProduct.max_product
            (Tree.Node a (Tree.Node b Tree.Null Tree.Null) (Tree.Node c Tree.Null Tree.Null)) = ok r →
        r.val = (max (b.val * (a.val + c.val)) (c.val * (a.val + b.val))) % MOD := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Std.I64) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
        (hb : 1 ≤ b.val ∧ b.val ≤ 10000) (hc : 1 ≤ c.val ∧ c.val ≤ 10000), ∀ r : Std.I64,
          Aegis.MaxProduct.max_product
              (Tree.Node a (Tree.Node b Tree.Null Tree.Null) (Tree.Node c Tree.Null Tree.Null)) = ok r →
          r.val = (max (b.val * (a.val + c.val)) (c.val * (a.val + b.val))) % MOD) := by
    sorry

  /-- Let mirror(root) be the tree obtained from root by recursively swapping the left and right children of every node. If the function returns r on root and returns r' on mirror(root), then r = r'.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_7 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∀ r r' : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        Aegis.MaxProduct.max_product (mirror root) = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∀ r r' : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          Aegis.MaxProduct.max_product (mirror root) = ok r' → r = r') := by
    sorry

  /-- Let T be the total sum of node values, and for each non-root node v let s(v) be the sum of the subtree rooted at v. If T is even and there exists a non-root node v with s(v) = T/2, then whenever the function returns r, r = ((T/2) * (T/2)) mod MOD, where MOD = 1000000007.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_8 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) (heven : totalSum root % 2 = 0)
      (hex : ∃ v : Int, v ∈ nonrootSums root ∧ v = totalSum root / 2) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        r.val = ((totalSum root / 2) * (totalSum root / 2)) % MOD := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root) (heven : totalSum root % 2 = 0)
        (hex : ∃ v : Int, v ∈ nonrootSums root ∧ v = totalSum root / 2), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          r.val = ((totalSum root / 2) * (totalSum root / 2)) % MOD) := by
    sorry

  /-- Let MOD = 1000000007. Let T be the total sum of node values, and let M be the maximum of s(v) * (T - s(v)) over all non-root nodes v, where s(v) is the subtree sum at v. If the function returns r, then there exists an integer k >= 0 such that M = r + k * MOD, and 4 * M <= T * T.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_9 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        ∃ k : Int, 0 ≤ k ∧ maxProd root = r.val + k * MOD ∧
          4 * maxProd root ≤ totalSum root * totalSum root := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          ∃ k : Int, 0 ≤ k ∧ maxProd root = r.val + k * MOD ∧
            4 * maxProd root ≤ totalSum root * totalSum root) := by
    sorry

  /-- Let MOD = 1000000007. Let T and s(v) be as above, and let M be the maximum of s(v) * (T - s(v)) over all non-root nodes v. If M < MOD, then whenever the function returns r, r = M.
    Preconditions: root is a finite binary tree with at least 2 and at most 50000 nodes, and every node value is an integer in [1, 10000]. -/
  theorem spec_10 (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
      (hval : inRange 1 10000 root) (hsmall : maxProd root < MOD) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r → r.val = maxProd root := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hsize : 2 ≤ size root ∧ size root ≤ 50000)
        (hval : inRange 1 10000 root) (hsmall : maxProd root < MOD), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r → r.val = maxProd root) := by
    sorry

  /-- Let a be the root value, b the unique child value, and c the only grandchild value. The two possible edge removals yield products a * (b + c) and c * (a + b). Whenever the function returns r, r = (max(a * (b + c), c * (a + b))) mod MOD, where MOD = 1000000007.
    Preconditions: root is a chain of exactly 3 nodes: there exist values a, b, c in [1, 10000] such that the nodes from the root downward are a, then b, then c, with each non-leaf having exactly one child (left or right). -/
  theorem spec_11 (root : Tree) (a b c : Std.I64) (hsize : size root = 3)
      (hval : inRange 1 10000 root) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
      (hb : 1 ≤ b.val ∧ b.val ≤ 10000) (hc : 1 ≤ c.val ∧ c.val ≤ 10000)
      (hshape : root = Tree.Node a (Tree.Node b (Tree.Node c Tree.Null Tree.Null) Tree.Null) Tree.Null ∨
        root = Tree.Node a (Tree.Node b Tree.Null (Tree.Node c Tree.Null Tree.Null)) Tree.Null ∨
        root = Tree.Node a Tree.Null (Tree.Node b (Tree.Node c Tree.Null Tree.Null) Tree.Null) ∨
        root = Tree.Node a Tree.Null (Tree.Node b Tree.Null (Tree.Node c Tree.Null Tree.Null))) :
      ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
        r.val = (max (a.val * (b.val + c.val)) (c.val * (a.val + b.val))) % MOD := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (a b c : Std.I64) (hsize : size root = 3)
        (hval : inRange 1 10000 root) (ha : 1 ≤ a.val ∧ a.val ≤ 10000)
        (hb : 1 ≤ b.val ∧ b.val ≤ 10000) (hc : 1 ≤ c.val ∧ c.val ≤ 10000)
        (hshape : root = Tree.Node a (Tree.Node b (Tree.Node c Tree.Null Tree.Null) Tree.Null) Tree.Null ∨
          root = Tree.Node a (Tree.Node b Tree.Null (Tree.Node c Tree.Null Tree.Null)) Tree.Null ∨
          root = Tree.Node a Tree.Null (Tree.Node b (Tree.Node c Tree.Null Tree.Null) Tree.Null) ∨
          root = Tree.Node a Tree.Null (Tree.Node b Tree.Null (Tree.Node c Tree.Null Tree.Null))), ∀ r : Std.I64, Aegis.MaxProduct.max_product root = ok r →
          r.val = (max (a.val * (b.val + c.val)) (c.val * (a.val + b.val))) % MOD) := by
    sorry

  end AegisSpec.MaxProduct
