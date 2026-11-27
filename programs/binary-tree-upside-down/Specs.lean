import Aegis.UpsideDownBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.UpsideDownBinaryTree.upside_down_binary_tree`

LeetCode problem `binary-tree-upside-down`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.UpsideDownBinaryTree

  open Aegis.UpsideDownBinaryTree

  def numNodes : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + numNodes l + numNodes r

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (height l) (height r)

  def numLeaves : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ Tree.Null Tree.Null => 1
    | Tree.Node _ l r => numLeaves l + numLeaves r

  def countVal : Tree → Int → Nat
    | Tree.Null, _ => 0
    | Tree.Node v l r, a => (if v.val = a then 1 else 0) + countVal l a + countVal r a

  def nodeVals : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (nodeVals l ++ nodeVals r)

  def nodes : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r => Tree.Node v l r :: (nodes l ++ nodes r)

  def leftChild : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node _ l _ => l

  def rightChild : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node _ _ r => r

  def treeVal : Tree → Option Int
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

  def isLeaf (t : Tree) : Prop :=
    ∀ (v : Std.I64) (l u : Tree), t = Tree.Node v l u → l = Tree.Null ∧ u = Tree.Null

  def leftSpine : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r => Tree.Node v l r :: leftSpine l

  def rightSpine : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r => Tree.Node v l r :: rightSpine r

  def validInput (t : Tree) : Prop :=
    numNodes t ≤ 10
      ∧ (∀ a, a ∈ nodeVals t → (1 : Int) ≤ a ∧ a ≤ 10)
      ∧ (∀ n, n ∈ nodes t →
          ∀ (v : Std.I64) (l u : Tree), n = Tree.Node v l u →
            u ≠ Tree.Null → l ≠ Tree.Null ∧ isLeaf u)

  def cloneTree : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (cloneTree l) (cloneTree r)

  def upsideDownAux : Tree → Tree → Tree → Tree
    | Tree.Null, _, acc => acc
    | Tree.Node v l r, prevR, acc =>
      upsideDownAux l r (Tree.Node v (cloneTree prevR) acc)

  def upsideDownResult (root : Tree) : Tree := upsideDownAux root Tree.Null Tree.Null

  /-- If root = Null, the function returns Result.ok Null. Otherwise let v_0,...,v_k (k >= 0) be the left spine of root: v_0 is root, for 0 <= i < k the left child of v_i is v_{i+1}, and the left child of v_k is Null. For 0 <= i < k let R_i be the right child of v_i (possibly Null); the guarantee implies each non-null R_i is a leaf and R_k is Null. The function returns Result.ok r, where r is the tree consisting exactly of nodes w_0,...,w_k plus, for each i with 0 <= i < k and R_i non-null, one copy u_i of R_i, with these parent-child relations: w_k is the root of r; for every i with 1 <= i <= k, the left child of w_i is u_{i-1} if R_{i-1} is non-null and Null otherwise, and the right child of w_i is w_{i-1}; w_0 has both children Null; every u_i has the same value and children as R_i (hence is a leaf under the guarantee); and there are no other nodes or edges in r. Each w_i has the same value as v_i.
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every node that is a right child has a left sibling (a left child of the same parent) and has no children. -/
  theorem spec_1 (root : Tree) (hvalid : validInput root) :
      upside_down_binary_tree root = Result.ok (upsideDownResult root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), upside_down_binary_tree root = Result.ok (upsideDownResult root)) := by
    sorry

  /-- The function returns a result Result.ok r for some Tree r; it never fails, overflows, or panics.
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_2 (root : Tree) (hvalid : validInput root) :
      ∃ r : Tree, upside_down_binary_tree root = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∃ r : Tree, upside_down_binary_tree root = Result.ok r) := by
    sorry

  /-- Let r be the tree returned by the function. Then r = Null if and only if root = Null.
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_3 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        (r = Tree.Null ↔ root = Tree.Null) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          (r = Tree.Null ↔ root = Tree.Null)) := by
    sorry

  /-- Let r be the returned tree. Define len_nodes(Null)=0 and len_nodes(Node(_,l,u))=1+len_nodes(l)+len_nodes(u). Then len_nodes(r)=len_nodes(root).
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_4 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        numNodes r = numNodes root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          numNodes r = numNodes root) := by
    sorry

  /-- Let r be the returned tree. For every integer a, the number of nodes in r whose value is a equals the number of nodes in root whose value is a.
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_5 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        ∀ a : Int, countVal r a = countVal root a := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          ∀ a : Int, countVal r a = countVal root a) := by
    sorry

  /-- The value at the root of the returned tree r is the value of v_k, the last node on the left spine of root.
    Preconditions: root is a non-null valid problem input, with left spine v_0,...,v_k: v_0=root, v_{i+1} is the left child of v_i for 0 <= i < k, and v_k has no left child. -/
  theorem spec_6 (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        treeVal r = treeVal ((leftSpine root).getLastD Tree.Null) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          treeVal r = treeVal ((leftSpine root).getLastD Tree.Null)) := by
    sorry

  /-- Let w_i be the node in the returned tree r corresponding to v_i. If k=0 then the root of r has no right child. If k>=1 then each w_i with 1 <= i <= k has right child w_{i-1}, and w_0 has no right child. Hence the right spine of r is exactly w_k,w_{k-1},...,w_0.
    Preconditions: root is a non-null valid problem input, with left spine v_0,...,v_k (v_0=root, v_{i+1} is the left child of v_i for 0 <= i < k, and v_k has no left child). -/
  theorem spec_7 (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        (rightSpine r).length = (leftSpine root).length
          ∧ (rightSpine r).map treeVal = ((leftSpine root).map treeVal).reverse := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          (rightSpine r).length = (leftSpine root).length
            ∧ (rightSpine r).map treeVal = ((leftSpine root).map treeVal).reverse) := by
    sorry

  /-- Let w_i be the node in the returned tree r corresponding to v_i. If k=0 then the root of r has no left child. If k>=1 then the left child of the root of r is a copy of R_{k-1}, the right child of v_{k-1}, or Null if v_{k-1} has no right child. More generally, for every i with 1 <= i <= k, the left child of w_i is a copy of R_{i-1}.
    Preconditions: root is a non-null valid problem input, with left spine v_0,...,v_k and right children R_i of v_i for 0 <= i < k (possibly Null). -/
  theorem spec_8 (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        (rightSpine r).map leftChild
          = (((leftSpine root).map rightChild).dropLast).reverse ++ [Tree.Null] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          (rightSpine r).map leftChild
            = (((leftSpine root).map rightChild).dropLast).reverse ++ [Tree.Null]) := by
    sorry

  /-- In the returned tree r, the node w_0 corresponding to the original root v_0 is a leaf: both of its children are Null. In particular, if k=0 then r is a single leaf with the same value as root.
    Preconditions: root is a non-null valid problem input, with left spine v_0,...,v_k (v_0=root, v_{i+1} is the left child of v_i for 0 <= i < k, and v_k has no left child). -/
  theorem spec_9 (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        leftChild ((rightSpine r).getLastD Tree.Null) = Tree.Null
          ∧ rightChild ((rightSpine r).getLastD Tree.Null) = Tree.Null
          ∧ ((leftSpine root).length = 1 →
              ∃ (v : Std.I64) (l u : Tree),
                root = Tree.Node v l u ∧ r = Tree.Node v Tree.Null Tree.Null) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root) (hne : root ≠ Tree.Null), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          leftChild ((rightSpine r).getLastD Tree.Null) = Tree.Null
            ∧ rightChild ((rightSpine r).getLastD Tree.Null) = Tree.Null
            ∧ ((leftSpine root).length = 1 →
                ∃ (v : Std.I64) (l u : Tree),
                  root = Tree.Node v l u ∧ r = Tree.Node v Tree.Null Tree.Null)) := by
    sorry

  /-- Define height(Null)=0 and height(Node(_,l,u))=1+max(height(l),height(u)). Let r be the returned tree. Then height(r)=height(root).
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_10 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        height r = height root := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          height r = height root) := by
    sorry

  /-- Call a node a leaf if it is non-null and both of its children are Null. Let leaves(t) be the number of leaves in a tree t. If r is the returned tree, then leaves(r)=leaves(root).
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_11 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        numLeaves r = numLeaves root := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          numLeaves r = numLeaves root) := by
    sorry

  /-- In the returned tree r, every non-null left child is a leaf (both of its children are Null).
    Preconditions: root is a valid problem input: its number of nodes is between 0 and 10, every node value is in [1,10], and every right child has a left sibling and no children. -/
  theorem spec_12 (root : Tree) (hvalid : validInput root) :
      ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
        ∀ n, n ∈ nodes r →
          ∀ (v : Std.I64) (l u : Tree), n = Tree.Node v l u →
            l ≠ Tree.Null → isLeaf l := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (hvalid : validInput root), ∀ r : Tree, upside_down_binary_tree root = Result.ok r →
          ∀ n, n ∈ nodes r →
            ∀ (v : Std.I64) (l u : Tree), n = Tree.Node v l u →
              l ≠ Tree.Null → isLeaf l) := by
    sorry

  end AegisSpec.UpsideDownBinaryTree
