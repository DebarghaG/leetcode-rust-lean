import Aegis.LongestConsecutive.Code.Funs

/-!
# Specifications of `Aegis.LongestConsecutive.longest_consecutive`

LeetCode problem `binary-tree-longest-consecutive-sequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestConsecutive

  open Aegis.LongestConsecutive

  def nodeValue : Tree → Int
    | Tree.Null => 0
    | Tree.Node v _ _ => v.val

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def Occurs (u : Tree) : Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => u = Tree.Node v l r ∨ Occurs u l ∨ Occurs u r

  def singletonNode : Tree → List Tree
    | Tree.Null => []
    | t@(Tree.Node _ _ _) => [t]

  def childNodes : Tree → List Tree
    | Tree.Null => []
    | Tree.Node _ l r => singletonNode l ++ singletonNode r

  def ParentOf (p c : Tree) : Prop := c ∈ childNodes p

  def Adjacent (u w : Tree) : Prop := ParentOf u w ∨ ParentOf w u

  def ChainRel {α : Type} (R : α → α → Prop) : List α → Prop
    | [] => True
    | [_] => True
    | u :: w :: rest => R u w ∧ ChainRel R (w :: rest)

  def IsConsecPath (root : Tree) (vs : List Tree) : Prop :=
    vs ≠ [] ∧
      (∀ v ∈ vs, Occurs v root) ∧
      vs.Nodup ∧
      ∃ s : Int,
        (s = 1 ∨ s = -1) ∧
          ChainRel (fun u w => Adjacent u w ∧ nodeValue w = nodeValue u + s) vs

  noncomputable def maxConsecPathLen (root : Tree) : Nat :=
    by
    classical
    exact
      (List.range (nodeCount root + 1)).foldr
        (fun k acc =>
          if ∃ vs : List Tree, IsConsecPath root vs ∧ vs.length = k then Nat.max k acc else acc)
        0

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def i64OfInt (n : Int) : Std.I64 := ⟨BitVec.ofInt 64 n⟩

  def addToValues (c : Int) : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node (i64OfInt (v.val + c)) (addToValues c l) (addToValues c r)

  def StepInt (x y : Int) : Prop := y = x + 1 ∨ y = x - 1

  def spineValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v Tree.Null Tree.Null => [v.val]
    | Tree.Node v Tree.Null (Tree.Node w l r) => v.val :: spineValues (Tree.Node w l r)
    | Tree.Node v (Tree.Node w l r) _ => v.val :: spineValues (Tree.Node w l r)

  def IsRun (a : List Int) (i j : Nat) : Prop :=
    i ≤ j ∧
      j < a.length ∧
        ∃ s : Int, (s = 1 ∨ s = -1) ∧ ChainRel (fun x y => y = x + s) ((a.drop i).take (j + 1 - i))

  noncomputable def maxRunLen (a : List Int) : Nat :=
    by
    classical
    exact
      ((List.range a.length).flatMap
          (fun i => (List.range a.length).map (fun j => (i, j)))).foldr
        (fun p acc => if IsRun a p.1 p.2 then Nat.max (p.2 - p.1 + 1) acc else acc)
        0

  /-- Whenever longest_consecutive(root) returns a result r, r is exactly the following maximum. Consider every finite sequence (v0, ..., v_{k-1}) with k >= 1 of distinct nodes of root such that (a) for each i with 0 <= i < k-1, either v_i is the parent of v_{i+1} or v_{i+1} is the parent of v_i; and (b) there exists s in {1, -1} such that for every i with 0 <= i < k-1, value(v_{i+1}) = value(v_i) + s. For such a sequence let its length be k. Then r is the maximum length among all such sequences in root.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_1 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ r : Std.I64,
        longest_consecutive root = ok r → r.val = (maxConsecPathLen root : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ r : Std.I64,
          longest_consecutive root = ok r → r.val = (maxConsecPathLen root : Int)) := by
    sorry

  /-- For every root satisfying the preconditions, longest_consecutive(root) returns a result r (it does not fail, panic, or overflow).
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_2 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∃ r : Std.I64, longest_consecutive root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∃ r : Std.I64, longest_consecutive root = ok r) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, 1 <= r <= n, where n is the number of nodes of root.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_3 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ r : Std.I64,
        longest_consecutive root = ok r → 1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ r : Std.I64,
          longest_consecutive root = ok r → 1 ≤ r.val ∧ r.val ≤ (nodeCount root : Int)) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, there exists a consecutive path in root, meaning a sequence of distinct nodes along parent-child edges in which all consecutive value differences equal the same sign 1 or -1, having exactly r nodes.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_4 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ r : Std.I64,
        longest_consecutive root = ok r →
          ∃ vs : List Tree, IsConsecPath root vs ∧ (vs.length : Int) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ r : Std.I64,
          longest_consecutive root = ok r →
            ∃ vs : List Tree, IsConsecPath root vs ∧ (vs.length : Int) = r.val) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, every consecutive path in root, meaning every sequence of distinct nodes along parent-child edges in which all consecutive value differences equal the same sign 1 or -1, has at most r nodes.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_5 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ r : Std.I64,
        longest_consecutive root = ok r →
          ∀ vs : List Tree, IsConsecPath root vs → (vs.length : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ r : Std.I64,
          longest_consecutive root = ok r →
            ∀ vs : List Tree, IsConsecPath root vs → (vs.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, r = 1.
    Preconditions: root = Node(v, Null, Null) for some integer v with -30000 <= v <= 30000. -/
  theorem spec_6 (v : Std.I64)
      (hv : -30000 ≤ v.val ∧ v.val ≤ 30000) :
      ∀ r : Std.I64,
        longest_consecutive (Tree.Node v Tree.Null Tree.Null) = ok r → r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (v : Std.I64)
        (hv : -30000 ≤ v.val ∧ v.val ≤ 30000), ∀ r : Std.I64,
          longest_consecutive (Tree.Node v Tree.Null Tree.Null) = ok r → r.val = 1) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, r = 2.
    Preconditions: root has exactly two nodes; thus it is either Node(v, Node(w, Null, Null), Null) or Node(v, Null, Node(w, Null, Null)) for integers v and w, with -30000 <= v <= 30000, -30000 <= w <= 30000, and |v - w| = 1. -/
  theorem spec_7 (v w : Std.I64)
      (hv : -30000 ≤ v.val ∧ v.val ≤ 30000)
      (hw : -30000 ≤ w.val ∧ w.val ≤ 30000)
      (hdiff : StepInt v.val w.val) :
      (∀ r : Std.I64,
          longest_consecutive (Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null) = ok r →
            r.val = 2) ∧
        ∀ r : Std.I64,
          longest_consecutive (Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null)) = ok r →
            r.val = 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (v w : Std.I64)
        (hv : -30000 ≤ v.val ∧ v.val ≤ 30000)
        (hw : -30000 ≤ w.val ∧ w.val ≤ 30000)
        (hdiff : StepInt v.val w.val), (∀ r : Std.I64,
            longest_consecutive (Tree.Node v (Tree.Node w Tree.Null Tree.Null) Tree.Null) = ok r →
              r.val = 2) ∧
          ∀ r : Std.I64,
            longest_consecutive (Tree.Node v Tree.Null (Tree.Node w Tree.Null Tree.Null)) = ok r →
              r.val = 2) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, r = 3.
    Preconditions: root has exactly three nodes and consists of a root node with value v and two leaf children whose values are v - 1 and v + 1, one on the left and one on the right in either order, with -30000 <= v - 1 < v + 1 <= 30000. -/
  theorem spec_8 (v : Std.I64)
      (hlo : -30000 ≤ v.val - 1)
      (hhi : v.val + 1 ≤ 30000) :
      (∀ r : Std.I64,
          longest_consecutive
              (Tree.Node v
                (Tree.Node (i64OfInt (v.val - 1)) Tree.Null Tree.Null)
                (Tree.Node (i64OfInt (v.val + 1)) Tree.Null Tree.Null)) =
            ok r →
            r.val = 3) ∧
        ∀ r : Std.I64,
          longest_consecutive
              (Tree.Node v
                (Tree.Node (i64OfInt (v.val + 1)) Tree.Null Tree.Null)
                (Tree.Node (i64OfInt (v.val - 1)) Tree.Null Tree.Null)) =
            ok r →
            r.val = 3 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v : Std.I64)
        (hlo : -30000 ≤ v.val - 1)
        (hhi : v.val + 1 ≤ 30000), (∀ r : Std.I64,
            longest_consecutive
                (Tree.Node v
                  (Tree.Node (i64OfInt (v.val - 1)) Tree.Null Tree.Null)
                  (Tree.Node (i64OfInt (v.val + 1)) Tree.Null Tree.Null)) =
              ok r →
              r.val = 3) ∧
          ∀ r : Std.I64,
            longest_consecutive
                (Tree.Node v
                  (Tree.Node (i64OfInt (v.val + 1)) Tree.Null Tree.Null)
                  (Tree.Node (i64OfInt (v.val - 1)) Tree.Null Tree.Null)) =
              ok r →
              r.val = 3) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, r >= 2.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, every node value v satisfies -30000 <= v <= 30000, and there exists a node u of root with a child c such that |value(u) - value(c)| = 1. -/
  theorem spec_9 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
      (hedge : ∃ u c : Tree, Occurs u root ∧ ParentOf u c ∧ StepInt (nodeValue u) (nodeValue c)) :
      ∀ r : Std.I64, longest_consecutive root = ok r → 2 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
        (hedge : ∃ u c : Tree, Occurs u root ∧ ParentOf u c ∧ StepInt (nodeValue u) (nodeValue c)), ∀ r : Std.I64, longest_consecutive root = ok r → 2 ≤ r.val) := by
    sorry

  /-- For every node u of root, let T_u be the subtree of root consisting of u and all descendants of u, with the same left/right child structure and node values. Whenever longest_consecutive(root) returns a result r and longest_consecutive(T_u) returns a result r_u, we have r_u <= r.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_10 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ u : Tree,
        Occurs u root →
          ∀ r ru : Std.I64,
            longest_consecutive root = ok r →
              longest_consecutive u = ok ru → ru.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ u : Tree,
          Occurs u root →
            ∀ r ru : Std.I64,
              longest_consecutive root = ok r →
                longest_consecutive u = ok ru → ru.val ≤ r.val) := by
    sorry

  /-- Let mirror(root) be the tree obtained from root by recursively swapping the left and right child of every node. Whenever longest_consecutive(root) returns a result r, longest_consecutive(mirror(root)) also returns the same result r; conversely, whenever longest_consecutive(mirror(root)) returns r, longest_consecutive(root) returns r.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_11 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      (∀ r : Std.I64,
          longest_consecutive root = ok r → longest_consecutive (mirror root) = ok r) ∧
        ∀ r : Std.I64,
          longest_consecutive (mirror root) = ok r → longest_consecutive root = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), (∀ r : Std.I64,
            longest_consecutive root = ok r → longest_consecutive (mirror root) = ok r) ∧
          ∀ r : Std.I64,
            longest_consecutive (mirror root) = ok r → longest_consecutive root = ok r) := by
    sorry

  /-- For every integer c such that -30000 <= value(u) + c <= 30000 for every node u of root, let root+c be the tree obtained by adding c to every node value. Whenever longest_consecutive(root) returns a result r, longest_consecutive(root+c) also returns the same result r; conversely, whenever longest_consecutive(root+c) returns r, longest_consecutive(root) returns r.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, and every node value v satisfies -30000 <= v <= 30000. -/
  theorem spec_12 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000) :
      ∀ c : Int,
        (∀ u, Occurs u root → -30000 ≤ nodeValue u + c ∧ nodeValue u + c ≤ 30000) →
          (∀ r : Std.I64,
              longest_consecutive root = ok r →
                longest_consecutive (addToValues c root) = ok r) ∧
            ∀ r : Std.I64,
              longest_consecutive (addToValues c root) = ok r →
                longest_consecutive root = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000), ∀ c : Int,
          (∀ u, Occurs u root → -30000 ≤ nodeValue u + c ∧ nodeValue u + c ≤ 30000) →
            (∀ r : Std.I64,
                longest_consecutive root = ok r →
                  longest_consecutive (addToValues c root) = ok r) ∧
              ∀ r : Std.I64,
                longest_consecutive (addToValues c root) = ok r →
                  longest_consecutive root = ok r) := by
    sorry

  /-- Let p0, p1, ..., p_{n-1} be the nodes obtained starting at the root and repeatedly taking the unique child until no child remains, and let a_i = value(p_i). Whenever longest_consecutive(root) returns a result r, r is the maximum of j - i + 1 over all pairs of indices 0 <= i <= j < n such that there exists s in {1, -1} with a_{k+1} = a_k + s for every k with i <= k < j.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, every node value v satisfies -30000 <= v <= 30000, and every node of root has at most one child. -/
  theorem spec_13 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
      (hchain : ∀ u, Occurs u root → (childNodes u).length ≤ 1) :
      ∀ r : Std.I64,
        longest_consecutive root = ok r → r.val = (maxRunLen (spineValues root) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
        (hchain : ∀ u, Occurs u root → (childNodes u).length ≤ 1), ∀ r : Std.I64,
          longest_consecutive root = ok r → r.val = (maxRunLen (spineValues root) : Int)) := by
    sorry

  /-- Whenever longest_consecutive(root) returns a result r, r >= 3.
    Preconditions: root is a Tree with at least one node and at most 30000 nodes, every node value v satisfies -30000 <= v <= 30000, and there exists a node u of root with value x having two children c1 and c2 with value(c1) = x - 1 and value(c2) = x + 1, in either order. -/
  theorem spec_14 (root : Tree)
      (hpos : 1 ≤ nodeCount root)
      (hsize : nodeCount root ≤ 30000)
      (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
      (hfork : ∃ (u c1 c2 : Tree),
        Occurs u root ∧ ParentOf u c1 ∧ ParentOf u c2 ∧ c1 ≠ c2 ∧
          nodeValue c1 = nodeValue u - 1 ∧ nodeValue c2 = nodeValue u + 1) :
      ∀ r : Std.I64, longest_consecutive root = ok r → 3 ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root : Tree)
        (hpos : 1 ≤ nodeCount root)
        (hsize : nodeCount root ≤ 30000)
        (hval : ∀ u, Occurs u root → -30000 ≤ nodeValue u ∧ nodeValue u ≤ 30000)
        (hfork : ∃ (u c1 c2 : Tree),
          Occurs u root ∧ ParentOf u c1 ∧ ParentOf u c2 ∧ c1 ≠ c2 ∧
            nodeValue c1 = nodeValue u - 1 ∧ nodeValue c2 = nodeValue u + 1), ∀ r : Std.I64, longest_consecutive root = ok r → 3 ≤ r.val) := by
    sorry

  end AegisSpec.LongestConsecutive
