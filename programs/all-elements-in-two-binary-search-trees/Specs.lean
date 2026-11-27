import Aegis.GetAllElements.Code.Funs

/-!
# Specifications of `Aegis.GetAllElements.get_all_elements`

LeetCode problem `all-elements-in-two-binary-search-trees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetAllElements

  open Aegis.GetAllElements

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ left right => size left + size right + 1

  def nodeValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v left right => nodeValues left ++ v.val :: nodeValues right

  def countNodes : Tree → Int → Nat
    | Tree.Null, _ => 0
    | Tree.Node v left right, x =>
        countNodes left x + (if v.val = x then 1 else 0) + countNodes right x

  def isBST : Tree → Prop
    | Tree.Null => True
    | Tree.Node v left right =>
        (∀ x ∈ nodeValues left, x ≤ v.val) ∧ (∀ x ∈ nodeValues right, v.val ≤ x) ∧
          isBST left ∧ isBST right

  def valuesInRange (T : Tree) : Prop := ∀ v ∈ nodeValues T, -100000 ≤ v ∧ v ≤ 100000

  /-- Whenever get_all_elements(root1, root2) returns a result r, r is exactly the nondecreasing sorted list of all node values of root1 and root2, with duplicates preserved. Equivalently: (a) len(r) = size(root1) + size(root2), where size(T) is the number of Node constructors in T; (b) for every i with 0 <= i < len(r) - 1, r[i] <= r[i+1]; and (c) for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals count_nodes(root1, v) + count_nodes(root2, v), where count_nodes(T, v) is the number of nodes of T whose value is v.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_1 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        r.val.length = size root1 + size root2 ∧
          (∀ i (hi : i + 1 < r.val.length), (r.val[i]).val ≤ (r.val[i + 1]).val) ∧
          (∀ v : Int,
            (r.val.filter (fun x => x.val = v)).length = countNodes root1 v + countNodes root2 v) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          r.val.length = size root1 + size root2 ∧
            (∀ i (hi : i + 1 < r.val.length), (r.val[i]).val ≤ (r.val[i + 1]).val) ∧
            (∀ v : Int,
              (r.val.filter (fun x => x.val = v)).length = countNodes root1 v + countNodes root2 v)) := by
    sorry

  /-- get_all_elements(root1, root2) returns a result r; it does not fail, overflow, or panic.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_2 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∃ r, get_all_elements root1 root2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∃ r, get_all_elements root1 root2 = ok r) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, len(r) = size(root1) + size(root2), where size(T) is the number of Node constructors in T.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_3 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        r.val.length = size root1 + size root2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          r.val.length = size root1 + size root2) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, for every i with 0 <= i < len(r) - 1, r[i] <= r[i+1].
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_4 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ i (hi : i + 1 < r.val.length), (r.val[i]).val ≤ (r.val[i + 1]).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ i (hi : i + 1 < r.val.length), (r.val[i]).val ≤ (r.val[i + 1]).val) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at most count_nodes(root1, v) + count_nodes(root2, v), where count_nodes(T, v) is the number of nodes of T whose value is v.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_5 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ v : Int,
          (r.val.filter (fun x => x.val = v)).length ≤
            countNodes root1 v + countNodes root2 v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ v : Int,
            (r.val.filter (fun x => x.val = v)).length ≤
              countNodes root1 v + countNodes root2 v) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v is at least count_nodes(root1, v) + count_nodes(root2, v), where count_nodes(T, v) is the number of nodes of T whose value is v.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_6 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ v : Int,
          countNodes root1 v + countNodes root2 v ≤
            (r.val.filter (fun x => x.val = v)).length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ v : Int,
            countNodes root1 v + countNodes root2 v ≤
              (r.val.filter (fun x => x.val = v)).length) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, for every i with 0 <= i < len(r), -100000 <= r[i] <= 100000.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_7 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ i (hi : i < r.val.length), -100000 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 100000 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ i (hi : i < r.val.length), -100000 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 100000) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, len(r) <= 10000.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_8 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r → r.val.length ≤ 10000 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r → r.val.length ≤ 10000) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r and len(r) > 0, r[0] is the minimum of all node values occurring in root1 and root2; that is, r[0] <= v for every node value v in either tree, and r[0] is equal to some node value in root1 or root2.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_9 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ (hpos : 0 < r.val.length),
          (∀ x ∈ nodeValues root1 ++ nodeValues root2, (r.val[0]).val ≤ x) ∧
            (r.val[0]).val ∈ nodeValues root1 ++ nodeValues root2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ (hpos : 0 < r.val.length),
            (∀ x ∈ nodeValues root1 ++ nodeValues root2, (r.val[0]).val ≤ x) ∧
              (r.val[0]).val ∈ nodeValues root1 ++ nodeValues root2) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r and len(r) > 0, r[len(r) - 1] is the maximum of all node values occurring in root1 and root2; that is, r[len(r) - 1] >= v for every node value v in either tree, and r[len(r) - 1] is equal to some node value in root1 or root2.
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_10 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ (hpos : 0 < r.val.length),
          (∀ x ∈ nodeValues root1 ++ nodeValues root2, x ≤ (r.val[r.val.length - 1]).val) ∧
            (r.val[r.val.length - 1]).val ∈ nodeValues root1 ++ nodeValues root2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ (hpos : 0 < r.val.length),
            (∀ x ∈ nodeValues root1 ++ nodeValues root2, x ≤ (r.val[r.val.length - 1]).val) ∧
              (r.val[r.val.length - 1]).val ∈ nodeValues root1 ++ nodeValues root2) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns r and get_all_elements(root2, root1) returns r', we have len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(r).
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_11 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r r', get_all_elements root1 root2 = ok r → get_all_elements root2 root1 = ok r' →
        r.val.length = r'.val.length ∧
          r.val.map (fun x => x.val) = r'.val.map (fun x => x.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r r', get_all_elements root1 root2 = ok r → get_all_elements root2 root1 = ok r' →
          r.val.length = r'.val.length ∧
            r.val.map (fun x => x.val) = r'.val.map (fun x => x.val)) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns r and get_all_elements(root1', root2') returns r', we have len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < len(r).
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. For the shape-invariance claim, root1' and root2' are any binary search trees satisfying the same node-count and value-range constraints and having the same combined multiset of node values as root1 and root2. -/
  theorem spec_12 (root1 root2 root1' root2' : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2)
      (hbst1' : isBST root1') (hbst2' : isBST root2')
      (hsize1' : size root1' ≤ 5000) (hsize2' : size root2' ≤ 5000)
      (hrange1' : valuesInRange root1') (hrange2' : valuesInRange root2')
      (hmultiset : ∀ v : Int, countNodes root1' v + countNodes root2' v
        = countNodes root1 v + countNodes root2 v) :
      ∀ r r', get_all_elements root1 root2 = ok r → get_all_elements root1' root2' = ok r' →
        r.val.length = r'.val.length ∧
          r.val.map (fun x => x.val) = r'.val.map (fun x => x.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root1 root2 root1' root2' : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2)
        (hbst1' : isBST root1') (hbst2' : isBST root2')
        (hsize1' : size root1' ≤ 5000) (hsize2' : size root2' ≤ 5000)
        (hrange1' : valuesInRange root1') (hrange2' : valuesInRange root2')
        (hmultiset : ∀ v : Int, countNodes root1' v + countNodes root2' v
          = countNodes root1 v + countNodes root2 v), ∀ r r', get_all_elements root1 root2 = ok r → get_all_elements root1' root2' = ok r' →
          r.val.length = r'.val.length ∧
            r.val.map (fun x => x.val) = r'.val.map (fun x => x.val)) := by
    sorry

  /-- Whenever get_all_elements(root1, root2) returns a result r, for every i with 0 <= i < len(r), there exists a node in root1 or in root2 whose value is r[i].
    Preconditions: root1 and root2 are binary search trees (for every node with value v, all values in its left subtree are <= v and all values in its right subtree are >= v); each tree contains between 0 and 5000 nodes; and every node value v satisfies -100000 <= v <= 100000. -/
  theorem spec_13 (root1 root2 : Tree)
      (hbst1 : isBST root1) (hbst2 : isBST root2)
      (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
      (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2) :
      ∀ r, get_all_elements root1 root2 = ok r →
        ∀ i (hi : i < r.val.length),
          (r.val[i]).val ∈ nodeValues root1 ++ nodeValues root2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root1 root2 : Tree)
        (hbst1 : isBST root1) (hbst2 : isBST root2)
        (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
        (hrange1 : valuesInRange root1) (hrange2 : valuesInRange root2), ∀ r, get_all_elements root1 root2 = ok r →
          ∀ i (hi : i < r.val.length),
            (r.val[i]).val ∈ nodeValues root1 ++ nodeValues root2) := by
    sorry

  end AegisSpec.GetAllElements
