import Aegis.IsUnivalTree.Code.Funs

/-!
# Specifications of `Aegis.IsUnivalTree.is_unival_tree`

LeetCode problem `univalued-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsUnivalTree

  open Aegis.IsUnivalTree

  def reachableNodes : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r => Tree.Node v l r :: (reachableNodes l ++ reachableNodes r)

  def nodeValue : Tree → Int
    | Tree.Null => 0
    | Tree.Node v _ _ => v.val

  def nodeCount (t : Tree) : Nat := (reachableNodes t).length

  def valueSet (t : Tree) : Finset Int := (reachableNodes t).map nodeValue |>.toFinset

  def countValue (t : Tree) (v : Int) : Nat :=
    (reachableNodes t).countP (fun n => decide (nodeValue n = v))

  def IsChild (p c : Tree) : Prop :=
    (∃ (v : Std.I64) (r : Tree), p = Tree.Node v c r) ∨
      (∃ (v : Std.I64) (l : Tree), p = Tree.Node v l c)

  def ValuesInRange (t : Tree) : Prop :=
    ∀ n ∈ reachableNodes t, (0 : Int) ≤ nodeValue n ∧ nodeValue n < 100

  def MapValuesRel (f : Int → Int) : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node v l r, Tree.Node w l' r' =>
      w.val = f v.val ∧ MapValuesRel f l l' ∧ MapValuesRel f r r'
    | _, _ => False

  /-- The function returns a result r (it does not fail). Let S be the set of stored integer values of all Node constructors reachable from root, including root itself. Then r = true if and only if S has exactly one element; equivalently, there exists an integer v such that every reachable Node has stored value v. In particular, r = false if and only if there exist two reachable Nodes with different stored values.
    Preconditions: root is not Tree.Null; the number of Node constructors reachable from root is between 1 and 100 inclusive; every stored value is an integer in [0, 100). -/
  theorem spec_1 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root) :
      ∃ r : Bool, is_unival_tree root = ok r ∧
        (r = true ↔ (valueSet root).card = 1) ∧
        (r = true ↔ ∃ v : Int, ∀ n ∈ reachableNodes root, nodeValue n = v) ∧
        (r = false ↔ ∃ n1 ∈ reachableNodes root, ∃ n2 ∈ reachableNodes root,
          nodeValue n1 ≠ nodeValue n2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root), ∃ r : Bool, is_unival_tree root = ok r ∧
          (r = true ↔ (valueSet root).card = 1) ∧
          (r = true ↔ ∃ v : Int, ∀ n ∈ reachableNodes root, nodeValue n = v) ∧
          (r = false ↔ ∃ n1 ∈ reachableNodes root, ∃ n2 ∈ reachableNodes root,
            nodeValue n1 ≠ nodeValue n2)) := by
    sorry

  /-- The function returns a result r; it never fails (in particular, no integer overflow, out-of-bounds access, or panic occurs).
    Preconditions: None; root may be any Tree, including Tree.Null, and stored values may be arbitrary 64-bit integers. -/
  theorem spec_2 (root : Tree) :
      ∃ r : Bool, is_unival_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree), ∃ r : Bool, is_unival_tree root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: root is not Tree.Null and satisfies the problem constraints (1 to 100 nodes, stored values in [0, 100)). There are reachable Nodes p and c such that c is the left child or the right child of p, c is not Tree.Null, and the stored value of p differs from the stored value of c. -/
  theorem spec_3 (root p c : Tree)
      (hne : root ≠ Tree.Null)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root)
      (hp : p ∈ reachableNodes root)
      (hchild : IsChild p c)
      (hcne : c ≠ Tree.Null)
      (hdiff : nodeValue p ≠ nodeValue c) :
      ∀ r : Bool, is_unival_tree root = ok r → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root p c : Tree)
        (hne : root ≠ Tree.Null)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root)
        (hp : p ∈ reachableNodes root)
        (hchild : IsChild p c)
        (hcne : c ≠ Tree.Null)
        (hdiff : nodeValue p ≠ nodeValue c), ∀ r : Bool, is_unival_tree root = ok r → r = false) := by
    sorry

  /-- Whenever the function returns a result r, r = true.
    Preconditions: root is not Tree.Null and satisfies the problem constraints (1 to 100 nodes, stored values in [0, 100)). For every reachable Node p and every non-Null child c of p (left or right), the stored value of p equals the stored value of c. -/
  theorem spec_4 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root)
      (huni : ∀ p ∈ reachableNodes root, ∀ c : Tree, IsChild p c → c ≠ Tree.Null →
        nodeValue p = nodeValue c) :
      ∀ r : Bool, is_unival_tree root = ok r → r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root)
        (huni : ∀ p ∈ reachableNodes root, ∀ c : Tree, IsChild p c → c ≠ Tree.Null →
          nodeValue p = nodeValue c), ∀ r : Bool, is_unival_tree root = ok r → r = true) := by
    sorry

  /-- Whenever the function returns a result res, res = false.
    Preconditions: root = Tree.Node(v, l, rt) and root satisfies the problem constraints (1 to 100 nodes, stored values in [0, 100)). Either (a) l is nonempty and there exist two Nodes n1 and n2 reachable from l whose stored values differ, or (b) rt is nonempty and there exist two Nodes n1 and n2 reachable from rt whose stored values differ. -/
  theorem spec_5 (root : Tree) (v : Std.I64) (l rt : Tree)
      (hroot : root = Tree.Node v l rt)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root)
      (hwit : (l ≠ Tree.Null ∧ ∃ n1 ∈ reachableNodes l, ∃ n2 ∈ reachableNodes l,
          nodeValue n1 ≠ nodeValue n2) ∨
        (rt ≠ Tree.Null ∧ ∃ n1 ∈ reachableNodes rt, ∃ n2 ∈ reachableNodes rt,
          nodeValue n1 ≠ nodeValue n2)) :
      ∀ res : Bool, is_unival_tree root = ok res → res = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (l rt : Tree)
        (hroot : root = Tree.Node v l rt)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root)
        (hwit : (l ≠ Tree.Null ∧ ∃ n1 ∈ reachableNodes l, ∃ n2 ∈ reachableNodes l,
            nodeValue n1 ≠ nodeValue n2) ∨
          (rt ≠ Tree.Null ∧ ∃ n1 ∈ reachableNodes rt, ∃ n2 ∈ reachableNodes rt,
            nodeValue n1 ≠ nodeValue n2)), ∀ res : Bool, is_unival_tree root = ok res → res = false) := by
    sorry

  /-- For every Node n reachable from root, whenever the function is applied to the subtree rooted at n, it returns a result r_n with r_n = true.
    Preconditions: root is not Tree.Null and satisfies the problem constraints. Every Node reachable from root has the same stored value v. -/
  theorem spec_6 (root : Tree) (v : Int)
      (hne : root ≠ Tree.Null)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root)
      (huni : ∀ n ∈ reachableNodes root, nodeValue n = v) :
      ∀ n ∈ reachableNodes root, ∀ rn : Bool, is_unival_tree n = ok rn → rn = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (v : Int)
        (hne : root ≠ Tree.Null)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root)
        (huni : ∀ n ∈ reachableNodes root, nodeValue n = v), ∀ n ∈ reachableNodes root, ∀ rn : Bool, is_unival_tree n = ok rn → rn = true) := by
    sorry

  /-- Whenever the function returns r1 on T1 and r2 on T2, r1 = r2.
    Preconditions: T1 and T2 are nonempty trees, each satisfying the problem constraints (1 to 100 nodes, stored values in [0, 100)), and for every integer v the number of Nodes with stored value v in T1 equals the number of Nodes with stored value v in T2. -/
  theorem spec_7 (T1 T2 : Tree)
      (hne1 : T1 ≠ Tree.Null) (hne2 : T2 ≠ Tree.Null)
      (hcnt1_ge : 1 ≤ nodeCount T1) (hcnt1_le : nodeCount T1 ≤ 100)
      (hcnt2_ge : 1 ≤ nodeCount T2) (hcnt2_le : nodeCount T2 ≤ 100)
      (hvals1 : ValuesInRange T1) (hvals2 : ValuesInRange T2)
      (hmult : ∀ v : Int, countValue T1 v = countValue T2 v) :
      ∀ r1 r2 : Bool, is_unival_tree T1 = ok r1 → is_unival_tree T2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (T1 T2 : Tree)
        (hne1 : T1 ≠ Tree.Null) (hne2 : T2 ≠ Tree.Null)
        (hcnt1_ge : 1 ≤ nodeCount T1) (hcnt1_le : nodeCount T1 ≤ 100)
        (hcnt2_ge : 1 ≤ nodeCount T2) (hcnt2_le : nodeCount T2 ≤ 100)
        (hvals1 : ValuesInRange T1) (hvals2 : ValuesInRange T2)
        (hmult : ∀ v : Int, countValue T1 v = countValue T2 v), ∀ r1 r2 : Bool, is_unival_tree T1 = ok r1 → is_unival_tree T2 = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever the function returns r on root and r_f on root_f, r = r_f.
    Preconditions: root is nonempty and satisfies the problem constraints. f is a function from integers to integers that is injective on the set S of stored values occurring in root and maps S into [0, 100). root_f is obtained from root by replacing every stored value v by f(v). -/
  theorem spec_8 (root root_f : Tree) (f : Int → Int)
      (hne : root ≠ Tree.Null)
      (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
      (hvals : ValuesInRange root)
      (hinj : ∀ v ∈ valueSet root, ∀ w ∈ valueSet root, f v = f w → v = w)
      (hrange : ∀ v ∈ valueSet root, (0 : Int) ≤ f v ∧ f v < 100)
      (hmap : MapValuesRel f root root_f) :
      ∀ r rf : Bool, is_unival_tree root = ok r → is_unival_tree root_f = ok rf → r = rf := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root root_f : Tree) (f : Int → Int)
        (hne : root ≠ Tree.Null)
        (hnode_ge : 1 ≤ nodeCount root) (hnode_le : nodeCount root ≤ 100)
        (hvals : ValuesInRange root)
        (hinj : ∀ v ∈ valueSet root, ∀ w ∈ valueSet root, f v = f w → v = w)
        (hrange : ∀ v ∈ valueSet root, (0 : Int) ≤ f v ∧ f v < 100)
        (hmap : MapValuesRel f root root_f), ∀ r rf : Bool, is_unival_tree root = ok r → is_unival_tree root_f = ok rf → r = rf) := by
    sorry

  end AegisSpec.IsUnivalTree
