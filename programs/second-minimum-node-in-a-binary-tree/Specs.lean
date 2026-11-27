import Aegis.FindSecondMinimumValue.Code.Funs

/-!
# Specifications of `Aegis.FindSecondMinimumValue.find_second_minimum_value`

LeetCode problem `second-minimum-node-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindSecondMinimumValue

  open Aegis.FindSecondMinimumValue

  def values : Aegis.FindSecondMinimumValue.Tree → Finset ℤ
    | Tree.Null => ∅
    | Tree.Node v l r => insert v.val (values l ∪ values r)

  def size : Aegis.FindSecondMinimumValue.Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + size l + size r

  def rootVal : Aegis.FindSecondMinimumValue.Tree → Option ℤ
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

  def IsSpecial : Aegis.FindSecondMinimumValue.Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r =>
        (l = Tree.Null ∧ r = Tree.Null) ∨
          (l ≠ Tree.Null ∧ r ≠ Tree.Null ∧ IsSpecial l ∧ IsSpecial r)

  def MinProp : Aegis.FindSecondMinimumValue.Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        (∀ a b : ℤ, rootVal l = some a → rootVal r = some b → v.val = min a b) ∧
          MinProp l ∧ MinProp r

  def NodeBounds : Aegis.FindSecondMinimumValue.Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        (1 ≤ v.val ∧ v.val ≤ 2 ^ 31 - 1) ∧ NodeBounds l ∧ NodeBounds r

  def Pre (root : Aegis.FindSecondMinimumValue.Tree) : Prop :=
    root ≠ Tree.Null ∧ IsSpecial root ∧ MinProp root ∧ NodeBounds root ∧ size root ≤ 25

  def IsMin (S : Finset ℤ) (m : ℤ) : Prop :=
    m ∈ S ∧ ∀ x ∈ S, m ≤ x

  def IsMax (S : Finset ℤ) (M : ℤ) : Prop :=
    M ∈ S ∧ ∀ x ∈ S, x ≤ M

  def Occurs (x : ℤ) : Aegis.FindSecondMinimumValue.Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => v.val = x ∨ Occurs x l ∨ Occurs x r

  inductive IsSubtree : Aegis.FindSecondMinimumValue.Tree → Aegis.FindSecondMinimumValue.Tree → Prop
    | refl (t : Aegis.FindSecondMinimumValue.Tree) : IsSubtree t t
    | left {n : Aegis.FindSecondMinimumValue.Tree} {v : Std.I64}
        {l r : Aegis.FindSecondMinimumValue.Tree} :
        IsSubtree n l → IsSubtree n (Tree.Node v l r)
    | right {n : Aegis.FindSecondMinimumValue.Tree} {v : Std.I64}
        {l r : Aegis.FindSecondMinimumValue.Tree} :
        IsSubtree n r → IsSubtree n (Tree.Node v l r)

  def childValsOfMin (m : ℤ) : Aegis.FindSecondMinimumValue.Tree → Finset ℤ
    | Tree.Null => ∅
    | Tree.Node v l r =>
        (if v.val = m then
            ((rootVal l).toFinset ∪ (rootVal r).toFinset).filter (fun c => m < c)
          else ∅) ∪
          childValsOfMin m l ∪ childValsOfMin m r

  /-- Let S be the set of all node values in root, defined recursively by values(Tree.Null) = empty and values(Tree.Node(v,l,r)) = {v} union values(l) union values(r). Let m = min S. The function returns a result r and: if {x in S | x > m} is empty, then r = -1; otherwise r = min {x in S | x > m}.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_1 (root : Tree) (h : Pre root) :
      ∃ r : Std.I64,
        find_second_minimum_value root = ok r ∧
          ∀ m : ℤ, IsMin (values root) m →
            ((¬ ∃ x ∈ values root, m < x) → r.val = -1) ∧
            ((∃ x ∈ values root, m < x) →
              ∃ s : ℤ,
                s ∈ values root ∧ m < s ∧ r.val = s ∧
                  ∀ x ∈ values root, m < x → s ≤ x) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∃ r : Std.I64,
          find_second_minimum_value root = ok r ∧
            ∀ m : ℤ, IsMin (values root) m →
              ((¬ ∃ x ∈ values root, m < x) → r.val = -1) ∧
              ((∃ x ∈ values root, m < x) →
                ∃ s : ℤ,
                  s ∈ values root ∧ m < s ∧ r.val = s ∧
                    ∀ x ∈ values root, m < x → s ≤ x)) := by
    sorry

  /-- For every root satisfying the preconditions, the function returns some result r and does not fail: there is no panic, no out-of-bounds access, and no i64 overflow.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_2 (root : Tree) (h : Pre root) :
      ∃ r : Std.I64, find_second_minimum_value root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∃ r : Std.I64, find_second_minimum_value root = ok r) := by
    sorry

  /-- Let S be the set of all node values in root. The function returns a result r and r = -1 if and only if S has exactly one element (equivalently, every node of root has value root.val).
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_3 (root : Tree) (h : Pre root) :
      ∃ r : Std.I64,
        find_second_minimum_value root = ok r ∧
          (r.val = -1 ↔ (values root).card = 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∃ r : Std.I64,
          find_second_minimum_value root = ok r ∧
            (r.val = -1 ↔ (values root).card = 1)) := by
    sorry

  /-- Let S be the set of all node values in root. Whenever the function returns a result r with r != -1, there exists a node n of root such that n.val = r (that is, r is in S).
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_4 (root : Tree) (h : Pre root) :
      ∀ r : Std.I64,
        find_second_minimum_value root = ok r → r.val ≠ -1 → Occurs r.val root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∀ r : Std.I64,
          find_second_minimum_value root = ok r → r.val ≠ -1 → Occurs r.val root) := by
    sorry

  /-- Let S be the set of all node values in root, m = min S, and M = max S. Whenever the function returns a result r with r != -1, m < r <= M and 1 <= r <= 2^31 - 1.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_5 (root : Tree) (h : Pre root) :
      ∀ r : Std.I64,
        find_second_minimum_value root = ok r → r.val ≠ -1 →
          ∀ m M : ℤ,
            IsMin (values root) m →
              IsMax (values root) M →
                m < r.val ∧ r.val ≤ M ∧ 1 ≤ r.val ∧ r.val ≤ 2 ^ 31 - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∀ r : Std.I64,
          find_second_minimum_value root = ok r → r.val ≠ -1 →
            ∀ m M : ℤ,
              IsMin (values root) m →
                IsMax (values root) M →
                  m < r.val ∧ r.val ≤ M ∧ 1 ≤ r.val ∧ r.val ≤ 2 ^ 31 - 1) := by
    sorry

  /-- Let S be the set of all node values in root and m = min S. Whenever the function returns a result r with r != -1, no value x in S satisfies m < x < r; equivalently, for every x in S, if x > m then x >= r.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_6 (root : Tree) (h : Pre root) :
      ∀ r : Std.I64,
        find_second_minimum_value root = ok r → r.val ≠ -1 →
          ∀ m : ℤ,
            IsMin (values root) m →
              ∀ x ∈ values root, m < x → r.val ≤ x := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∀ r : Std.I64,
          find_second_minimum_value root = ok r → r.val ≠ -1 →
            ∀ m : ℤ,
              IsMin (values root) m →
                ∀ x ∈ values root, m < x → r.val ≤ x) := by
    sorry

  /-- Let S1 be the set of all node values in root1 and spec_2 the set of all node values in root2. If S1 = S2, then the function returns a result r1 for root1 and a result r2 for root2, and r1 = r2.
    Preconditions: root1 and root2 each satisfy: it is a non-empty special binary tree (the root is not Tree.Null; every node has either zero or two children; for every internal node n, n.val = min(n.left.val, n.right.val)); every node value is in [1, 2^31 - 1]; and it has at most 25 nodes. -/
  theorem spec_7 (root1 root2 : Tree) (h1 : Pre root1) (h2 : Pre root2) :
      values root1 = values root2 →
        ∃ r1 r2 : Std.I64,
          find_second_minimum_value root1 = ok r1 ∧
            find_second_minimum_value root2 = ok r2 ∧ r1.val = r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root1 root2 : Tree) (h1 : Pre root1) (h2 : Pre root2), values root1 = values root2 →
          ∃ r1 r2 : Std.I64,
            find_second_minimum_value root1 = ok r1 ∧
              find_second_minimum_value root2 = ok r2 ∧ r1.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists an internal node n of root (a node whose two children are non-null) such that n.val = root.val, one child of n has value root.val, and the other child of n has value r.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_8 (root : Tree) (h : Pre root) :
      ∀ r : Std.I64,
        find_second_minimum_value root = ok r → r.val ≠ -1 →
          ∃ (rv : ℤ) (v : Std.I64) (l rr : Tree),
            rootVal root = some rv ∧
              IsSubtree (Tree.Node v l rr) root ∧
                l ≠ Tree.Null ∧
                  rr ≠ Tree.Null ∧
                    v.val = rv ∧
                      ((rootVal l = some rv ∧ rootVal rr = some r.val) ∨
                        (rootVal rr = some rv ∧ rootVal l = some r.val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∀ r : Std.I64,
          find_second_minimum_value root = ok r → r.val ≠ -1 →
            ∃ (rv : ℤ) (v : Std.I64) (l rr : Tree),
              rootVal root = some rv ∧
                IsSubtree (Tree.Node v l rr) root ∧
                  l ≠ Tree.Null ∧
                    rr ≠ Tree.Null ∧
                      v.val = rv ∧
                        ((rootVal l = some rv ∧ rootVal rr = some r.val) ∨
                          (rootVal rr = some rv ∧ rootVal l = some r.val))) := by
    sorry

  /-- Let S be the set of all node values in root, m = min S, and let C = { c | there exists an internal node n of root such that n.val = m, c is the value of one of n's two children, and c > m }. If C is empty, the function returns r = -1; otherwise it returns r = min C.
    Preconditions: root is a non-empty special binary tree: root != Tree.Null; every node of root has either zero or two children (a leaf is Node(v, Null, Null)); for every internal node n of root, n.val = min(n.left.val, n.right.val); every node value v satisfies 1 <= v <= 2^31 - 1; and root has at most 25 nodes. -/
  theorem spec_9 (root : Tree) (h : Pre root) :
      ∃ r : Std.I64,
        find_second_minimum_value root = ok r ∧
          ∀ m : ℤ, IsMin (values root) m →
            (childValsOfMin m root = ∅ → r.val = -1) ∧
            (childValsOfMin m root ≠ ∅ →
              ∃ c : ℤ,
                c ∈ childValsOfMin m root ∧ r.val = c ∧
                  ∀ d ∈ childValsOfMin m root, c ≤ d) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (h : Pre root), ∃ r : Std.I64,
          find_second_minimum_value root = ok r ∧
            ∀ m : ℤ, IsMin (values root) m →
              (childValsOfMin m root = ∅ → r.val = -1) ∧
              (childValsOfMin m root ≠ ∅ →
                ∃ c : ℤ,
                  c ∈ childValsOfMin m root ∧ r.val = c ∧
                    ∀ d ∈ childValsOfMin m root, c ≤ d)) := by
    sorry

  end AegisSpec.FindSecondMinimumValue
