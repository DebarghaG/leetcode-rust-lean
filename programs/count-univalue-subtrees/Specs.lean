import Aegis.CountUnivalSubtrees.Code.Funs

/-!
# Specifications of `Aegis.CountUnivalSubtrees.count_unival_subtrees`

LeetCode problem `count-univalue-subtrees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.CountUnivalSubtrees

  namespace AegisSpec.CountUnivalSubtrees

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def leafCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ Tree.Null Tree.Null => 1
    | Tree.Node _ l r => leafCount l + leafCount r

  def valsIn : Tree → ℤ → ℤ → Prop
    | Tree.Null, _, _ => True
    | Tree.Node v l r, lo, hi =>
        (lo ≤ v.val ∧ v.val ≤ hi) ∧ valsIn l lo hi ∧ valsIn r lo hi

  def hasVal : Tree → Std.I64 → Prop
    | Tree.Null, _ => False
    | Tree.Node w l r, v => w.val = v.val ∨ hasVal l v ∨ hasVal r v

  def allEq : Tree → Std.I64 → Prop
    | Tree.Null, _ => True
    | Tree.Node w l r, v => w.val = v.val ∧ allEq l v ∧ allEq r v

  @[instance_reducible] def decAllEq : (t : Tree) → (v : Std.I64) → Decidable (allEq t v)
    | Tree.Null, _ => isTrue trivial
    | Tree.Node w l r, v =>
        match decAllEq l v, decAllEq r v with
        | isTrue hl, isTrue hr =>
            if h : w.val = v.val then isTrue ⟨h, hl, hr⟩
            else isFalse fun hc => h hc.1
        | isFalse hl, _ => isFalse fun hc => hl hc.2.1
        | _, isFalse hr => isFalse fun hc => hr hc.2.2

  attribute [instance] decAllEq

  def unival : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r => allEq l v ∧ allEq r v

  def univalCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node v l r =>
        (if allEq l v ∧ allEq r v then 1 else 0) + univalCount l + univalCount r

  def differsFrom (v : Std.I64) : Tree → Prop
    | Tree.Null => True
    | Tree.Node w _ _ => v.val ≠ w.val

  def childValsDiffer : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        differsFrom v l ∧ differsFrom v r ∧ childValsDiffer l ∧ childValsDiffer r

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def mapVals (f : Std.I64 → Std.I64) : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node (f v) (mapVals f l) (mapVals f r)

  /-- The function returns a result r, and r equals the number of Node occurrences n in root for which every node in the subtree rooted at n has the same value as n. If root is Null then r = 0.
    Preconditions: root has at most 1000 Node occurrences, and every Node value v satisfies -1000 <= v <= 1000. -/
  theorem spec_1 (root : Tree)
      (hsize : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000) :
      ∃ r : Std.I64,
        count_unival_subtrees root = ok r ∧ r.val = (univalCount root : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hsize : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000), ∃ r : Std.I64,
          count_unival_subtrees root = ok r ∧ r.val = (univalCount root : ℤ)) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail (no overflow, panic, or out-of-bounds access).
    Preconditions: root has at most 1000 Node occurrences; node values may be arbitrary 64-bit integers. -/
  theorem spec_2 (root : Tree)
      (hsize : nodeCount root ≤ 1000) :
      ∃ r : Std.I64, count_unival_subtrees root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hsize : nodeCount root ≤ 1000), ∃ r : Std.I64, count_unival_subtrees root = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= N, where N is the number of Node occurrences in root.
    Preconditions: root has at most 1000 Node occurrences; node values may be arbitrary 64-bit integers. -/
  theorem spec_3 (root : Tree)
      (hsize : nodeCount root ≤ 1000) :
      ∀ r : Std.I64,
        count_unival_subtrees root = ok r → 0 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hsize : nodeCount root ≤ 1000), ∀ r : Std.I64,
          count_unival_subtrees root = ok r → 0 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ)) := by
    sorry

  /-- The function returns a result r and r = N, where N is the number of Node occurrences in root.
    Preconditions: root has between 2 and 1000 Node occurrences, every Node value lies in [-1000, 1000], and any two Node occurrences in root have equal values. -/
  theorem spec_4 (root : Tree)
      (hsize_lo : 2 ≤ nodeCount root)
      (hsize_hi : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000)
      (hall : ∀ v₁ v₂ : Std.I64, hasVal root v₁ → hasVal root v₂ → v₁.val = v₂.val) :
      ∃ r : Std.I64,
        count_unival_subtrees root = ok r ∧ r.val = (nodeCount root : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ nodeCount root)
        (hsize_hi : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000)
        (hall : ∀ v₁ v₂ : Std.I64, hasVal root v₁ → hasVal root v₂ → v₁.val = v₂.val), ∃ r : Std.I64,
          count_unival_subtrees root = ok r ∧ r.val = (nodeCount root : ℤ)) := by
    sorry

  /-- The function returns a result r and r >= L, where L is the number of leaves in root, i.e. Node occurrences whose left and right children are both Null.
    Preconditions: root has at most 1000 Node occurrences and every Node value lies in [-1000, 1000]. -/
  theorem spec_5 (root : Tree)
      (hsize : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000) :
      ∃ r : Std.I64,
        count_unival_subtrees root = ok r ∧ (leafCount root : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hsize : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000), ∃ r : Std.I64,
          count_unival_subtrees root = ok r ∧ (leafCount root : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r_out. Let r_l be the result of count_unival_subtrees(l) and let r_r be the result of count_unival_subtrees(r); then r_out = r_l + r_r.
    Preconditions: root = Node(v, l, r) with at least one of l, r not Null; root has at most 1000 Node occurrences; every Node value lies in [-1000, 1000]; and every Node occurrence in l or r has a value different from v. -/
  theorem spec_6 (root : Tree) (v : Std.I64) (l r : Tree)
      (hroot : root = Tree.Node v l r)
      (hnonnull : l ≠ Tree.Null ∨ r ≠ Tree.Null)
      (hsize : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000)
      (hl : ∀ w : Std.I64, hasVal l w → w.val ≠ v.val)
      (hr : ∀ w : Std.I64, hasVal r w → w.val ≠ v.val) :
      ∃ r_out r_l r_r : Std.I64,
        count_unival_subtrees root = ok r_out ∧
        count_unival_subtrees l = ok r_l ∧
        count_unival_subtrees r = ok r_r ∧
        r_out.val = r_l.val + r_r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (l r : Tree)
        (hroot : root = Tree.Node v l r)
        (hnonnull : l ≠ Tree.Null ∨ r ≠ Tree.Null)
        (hsize : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000)
        (hl : ∀ w : Std.I64, hasVal l w → w.val ≠ v.val)
        (hr : ∀ w : Std.I64, hasVal r w → w.val ≠ v.val), ∃ r_out r_l r_r : Std.I64,
          count_unival_subtrees root = ok r_out ∧
          count_unival_subtrees l = ok r_l ∧
          count_unival_subtrees r = ok r_r ∧
          r_out.val = r_l.val + r_r.val) := by
    sorry

  /-- Let mirror(root) be the tree obtained recursively by replacing each Node(v, l, r) with Node(v, mirror(r), mirror(l)) and leaving Null as Null. If the function returns r on root and r_m on mirror(root), then r = r_m.
    Preconditions: root has at most 1000 Node occurrences; node values may be arbitrary 64-bit integers. -/
  theorem spec_7 (root : Tree)
      (hsize : nodeCount root ≤ 1000) :
      ∀ r r_m : Std.I64,
        count_unival_subtrees root = ok r →
        count_unival_subtrees (mirror root) = ok r_m → r.val = r_m.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hsize : nodeCount root ≤ 1000), ∀ r r_m : Std.I64,
          count_unival_subtrees root = ok r →
          count_unival_subtrees (mirror root) = ok r_m → r.val = r_m.val) := by
    sorry

  /-- If the function returns r on root and r_f on T_f, then r = r_f.
    Preconditions: root has at most 1000 Node occurrences; f is an injective function from the set of node values occurring in root into the set of 64-bit integers. Let T_f be obtained by replacing each Node value v with f(v). -/
  theorem spec_8 (root : Tree) (f : Std.I64 → Std.I64)
      (hsize : nodeCount root ≤ 1000)
      (hinj : ∀ v₁ v₂ : Std.I64,
        hasVal root v₁ → hasVal root v₂ → (f v₁).val = (f v₂).val → v₁.val = v₂.val) :
      ∀ r r_f : Std.I64,
        count_unival_subtrees root = ok r →
        count_unival_subtrees (mapVals f root) = ok r_f → r.val = r_f.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (f : Std.I64 → Std.I64)
        (hsize : nodeCount root ≤ 1000)
        (hinj : ∀ v₁ v₂ : Std.I64,
          hasVal root v₁ → hasVal root v₂ → (f v₁).val = (f v₂).val → v₁.val = v₂.val), ∀ r r_f : Std.I64,
          count_unival_subtrees root = ok r →
          count_unival_subtrees (mapVals f root) = ok r_f → r.val = r_f.val) := by
    sorry

  /-- The function returns a result r and r = L, where L is the number of leaves in root (Node occurrences whose left and right children are both Null).
    Preconditions: root has at least 2 and at most 1000 Node occurrences, every Node value lies in [-1000, 1000], and for every Node occurrence n with a non-Null child c, the value of n differs from the value of c. -/
  theorem spec_9 (root : Tree)
      (hsize_lo : 2 ≤ nodeCount root)
      (hsize_hi : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000)
      (hdiff : childValsDiffer root) :
      ∃ r : Std.I64,
        count_unival_subtrees root = ok r ∧ r.val = (leafCount root : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hsize_lo : 2 ≤ nodeCount root)
        (hsize_hi : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000)
        (hdiff : childValsDiffer root), ∃ r : Std.I64,
          count_unival_subtrees root = ok r ∧ r.val = (leafCount root : ℤ)) := by
    sorry

  /-- The function returns a result r_out. Let r_r be the result of count_unival_subtrees(r). Then r_out = r_r + 1 if every Node occurrence in r has value v, and r_out = r_r otherwise.
    Preconditions: root = Node(v, Null, r) with r not Null; root has at most 1000 Node occurrences; every Node value lies in [-1000, 1000]. -/
  theorem spec_10 (root : Tree) (v : Std.I64) (r : Tree)
      (hroot : root = Tree.Node v Tree.Null r)
      (hne : r ≠ Tree.Null)
      (hsize : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000) :
      ∃ r_out r_r : Std.I64,
        count_unival_subtrees root = ok r_out ∧
        count_unival_subtrees r = ok r_r ∧
        r_out.val = (if allEq r v then r_r.val + 1 else r_r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (r : Tree)
        (hroot : root = Tree.Node v Tree.Null r)
        (hne : r ≠ Tree.Null)
        (hsize : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000), ∃ r_out r_r : Std.I64,
          count_unival_subtrees root = ok r_out ∧
          count_unival_subtrees r = ok r_r ∧
          r_out.val = (if allEq r v then r_r.val + 1 else r_r.val)) := by
    sorry

  /-- The function returns a result r_out. Let r_l be the result of count_unival_subtrees(l) and let r_r be the result of count_unival_subtrees(r). Let AllEq_v(l) mean every Node occurrence in l has value v, with AllEq_v(Null) true, and define AllEq_v(r) similarly. Then r_out = r_l + r_r + 1 if AllEq_v(l) and AllEq_v(r), and r_out = r_l + r_r otherwise.
    Preconditions: root = Node(v, l, r); root has at most 1000 Node occurrences; every Node value lies in [-1000, 1000]. -/
  theorem spec_11 (root : Tree) (v : Std.I64) (l r : Tree)
      (hroot : root = Tree.Node v l r)
      (hsize : nodeCount root ≤ 1000)
      (hvals : valsIn root (-1000) 1000) :
      ∃ r_out r_l r_r : Std.I64,
        count_unival_subtrees root = ok r_out ∧
        count_unival_subtrees l = ok r_l ∧
        count_unival_subtrees r = ok r_r ∧
        r_out.val =
          (if allEq l v ∧ allEq r v then r_l.val + r_r.val + 1 else r_l.val + r_r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (l r : Tree)
        (hroot : root = Tree.Node v l r)
        (hsize : nodeCount root ≤ 1000)
        (hvals : valsIn root (-1000) 1000), ∃ r_out r_l r_r : Std.I64,
          count_unival_subtrees root = ok r_out ∧
          count_unival_subtrees l = ok r_l ∧
          count_unival_subtrees r = ok r_r ∧
          r_out.val =
            (if allEq l v ∧ allEq r v then r_l.val + r_r.val + 1 else r_l.val + r_r.val)) := by
    sorry

  end AegisSpec.CountUnivalSubtrees
