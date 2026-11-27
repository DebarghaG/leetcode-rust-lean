import Aegis.FlipEquiv.Code.Funs

/-!
# Specifications of `Aegis.FlipEquiv.flip_equiv`

LeetCode problem `flip-equivalent-binary-trees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FlipEquiv

  open Aegis.FlipEquiv

  def values : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def node_count : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + node_count l + node_count r

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (height l) (height r)

  def countAtDepth : Tree → Nat → ℤ → Nat
    | Tree.Null, _, _ => 0
    | Tree.Node v _ _, 0, x => if v.val = x then 1 else 0
    | Tree.Node _ l r, d + 1, x => countAtDepth l d x + countAtDepth r d x

  def SmallTree (t : Tree) : Prop := node_count t ≤ 100

  def InValueRange (t : Tree) : Prop := ∀ x ∈ values t, 0 ≤ x ∧ x ≤ 99

  def ValuesDistinct (t : Tree) : Prop := (values t).Nodup

  def ProblemConstraints (t : Tree) : Prop :=
    SmallTree t ∧ InValueRange t ∧ ValuesDistinct t

  inductive FlipEquivRel : Tree → Tree → Prop where
    | null : FlipEquivRel Tree.Null Tree.Null
    | node {v : I64} {l1 r1 l2 r2 : Tree}
        (hl : FlipEquivRel l1 l2) (hr : FlipEquivRel r1 r2) :
        FlipEquivRel (Tree.Node v l1 r1) (Tree.Node v l2 r2)
    | nodeCross {v : I64} {l1 r1 l2 r2 : Tree}
        (hl : FlipEquivRel l1 r2) (hr : FlipEquivRel r1 l2) :
        FlipEquivRel (Tree.Node v l1 r1) (Tree.Node v l2 r2)

  inductive FlipStep : Tree → Tree → Prop where
    | root (v : I64) (l r : Tree) :
        FlipStep (Tree.Node v l r) (Tree.Node v r l)
    | left {v : I64} {l l' r : Tree} :
        FlipStep l l' → FlipStep (Tree.Node v l r) (Tree.Node v l' r)
    | right {v : I64} {l r r' : Tree} :
        FlipStep r r' → FlipStep (Tree.Node v l r) (Tree.Node v l r')

  def FlipReachable : Tree → Tree → Prop := Relation.ReflTransGen FlipStep

  /-- Let FlipEquiv be the least relation on Tree defined by: (i) FlipEquiv(Null, Null) holds; (ii) FlipEquiv(Node(v,l1,r1), Node(w,l2,r2)) holds iff v = w and either (FlipEquiv(l1,l2) and FlipEquiv(r1,r2)) or (FlipEquiv(l1,r2) and FlipEquiv(r1,l2)); (iii) no other pairs are related. Whenever flip_equiv root1 root2 returns Result.ok b with b a Boolean, b = true if and only if FlipEquiv(root1, root2) holds, and b = false otherwise.
    Preconditions: root1 and root2 are finite binary trees represented by Tree and satisfy the problem constraints: each has at most 100 nodes, and all node values within any one tree are distinct integers in [0,99]. -/
  theorem spec_1 (root1 root2 : Tree)
      (h1 : ProblemConstraints root1) (h2 : ProblemConstraints root2) :
      ∃ b : Bool, flip_equiv root1 root2 = ok b ∧ (b = true ↔ FlipEquivRel root1 root2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root1 root2 : Tree)
        (h1 : ProblemConstraints root1) (h2 : ProblemConstraints root2), ∃ b : Bool, flip_equiv root1 root2 = ok b ∧ (b = true ↔ FlipEquivRel root1 root2)) := by
    sorry

  /-- The call flip_equiv root1 root2 does not fail: it returns Result.ok b for some Boolean b. In particular, there is no overflow, out-of-bounds access, or panic.
    Preconditions: root1 and root2 are finite binary trees represented by Tree and satisfy the problem constraints. -/
  theorem spec_2 (root1 root2 : Tree)
      (h1 : ProblemConstraints root1) (h2 : ProblemConstraints root2) :
      ∃ b : Bool, flip_equiv root1 root2 = ok b := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root1 root2 : Tree)
        (h1 : ProblemConstraints root1) (h2 : ProblemConstraints root2), ∃ b : Bool, flip_equiv root1 root2 = ok b) := by
    sorry

  /-- flip_equiv Null t returns Result.ok false.
    Preconditions: t is a non-null finite Tree, i.e. t = Node(v,l,r) for some i64 v and finite subtrees l and r. -/
  theorem spec_3 (v : I64) (l r : Tree) :
      flip_equiv Tree.Null (Tree.Node v l r) = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (v : I64) (l r : Tree), flip_equiv Tree.Null (Tree.Node v l r) = ok false) := by
    sorry

  /-- flip_equiv t t returns Result.ok true.
    Preconditions: t is a finite Tree. -/
  theorem spec_4 (t : Tree) :
      flip_equiv t t = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (t : Tree), flip_equiv t t = ok true) := by
    sorry

  /-- For every Boolean ba and bb, if flip_equiv a b returns Result.ok ba and flip_equiv b a returns Result.ok bb, then ba = bb. Equivalently, flip_equiv a b returns Result.ok true exactly when flip_equiv b a returns Result.ok true.
    Preconditions: a and b are finite Trees. -/
  theorem spec_5 (a b : Tree) :
      ∀ (ba bb : Bool), flip_equiv a b = ok ba → flip_equiv b a = ok bb → ba = bb := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a b : Tree), ∀ (ba bb : Bool), flip_equiv a b = ok ba → flip_equiv b a = ok bb → ba = bb) := by
    sorry

  /-- If flip_equiv a b returns Result.ok true and flip_equiv b c returns Result.ok true, then flip_equiv a c returns Result.ok true.
    Preconditions: a, b, and c are finite Trees. -/
  theorem spec_6 (a b c : Tree) :
      flip_equiv a b = ok true → flip_equiv b c = ok true →
        flip_equiv a c = ok true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Tree), flip_equiv a b = ok true → flip_equiv b c = ok true →
          flip_equiv a c = ok true) := by
    sorry

  /-- flip_equiv (Node(v,l1,r1)) (Node(w,l2,r2)) returns Result.ok false.
    Preconditions: v and w are i64 integers with v ≠ w; l1, r1, l2, r2 are finite Trees. -/
  theorem spec_7 (v w : I64) (l1 r1 l2 r2 : Tree) (h : v ≠ w) :
      flip_equiv (Tree.Node v l1 r1) (Tree.Node w l2 r2) = ok false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (v w : I64) (l1 r1 l2 r2 : Tree) (h : v ≠ w), flip_equiv (Tree.Node v l1 r1) (Tree.Node w l2 r2) = ok false) := by
    sorry

  /-- flip_equiv (Node(v,Null,Null)) t returns Result.ok true if and only if t = Node(v,Null,Null).
    Preconditions: v is an i64 integer; t is a finite Tree. -/
  theorem spec_8 (v : I64) (t : Tree) :
      flip_equiv (Tree.Node v Tree.Null Tree.Null) t = ok true ↔
        t = Tree.Node v Tree.Null Tree.Null := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v : I64) (t : Tree), flip_equiv (Tree.Node v Tree.Null Tree.Null) t = ok true ↔
          t = Tree.Node v Tree.Null Tree.Null) := by
    sorry

  /-- If flip_equiv l1 l2 returns Result.ok true and flip_equiv r1 r2 returns Result.ok true, then flip_equiv (Node(v,l1,r1)) (Node(v,l2,r2)) returns Result.ok true.
    Preconditions: v is an i64 integer; l1, r1, l2, r2 are finite Trees; the constructed trees Node(v,l1,r1) and Node(v,l2,r2) satisfy the problem constraints. -/
  theorem spec_9 (v : I64) (l1 r1 l2 r2 : Tree)
      (hc1 : ProblemConstraints (Tree.Node v l1 r1))
      (hc2 : ProblemConstraints (Tree.Node v l2 r2))
      (h1 : flip_equiv l1 l2 = ok true) (h2 : flip_equiv r1 r2 = ok true) :
      flip_equiv (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (v : I64) (l1 r1 l2 r2 : Tree)
        (hc1 : ProblemConstraints (Tree.Node v l1 r1))
        (hc2 : ProblemConstraints (Tree.Node v l2 r2))
        (h1 : flip_equiv l1 l2 = ok true) (h2 : flip_equiv r1 r2 = ok true), flip_equiv (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true) := by
    sorry

  /-- If flip_equiv l1 r2 returns Result.ok true and flip_equiv r1 l2 returns Result.ok true, then flip_equiv (Node(v,l1,r1)) (Node(v,l2,r2)) returns Result.ok true.
    Preconditions: v is an i64 integer; l1, r1, l2, r2 are finite Trees; the constructed trees Node(v,l1,r1) and Node(v,l2,r2) satisfy the problem constraints. -/
  theorem spec_10 (v : I64) (l1 r1 l2 r2 : Tree)
      (hc1 : ProblemConstraints (Tree.Node v l1 r1))
      (hc2 : ProblemConstraints (Tree.Node v l2 r2))
      (h1 : flip_equiv l1 r2 = ok true) (h2 : flip_equiv r1 l2 = ok true) :
      flip_equiv (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (v : I64) (l1 r1 l2 r2 : Tree)
        (hc1 : ProblemConstraints (Tree.Node v l1 r1))
        (hc2 : ProblemConstraints (Tree.Node v l2 r2))
        (h1 : flip_equiv l1 r2 = ok true) (h2 : flip_equiv r1 l2 = ok true), flip_equiv (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true) := by
    sorry

  /-- If flip_equiv root1 root2 returns Result.ok true, then node_count(root1) = node_count(root2), where node_count(Null) = 0 and node_count(Node(_,l,r)) = 1 + node_count(l) + node_count(r).
    Preconditions: root1 and root2 are finite Trees. -/
  theorem spec_11 (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true) :
      node_count root1 = node_count root2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true), node_count root1 = node_count root2) := by
    sorry

  /-- If flip_equiv root1 root2 returns Result.ok true, then for every integer d ≥ 0 and every i64 value v, the number of nodes of value v at depth d in root1 equals the number of nodes of value v at depth d in root2, where the root has depth 0.
    Preconditions: root1 and root2 are finite Trees. -/
  theorem spec_12 (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true) :
      ∀ (d : Nat) (v : I64), countAtDepth root1 d v.val = countAtDepth root2 d v.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true), ∀ (d : Nat) (v : I64), countAtDepth root1 d v.val = countAtDepth root2 d v.val) := by
    sorry

  /-- Whenever flip_equiv root1 root2 returns Result.ok b with b a Boolean, b = true if and only if there exists a finite sequence, possibly empty, of flip operations, each replacing some node Node(v,L,R) by Node(v,R,L) within its containing tree, that transforms root1 into root2.
    Preconditions: root1 and root2 are finite Trees. -/
  theorem spec_13 (root1 root2 : Tree) :
      ∀ (b : Bool), flip_equiv root1 root2 = ok b →
        (b = true ↔ FlipReachable root1 root2) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (root1 root2 : Tree), ∀ (b : Bool), flip_equiv root1 root2 = ok b →
          (b = true ↔ FlipReachable root1 root2)) := by
    sorry

  /-- If flip_equiv root1 root2 returns Result.ok true, then height(root1) = height(root2), where height(Null) = 0 and height(Node(_,l,r)) = 1 + max(height(l), height(r)).
    Preconditions: root1 and root2 are finite Trees. -/
  theorem spec_14 (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true) :
      height root1 = height root2 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (root1 root2 : Tree) (h : flip_equiv root1 root2 = ok true), height root1 = height root2) := by
    sorry

  end AegisSpec.FlipEquiv
