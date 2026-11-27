import Aegis.Rob.Code.Funs

/-!
# Specifications of `Aegis.Rob.rob`

LeetCode problem `house-robber-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Rob

  open Aegis.Rob

  def IsFiniteTree (_t : Tree) : Prop := True

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => nodeCount l + nodeCount r + 1

  def nodeValues : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

  def ValuesBounded (t : Tree) : Prop := ∀ v ∈ nodeValues t, 0 ≤ v ∧ v ≤ 10000

  def ValuesNonneg (t : Tree) : Prop := ∀ v ∈ nodeValues t, 0 ≤ v

  def rootValue : Tree → ℤ
    | Tree.Null => 0
    | Tree.Node v _ _ => v.val

  def totalSum (t : Tree) : ℤ := (nodeValues t).sum

  def SubtreeAt : Tree → List Bool → Option Tree
    | t, [] => some t
    | Tree.Null, _ :: _ => none
    | Tree.Node _ l _, true :: bs => SubtreeAt l bs
    | Tree.Node _ _ r, false :: bs => SubtreeAt r bs

  def NodePositions : Tree → Finset (List Bool)
    | Tree.Null => ∅
    | Tree.Node _ l r =>
        insert [] ((NodePositions l).image (fun p => [true] ++ p) ∪
                   (NodePositions r).image (fun p => [false] ++ p))

  def IsNodeAt (t : Tree) (p : List Bool) : Prop :=
    ∃ v l r, SubtreeAt t p = some (Tree.Node v l r)

  def NodeValueAt (t : Tree) (p : List Bool) : ℤ :=
    match SubtreeAt t p with
    | some (Tree.Node v _ _) => v.val
    | _ => 0

  def IsNodeSet (t : Tree) (S : Finset (List Bool)) : Prop := ∀ p ∈ S, IsNodeAt t p

  def Linked (p q : List Bool) : Prop := q = p ++ [true] ∨ q = p ++ [false]

  def Independent (S : Finset (List Bool)) : Prop := ∀ p ∈ S, ∀ q ∈ S, ¬ Linked p q

  instance instDecidableIndependent (S : Finset (List Bool)) : Decidable (Independent S) :=
    decidable_of_iff
      (∀ p ∈ S, ∀ q ∈ S, ¬ (q = p ++ [true] ∨ q = p ++ [false])) Iff.rfl

  def setSum (t : Tree) (S : Finset (List Bool)) : ℤ := ∑ p ∈ S, NodeValueAt t p

  def indepNodeSets (t : Tree) : Finset (Finset (List Bool)) :=
    (NodePositions t).powerset.filter (fun S => Independent S)

  noncomputable def best (t : Tree) : ℤ :=
    (indepNodeSets t).toList.foldr (fun S acc => max (setSum t S) acc) 0

  def Mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (Mirror r) (Mirror l)

  def SameShape : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node _ l₁ r₁, Tree.Node _ l₂ r₂ => SameShape l₁ l₂ ∧ SameShape r₁ r₂
    | _, _ => False

  def AllCorresponding (R : ℤ → ℤ → Prop) : Tree → Tree → Prop
    | Tree.Null, Tree.Null => True
    | Tree.Node v₁ l₁ r₁, Tree.Node v₂ l₂ r₂ =>
        R v₁.val v₂.val ∧ AllCorresponding R l₁ l₂ ∧ AllCorresponding R r₁ r₂
    | _, _ => False

  def zeroLeaf : Tree := Tree.Node 0#i64 Tree.Null Tree.Null

  inductive AddZeroLeaf : Tree → Tree → Prop where
    | left {v l r} (h : l = Tree.Null) :
        AddZeroLeaf (Tree.Node v l r) (Tree.Node v zeroLeaf r)
    | right {v l r} (h : r = Tree.Null) :
        AddZeroLeaf (Tree.Node v l r) (Tree.Node v l zeroLeaf)
    | in_left {v l r l'} (h : AddZeroLeaf l l') :
        AddZeroLeaf (Tree.Node v l r) (Tree.Node v l' r)
    | in_right {v l r r'} (h : AddZeroLeaf r r') :
        AddZeroLeaf (Tree.Node v l r) (Tree.Node v l r')

  /-- Let best(T) be the maximum, over all sets S of nodes of T such that no two nodes in S are directly linked (one is the parent of the other), of the sum of the values of the nodes in S, and let best(Null) = 0. The function returns a result r and r = best(root).
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_1 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∃ res : I64, rob root = ok res ∧ res.val = best root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∃ res : I64, rob root = ok res ∧ res.val = best root) := by
    sorry

  /-- The function returns some result r; it does not fail because of overflow, out-of-bounds access, or a panic.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_2 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∃ res : I64, rob root = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∃ res : I64, rob root = ok res) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set S of nodes of root such that no two nodes in S are directly linked (one is the parent of the other) and the sum of the values of the nodes in S is exactly r.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_3 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∀ res : I64, rob root = ok res →
        ∃ S : Finset (List Bool), IsNodeSet root S ∧ Independent S ∧ setSum root S = res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∀ res : I64, rob root = ok res →
          ∃ S : Finset (List Bool), IsNodeSet root S ∧ Independent S ∧ setSum root S = res.val) := by
    sorry

  /-- Whenever the function returns a result r, for every set S of nodes of root such that no two nodes in S are directly linked (one is the parent of the other), the sum of the values of the nodes in S is at most r.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_4 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∀ res : I64, rob root = ok res →
        ∀ S : Finset (List Bool), IsNodeSet root S → Independent S → setSum root S ≤ res.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∀ res : I64, rob root = ok res →
          ∀ S : Finset (List Bool), IsNodeSet root S → Independent S → setSum root S ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_5 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∀ res : I64, rob root = ok res → 0 ≤ res.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∀ res : I64, rob root = ok res → 0 ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at most the sum of the values of all nodes of root.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_6 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∀ res : I64, rob root = ok res → res.val ≤ totalSum root := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∀ res : I64, rob root = ok res → res.val ≤ totalSum root) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the value of the root node.
    Preconditions: root is a finite tree that is not Null, has at most 10^4 nodes, and every node value is an integer v with 0 <= v <= 10^4. -/
  theorem spec_7 (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
      (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root) :
      ∀ res : I64, rob root = ok res → rootValue root ≤ res.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (hfin : IsFiniteTree root) (hne : root ≠ Tree.Null)
        (hcount : nodeCount root ≤ 10000) (hbounded : ValuesBounded root), ∀ res : I64, rob root = ok res → rootValue root ≤ res.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= best(left) + best(right), where best(T) is defined as in spec_1 and best(Null) = 0.
    Preconditions: root = Node(v, left, right), where left and right are finite trees, and every node value in root is an integer in [0,10^4]. -/
  theorem spec_8 (v : I64) (left right : Tree) (hfinl : IsFiniteTree left)
      (hfinr : IsFiniteTree right) (hfin : IsFiniteTree (Tree.Node v left right))
      (hbounded : ValuesBounded (Tree.Node v left right)) :
      ∀ res : I64, rob (Tree.Node v left right) = ok res → best left + best right ≤ res.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (v : I64) (left right : Tree) (hfinl : IsFiniteTree left)
        (hfinr : IsFiniteTree right) (hfin : IsFiniteTree (Tree.Node v left right))
        (hbounded : ValuesBounded (Tree.Node v left right)), ∀ res : I64, rob (Tree.Node v left right) = ok res → best left + best right ≤ res.val) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: root = Null. -/
  theorem spec_9 (root : Tree) (h : root = Tree.Null) :
      ∃ res : I64, rob root = ok res ∧ res.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (h : root = Tree.Null), ∃ res : I64, rob root = ok res ∧ res.val = 0) := by
    sorry

  /-- Whenever the function returns results r1 on t1 and r2 on t2, r1 <= r2.
    Preconditions: t1 and t2 are finite trees with the same shape (the same positions of Null and Node), and for every corresponding node x in t1 and x' in t2, 0 <= value(x) <= value(x') <= 10^4. -/
  theorem spec_10 (t₁ t₂ : Tree) (hfin₁ : IsFiniteTree t₁) (hfin₂ : IsFiniteTree t₂)
      (hshape : SameShape t₁ t₂)
      (hcorr : AllCorresponding (fun a b => 0 ≤ a ∧ a ≤ b ∧ b ≤ 10000) t₁ t₂) :
      ∀ r₁ r₂ : I64, rob t₁ = ok r₁ → rob t₂ = ok r₂ → r₁.val ≤ r₂.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (t₁ t₂ : Tree) (hfin₁ : IsFiniteTree t₁) (hfin₂ : IsFiniteTree t₂)
        (hshape : SameShape t₁ t₂)
        (hcorr : AllCorresponding (fun a b => 0 ≤ a ∧ a ≤ b ∧ b ≤ 10000) t₁ t₂), ∀ r₁ r₂ : I64, rob t₁ = ok r₁ → rob t₂ = ok r₂ → r₁.val ≤ r₂.val) := by
    sorry

  /-- Whenever the function returns a result r on t and a result r' on mirror(t), r = r'.
    Preconditions: t is a finite tree with all node values in [0,10^4], and mirror(t) is the tree obtained by recursively swapping left and right children at every node. -/
  theorem spec_11 (t : Tree) (hfin : IsFiniteTree t) (hbounded : ValuesBounded t) :
      ∀ r r' : I64, rob t = ok r → rob (Mirror t) = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (t : Tree) (hfin : IsFiniteTree t) (hbounded : ValuesBounded t), ∀ r r' : I64, rob t = ok r → rob (Mirror t) = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r on t and a result r' on t', r' = c * r.
    Preconditions: t and t' are finite trees with the same shape; c is an integer with c >= 0; for every corresponding node, value_t'(x) = c * value_t(x); every value in t is nonnegative; and every value in t' lies in [0,10^4]. -/
  theorem spec_12 (t t' : Tree) (c : ℤ) (hfin : IsFiniteTree t) (hfin' : IsFiniteTree t')
      (hshape : SameShape t t') (hc : 0 ≤ c)
      (hcorr : AllCorresponding (fun a b => b = c * a) t t')
      (hnonneg : ValuesNonneg t) (hbounded : ValuesBounded t') :
      ∀ r r' : I64, rob t = ok r → rob t' = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (t t' : Tree) (c : ℤ) (hfin : IsFiniteTree t) (hfin' : IsFiniteTree t')
        (hshape : SameShape t t') (hc : 0 ≤ c)
        (hcorr : AllCorresponding (fun a b => b = c * a) t t')
        (hnonneg : ValuesNonneg t) (hbounded : ValuesBounded t'), ∀ r r' : I64, rob t = ok r → rob t' = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever the function returns a result r on t and a result r' on t', r = r'.
    Preconditions: t is a finite tree with all node values in [0,10^4], and t' is obtained from t by choosing a node that has a Null child and replacing that Null child with a new leaf Node(0, Null, Null). -/
  theorem spec_13 (t t' : Tree) (hfin : IsFiniteTree t) (hbounded : ValuesBounded t)
      (h : AddZeroLeaf t t') :
      ∀ r r' : I64, rob t = ok r → rob t' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (t t' : Tree) (hfin : IsFiniteTree t) (hbounded : ValuesBounded t)
        (h : AddZeroLeaf t t'), ∀ r r' : I64, rob t = ok r → rob t' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.Rob
