import Aegis.CreateBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.CreateBinaryTree.create_binary_tree`

LeetCode problem `create-binary-tree-from-descriptions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CreateBinaryTree

noncomputable section

namespace Aegis.CreateBinaryTree.Tree

def label? : Tree → Option Int
  | Tree.Null => none
  | Tree.Node v _ _ => some v.val

def left : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node _ l _ => l

def right : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node _ _ r => r

def labels : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => l.labels ++ [v.val] ++ r.labels

def find? : Tree → Int → Option Tree
  | Tree.Null, _ => none
  | t@(Tree.Node v l r), x =>
    if v.val = x then some t
    else
      match l.find? x with
      | some u => some u
      | none => r.find? x

def parentOf? : Tree → Int → Option Tree
  | Tree.Null, _ => none
  | t@(Tree.Node _ l r), x =>
    if l.label? = some x ∨ r.label? = some x then some t
    else
      match l.parentOf? x with
      | some u => some u
      | none => r.parentOf? x

def depthOf? : Tree → Int → Option Nat
  | Tree.Null, _ => none
  | Tree.Node v l r, x =>
    if v.val = x then some 0
    else
      match l.depthOf? x with
      | some k => some (k + 1)
      | none =>
        match r.depthOf? x with
        | some k => some (k + 1)
        | none => none

def subtreeValues? (t : Tree) (x : Int) : Option (Finset Int) :=
  (t.find? x).map (fun u => u.labels.toFinset)

end Aegis.CreateBinaryTree.Tree

namespace AegisSpec.CreateBinaryTree

structure DescRow where

  parent : Int

  child : Int

  isLeft : Int

def rowOf (v : alloc.vec.Vec Std.I64) : Option DescRow :=
  match v.val with
  | [p, c, l] => some { parent := p.val, child := c.val, isLeft := l.val }
  | _ => none

def rows (d : Slice (alloc.vec.Vec Std.I64)) : List DescRow := d.val.filterMap rowOf

def rowAt (d : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option DescRow :=
  (d.val[i]?).bind rowOf

def valuesOf (rs : List DescRow) : Finset Int :=
  (rs.flatMap (fun r => [r.parent, r.child])).toFinset

def values (d : Slice (alloc.vec.Vec Std.I64)) : Finset Int := valuesOf (rows d)

def Edge (rs : List DescRow) (x y : Int) : Prop :=
  ∃ r ∈ rs, r.parent = x ∧ r.child = y

def Reaches (rs : List DescRow) (x y : Int) : Prop := Relation.ReflTransGen (Edge rs) x y

inductive PathOfLen (rs : List DescRow) : Int → Int → Nat → Prop where
  | nil (x : Int) : PathOfLen rs x x 0
  | cons {x y z : Int} {n : Nat} :
      Edge rs x y → PathOfLen rs y z n → PathOfLen rs x z (n + 1)

def EdgesFromRows (rs : List DescRow) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r =>
    (∀ c : Int, l.label? = some c →
        ∃ row ∈ rs, row.parent = v.val ∧ row.child = c ∧ row.isLeft = 1) ∧
      (∀ c : Int, r.label? = some c →
        ∃ row ∈ rs, row.parent = v.val ∧ row.child = c ∧ row.isLeft = 0) ∧
      EdgesFromRows rs l ∧ EdgesFromRows rs r

def InputOK (d : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ d.val.length ∧
    d.val.length ≤ 10 ^ 4 ∧
    (∀ (i : Nat) (v : alloc.vec.Vec Std.I64), d.val[i]? = some v → v.val.length = 3) ∧
    (∀ row, row ∈ rows d →
      1 ≤ row.parent ∧ row.parent ≤ 10 ^ 5 ∧
        1 ≤ row.child ∧ row.child ≤ 10 ^ 5 ∧ (row.isLeft = 0 ∨ row.isLeft = 1))

def TreeValid (d : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  (∀ (r₁ : DescRow), r₁ ∈ rows d → ∀ (r₂ : DescRow), r₂ ∈ rows d →
      r₁.child = r₂.child → r₁ = r₂) ∧
    (∀ (r₁ : DescRow), r₁ ∈ rows d → ∀ (r₂ : DescRow), r₂ ∈ rows d →
      r₁.parent = r₂.parent → r₁.isLeft = r₂.isLeft → r₁ = r₂) ∧
    (∀ (v : Int) (n : Nat), 0 < n → ¬ PathOfLen (rows d) v v n) ∧
    (∃ root ∈ values d,
      (∀ row, row ∈ rows d → row.child ≠ root) ∧
        ∀ v ∈ values d, Reaches (rows d) root v)

def ValidDescriptions (d : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  InputOK d ∧ TreeValid d

/-- Whenever create_binary_tree(descriptions) returns a result r, r is the unique binary tree T described by descriptions. Equivalently: the set of node labels of r is exactly V, with each v in V labeling exactly one node; the root of r is labeled root; for every i, if descriptions[i][2] = 1 then the node labeled descriptions[i][0] in r has as its immediate left child the node labeled descriptions[i][1], and if descriptions[i][2] = 0 then it has as its immediate right child the node labeled descriptions[i][1]; and for every v in V, if no row has parent v and isLeft 1 then the left child slot of the node labeled v is Tree.Null, and if no row has parent v and isLeft 0 then its right child slot is Tree.Null. Here immediate child means the root of the corresponding left or right subtree (Tree.Null if that subtree is Tree.Null).
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values (each value is a distinct node, every non-root value has exactly one parent, each parent has at most one left and at most one right child, and the parent-child graph is acyclic and connected with the unique parentless value as root). Let V be the set of all integers appearing in any row of descriptions (as descriptions[i][0] or descriptions[i][1]), and let root be the unique value in V that never occurs as descriptions[i][1]. -/
theorem spec_1 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    (∀ v : Int, v ∈ r.labels ↔ v ∈ values d) ∧
      r.labels.Nodup ∧
      (∀ root : Int, root ∈ values d →
        (∀ row, row ∈ rows d → row.child ≠ root) → r.label? = some root) ∧
      (∀ (i : Nat) (row : DescRow), rowAt d i = some row →
        ∃ n : Tree, r.find? row.parent = some n ∧
          (row.isLeft = 1 → n.left.label? = some row.child) ∧
          (row.isLeft = 0 → n.right.label? = some row.child)) ∧
      (∀ (v : Int) (n : Tree), v ∈ values d → r.find? v = some n →
        ((∀ row, row ∈ rows d → ¬ (row.parent = v ∧ row.isLeft = 1)) →
            n.left = Tree.Null) ∧
          ((∀ row, row ∈ rows d → ¬ (row.parent = v ∧ row.isLeft = 0)) →
            n.right = Tree.Null)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), (∀ v : Int, v ∈ r.labels ↔ v ∈ values d) ∧
      r.labels.Nodup ∧
      (∀ root : Int, root ∈ values d →
        (∀ row, row ∈ rows d → row.child ≠ root) → r.label? = some root) ∧
      (∀ (i : Nat) (row : DescRow), rowAt d i = some row →
        ∃ n : Tree, r.find? row.parent = some n ∧
          (row.isLeft = 1 → n.left.label? = some row.child) ∧
          (row.isLeft = 0 → n.right.label? = some row.child)) ∧
      (∀ (v : Int) (n : Tree), v ∈ values d → r.find? v = some n →
        ((∀ row, row ∈ rows d → ¬ (row.parent = v ∧ row.isLeft = 1)) →
            n.left = Tree.Null) ∧
          ((∀ row, row ∈ rows d → ¬ (row.parent = v ∧ row.isLeft = 0)) →
            n.right = Tree.Null))) := by
  sorry

/-- For every descriptions satisfying the precondition, create_binary_tree(descriptions) returns a result r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access).
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. -/
theorem spec_2 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d) :
    ∃ r : Tree, create_binary_tree d = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d), ∃ r : Tree, create_binary_tree d = ok r) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, the multiset of node labels of r is exactly V: every v in V labels exactly one node of r, and no node of r has a label outside V.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let V be the set of all integers appearing in any row of descriptions (as descriptions[i][0] or descriptions[i][1]). -/
theorem spec_3 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    r.labels.Nodup ∧ r.labels.toFinset = values d := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), r.labels.Nodup ∧ r.labels.toFinset = values d) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, r is not Tree.Null and the label of the root of r is root, the unique value in V that does not occur as descriptions[i][1] for any i.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let V be the set of all integers appearing in any row of descriptions, and let root be the unique value in V that does not occur as descriptions[i][1] for any i. -/
theorem spec_4 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    r ≠ Tree.Null ∧
      ∀ root : Int, root ∈ values d →
        (∀ row, row ∈ rows d → row.child ≠ root) → r.label? = some root := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), r ≠ Tree.Null ∧
      ∀ root : Int, root ∈ values d →
        (∀ row, row ∈ rows d → row.child ≠ root) → r.label? = some root) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, for every i with 0 <= i < len(descriptions), in r the node labeled descriptions[i][0] has the node labeled descriptions[i][1] as its immediate left child when descriptions[i][2] = 1, and as its immediate right child when descriptions[i][2] = 0.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. -/
theorem spec_5 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ n : Tree, r.find? row.parent = some n ∧
        (row.isLeft = 1 → n.left.label? = some row.child) ∧
        (row.isLeft = 0 → n.right.label? = some row.child) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ n : Tree, r.find? row.parent = some n ∧
        (row.isLeft = 1 → n.left.label? = some row.child) ∧
        (row.isLeft = 0 → n.right.label? = some row.child)) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, every immediate child edge in r comes from a row of descriptions: for every node v in r, if its immediate left child is a node u then there is an i with descriptions[i][0] = v, descriptions[i][1] = u, and descriptions[i][2] = 1; and if its immediate right child is a node u then there is an i with descriptions[i][0] = v, descriptions[i][1] = u, and descriptions[i][2] = 0.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. -/
theorem spec_6 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    EdgesFromRows (rows d) r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), EdgesFromRows (rows d) r) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, for every v in V, the node labeled v in r is a leaf (both its immediate left and right children are Tree.Null) if and only if v does not occur as descriptions[i][0] for any i.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let V be the set of all integers appearing in any row of descriptions. -/
theorem spec_7 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    ∀ v : Int, v ∈ values d →
      ((∃ n : Tree, r.find? v = some n ∧ n.left = Tree.Null ∧ n.right = Tree.Null) ↔
        ∀ row, row ∈ rows d → row.parent ≠ v) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), ∀ v : Int, v ∈ values d →
      ((∃ n : Tree, r.find? v = some n ∧ n.left = Tree.Null ∧ n.right = Tree.Null) ↔
        ∀ row, row ∈ rows d → row.parent ≠ v)) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r and create_binary_tree(d') returns a result r', we have r = r' (structural equality of Tree).
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let d' be any permutation of the rows of descriptions (the same multiset of rows in a different order); by the validity guarantee d' also satisfies the validity precondition. -/
theorem spec_8 (d d' : Slice (alloc.vec.Vec Std.I64))
    (hd : ValidDescriptions d) (hd' : ValidDescriptions d')
    (hperm : List.Perm d.val d'.val)
    (r r' : Tree) (hr : create_binary_tree d = ok r) (hr' : create_binary_tree d' = ok r') :
    r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (d d' : Slice (alloc.vec.Vec Std.I64))
    (hd : ValidDescriptions d) (hd' : ValidDescriptions d')
    (hperm : List.Perm d.val d'.val)
    (r r' : Tree) (hr : create_binary_tree d = ok r) (hr' : create_binary_tree d' = ok r'), r = r') := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, for every row i let c = descriptions[i][1]. The set of node labels in the subtree of r rooted at the node labeled c is exactly the set of all v in V such that v = c or there is a directed path from c to v in the graph whose edges are the parent-to-child pairs given by the rows (ignoring the isLeft labels).
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let V be the set of all integers appearing in any row of descriptions. -/
theorem spec_9 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ s : Finset Int, r.subtreeValues? row.child = some s ∧
        ∀ v : Int, v ∈ s ↔
          (v ∈ values d ∧ (v = row.child ∨ Reaches (rows d) row.child v)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ s : Finset Int, r.subtreeValues? row.child = some s ∧
        ∀ v : Int, v ∈ s ↔
          (v ∈ values d ∧ (v = row.child ∨ Reaches (rows d) row.child v))) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, for every v in V, the depth of the node labeled v in r (the number of edges on the path from the root of r to that node) equals the length of the unique directed path from root to v in the graph whose edges are the parent-to-child pairs given by the rows.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. Let V be the set of all integers appearing in any row of descriptions, and let root be the unique value in V that does not occur as descriptions[i][1] for any i. -/
theorem spec_10 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    ∀ (root v : Int), root ∈ values d →
      (∀ row, row ∈ rows d → row.child ≠ root) → v ∈ values d →
        ∃ n : Nat, r.depthOf? v = some n ∧ PathOfLen (rows d) root v n ∧
          ∀ k : Nat, PathOfLen (rows d) root v k → k = n := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), ∀ (root v : Int), root ∈ values d →
      (∀ row, row ∈ rows d → row.child ≠ root) → v ∈ values d →
        ∃ n : Nat, r.depthOf? v = some n ∧ PathOfLen (rows d) root v n ∧
          ∀ k : Nat, PathOfLen (rows d) root v k → k = n) := by
  sorry

/-- Whenever create_binary_tree(descriptions) returns a result r, for every i, the immediate parent in r of the node labeled descriptions[i][1] is the node labeled descriptions[i][0]; equivalently, every value that occurs as a child in descriptions has exactly that listed value as its parent in r.
  Preconditions: descriptions satisfies the problem constraints and validity guarantee: 1 <= len(descriptions) <= 10^4; every descriptions[i] has length 3; for each row [p,c,l], 1 <= p,c <= 10^5 and l in {0,1}; and the rows describe a valid binary tree of unique values. -/
theorem spec_11 (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r) :
    ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ p : Tree, r.parentOf? row.child = some p ∧ p.label? = some row.parent := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (d : Slice (alloc.vec.Vec Std.I64)) (hd : ValidDescriptions d)
    (r : Tree) (hr : create_binary_tree d = ok r), ∀ (i : Nat) (row : DescRow), rowAt d i = some row →
      ∃ p : Tree, r.parentOf? row.child = some p ∧ p.label? = some row.parent) := by
  sorry

end AegisSpec.CreateBinaryTree
