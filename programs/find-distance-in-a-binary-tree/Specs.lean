import Aegis.FindDistance.Code.Funs

/-!
# Specifications of `Aegis.FindDistance.find_distance`

LeetCode problem `find-distance-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  set_option autoImplicit false

  namespace AegisSpec.FindDistance

  open Aegis.FindDistance

  def NodeVals : Tree → List Int
    | .Null => []
    | .Node v l r => v.val :: (NodeVals l ++ NodeVals r)

  def Occurs (t : Tree) (x : Int) : Prop := x ∈ NodeVals t

  def DistinctVals (t : Tree) : Prop := (NodeVals t).Nodup

  def nodeCount : Tree → Nat
    | .Null => 0
    | .Node _ l r => nodeCount l + nodeCount r + 1

  def rootVal : Tree → Option Int
    | .Null => none
    | .Node v _ _ => some v.val

  def Edge : Tree → Int → Int → Prop
    | .Null, _, _ => False
    | .Node v l r, x, y =>
        (x = v.val ∧ (rootVal l = some y ∨ rootVal r = some y)) ∨ Edge l x y ∨ Edge r x y

  def Adj (t : Tree) (x y : Int) : Prop := Edge t x y ∨ Edge t y x

  def Walks (t : Tree) (x y : Int) : Nat → Prop
    | 0 => x = y
    | k + 1 => ∃ z : Int, Adj t x z ∧ Walks t z y k

  def Descends (t : Tree) (x y : Int) : Nat → Prop
    | 0 => x = y
    | k + 1 => ∃ z : Int, Edge t x z ∧ Descends t z y k

  def Ancestor (t : Tree) (x y : Int) : Prop := ∃ k : Nat, Descends t x y k

  def depthOpt : Tree → Int → Option Nat
    | .Null, _ => none
    | .Node v l r, x =>
        if v.val = x then some 0
        else
          match depthOpt l x with
          | some d => some (d + 1)
          | none => (depthOpt r x).map (fun d => d + 1)

  def depth (t : Tree) (x : Int) : Nat := (depthOpt t x).getD 0

  def IsDistance (t : Tree) (x y : Int) (k : Nat) : Prop :=
    Walks t x y k ∧ ∀ j : Nat, j < k → ¬ Walks t x y j

  def IsLCA (t : Tree) (p q x : Int) : Prop :=
    Ancestor t x p ∧ Ancestor t x q ∧
      ∀ y : Int, Ancestor t y p → Ancestor t y q → depth t y ≤ depth t x

  def absDiff (a b : Nat) : Int := if a ≤ b then (b : Int) - (a : Int) else (a : Int) - (b : Int)

  /-- Whenever find_distance(root, p, q) returns a result r, r equals the distance between the node of value p and the node of value q, defined as the least k >= 0 for which there exist values v_0, ..., v_k with v_0 = p, v_k = q, and for every i with 0 <= i < k the nodes of value v_i and v_{i+1} are joined by a parent-child edge in root (one is the parent of the other).
    Preconditions: root is a binary tree in which p and q each occur as the value of some node (i.e., there is a node of root with value p and a node of root with value q), and all node values of root are distinct. -/
  theorem spec_1 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      ∃ k : Nat, r.val = (k : Int) ∧ IsDistance root p.val q.val k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r : Std.I64) (hr : find_distance root p q = ok r), ∃ k : Nat, r.val = (k : Int) ∧ IsDistance root p.val q.val k) := by
    sorry

  /-- find_distance(root, p, q) returns a result r (it does not fail).
    Preconditions: root has between 1 and 10^4 nodes, every node value is in the range [0, 10^9], all node values of root are distinct, and p and q each occur as the value of some node of root. -/
  theorem spec_2 (root : Tree) (p q : Std.I64)
      (hsize : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10 ^ 4)
      (hval : ∀ x : Int, x ∈ NodeVals root → 0 ≤ x ∧ x ≤ 10 ^ 9)
      (hnd : DistinctVals root) (hp : Occurs root p.val) (hq : Occurs root q.val) :
      ∃ r : Std.I64, find_distance root p q = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hsize : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10 ^ 4)
        (hval : ∀ x : Int, x ∈ NodeVals root → 0 ≤ x ∧ x ≤ 10 ^ 9)
        (hnd : DistinctVals root) (hp : Occurs root p.val) (hq : Occurs root q.val), ∃ r : Std.I64, find_distance root p q = ok r) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r, r <= N(root) - 1, where N(root) is the number of nodes of root.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_3 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val ≤ (nodeCount root : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val ≤ (nodeCount root : Int) - 1) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r, r <= depth(root, p) + depth(root, q), where depth(T, v) is the number of edges on the unique path from the root of T down to the node of value v.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_4 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val ≤ (depth root p.val : Int) + (depth root q.val : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val ≤ (depth root p.val : Int) + (depth root q.val : Int)) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r, r >= |depth(root, p) - depth(root, q)|, where depth(T, v) is the number of edges on the unique path from the root of T down to the node of value v.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_5 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      absDiff (depth root p.val) (depth root q.val) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r : Std.I64) (hr : find_distance root p q = ok r), absDiff (depth root p.val) (depth root q.val) ≤ r.val) := by
    sorry

  /-- If the node of value p is the parent of the node of value q, or the node of value q is the parent of the node of value p, then whenever find_distance(root, p, q) returns a result r, r = 1.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_6 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (hparent : Edge root p.val q.val ∨ Edge root q.val p.val)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (hparent : Edge root p.val q.val ∨ Edge root q.val p.val)
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val = 1) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r1 and find_distance(root, q, p) returns a result r2, r1 = r2.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_7 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r1 r2 : Std.I64) (hr1 : find_distance root p q = ok r1)
      (hr2 : find_distance root q p = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r1 r2 : Std.I64) (hr1 : find_distance root p q = ok r1)
        (hr2 : find_distance root q p = ok r2), r1 = r2) := by
    sorry

  /-- If p != q and the node of value p is an ancestor of the node of value q (that is, it lies on the path from the root down to the node of value q), then whenever find_distance(root, p, q) returns a result r, r = depth(root, q) - depth(root, p), where depth(T, v) is the number of edges on the unique path from the root of T down to the node of value v.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_8 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (hne : p ≠ q) (hanc : Ancestor root p.val q.val)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val = (depth root q.val : Int) - (depth root p.val : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (hne : p ≠ q) (hanc : Ancestor root p.val q.val)
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val = (depth root q.val : Int) - (depth root p.val : Int)) := by
    sorry

  /-- If root is a node with value a, left subtree L and right subtree R, and p occurs in L while q occurs in R (or p occurs in R while q occurs in L), then whenever find_distance(root, p, q) returns a result r, r = depth(root, p) + depth(root, q), where depth(T, v) is the number of edges on the unique path from the root of T down to the node of value v.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_9 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (a : Std.I64) (L R : Tree) (hroot : root = .Node a L R)
      (hsep : (Occurs L p.val ∧ Occurs R q.val) ∨ (Occurs R p.val ∧ Occurs L q.val))
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val = (depth root p.val : Int) + (depth root q.val : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (a : Std.I64) (L R : Tree) (hroot : root = .Node a L R)
        (hsep : (Occurs L p.val ∧ Occurs R q.val) ∨ (Occurs R p.val ∧ Occurs L q.val))
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val = (depth root p.val : Int) + (depth root q.val : Int)) := by
    sorry

  /-- If root is a node with value a, left subtree L and right subtree R, and both p and q occur in L, then whenever find_distance(root, p, q) returns a result r1 and find_distance(L, p, q) returns a result r2, r1 = r2.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_10 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (a : Std.I64) (L R : Tree) (hroot : root = .Node a L R)
      (hpL : Occurs L p.val) (hqL : Occurs L q.val)
      (r1 r2 : Std.I64) (hr1 : find_distance root p q = ok r1)
      (hr2 : find_distance L p q = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (a : Std.I64) (L R : Tree) (hroot : root = .Node a L R)
        (hpL : Occurs L p.val) (hqL : Occurs L q.val)
        (r1 r2 : Std.I64) (hr1 : find_distance root p q = ok r1)
        (hr2 : find_distance L p q = ok r2), r1 = r2) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r, there exist values v_0, ..., v_r with v_0 = p, v_r = q, and for every i with 0 <= i < r the nodes of value v_i and v_{i+1} are joined by a parent-child edge in root.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_11 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      ∃ k : Nat, r.val = (k : Int) ∧ Walks root p.val q.val k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (r : Std.I64) (hr : find_distance root p q = ok r), ∃ k : Nat, r.val = (k : Int) ∧ Walks root p.val q.val k) := by
    sorry

  /-- Whenever find_distance(root, p, q) returns a result r, if x is the lowest common ancestor of the nodes of value p and q (the unique node of maximum depth that is an ancestor of both), then r = depth(root, p) + depth(root, q) - 2 * depth(root, x), where depth(T, v) is the number of edges on the unique path from the root of T down to the node of value v.
    Preconditions: root is a binary tree in which p and q each occur as the value of some node, and all node values of root are distinct. -/
  theorem spec_12 (root : Tree) (p q : Std.I64)
      (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
      (x : Int) (hx : IsLCA root p.val q.val x)
      (r : Std.I64) (hr : find_distance root p q = ok r) :
      r.val = (depth root p.val : Int) + (depth root q.val : Int) - 2 * (depth root x : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (p q : Std.I64)
        (hp : Occurs root p.val) (hq : Occurs root q.val) (hnd : DistinctVals root)
        (x : Int) (hx : IsLCA root p.val q.val x)
        (r : Std.I64) (hr : find_distance root p q = ok r), r.val = (depth root p.val : Int) + (depth root q.val : Int) - 2 * (depth root x : Int)) := by
    sorry

  end AegisSpec.FindDistance
