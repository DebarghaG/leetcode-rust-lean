import Aegis.AddOneRow.Code.Funs

/-!
# Specifications of `Aegis.AddOneRow.add_one_row`

LeetCode problem `add-one-row-to-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.AddOneRow

  namespace AegisSpec.AddOneRow

  inductive Dir where

  | left : Dir

  | right : Dir
  deriving DecidableEq, Repr

  def getPath : Tree → List Dir → Option Tree
    | t, [] => some t
    | Tree.Null, _ :: _ => none
    | Tree.Node _ l _, Dir.left :: rest => getPath l rest
    | Tree.Node _ _ r, Dir.right :: rest => getPath r rest

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (height l) (height r)

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + size l + size r

  def valueOf : Tree → Option Std.I64
    | Tree.Null => none
    | Tree.Node v _ _ => some v

  def valuesOf : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (valuesOf l ++ valuesOf r)

  def levelBelow : Tree → Nat → List Tree
    | Tree.Null, _ => []
    | Tree.Node v l r, 0 => [Tree.Node v l r]
    | Tree.Node _ l r, k + 1 => levelBelow l k ++ levelBelow r k

  def level (t : Tree) (k : Nat) : List Tree :=
    match k with
    | 0 => []
    | k + 1 => levelBelow t k

  def numAt (t : Tree) (k : Nat) : Nat := (level t k).length

  def nodeCount (t : Tree) (v : ℤ) : Nat := (valuesOf t).count v

  def ValuesInRange (lo hi : ℤ) : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        lo ≤ v.val ∧ v.val ≤ hi ∧ ValuesInRange lo hi l ∧ ValuesInRange lo hi r

  def insertRowAux : Tree → Std.I64 → Nat → Tree
    | Tree.Null, _, _ => Tree.Null
    | Tree.Node v l r, val, 0 =>
        Tree.Node v (Tree.Node val l Tree.Null) (Tree.Node val Tree.Null r)
    | Tree.Node v l r, val, k + 1 =>
        Tree.Node v (insertRowAux l val k) (insertRowAux r val k)

  def transform (root : Tree) (val : Std.I64) : Nat → Tree
    | 0 => root
    | 1 => Tree.Node val root Tree.Null
    | k + 2 => insertRowAux root val k

  /-- Whenever the function returns a result r, r is the tree obtained from root by the following unique transformation. If depth = 1, then r = Node(val, root, Null). If depth > 1, let S be the set of nodes of root at depth depth-1 (root depth 1; S is empty when depth-1 > height(root), where height(Null)=0 and height(Node(_,l,r))=1+max(height(l),height(r))). For every cur in S, let L and R be cur's left and right children in root. The transformation leaves every node not in S and every edge not incident from a node in S unchanged, and replaces cur's left child by Node(val, L, Null) and cur's right child by Node(val, Null, R). Thus each cur in S keeps its value and original depth, gets two new children of value val, the new left child has right child Null and left subtree L, and the new right child has left child Null and right subtree R. If S is empty, r = root.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. (No upper bound on depth is assumed; depth may exceed height(root)+1.) -/
  theorem spec_1 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      r = transform root val depth.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), r = transform root val depth.val.toNat) := by
    sorry

  /-- For every root, val and depth satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_2 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val) :
      ∃ r : Tree, add_one_row root val depth = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val), ∃ r : Tree, add_one_row root val depth = ok r) := by
    sorry

  /-- Whenever the function returns a result r, let size(t) be the number of Node constructors in t (size(Null)=0 and size(Node(_,l,r))=1+size(l)+size(r)). If depth = 1 then size(r) = size(root)+1. If depth > 1 then size(r) = size(root) + 2*c, where c is the number of nodes of root at depth depth-1 (c=0 if depth-1 > height(root)).
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_3 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      (depth.val = 1 → size r = size root + 1) ∧
        (1 < depth.val → size r = size root + 2 * numAt root (depth.val.toNat - 1)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), (depth.val = 1 → size r = size root + 1) ∧
          (1 < depth.val → size r = size root + 2 * numAt root (depth.val.toNat - 1))) := by
    sorry

  /-- Whenever the function returns a result r, let H = height(root), where height(Null)=0 and height(Node(_,l,r))=1+max(height(l),height(r)). If depth = 1 or (depth > 1 and depth <= H+1), then height(r) = H+1. If depth > H+1, then height(r) = H.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_4 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      ((depth.val = 1 ∨ (1 < depth.val ∧ depth.val ≤ (height root : ℤ) + 1)) →
          height r = height root + 1) ∧
        ((height root : ℤ) + 1 < depth.val → height r = height root) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), ((depth.val = 1 ∨ (1 < depth.val ∧ depth.val ≤ (height root : ℤ) + 1)) →
            height r = height root + 1) ∧
          ((height root : ℤ) + 1 < depth.val → height r = height root)) := by
    sorry

  /-- Whenever the function returns a result r, for a tree t let N_t(k) be the number of nodes of t at depth k (root depth 1; N_t(k)=0 for k<1 or k>height(t)). If depth = 1, then N_r(1)=1 and N_r(k)=N_root(k-1) for every integer k >= 2. If depth > 1, then N_r(k)=N_root(k) for every 1 <= k < depth, N_r(depth)=2*N_root(depth-1), and N_r(k)=N_root(k-1) for every k > depth.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_5 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      ((depth.val = 1 →
          numAt r 1 = 1 ∧ (∀ k : Nat, 2 ≤ k → numAt r k = numAt root (k - 1))) ∧
        (1 < depth.val →
          (∀ k : Nat, 1 ≤ k → k < depth.val.toNat → numAt r k = numAt root k) ∧
            numAt r depth.val.toNat = 2 * numAt root (depth.val.toNat - 1) ∧
              (∀ k : Nat, depth.val.toNat < k → numAt r k = numAt root (k - 1)))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), ((depth.val = 1 →
            numAt r 1 = 1 ∧ (∀ k : Nat, 2 ≤ k → numAt r k = numAt root (k - 1))) ∧
          (1 < depth.val →
            (∀ k : Nat, 1 ≤ k → k < depth.val.toNat → numAt r k = numAt root k) ∧
              numAt r depth.val.toNat = 2 * numAt root (depth.val.toNat - 1) ∧
                (∀ k : Nat, depth.val.toNat < k → numAt r k = numAt root (k - 1))))) := by
    sorry

  /-- Whenever the function returns a result r, the following holds. If depth = 1, the root of r has value val. If depth > 1, every node of r at depth depth (root depth 1) has value val; if there are no such nodes this is vacuous.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_6 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      (depth.val = 1 → valueOf r = some val) ∧
        (1 < depth.val →
          ∀ t : Tree, t ∈ level r depth.val.toNat → valueOf t = some val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), (depth.val = 1 → valueOf r = some val) ∧
          (1 < depth.val →
            ∀ t : Tree, t ∈ level r depth.val.toNat → valueOf t = some val)) := by
    sorry

  /-- Whenever the function returns a result r and depth > 1, for every node cur of root at depth depth-1, let L be cur's left child in root (L may be Null). Let cur' be the node of r reached from the root by the same sequence of left/right child steps as cur. Then cur' exists, has the same value as cur, and cur' has left child Node(val, L, Null). Equivalently, the new left child has value val, its left subtree is exactly L, and its right child is Null.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_7 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r)
      (hdep : 1 < depth.val)
      (p : List Dir) (v : Std.I64) (L R : Tree)
      (hp : getPath root p = some (Tree.Node v L R))
      (hlen : p.length + 1 = depth.val.toNat - 1) :
      ∃ R' : Tree, getPath r p = some (Tree.Node v (Tree.Node val L Tree.Null) R') := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r)
        (hdep : 1 < depth.val)
        (p : List Dir) (v : Std.I64) (L R : Tree)
        (hp : getPath root p = some (Tree.Node v L R))
        (hlen : p.length + 1 = depth.val.toNat - 1), ∃ R' : Tree, getPath r p = some (Tree.Node v (Tree.Node val L Tree.Null) R')) := by
    sorry

  /-- Whenever the function returns a result r and depth > 1, for every node cur of root at depth depth-1, let R be cur's right child in root (R may be Null). Let cur' be the node of r reached from the root by the same sequence of left/right child steps as cur. Then cur' exists, has the same value as cur, and cur' has right child Node(val, Null, R). Equivalently, the new right child has value val, its left child is Null, and its right subtree is exactly R.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_8 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r)
      (hdep : 1 < depth.val)
      (p : List Dir) (v : Std.I64) (L R : Tree)
      (hp : getPath root p = some (Tree.Node v L R))
      (hlen : p.length + 1 = depth.val.toNat - 1) :
      ∃ L' : Tree, getPath r p = some (Tree.Node v L' (Tree.Node val Tree.Null R)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r)
        (hdep : 1 < depth.val)
        (p : List Dir) (v : Std.I64) (L R : Tree)
        (hp : getPath root p = some (Tree.Node v L R))
        (hlen : p.length + 1 = depth.val.toNat - 1), ∃ L' : Tree, getPath r p = some (Tree.Node v L' (Tree.Node val Tree.Null R))) := by
    sorry

  /-- Whenever the function returns a result r and depth > 2, for every node cur of root at depth k with 1 <= k <= depth-2, let cur' be the node of r reached from the root by the same sequence of left/right child steps as cur. Then cur' exists and has the same value as cur. Also, if cur has a left child cL in root, then the left child of cur' in r is the node reached by the same step sequence as cL; if cur has no left child, neither does cur'. The same holds for the right child.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_9 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r)
      (hdep : 2 < depth.val)
      (p : List Dir) (v : Std.I64) (L R : Tree)
      (hp : getPath root p = some (Tree.Node v L R))
      (hlen : p.length + 1 ≤ depth.val.toNat - 2) :
      (∃ L' R' : Tree, getPath r p = some (Tree.Node v L' R')) ∧
        getPath r (p ++ [Dir.left]) = getPath root (p ++ [Dir.left]) ∧
          getPath r (p ++ [Dir.right]) = getPath root (p ++ [Dir.right]) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r)
        (hdep : 2 < depth.val)
        (p : List Dir) (v : Std.I64) (L R : Tree)
        (hp : getPath root p = some (Tree.Node v L R))
        (hlen : p.length + 1 ≤ depth.val.toNat - 2), (∃ L' R' : Tree, getPath r p = some (Tree.Node v L' R')) ∧
          getPath r (p ++ [Dir.left]) = getPath root (p ++ [Dir.left]) ∧
            getPath r (p ++ [Dir.right]) = getPath root (p ++ [Dir.right])) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, let count(t,v) be the number of nodes of t with stored value v. If depth = 1 then count(r,v) = count(root,v) + (1 if v = val else 0). If depth > 1 and c is the number of nodes of root at depth depth-1, then count(r,v) = count(root,v) + (2*c if v = val else 0).
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_10 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r) :
      ((depth.val = 1 →
          ∀ v : ℤ, nodeCount r v = nodeCount root v + (if v = val.val then 1 else 0)) ∧
        (1 < depth.val →
          ∀ v : ℤ,
            nodeCount r v =
              nodeCount root v +
                (if v = val.val then 2 * numAt root (depth.val.toNat - 1) else 0))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r), ((depth.val = 1 →
            ∀ v : ℤ, nodeCount r v = nodeCount root v + (if v = val.val then 1 else 0)) ∧
          (1 < depth.val →
            ∀ v : ℤ,
              nodeCount r v =
                nodeCount root v +
                  (if v = val.val then 2 * numAt root (depth.val.toNat - 1) else 0)))) := by
    sorry

  /-- Whenever the function returns a result r and depth > 1, for every node x of root at depth k >= depth, x appears in r at depth k+1 with the same value. More precisely, let cur be the ancestor of x at depth depth-1, and write the path from cur to x as s0,s1,...,s_{k-depth}, where each s_i is L or R. Then the path from cur to x in r is s0,s0,s1,...,s_{k-depth}: the first step goes to the new val child, the second step goes back to the original child subtree, and the remaining steps are unchanged. All parent-child links inside the original subtrees below the new row are unchanged.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_11 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r)
      (hdep : 1 < depth.val)
      (pref : List Dir) (s0 : Dir) (rest : List Dir) (x : Tree)
      (hlen : pref.length = depth.val.toNat - 2)
      (hx : getPath root (pref ++ [s0] ++ rest) = some x) :
      getPath r (pref ++ [s0, s0] ++ rest) = some x := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r)
        (hdep : 1 < depth.val)
        (pref : List Dir) (s0 : Dir) (rest : List Dir) (x : Tree)
        (hlen : pref.length = depth.val.toNat - 2)
        (hx : getPath root (pref ++ [s0] ++ rest) = some x), getPath r (pref ++ [s0, s0] ++ rest) = some x) := by
    sorry

  /-- Whenever the function returns a result r and depth > 1, let c be the number of nodes of root at depth depth-1. If c > 0, then r has exactly 2*c nodes at depth depth, all of value val; in particular r contains at least two distinct nodes with value val at depth depth.
    Preconditions: root is not Null; every stored value of a node in root is in [-100,100]; -100000 <= val <= 100000; 1 <= depth. -/
  theorem spec_12 (root : Tree) (val depth : Std.I64)
      (hroot : root ≠ Tree.Null)
      (hrange : ValuesInRange (-100) 100 root)
      (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
      (hdepth : 1 ≤ depth.val)
      (r : Tree) (hr : add_one_row root val depth = ok r)
      (hdep : 1 < depth.val)
      (hpos : 0 < numAt root (depth.val.toNat - 1)) :
      numAt r depth.val.toNat = 2 * numAt root (depth.val.toNat - 1) ∧
        (∀ t : Tree, t ∈ level r depth.val.toNat → valueOf t = some val) ∧
          2 ≤ numAt r depth.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root : Tree) (val depth : Std.I64)
        (hroot : root ≠ Tree.Null)
        (hrange : ValuesInRange (-100) 100 root)
        (hval_lo : -100000 ≤ val.val) (hval_hi : val.val ≤ 100000)
        (hdepth : 1 ≤ depth.val)
        (r : Tree) (hr : add_one_row root val depth = ok r)
        (hdep : 1 < depth.val)
        (hpos : 0 < numAt root (depth.val.toNat - 1)), numAt r depth.val.toNat = 2 * numAt root (depth.val.toNat - 1) ∧
          (∀ t : Tree, t ∈ level r depth.val.toNat → valueOf t = some val) ∧
            2 ≤ numAt r depth.val.toNat) := by
    sorry

  end AegisSpec.AddOneRow
