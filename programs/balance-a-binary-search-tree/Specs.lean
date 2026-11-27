import Aegis.BalanceBst.Code.Funs

/-!
# Specifications of `Aegis.BalanceBst.balance_bst`

LeetCode problem `balance-a-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BalanceBst

abbrev Tree := _root_.Aegis.BalanceBst.Tree

def values : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: (values l ++ values r)

def Occurs (v : Int) (t : Tree) : Prop := v ∈ values t

def StrictBst : Tree → Prop
  | .Null => True
  | .Node v l r =>
      StrictBst l ∧ StrictBst r ∧
        (∀ x ∈ values l, x < v.val) ∧ (∀ x ∈ values r, v.val < x)

def height : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + max (height l) (height r)

def Balanced : Tree → Prop
  | .Null => True
  | .Node _ l r =>
      Balanced l ∧ Balanced r ∧ height l ≤ height r + 1 ∧ height r ≤ height l + 1

def inorder : Tree → List Int
  | .Null => []
  | .Node v l r => inorder l ++ [v.val] ++ inorder r

def size : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + size l + size r

def countValue (v : Int) (t : Tree) : Nat := ((values t).filter (fun w => w = v)).length

def listMin : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => min acc y) x)

def listMax : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl (fun acc y => max acc y) x)

def treeMin (t : Tree) : Option Int := listMin (values t)

def treeMax (t : Tree) : Option Int := listMax (values t)

/-- The function returns a result r such that: (a) r is a strict binary search tree: for every node Node(v,l,r') occurring in r, every value occurring in l is strictly less than v and every value occurring in r' is strictly greater than v; (b) r is balanced: for every node Node(v,l,r') occurring in r, |height(l) - height(r')| <= 1, where height(Null)=0 and height(Node(_,a,b))=1+max(height(a),height(b)); (c) for every integer v, the number of nodes of r with value v equals the number of nodes of root with value v.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_1 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.BalanceBst.balance_bst root = ok r ∧
      StrictBst r ∧ Balanced r ∧
      (∀ v : Int, countValue v r = countValue v root) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.BalanceBst.balance_bst root = ok r ∧
      StrictBst r ∧ Balanced r ∧
      (∀ v : Int, countValue v r = countValue v root)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_2 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∃ r, Aegis.BalanceBst.balance_bst root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∃ r, Aegis.BalanceBst.balance_bst root = ok r) := by
  sorry

/-- Whenever the function returns a result r, r is a strict binary search tree: for every node Node(v,l,r') occurring in r, every value occurring in l is strictly less than v and every value occurring in r' is strictly greater than v.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_3 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r → StrictBst r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r → StrictBst r) := by
  sorry

/-- Whenever the function returns a result r, r is balanced: for every node Node(v,l,r') occurring in r, |height(l) - height(r')| <= 1, where height(Null)=0 and height(Node(_,a,b))=1+max(height(a),height(b)).
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_4 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r → Balanced r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r → Balanced r) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of nodes of r with value v equals the number of nodes of root with value v.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_5 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, countValue v r = countValue v root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, countValue v r = countValue v root) := by
  sorry

/-- Let inorder(Null)=[] and inorder(Node(v,l,r'))=inorder(l) ++ [v] ++ inorder(r'). Whenever the function returns a result r, inorder(r)=inorder(root).
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_6 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r → inorder r = inorder root := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r → inorder r = inorder root) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, v occurs as a node value in r if and only if v occurs as a node value in root.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_7 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, Occurs v r ↔ Occurs v root := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, Occurs v r ↔ Occurs v root) := by
  sorry

/-- Whenever the function returns a result r, the number of Node nodes in r equals the number of Node nodes in root.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_8 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r → size r = size root := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r → size r = size root) := by
  sorry

/-- Whenever the function returns a result r, every value occurring in r is an integer between 1 and 100000 inclusive.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_9 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v ∈ values r, 1 ≤ v ∧ v ≤ 100000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v ∈ values r, 1 ≤ v ∧ v ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r, height(r) <= 2 * ceil(log2(n+1)), where n is the number of Node nodes in root, height(Null)=0, height(Node(_,a,b))=1+max(height(a),height(b)), and log2 is logarithm base 2.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_10 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      height r ≤ 2 * Nat.clog 2 (size root + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      height r ≤ 2 * Nat.clog 2 (size root + 1)) := by
  sorry

/-- Whenever the function returns a result r, r is nonempty, and min(r) = min(root) and max(r) = max(root), where for a nonempty tree t, min(t) is the minimum value occurring in t and max(t) is the maximum value occurring in t.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_11 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      r ≠ .Null ∧ treeMin r = treeMin root ∧ treeMax r = treeMax root := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      r ≠ .Null ∧ treeMin r = treeMin root ∧ treeMax r = treeMax root) := by
  sorry

/-- Whenever the function returns a result r, for every integer v that occurs as a node value in root, there is at least one node of r whose value is v.
  Preconditions: root is a strict binary search tree: for every node Node(v,l,r) occurring in root, every value occurring in l is strictly less than v and every value occurring in r is strictly greater than v; the number of Node nodes in root is between 1 and 10000 inclusive; every value occurring in root is between 1 and 100000 inclusive. -/
theorem spec_12 (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000) :
    ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, Occurs v root → Occurs v r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree)
    (hbst : StrictBst root)
    (hsize : 1 ≤ size root ∧ size root ≤ 10000)
    (hbounds : ∀ v ∈ values root, 1 ≤ v ∧ v ≤ 100000), ∀ r, Aegis.BalanceBst.balance_bst root = ok r →
      ∀ v : Int, Occurs v root → Occurs v r) := by
  sorry

end AegisSpec.BalanceBst
