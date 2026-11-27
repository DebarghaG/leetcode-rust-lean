import Aegis.LeafSimilar.Code.Funs

/-!
# Specifications of `Aegis.LeafSimilar.leaf_similar`

LeetCode problem `leaf-similar-trees`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LeafSimilar

open Aegis.LeafSimilar

def numNodes : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ left right => 1 + numNodes left + numNodes right

def nodeValues : Tree → List Int
  | Tree.Null => []
  | Tree.Node v left right => v.val :: (nodeValues left ++ nodeValues right)

def valuesInRange (t : Tree) : Prop := ∀ x ∈ nodeValues t, 0 ≤ x ∧ x ≤ 200

def sizeBounds (t : Tree) : Prop := 1 ≤ numNodes t ∧ numNodes t ≤ 200

def leafSeq : Tree → List Int
  | Tree.Null => []
  | Tree.Node v left right =>
    match left, right with
    | Tree.Null, Tree.Null => [v.val]
    | _, _ => leafSeq left ++ leafSeq right

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v left right => Tree.Node v (mirror right) (mirror left)

/-- Let leafSeq(t) be the leaf value sequence of t: the list of values of all leaves of t in left-to-right order, where a leaf is a node Node(v, Null, Null). Formally, leafSeq(Null) = [], leafSeq(Node(v, Null, Null)) = [v], and leafSeq(Node(v, l, r)) = leafSeq(l) ++ leafSeq(r) whenever l != Null or r != Null (++ is list concatenation). Whenever the function returns a result r, r = true if and only if leafSeq(root1) = leafSeq(root2) (the two lists have equal length and equal entries at every index).
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_1 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r) :
    (r = true ↔ leafSeq root1 = leafSeq root2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r), (r = true ↔ leafSeq root1 = leafSeq root2)) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions; r is a Bool.
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_2 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2) :
    ∃ r : Bool, leaf_similar root1 root2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2), ∃ r : Bool, leaf_similar root1 root2 = ok r) := by
  sorry

/-- Whenever leaf_similar(a, b) returns a result r1 and leaf_similar(b, a) returns a result r2, we have r1 = r2 (both true or both false).
  Preconditions: a and b are trees of type Tree. Let na and nb be the number of Node constructors in a and b respectively. Then 1 <= na <= 200 and 1 <= nb <= 200, and every value stored in a Node of a or b lies in the range [0, 200]. -/
theorem spec_3 (a b : Tree)
    (hsizea : sizeBounds a) (hsizeb : sizeBounds b)
    (hvala : valuesInRange a) (hvalb : valuesInRange b)
    (r1 r2 : Bool) (hr1 : leaf_similar a b = ok r1) (hr2 : leaf_similar b a = ok r2) :
    r1 = r2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b : Tree)
    (hsizea : sizeBounds a) (hsizeb : sizeBounds b)
    (hvala : valuesInRange a) (hvalb : valuesInRange b)
    (r1 r2 : Bool) (hr1 : leaf_similar a b = ok r1) (hr2 : leaf_similar b a = ok r2), r1 = r2) := by
  sorry

/-- Whenever the function returns a result r and r = true, len(leafSeq(root1)) = len(leafSeq(root2)) and 1 <= len(leafSeq(root1)) <= 200, where leafSeq(t) is the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)).
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_4 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r) (htrue : r = true) :
    (leafSeq root1).length = (leafSeq root2).length ∧
      1 ≤ (leafSeq root1).length ∧ (leafSeq root1).length ≤ 200 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r) (htrue : r = true), (leafSeq root1).length = (leafSeq root2).length ∧
      1 ≤ (leafSeq root1).length ∧ (leafSeq root1).length ≤ 200) := by
  sorry

/-- Whenever the function returns a result r, if leafSeq(root1) = leafSeq(root2) then r = true. Here leafSeq(t) is the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)).
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_5 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r)
    (hseq : leafSeq root1 = leafSeq root2) :
    r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r)
    (hseq : leafSeq root1 = leafSeq root2), r = true) := by
  sorry

/-- Whenever the function returns a result r, if leafSeq(root1) != leafSeq(root2) then r = false. Here leafSeq(t) is the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)).
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_6 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r)
    (hseq : leafSeq root1 ≠ leafSeq root2) :
    r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r)
    (hseq : leafSeq root1 ≠ leafSeq root2), r = false) := by
  sorry

/-- Let leafSeq(t) be the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)). Whenever leaf_similar(a, b) returns a result r and leaf_similar(a', b') returns a result r', if leafSeq(a) = leafSeq(a') and leafSeq(b) = leafSeq(b'), then r = r'.
  Preconditions: a, a', b, b' are trees of type Tree. Each has between 1 and 200 Node constructors, and every value stored in a Node of any of them lies in the range [0, 200]. -/
theorem spec_7 (a a' b b' : Tree)
    (hsizea : sizeBounds a) (hsizea' : sizeBounds a')
    (hsizeb : sizeBounds b) (hsizeb' : sizeBounds b')
    (hvala : valuesInRange a) (hvala' : valuesInRange a')
    (hvalb : valuesInRange b) (hvalb' : valuesInRange b')
    (r r' : Bool) (hr : leaf_similar a b = ok r) (hr' : leaf_similar a' b' = ok r')
    (ha : leafSeq a = leafSeq a') (hb : leafSeq b = leafSeq b') :
    r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a a' b b' : Tree)
    (hsizea : sizeBounds a) (hsizea' : sizeBounds a')
    (hsizeb : sizeBounds b) (hsizeb' : sizeBounds b')
    (hvala : valuesInRange a) (hvala' : valuesInRange a')
    (hvalb : valuesInRange b) (hvalb' : valuesInRange b')
    (r r' : Bool) (hr : leaf_similar a b = ok r) (hr' : leaf_similar a' b' = ok r')
    (ha : leafSeq a = leafSeq a') (hb : leafSeq b = leafSeq b'), r = r') := by
  sorry

/-- Let leafSeq(t) be the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)). Whenever the function returns a result r and r = false, then either len(leafSeq(root1)) != len(leafSeq(root2)), or there exists an integer i such that 0 <= i < len(leafSeq(root1)), 0 <= i < len(leafSeq(root2)), and leafSeq(root1)[i] != leafSeq(root2)[i].
  Preconditions: root1 and root2 are trees of type Tree. Let n1 and n2 be the number of Node constructors in root1 and root2 respectively. Then 1 <= n1 <= 200 and 1 <= n2 <= 200, and every value stored in a Node of root1 or root2 lies in the range [0, 200]. -/
theorem spec_8 (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r) (hfalse : r = false) :
    (leafSeq root1).length ≠ (leafSeq root2).length ∨
      ∃ (i : Nat) (h1 : i < (leafSeq root1).length) (h2 : i < (leafSeq root2).length),
        (leafSeq root1).get ⟨i, h1⟩ ≠ (leafSeq root2).get ⟨i, h2⟩ := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root1 root2 : Tree)
    (hsize1 : sizeBounds root1) (hsize2 : sizeBounds root2)
    (hval1 : valuesInRange root1) (hval2 : valuesInRange root2)
    (r : Bool) (hr : leaf_similar root1 root2 = ok r) (hfalse : r = false), (leafSeq root1).length ≠ (leafSeq root2).length ∨
      ∃ (i : Nat) (h1 : i < (leafSeq root1).length) (h2 : i < (leafSeq root2).length),
        (leafSeq root1).get ⟨i, h1⟩ ≠ (leafSeq root2).get ⟨i, h2⟩) := by
  sorry

/-- Define mirror(t) recursively by mirror(Null) = Null and mirror(Node(v, l, r)) = Node(v, mirror(r), mirror(l)). Let leafSeq(t) be the list of leaf values of t in left-to-right order (a leaf is a node Node(v, Null, Null)). Whenever leaf_similar(t, mirror(t)) returns a result r, r = true if and only if leafSeq(t) = reverse(leafSeq(t)), where reverse(L) is the list obtained by reversing L.
  Preconditions: t is a tree of type Tree with between 1 and 200 nodes, and every value stored in a Node of t lies in the range [0, 200]. -/
theorem spec_9 (t : Tree)
    (hsize : sizeBounds t) (hval : valuesInRange t)
    (r : Bool) (hr : leaf_similar t (mirror t) = ok r) :
    (r = true ↔ leafSeq t = (leafSeq t).reverse) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (t : Tree)
    (hsize : sizeBounds t) (hval : valuesInRange t)
    (r : Bool) (hr : leaf_similar t (mirror t) = ok r), (r = true ↔ leafSeq t = (leafSeq t).reverse)) := by
  sorry

end AegisSpec.LeafSimilar
