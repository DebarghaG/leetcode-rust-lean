import Aegis.IsBalanced.Code.Funs

/-!
# Specifications of `Aegis.IsBalanced.is_balanced`

LeetCode problem `balanced-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsBalanced

open Aegis.IsBalanced (Tree)

def size : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => size l + size r + 1

def h : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + max (h l) (h r)

def hdist (l r : Tree) : Nat := Int.natAbs ((h l : Int) - (h r : Int))

def B : Tree → Bool
  | Tree.Null => true
  | Tree.Node _ l r => B l && B r && decide (hdist l r ≤ 1)

def AllValues (P : Int → Prop) : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => P v.val ∧ AllValues P l ∧ AllValues P r

def ValuesInBounds (t : Tree) : Prop :=
  AllValues (fun v => -10000 ≤ v ∧ v ≤ 10000) t

def SubtreeOcc (s : Tree) : Tree → Prop
  | Tree.Null => s = Tree.Null
  | Tree.Node v l r => s = Tree.Node v l r ∨ SubtreeOcc s l ∨ SubtreeOcc s r

def SameShape : Tree → Tree → Prop
  | Tree.Null, Tree.Null => True
  | Tree.Node _ l₁ r₁, Tree.Node _ l₂ r₂ => SameShape l₁ l₂ ∧ SameShape r₁ r₂
  | _, _ => False

/-- Define h(t) recursively by h(Null)=0 and h(Node(_, l, r))=1+max(h(l), h(r)). Define B(t) recursively by B(Null)=true and B(Node(_, l, r)) = (B(l) and B(r) and |h(l)-h(r)| <= 1), where |h(l)-h(r)| is the absolute difference of the nonnegative heights. Then for every such root, is_balanced(root) returns a result res and res=true if and only if B(root)=true; equivalently, res=false exactly when B(root)=false.
  Preconditions: root is any Tree satisfying the problem constraints: the number of nodes in root is at most 5000, and every node value v satisfies -10000 <= v <= 10000. -/
theorem spec_1 (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root) :
    ∃ res : Bool, Aegis.IsBalanced.is_balanced root = ok res ∧ (res = true ↔ B root = true) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root), ∃ res : Bool, Aegis.IsBalanced.is_balanced root = ok res ∧ (res = true ↔ B root = true)) := by
  sorry

/-- is_balanced(root) returns a result, either true or false; it does not fail.
  Preconditions: root is any finite Tree with at most 5000 nodes; node values may be arbitrary i64 values. -/
theorem spec_2 (root : Tree) (hsize : size root ≤ 5000) :
    ∃ res : Bool, Aegis.IsBalanced.is_balanced root = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hsize : size root ≤ 5000), ∃ res : Bool, Aegis.IsBalanced.is_balanced root = ok res) := by
  sorry

/-- Whenever is_balanced(root) returns a result res with res=true, for every subtree occurrence s of root that is of the form Node(v, l, r), the heights of l and r differ by at most 1, i.e. |h(l)-h(r)| <= 1. Here h(Null)=0, h(Node(_,a,b))=1+max(h(a),h(b)), and a subtree occurrence means any tree obtained by following zero or more left or right child pointers from root, with root itself included.
  Preconditions: root is any Tree satisfying the problem constraints: the number of nodes in root is at most 5000 and all node values are in [-10000,10000]. -/
theorem spec_3 (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root)
    (hres : Aegis.IsBalanced.is_balanced root = ok true) :
    ∀ s : Tree, SubtreeOcc s root → ∀ (v : Std.I64) (l r : Tree),
      s = Tree.Node v l r → hdist l r ≤ 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root)
    (hres : Aegis.IsBalanced.is_balanced root = ok true), ∀ s : Tree, SubtreeOcc s root → ∀ (v : Std.I64) (l r : Tree),
      s = Tree.Node v l r → hdist l r ≤ 1) := by
  sorry

/-- Whenever is_balanced(root) returns a result res with res=false, there exists a subtree occurrence s of root of the form Node(v, l, r) such that |h(l)-h(r)| > 1, where h(Null)=0, h(Node(_,a,b))=1+max(h(a),h(b)), and a subtree occurrence means any tree obtained by following zero or more left or right child pointers from root, with root itself included.
  Preconditions: root is any Tree satisfying the problem constraints: the number of nodes in root is at most 5000 and all node values are in [-10000,10000]. -/
theorem spec_4 (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root)
    (hres : Aegis.IsBalanced.is_balanced root = ok false) :
    ∃ s : Tree, SubtreeOcc s root ∧ ∃ (v : Std.I64) (l r : Tree),
      s = Tree.Node v l r ∧ 1 < hdist l r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hsize : size root ≤ 5000) (hvals : ValuesInBounds root)
    (hres : Aegis.IsBalanced.is_balanced root = ok false), ∃ s : Tree, SubtreeOcc s root ∧ ∃ (v : Std.I64) (l r : Tree),
      s = Tree.Node v l r ∧ 1 < hdist l r) := by
  sorry

/-- Whenever is_balanced(root1) returns a result res1 and is_balanced(root2) returns a result res2, res1 = res2.
  Preconditions: root1 and root2 are Trees with the same shape, meaning they have Null at exactly the same positions and Node at exactly the same positions, while stored i64 values may differ; each has at most 5000 nodes. -/
theorem spec_5 (root1 root2 : Tree) (hshape : SameShape root1 root2)
    (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
    (res1 res2 : Bool)
    (hres1 : Aegis.IsBalanced.is_balanced root1 = ok res1)
    (hres2 : Aegis.IsBalanced.is_balanced root2 = ok res2) :
    res1 = res2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root1 root2 : Tree) (hshape : SameShape root1 root2)
    (hsize1 : size root1 ≤ 5000) (hsize2 : size root2 ≤ 5000)
    (res1 res2 : Bool)
    (hres1 : Aegis.IsBalanced.is_balanced root1 = ok res1)
    (hres2 : Aegis.IsBalanced.is_balanced root2 = ok res2), res1 = res2) := by
  sorry

end AegisSpec.IsBalanced
