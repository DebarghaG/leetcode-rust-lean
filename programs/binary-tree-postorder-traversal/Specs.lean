import Aegis.PostorderTraversal.Code.Funs

/-!
# Specifications of `Aegis.PostorderTraversal.postorder_traversal`

LeetCode problem `binary-tree-postorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PostorderTraversal

open Aegis.PostorderTraversal (Tree postorder_traversal)

def postorder : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => postorder l ++ postorder r ++ [v.val]

def node_count : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + node_count l + node_count r

def values_in_range : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => -100 ≤ v.val ∧ v.val ≤ 100 ∧ values_in_range l ∧ values_in_range r

def constraints (t : Tree) : Prop := node_count t ≤ 100 ∧ values_in_range t

def vec_vals (r : alloc.vec.Vec Aeneas.Std.I64) : List ℤ := r.val.map (fun x => x.val)

def list_count (xs : List ℤ) (x : ℤ) : Nat := xs.countP (fun y => decide (y = x))

def occur_count : Tree → ℤ → Nat
  | Tree.Null, _ => 0
  | Tree.Node v l r, x => (if v.val = x then 1 else 0) + occur_count l x + occur_count r x

/-- Define postorder(Null) = [] (the empty sequence) and postorder(Node(v, L, R)) = postorder(L) concatenated with postorder(R) concatenated with [v]. Whenever the function returns a result r, the vector r is exactly postorder(root): len(r) = len(postorder(root)), and for every i with 0 <= i < len(r), r[i] is the (i+1)-st element of postorder(root).
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_1 (root : Tree) (hroot : constraints root) :
    ∃ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r ∧
        r.val.length = (postorder root).length ∧
          ∀ i : Nat, i < r.val.length →
            (r.val[i]?).map (fun x => x.val) = (postorder root)[i]? := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∃ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r ∧
        r.val.length = (postorder root).length ∧
          ∀ i : Nat, i < r.val.length →
            (r.val[i]?).map (fun x => x.val) = (postorder root)[i]?) := by
  sorry

/-- Define node_count(Null) = 0 and node_count(Node(v, L, R)) = 1 + node_count(L) + node_count(R). Whenever the function returns a result r, len(r) = node_count(root). Consequently, 0 <= len(r) <= 100.
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_2 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        r.val.length = node_count root ∧ 0 ≤ r.val.length ∧ r.val.length ≤ 100 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        r.val.length = node_count root ∧ 0 ≤ r.val.length ∧ r.val.length ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), the value r[i] satisfies -100 <= r[i] <= 100.
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_3 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), -100 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (i : Nat) (hi : i < r.val.length), -100 ≤ (r.val[i]'hi).val ∧ (r.val[i]'hi).val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, if root = Node(v, L, R) for some value v and subtrees L and R, then len(r) > 0 and r[len(r)-1] = v.
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_4 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          0 < r.val.length ∧ r.val.getLast? = some v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          0 < r.val.length ∧ r.val.getLast? = some v) := by
  sorry

/-- Whenever the function returns a result r, for every integer x, the number of indices i with 0 <= i < len(r) and r[i] = x equals the number of Node occurrences in root whose stored value is x, counted with multiplicity.
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_5 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ x : ℤ, list_count (vec_vals r) x = occur_count root x := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ x : ℤ, list_count (vec_vals r) x = occur_count root x) := by
  sorry

/-- Define node_count(Null) = 0, node_count(Node(a, A, B)) = 1 + node_count(A) + node_count(B), postorder(Null) = [], and postorder(Node(a, A, B)) = postorder(A) concatenated with postorder(B) concatenated with [a]. Whenever the function returns a result r, if root = Node(v, L, R), then len(r) >= node_count(L), and for every i with 0 <= i < node_count(L), r[i] = postorder(L)[i].
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_6 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          node_count l ≤ r.val.length ∧
            ∀ i : Nat, i < node_count l →
              (r.val[i]?).map (fun x => x.val) = (postorder l)[i]? := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          node_count l ≤ r.val.length ∧
            ∀ i : Nat, i < node_count l →
              (r.val[i]?).map (fun x => x.val) = (postorder l)[i]?) := by
  sorry

/-- Define node_count(Null) = 0, node_count(Node(a, A, B)) = 1 + node_count(A) + node_count(B), postorder(Null) = [], and postorder(Node(a, A, B)) = postorder(A) concatenated with postorder(B) concatenated with [a]. Whenever the function returns a result r, if root = Node(v, L, R), then len(r) >= node_count(L) + node_count(R), and for every i with 0 <= i < node_count(R), r[node_count(L) + i] = postorder(R)[i].
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_7 (root : Tree) (hroot : constraints root) :
    ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          node_count l + node_count rt ≤ r.val.length ∧
            ∀ i : Nat, i < node_count rt →
              (r.val[node_count l + i]?).map (fun x => x.val) = (postorder rt)[i]? := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∀ r : alloc.vec.Vec Aeneas.Std.I64,
      postorder_traversal root = ok r →
        ∀ (v : Aeneas.Std.I64) (l rt : Tree), root = Tree.Node v l rt →
          node_count l + node_count rt ≤ r.val.length ∧
            ∀ i : Nat, i < node_count rt →
              (r.val[node_count l + i]?).map (fun x => x.val) = (postorder rt)[i]?) := by
  sorry

/-- The function returns a result r for every such root; in particular, it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: The finite Tree root satisfies the problem constraints: it contains at most 100 Node constructors, and every stored value v satisfies -100 <= v <= 100. -/
theorem spec_8 (root : Tree) (hroot : constraints root) :
    ∃ r : alloc.vec.Vec Aeneas.Std.I64, postorder_traversal root = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (hroot : constraints root), ∃ r : alloc.vec.Vec Aeneas.Std.I64, postorder_traversal root = ok r) := by
  sorry

end AegisSpec.PostorderTraversal
