import Aegis.CheckTree.Code.Funs

/-!
# Specifications of `Aegis.CheckTree.check_tree`

LeetCode problem `root-equals-sum-of-children`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CheckTree

namespace AegisSpec.CheckTree

def InI64Range (n : ℤ) : Prop :=
  Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 ≤ n ∧
    n ≤ Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64

/-- The function returns a result r and r = true if and only if x = y + z; equivalently, r is the Boolean value of the equality x = y + z. Thus r = false exactly when x != y + z.
  Preconditions: root = Tree.Node(x, Tree.Node(y, Tree.Null, Tree.Null), Tree.Node(z, Tree.Null, Tree.Null)) for some integers x, y, z with -100 <= x <= 100, -100 <= y <= 100, and -100 <= z <= 100. -/
theorem spec_1 (root : Tree) (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100)
    (hroot : root = Tree.Node x (Tree.Node y Tree.Null Tree.Null)
      (Tree.Node z Tree.Null Tree.Null)) :
    ∃ r, check_tree root = ok r ∧ (r = true ↔ x.val = y.val + z.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100)
    (hroot : root = Tree.Node x (Tree.Node y Tree.Null Tree.Null)
      (Tree.Node z Tree.Null Tree.Null)), ∃ r, check_tree root = ok r ∧ (r = true ↔ x.val = y.val + z.val)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or get stuck.
  Preconditions: root = Tree.Node(x, Tree.Node(y, Tree.Null, Tree.Null), Tree.Node(z, Tree.Null, Tree.Null)) for some integers x, y, z with -100 <= x <= 100, -100 <= y <= 100, and -100 <= z <= 100. -/
theorem spec_2 (root : Tree) (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100)
    (hroot : root = Tree.Node x (Tree.Node y Tree.Null Tree.Null)
      (Tree.Node z Tree.Null Tree.Null)) :
    ∃ r, check_tree root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100)
    (hroot : root = Tree.Node x (Tree.Node y Tree.Null Tree.Null)
      (Tree.Node z Tree.Null Tree.Null)), ∃ r, check_tree root = ok r) := by
  sorry

/-- check_tree root1 returns result r1, check_tree root2 returns result r2, and r1 = r2.
  Preconditions: x, y, z are integers with -100 <= x <= 100, -100 <= y <= 100, and -100 <= z <= 100. Let root1 = Tree.Node(x, Tree.Node(y, Tree.Null, Tree.Null), Tree.Node(z, Tree.Null, Tree.Null)) and root2 = Tree.Node(x, Tree.Node(z, Tree.Null, Tree.Null), Tree.Node(y, Tree.Null, Tree.Null)). -/
theorem spec_3 (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100) :
    ∃ r1 r2,
      check_tree (Tree.Node x (Tree.Node y Tree.Null Tree.Null)
          (Tree.Node z Tree.Null Tree.Null)) = ok r1 ∧
        check_tree (Tree.Node x (Tree.Node z Tree.Null Tree.Null)
            (Tree.Node y Tree.Null Tree.Null)) = ok r2 ∧
          r1 = r2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x y z : Aeneas.Std.I64)
    (hx : -100 ≤ x.val ∧ x.val ≤ 100)
    (hy : -100 ≤ y.val ∧ y.val ≤ 100)
    (hz : -100 ≤ z.val ∧ z.val ≤ 100), ∃ r1 r2,
      check_tree (Tree.Node x (Tree.Node y Tree.Null Tree.Null)
          (Tree.Node z Tree.Null Tree.Null)) = ok r1 ∧
        check_tree (Tree.Node x (Tree.Node z Tree.Null Tree.Null)
            (Tree.Node y Tree.Null Tree.Null)) = ok r2 ∧
          r1 = r2) := by
  sorry

end AegisSpec.CheckTree
