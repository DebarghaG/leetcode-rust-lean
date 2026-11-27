import Aegis.IsValidBst.Code.Funs

/-!
# Specifications of `Aegis.IsValidBst.is_valid_bst`

LeetCode problem `validate-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsValidBst

open Aegis.IsValidBst
open Aeneas.Std.Result (ok)

def keys : Tree → List ℤ
  | .Null => []
  | .Node v L R => keys L ++ [v.val] ++ keys R

def Occurs (k : ℤ) : Tree → Prop
  | .Null => False
  | .Node v L R => v.val = k ∨ Occurs k L ∨ Occurs k R

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ L R => nodeCount L + 1 + nodeCount R

def KeysInInt32Range (t : Tree) : Prop :=
  ∀ k, Occurs k t → -2147483648 ≤ k ∧ k ≤ 2147483647

def SubtreeOf (u : Tree) : Tree → Prop
  | .Null => False
  | .Node v L R => u = .Node v L R ∨ SubtreeOf u L ∨ SubtreeOf u R

def ValidBST : Tree → Prop
  | .Null => True
  | .Node v L R =>
      ValidBST L ∧ ValidBST R ∧
        (∀ w, Occurs w L → w < v.val) ∧ (∀ w, Occurs w R → v.val < w)

def inorder : Tree → List ℤ
  | .Null => []
  | .Node v L R => inorder L ++ [v.val] ++ inorder R

def StrictlyIncreasing (l : List ℤ) : Prop :=
  ∀ (i : Nat) (h : i + 1 < l.length), l.get ⟨i, by omega⟩ < l.get ⟨i + 1, h⟩

def MaxKey (t : Tree) (m : ℤ) : Prop := Occurs m t ∧ ∀ w, Occurs w t → w ≤ m

def MinKey (t : Tree) (m : ℤ) : Prop := Occurs m t ∧ ∀ w, Occurs w t → m ≤ w

def countKey (k : ℤ) : Tree → Nat
  | .Null => 0
  | .Node v L R => (if v.val = k then 1 else 0) + countKey k L + countKey k R

def HasDuplicateKey (t : Tree) : Prop := ∃ k : ℤ, 2 ≤ countKey k t

def HasViolation (root : Tree) : Prop :=
  ∃ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
    SubtreeOf u root ∧ u = .Node v L R ∧
      ((∃ w, Occurs w L ∧ v.val ≤ w) ∨ (∃ w, Occurs w R ∧ w ≤ v.val))

def i64OfInt (n : ℤ) : Aeneas.Std.I64 := Aeneas.Std.IScalar.mk (BitVec.ofInt 64 n)

def mirrorNeg : Tree → Tree
  | .Null => .Null
  | .Node v L R => .Node (i64OfInt (-v.val)) (mirrorNeg R) (mirrorNeg L)

def shiftBy (c : ℤ) : Tree → Tree
  | .Null => .Null
  | .Node v L R => .Node (i64OfInt (v.val + c)) (shiftBy c L) (shiftBy c R)

/-- Define ValidBST(t) for every finite Tree t by: ValidBST(Null) is true; ValidBST(Node(v,L,R)) is true exactly when ValidBST(L) and ValidBST(R), every key occurring in L is < v, and every key occurring in R is > v. The function returns a result r : Bool (it does not fail), and r = true if and only if ValidBST(root) is true; equivalently, r = false if and only if ValidBST(root) is false.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_1 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∃ r : Bool,
      is_valid_bst root = ok r ∧ (r = true ↔ ValidBST root) ∧
        (r = false ↔ ¬ ValidBST root) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∃ r : Bool,
      is_valid_bst root = ok r ∧ (r = true ↔ ValidBST root) ∧
        (r = false ↔ ¬ ValidBST root)) := by
  sorry

/-- The call is_valid_bst root returns a result (an Ok Bool value) rather than failing.
  Preconditions: None beyond root being a finite Tree; root may be Null, may have any number of Node occurrences, and keys may be any i64 values. -/
theorem spec_2 (root : Tree) :
    ∃ r : Bool, is_valid_bst root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree), ∃ r : Bool, is_valid_bst root = ok r) := by
  sorry

/-- Whenever the function returns true, for every node occurrence u with key v, every node occurrence in the left subtree of u has key < v, and every node occurrence in the right subtree of u has key > v. Here the left subtree of u is the entire tree rooted at u's left child, including all descendants; if u has no such child the condition is vacuous.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_3 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          (∀ w, Occurs w L → w < v.val) ∧ (∀ w, Occurs w R → v.val < w) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          (∀ w, Occurs w L → w < v.val) ∧ (∀ w, Occurs w R → v.val < w)) := by
  sorry

/-- Whenever the function returns false, there exist two distinct node occurrences u and v such that either v lies in the left subtree of u and key(v) >= key(u), or v lies in the right subtree of u and key(v) <= key(u).
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_4 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = false → HasViolation root := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∀ r : Bool, is_valid_bst root = ok r → r = false → HasViolation root) := by
  sorry

/-- If there are two distinct node occurrences in root with equal keys, then the function returns false.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_5 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hdup : HasDuplicateKey root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hdup : HasDuplicateKey root), ∀ r : Bool, is_valid_bst root = ok r → r = false) := by
  sorry

/-- Whenever the function returns true, the in-order traversal of root is strictly increasing. The in-order traversal is the sequence formed by recursively listing the left subtree, then the node key, then the right subtree, with Null contributing no elements; strictly increasing means for every index i with 0 <= i < len(sequence) - 1, sequence[i] < sequence[i+1].
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_6 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = true → StrictlyIncreasing (inorder root) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∀ r : Bool, is_valid_bst root = ok r → r = true → StrictlyIncreasing (inorder root)) := by
  sorry

/-- Whenever the function returns true, for every node occurrence u with key v: if the left subtree of u is nonempty, then the maximum key among all node occurrences in that left subtree is < v; if the right subtree of u is nonempty, then the minimum key among all node occurrences in that right subtree is > v.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_7 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          (L ≠ .Null → ∃ m, MaxKey L m ∧ m < v.val) ∧
            (R ≠ .Null → ∃ m, MinKey R m ∧ v.val < m) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          (L ≠ .Null → ∃ m, MaxKey L m ∧ m < v.val) ∧
            (R ≠ .Null → ∃ m, MinKey R m ∧ v.val < m)) := by
  sorry

/-- Whenever the function returns true, for every node occurrence u, every key in the left subtree of u is strictly less than every key in the right subtree of u. If either subtree is empty, this condition is vacuous.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_8 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          ∀ a, Occurs a L → ∀ b, Occurs b R → a < b := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∀ r : Bool, is_valid_bst root = ok r → r = true →
      ∀ (u : Tree) (v : Aeneas.Std.I64) (L R : Tree),
        SubtreeOf u root → u = .Node v L R →
          ∀ a, Occurs a L → ∀ b, Occurs b R → a < b) := by
  sorry

/-- Define mirror_neg(root) recursively by mirror_neg(Null) = Null and mirror_neg(Node(v,L,R)) = Node(-v, mirror_neg(R), mirror_neg(L)). The function returns a Bool for root and for mirror_neg(root), and these two Bool results are equal.
  Preconditions: root is a finite Tree whose keys are all in [-2147483648, 2147483647]. -/
theorem spec_9 (root : Tree)
    (hkeys : KeysInInt32Range root) :
    ∃ r r' : Bool,
      is_valid_bst root = ok r ∧ is_valid_bst (mirrorNeg root) = ok r' ∧ r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hkeys : KeysInInt32Range root), ∃ r r' : Bool,
      is_valid_bst root = ok r ∧ is_valid_bst (mirrorNeg root) = ok r' ∧ r = r') := by
  sorry

/-- Let shift_c(root) be the tree with the same shape as root in which every node key v is replaced by v + c. The function returns Ok r for root and Ok r' for shift_c(root) (it does not fail), and r = r'.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]; c is an integer such that for every key v occurring in root, v + c is an integer in [-2147483648, 2147483647]. -/
theorem spec_10 (root : Tree) (c : ℤ)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hshift : ∀ k, Occurs k root → -2147483648 ≤ k + c ∧ k + c ≤ 2147483647) :
    ∃ r r' : Bool,
      is_valid_bst root = ok r ∧ is_valid_bst (shiftBy c root) = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (c : ℤ)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hshift : ∀ k, Occurs k root → -2147483648 ≤ k + c ∧ k + c ≤ 2147483647), ∃ r r' : Bool,
      is_valid_bst root = ok r ∧ is_valid_bst (shiftBy c root) = ok r' ∧ r = r') := by
  sorry

/-- The function returns Ok r (it does not fail), and r = true if and only if the in-order traversal of root is strictly increasing. The in-order traversal and strict increase are as defined in spec_6: recursively list the left subtree, then the node key, then the right subtree, with Null contributing no elements; strictly increasing means every adjacent pair in the sequence satisfies sequence[i] < sequence[i+1].
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_11 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root) :
    ∃ r : Bool, is_valid_bst root = ok r ∧ (r = true ↔ StrictlyIncreasing (inorder root)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root), ∃ r : Bool, is_valid_bst root = ok r ∧ (r = true ↔ StrictlyIncreasing (inorder root))) := by
  sorry

/-- If there exist two distinct node occurrences u and v such that either v lies in the left subtree of u and key(v) >= key(u), or v lies in the right subtree of u and key(v) <= key(u), then the function returns false (and does not fail). Equivalently, together with spec_4, the function returns false if and only if such a violating ancestor-descendant pair exists.
  Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10000; every node key is an integer in [-2147483648, 2147483647]. In particular root is not Null. -/
theorem spec_12 (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hviol : HasViolation root) :
    ∃ r : Bool, is_valid_bst root = ok r ∧ r = false := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree)
    (hsize : 1 ≤ nodeCount root) (hbound : nodeCount root ≤ 10000)
    (hkeys : KeysInInt32Range root)
    (hviol : HasViolation root), ∃ r : Bool, is_valid_bst root = ok r ∧ r = false) := by
  sorry

end AegisSpec.IsValidBst
