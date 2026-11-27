import Aegis.IsSubtree.Code.Funs

/-!
# Specifications of `Aegis.IsSubtree.is_subtree`

LeetCode problem `subtree-of-another-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsSubtree (Tree same_tree is_subtree)

  namespace AegisSpec.IsSubtree

  def size : Tree → Nat
    | .Null => 0
    | .Node _ l r => size l + size r + 1

  def structEq : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node v l r, .Node v' l' r' => v.val = v'.val ∧ structEq l l' ∧ structEq r r'
    | _, _ => False

  inductive occurs : Tree → Tree → Prop where
    | here {v : I64} {l r : Tree} : occurs (.Node v l r) (.Node v l r)
    | left {v : I64} {l r t : Tree} : occurs l t → occurs (.Node v l r) t
    | right {v : I64} {l r t : Tree} : occurs r t → occurs (.Node v l r) t

  def NodeVals : Tree → List I64
    | .Null => []
    | .Node v l r => v :: (NodeVals l ++ NodeVals r)

  def countVal (x : I64) : Tree → Nat
    | .Null => 0
    | .Node v l r => (if v.val = x.val then 1 else 0) + countVal x l + countVal x r

  def mirror : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node v (mirror r) (mirror l)

  def i64Add (v : I64) (c : ℤ) : I64 := IScalar.mk (BitVec.ofInt 64 (v.val + c))

  def shift (c : ℤ) : Tree → Tree
    | .Null => .Null
    | .Node v l r => .Node (i64Add v c) (shift c l) (shift c r)

  /-- The function returns a result r : Bool (it does not fail), and r = true if and only if there exists a node v of root such that the subtree of root rooted at v is structurally equal to subRoot. The subtree rooted at v consists of v and all descendants of v. Structural equality means the two trees have the same shape (Null matches only Null, Node matches Node with left and right corresponding) and equal i64 values at every corresponding Node.
    Preconditions: root and subRoot are binary Tree values satisfying the problem constraints: size(root) is between 1 and 2000 and size(subRoot) is between 1 and 1000, where size(T) is the number of Node constructors in T; every node value in root and subRoot lies in [-10000,10000]. -/
  theorem spec_1 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Bool,
        is_subtree root subRoot = ok r ∧
          (r = true ↔ ∃ t : Tree, occurs root t ∧ structEq t subRoot) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Bool,
          is_subtree root subRoot = ok r ∧
            (r = true ↔ ∃ t : Tree, occurs root t ∧ structEq t subRoot)) := by
    sorry

  /-- The function returns a Result Bool value; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: root and subRoot are binary Tree values satisfying the problem constraints: size(root) is between 1 and 2000 and size(subRoot) is between 1 and 1000, where size(T) is the number of Node constructors in T; every node value in root and subRoot lies in [-10000,10000]. -/
  theorem spec_2 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Bool, is_subtree root subRoot = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Bool, is_subtree root subRoot = ok r) := by
    sorry

  /-- The function returns false (and does not fail).
    Preconditions: root and subRoot are nonempty binary trees with all node values in [-10000,10000], size(root) <= 2000, size(subRoot) <= 1000, and size(subRoot) > size(root), where size(T) is the number of Node constructors in T. -/
  theorem spec_3 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hgt : size root < size subRoot) :
      is_subtree root subRoot = ok false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hgt : size root < size subRoot), is_subtree root subRoot = ok false) := by
    sorry

  /-- If there exists an i64 value x such that x occurs strictly more times as a node value in subRoot than as a node value in root, then the function returns false (and does not fail).
    Preconditions: root and subRoot are nonempty binary trees satisfying size(root) <= 2000, size(subRoot) <= 1000, and all node values in [-10000,10000]. -/
  theorem spec_4 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hcount : ∃ x : I64, countVal x root < countVal x subRoot) :
      is_subtree root subRoot = ok false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hcount : ∃ x : I64, countVal x root < countVal x subRoot), is_subtree root subRoot = ok false) := by
    sorry

  /-- The function returns true (and does not fail).
    Preconditions: root and subRoot are nonempty binary trees satisfying size(root) <= 2000, size(subRoot) <= 1000, all node values in [-10000,10000], and root and subRoot are structurally equal (same shape and equal corresponding node values). -/
  theorem spec_5 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (heq : structEq root subRoot) :
      is_subtree root subRoot = ok true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (heq : structEq root subRoot), is_subtree root subRoot = ok true) := by
    sorry

  /-- The function returns true if and only if root contains a leaf Node(b, Null, Null) with b = a; equivalently, some Node occurrence in root has value a and both children Null. (The function does not fail.)
    Preconditions: root is a nonempty binary tree satisfying size(root) <= 2000 and all node values in [-10000,10000], and subRoot = Node(a, Null, Null) for some i64 a in [-10000,10000]. -/
  theorem spec_6 (root : Tree) (a : I64)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (ha : -10000 ≤ a.val ∧ a.val ≤ 10000) :
      ∃ r : Bool,
        is_subtree root (.Node a .Null .Null) = ok r ∧
          (r = true ↔ ∃ b : I64, occurs root (.Node b .Null .Null) ∧ b.val = a.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree) (a : I64)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (ha : -10000 ≤ a.val ∧ a.val ≤ 10000), ∃ r : Bool,
          is_subtree root (.Node a .Null .Null) = ok r ∧
            (r = true ↔ ∃ b : I64, occurs root (.Node b .Null .Null) ∧ b.val = a.val)) := by
    sorry

  /-- If the call is_subtree(b, a) returns true and the call is_subtree(c, b) returns true, then the call is_subtree(c, a) returns true. All these calls do not fail.
    Preconditions: a and b are nonempty binary trees with all node values in [-10000,10000] and with size(a), size(b) at most 1000; c is a nonempty binary tree with all node values in [-10000,10000] and size(c) at most 2000, where size(T) is the number of Node constructors in T. -/
  theorem spec_7 (a b c : Tree)
      (ha_size : 1 ≤ size a ∧ size a ≤ 1000)
      (hb_size : 1 ≤ size b ∧ size b ≤ 1000)
      (hc_size : 1 ≤ size c ∧ size c ≤ 2000)
      (ha_vals : ∀ v ∈ NodeVals a, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hb_vals : ∀ v ∈ NodeVals b, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hc_vals : ∀ v ∈ NodeVals c, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hab : is_subtree b a = ok true)
      (hbc : is_subtree c b = ok true) :
      is_subtree c a = ok true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b c : Tree)
        (ha_size : 1 ≤ size a ∧ size a ≤ 1000)
        (hb_size : 1 ≤ size b ∧ size b ≤ 1000)
        (hc_size : 1 ≤ size c ∧ size c ≤ 2000)
        (ha_vals : ∀ v ∈ NodeVals a, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hb_vals : ∀ v ∈ NodeVals b, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hc_vals : ∀ v ∈ NodeVals c, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hab : is_subtree b a = ok true)
        (hbc : is_subtree c b = ok true), is_subtree c a = ok true) := by
    sorry

  /-- If is_subtree(a, b) returns true and is_subtree(b, a) returns true, then a and b are structurally equal (same shape and equal corresponding node values). Both calls do not fail.
    Preconditions: a and b are nonempty binary trees with all node values in [-10000,10000] and size(a), size(b) <= 1000. -/
  theorem spec_8 (a b : Tree)
      (ha_size : 1 ≤ size a ∧ size a ≤ 1000)
      (hb_size : 1 ≤ size b ∧ size b ≤ 1000)
      (ha_vals : ∀ v ∈ NodeVals a, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hb_vals : ∀ v ∈ NodeVals b, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hab : is_subtree a b = ok true)
      (hba : is_subtree b a = ok true) :
      structEq a b := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b : Tree)
        (ha_size : 1 ≤ size a ∧ size a ≤ 1000)
        (hb_size : 1 ≤ size b ∧ size b ≤ 1000)
        (ha_vals : ∀ v ∈ NodeVals a, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hb_vals : ∀ v ∈ NodeVals b, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hab : is_subtree a b = ok true)
        (hba : is_subtree b a = ok true), structEq a b) := by
    sorry

  /-- If s is a subtree of L (that is, L is nonempty and is_subtree(L, s) returns true) or s is a subtree of R (that is, R is nonempty and is_subtree(R, s) returns true), then is_subtree(root, s) returns true. The relevant calls do not fail.
    Preconditions: root = Node(v, L, R) is a nonempty binary tree with all node values in [-10000,10000] and size(root) <= 2000; s is a nonempty binary tree with all node values in [-10000,10000] and size(s) <= 1000. -/
  theorem spec_9 (v : I64) (L R s : Tree)
      (hroot_size : 1 ≤ size (.Node v L R) ∧ size (.Node v L R) ≤ 2000)
      (hroot_vals : ∀ x ∈ NodeVals (.Node v L R), -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hs_size : 1 ≤ size s ∧ size s ≤ 1000)
      (hs_vals : ∀ x ∈ NodeVals s, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hchild : (1 ≤ size L ∧ is_subtree L s = ok true) ∨
                (1 ≤ size R ∧ is_subtree R s = ok true)) :
      is_subtree (.Node v L R) s = ok true := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (v : I64) (L R s : Tree)
        (hroot_size : 1 ≤ size (.Node v L R) ∧ size (.Node v L R) ≤ 2000)
        (hroot_vals : ∀ x ∈ NodeVals (.Node v L R), -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hs_size : 1 ≤ size s ∧ size s ≤ 1000)
        (hs_vals : ∀ x ∈ NodeVals s, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hchild : (1 ≤ size L ∧ is_subtree L s = ok true) ∨
                  (1 ≤ size R ∧ is_subtree R s = ok true)), is_subtree (.Node v L R) s = ok true) := by
    sorry

  /-- The call is_subtree(mirror(root), mirror(subRoot)) returns the same Bool as is_subtree(root, subRoot); both calls do not fail.
    Preconditions: root and subRoot are nonempty binary trees satisfying size(root) <= 2000, size(subRoot) <= 1000, and all node values in [-10000,10000]. Let mirror(T) be defined by mirror(Null)=Null and mirror(Node(v,L,R))=Node(v,mirror(R),mirror(L)). -/
  theorem spec_10 (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r r' : Bool,
        is_subtree root subRoot = ok r ∧
          is_subtree (mirror root) (mirror subRoot) = ok r' ∧ r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_vals : ∀ v ∈ NodeVals root, -10000 ≤ v.val ∧ v.val ≤ 10000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r r' : Bool,
          is_subtree root subRoot = ok r ∧
            is_subtree (mirror root) (mirror subRoot) = ok r' ∧ r = r') := by
    sorry

  /-- The call is_subtree(shift_c(root), shift_c(subRoot)) returns the same Bool as is_subtree(root, subRoot); both calls do not fail.
    Preconditions: root and subRoot are nonempty binary trees satisfying size(root) <= 2000, size(subRoot) <= 1000, and all node values in [-10000,10000]. Let c be an integer such that every value x+c, for x a node value in root or subRoot, lies in [-10000,10000]. Define shift_c(T) recursively by replacing each node value x in T with x+c. -/
  theorem spec_11 (c : ℤ) (root subRoot : Tree)
      (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hroot_shift : ∀ v ∈ NodeVals root,
        -10000 ≤ v.val + c ∧ v.val + c ≤ 10000)
      (hsub_shift : ∀ v ∈ NodeVals subRoot,
        -10000 ≤ v.val + c ∧ v.val + c ≤ 10000) :
      ∃ r r' : Bool,
        is_subtree root subRoot = ok r ∧
          is_subtree (shift c root) (shift c subRoot) = ok r' ∧ r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (c : ℤ) (root subRoot : Tree)
        (hroot_size : 1 ≤ size root ∧ size root ≤ 2000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hroot_shift : ∀ v ∈ NodeVals root,
          -10000 ≤ v.val + c ∧ v.val + c ≤ 10000)
        (hsub_shift : ∀ v ∈ NodeVals subRoot,
          -10000 ≤ v.val + c ∧ v.val + c ≤ 10000), ∃ r r' : Bool,
          is_subtree root subRoot = ok r ∧
            is_subtree (shift c root) (shift c subRoot) = ok r' ∧ r = r') := by
    sorry

  /-- The function returns true if and only if subRoot is structurally equal to Node(a, Null, Null). (The function does not fail.)
    Preconditions: root = Node(a, Null, Null) for some i64 a in [-10000,10000]; subRoot is a nonempty binary tree with all node values in [-10000,10000] and size(subRoot) <= 1000. -/
  theorem spec_12 (a : I64) (subRoot : Tree)
      (ha : -10000 ≤ a.val ∧ a.val ≤ 10000)
      (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
      (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000) :
      ∃ r : Bool,
        is_subtree (.Node a .Null .Null) subRoot = ok r ∧
          (r = true ↔ structEq (.Node a .Null .Null) subRoot) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a : I64) (subRoot : Tree)
        (ha : -10000 ≤ a.val ∧ a.val ≤ 10000)
        (hsub_size : 1 ≤ size subRoot ∧ size subRoot ≤ 1000)
        (hsub_vals : ∀ v ∈ NodeVals subRoot, -10000 ≤ v.val ∧ v.val ≤ 10000), ∃ r : Bool,
          is_subtree (.Node a .Null .Null) subRoot = ok r ∧
            (r = true ↔ structEq (.Node a .Null .Null) subRoot)) := by
    sorry

  end AegisSpec.IsSubtree
