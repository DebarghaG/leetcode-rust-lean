import Aegis.FindBottomLeftValue.Code.Funs

/-!
# Specifications of `Aegis.FindBottomLeftValue.find_bottom_left_value`

LeetCode problem `find-bottom-left-tree-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindBottomLeftValue

  open Aegis.FindBottomLeftValue

  inductive Dir where
    | L : Dir
    | R : Dir
    deriving DecidableEq, Repr

  def nodeAt : Tree → List Dir → Option Tree
    | .Null, _ => none
    | t@(.Node _ _ _), [] => some t
    | .Node _ l _, .L :: p => nodeAt l p
    | .Node _ _ r, .R :: p => nodeAt r p

  def valueOf : Tree → Option Int
    | .Null => none
    | .Node v _ _ => some v.val

  def valueAt (t : Tree) (p : List Dir) : Option Int := (nodeAt t p).bind valueOf

  def IsOccurrence (t : Tree) (p : List Dir) : Prop := (nodeAt t p).isSome

  def depthOf (p : List Dir) : Int := (p.length : Int)

  def nodeDepths : Tree → List Int
    | .Null => []
    | .Node _ l r =>
      0 :: ((nodeDepths l).map (fun d => d + 1) ++ (nodeDepths r).map (fun d => d + 1))

  def maxDepth (t : Tree) : Int := (nodeDepths t).foldr max (-1)

  def height : Tree → Int
    | .Null => -1
    | .Node _ l r => 1 + max (height l) (height r)

  def nodeCount : Tree → Nat
    | .Null => 0
    | .Node _ l r => 1 + nodeCount l + nodeCount r

  def storedValues : Tree → List Int
    | .Null => []
    | .Node v l r => v.val :: (storedValues l ++ storedValues r)

  def minValueOf : List Int → Option Int
    | [] => none
    | x :: xs => some (xs.foldl (fun m y => min m y) x)

  def maxValueOf : List Int → Option Int
    | [] => none
    | x :: xs => some (xs.foldl (fun m y => max m y) x)

  def minValue (t : Tree) : Option Int := minValueOf (storedValues t)

  def maxValue (t : Tree) : Option Int := maxValueOf (storedValues t)

  def InI32Range (x : Int) : Prop := -2147483648 ≤ x ∧ x ≤ 2147483647

  def AllValuesInI32Range (t : Tree) : Prop := ∀ x ∈ storedValues t, InI32Range x

  def lexLtB : List Dir → List Dir → Bool
    | [], [] => false
    | [], _ :: _ => true
    | _ :: _, [] => false
    | a :: p, b :: q => if a = b then lexLtB p q else match a with | .L => true | .R => false

  def lexLt (p q : List Dir) : Prop := lexLtB p q = true

  instance decidableLexLt (p q : List Dir) : Decidable (lexLt p q) := by
    unfold lexLt
    infer_instance

  def IsBottomLeftPath (t : Tree) (p : List Dir) : Prop :=
    IsOccurrence t p ∧ depthOf p = maxDepth t ∧
      ∀ q : List Dir, IsOccurrence t q → depthOf q = maxDepth t → ¬ lexLt q p

  def IsBottomLeftValue (t : Tree) (r : Int) : Prop :=
    ∃ p : List Dir, IsBottomLeftPath t p ∧ valueAt t p = some r

  def SameShape : Tree → Tree → Prop
    | .Null, .Null => True
    | .Node _ l r, .Node _ l' r' => SameShape l l' ∧ SameShape r r'
    | _, _ => False

  /-- For every root satisfying the preconditions, the function returns a result r and r is the bottom-left value of root, defined as follows. A node occurrence is a root-to-node path over {L,R}; its depth is the number of edges on that path. Let D be the maximum depth of any node occurrence of root. Consider all node occurrences at depth D and order their paths lexicographically with L < R, so this is the left-to-right order of that row. The bottom-left value is the stored i64 value at the unique occurrence at depth D whose path is lexicographically least; r equals that value.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_1 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∃ r : Std.I64, find_bottom_left_value root = Result.ok r ∧ IsBottomLeftValue root r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∃ r : Std.I64, find_bottom_left_value root = Result.ok r ∧ IsBottomLeftValue root r.val) := by
    sorry

  /-- For every root satisfying the preconditions, the function returns a result r; it does not fail, panic, or return an error.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_2 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∃ r : Std.I64, find_bottom_left_value root = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∃ r : Std.I64, find_bottom_left_value root = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r for root, there exists a node occurrence n of root such that depth(n) = D(root), where D(root) is the maximum depth of any node occurrence of root, and the stored value at n is r.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_3 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
        ∃ p : List Dir, IsOccurrence root p ∧ depthOf p = maxDepth root ∧
          valueAt root p = some r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
          ∃ p : List Dir, IsOccurrence root p ∧ depthOf p = maxDepth root ∧
            valueAt root p = some r.val) := by
    sorry

  /-- Whenever the function returns a result r for root, let mn be the minimum stored value among all node occurrences of root and let mx be the maximum stored value among all node occurrences of root; then mn <= r <= mx.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_4 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
        ∀ mn mx : Int, minValue root = some mn → maxValue root = some mx →
          mn ≤ r.val ∧ r.val ≤ mx := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
          ∀ mn mx : Int, minValue root = some mn → maxValue root = some mx →
            mn ≤ r.val ∧ r.val ≤ mx) := by
    sorry

  /-- Whenever the function returns a result r for root, if exactly one node occurrence of root has depth D(root), where D(root) is the maximum depth of any node occurrence of root, then r equals the stored value at that unique occurrence.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_5 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
        (∃ p : List Dir, IsOccurrence root p ∧ depthOf p = maxDepth root ∧
          ∀ q : List Dir, IsOccurrence root q → depthOf q = maxDepth root → q = p) →
        ∀ p : List Dir, IsOccurrence root p → depthOf p = maxDepth root →
          valueAt root p = some r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
          (∃ p : List Dir, IsOccurrence root p ∧ depthOf p = maxDepth root ∧
            ∀ q : List Dir, IsOccurrence root q → depthOf q = maxDepth root → q = p) →
          ∀ p : List Dir, IsOccurrence root p → depthOf p = maxDepth root →
            valueAt root p = some r.val) := by
    sorry

  /-- Whenever the function returns a result r for root, there exists a node occurrence l of root whose stored value is r and whose left child and right child are both Null.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_6 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
        ∃ p : List Dir, ∃ v : Std.I64,
          nodeAt root p = some (Tree.Node v Tree.Null Tree.Null) ∧ r.val = v.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
          ∃ p : List Dir, ∃ v : Std.I64,
            nodeAt root p = some (Tree.Node v Tree.Null Tree.Null) ∧ r.val = v.val) := by
    sorry

  /-- Whenever the function returns a result r for root, r equals the bottom-left value of L, defined within L as the stored value at the maximum-depth node occurrence of L whose root-to-node path within L is lexicographically least over {L,R} with L < R.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, every stored value is in [-2^31, 2^31-1], and root is Node(v, L, R) for some i64 v and subtrees L and R such that L is not Null and H(L) >= H(R), where H(Null) = -1 and H(Node(_, a, b)) = 1 + max(H(a), H(b)). -/
  theorem spec_7 (root : Tree) (v : Std.I64) (L R : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root)
      (hroot : root = Tree.Node v L R)
      (hL : L ≠ Tree.Null)
      (hH : height R ≤ height L) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r → IsBottomLeftValue L r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (L R : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root)
        (hroot : root = Tree.Node v L R)
        (hL : L ≠ Tree.Null)
        (hH : height R ≤ height L), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r → IsBottomLeftValue L r.val) := by
    sorry

  /-- Whenever the function returns a result r for root, r equals the bottom-left value of R, defined within R as the stored value at the maximum-depth node occurrence of R whose root-to-node path within R is lexicographically least over {L,R} with L < R.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, every stored value is in [-2^31, 2^31-1], and root is Node(v, L, R) for some i64 v and subtrees L and R such that R is not Null and H(R) > H(L), where H(Null) = -1 and H(Node(_, a, b)) = 1 + max(H(a), H(b)). -/
  theorem spec_8 (root : Tree) (v : Std.I64) (L R : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root)
      (hroot : root = Tree.Node v L R)
      (hR : R ≠ Tree.Null)
      (hH : height L < height R) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r → IsBottomLeftValue R r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (v : Std.I64) (L R : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root)
        (hroot : root = Tree.Node v L R)
        (hR : R ≠ Tree.Null)
        (hH : height L < height R), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r → IsBottomLeftValue R r.val) := by
    sorry

  /-- Whenever the function returns result r for T and result r' for T', we have r = r'.
    Preconditions: T and T' are finite binary trees, each with between 1 and 10000 node occurrences and all stored values in [-2^31, 2^31-1], and T and T' have the same shape (both are Null, or both are Node with same-shaped left subtrees and same-shaped right subtrees). Let p be the lexicographically least root-to-node path among node occurrences of T at maximum depth D(T), where paths are ordered lexicographically with L < R. Assume T and T' store the same i64 value at path p, which exists in T' because the shapes agree. -/
  theorem spec_9 (T T' : Tree) (p : List Dir)
      (hcountT : 1 ≤ nodeCount T ∧ nodeCount T ≤ 10000)
      (hvalsT : AllValuesInI32Range T)
      (hcountT' : 1 ≤ nodeCount T' ∧ nodeCount T' ≤ 10000)
      (hvalsT' : AllValuesInI32Range T')
      (hshape : SameShape T T')
      (hp : IsBottomLeftPath T p)
      (hval : valueAt T p = valueAt T' p) :
      ∀ r r' : Std.I64, find_bottom_left_value T = Result.ok r →
        find_bottom_left_value T' = Result.ok r' → r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (T T' : Tree) (p : List Dir)
        (hcountT : 1 ≤ nodeCount T ∧ nodeCount T ≤ 10000)
        (hvalsT : AllValuesInI32Range T)
        (hcountT' : 1 ≤ nodeCount T' ∧ nodeCount T' ≤ 10000)
        (hvalsT' : AllValuesInI32Range T')
        (hshape : SameShape T T')
        (hp : IsBottomLeftPath T p)
        (hval : valueAt T p = valueAt T' p), ∀ r r' : Std.I64, find_bottom_left_value T = Result.ok r →
          find_bottom_left_value T' = Result.ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r for root, if every node occurrence of root at depth D(root) has the same stored value v, where D(root) is the maximum depth of any node occurrence of root, then r = v.
    Preconditions: root is a finite binary tree with between 1 and 10000 node occurrences, and every stored value is in [-2^31, 2^31-1]. -/
  theorem spec_10 (root : Tree)
      (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
      (hvals : AllValuesInI32Range root) :
      ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
        ∀ v : Std.I64,
          (∀ p : List Dir, IsOccurrence root p → depthOf p = maxDepth root →
            valueAt root p = some v.val) →
          r.val = v.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hcount : 1 ≤ nodeCount root ∧ nodeCount root ≤ 10000)
        (hvals : AllValuesInI32Range root), ∀ r : Std.I64, find_bottom_left_value root = Result.ok r →
          ∀ v : Std.I64,
            (∀ p : List Dir, IsOccurrence root p → depthOf p = maxDepth root →
              valueAt root p = some v.val) →
            r.val = v.val) := by
    sorry

  /-- Whenever the function returns result r for T and result r' for T', we have r != r'.
    Preconditions: T and T' are finite binary trees, each with between 1 and 10000 node occurrences and all stored values in [-2^31, 2^31-1], and T and T' have the same shape (both are Null, or both are Node with same-shaped left subtrees and same-shaped right subtrees). Let p be the lexicographically least root-to-node path among node occurrences of T at maximum depth D(T), where paths are ordered lexicographically with L < R. Assume T and T' store different i64 values at path p, which exists in T' because the shapes agree. -/
  theorem spec_11 (T T' : Tree) (p : List Dir)
      (hcountT : 1 ≤ nodeCount T ∧ nodeCount T ≤ 10000)
      (hvalsT : AllValuesInI32Range T)
      (hcountT' : 1 ≤ nodeCount T' ∧ nodeCount T' ≤ 10000)
      (hvalsT' : AllValuesInI32Range T')
      (hshape : SameShape T T')
      (hp : IsBottomLeftPath T p)
      (hval : valueAt T p ≠ valueAt T' p) :
      ∀ r r' : Std.I64, find_bottom_left_value T = Result.ok r →
        find_bottom_left_value T' = Result.ok r' → r.val ≠ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (T T' : Tree) (p : List Dir)
        (hcountT : 1 ≤ nodeCount T ∧ nodeCount T ≤ 10000)
        (hvalsT : AllValuesInI32Range T)
        (hcountT' : 1 ≤ nodeCount T' ∧ nodeCount T' ≤ 10000)
        (hvalsT' : AllValuesInI32Range T')
        (hshape : SameShape T T')
        (hp : IsBottomLeftPath T p)
        (hval : valueAt T p ≠ valueAt T' p), ∀ r r' : Std.I64, find_bottom_left_value T = Result.ok r →
          find_bottom_left_value T' = Result.ok r' → r.val ≠ r'.val) := by
    sorry

  end AegisSpec.FindBottomLeftValue
