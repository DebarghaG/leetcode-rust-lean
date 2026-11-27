import Aegis.SumEvenGrandparent.Code.Funs

/-!
# Specifications of `Aegis.SumEvenGrandparent.sum_even_grandparent`

LeetCode problem `sum-of-nodes-with-even-valued-grandparent`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumEvenGrandparent

  open Aegis.SumEvenGrandparent (Tree)

  abbrev Occ : Type := ℤ × List ℤ

  def nodeOccWith (t : Tree) (anc : List ℤ) : List Occ :=
    match t with
    | Tree.Null => []
    | Tree.Node v l r =>
      (v.val, anc) ::
        (nodeOccWith l (v.val :: anc) ++ nodeOccWith r (v.val :: anc))

  def nodeOcc (t : Tree) : List Occ := nodeOccWith t []

  def nodeCount (t : Tree) : Nat := (nodeOcc t).length

  def nodeValues (t : Tree) : List ℤ := (nodeOcc t).map (fun q => q.1)

  def occSum (t : Tree) (p : Occ → Bool) : ℤ := (((nodeOcc t).filter p).map (fun q => q.1)).sum

  def grandparentValue (q : Occ) : Option ℤ := q.2[1]?

  def HasEvenGrandparent (q : Occ) : Prop := ∃ g, grandparentValue q = some g ∧ g % 2 = 0

  def hasEvenGrandparentB (q : Occ) : Bool :=
    match grandparentValue q with
    | some g => g % 2 == 0
    | none => false

  theorem hasEvenGrandparent_iff (q : Occ) :
      HasEvenGrandparent q ↔ hasEvenGrandparentB q = true := by
    unfold HasEvenGrandparent hasEvenGrandparentB grandparentValue
    cases q.2[1]? with
    | none => simp
    | some g => simp

  def sumAll (t : Tree) : ℤ := occSum t (fun _ => true)

  def sumAtDepth (t : Tree) (d : Nat) : ℤ := occSum t (fun q => q.2.length == d)

  def sumAtDepthAtLeast (t : Tree) (d : Nat) : ℤ := occSum t (fun q => decide (d ≤ q.2.length))

  def grandparentSum (t : Tree) : ℤ := occSum t hasEvenGrandparentB

  def A (t : Tree) : ℤ := grandparentSum t

  def C (t : Tree) : ℤ := sumAtDepth t 1

  def ValuesInRange (t : Tree) : Prop := ∀ q ∈ nodeOcc t, 1 ≤ q.1 ∧ q.1 ≤ 100

  def ValuesEven (t : Tree) : Prop := ∀ q ∈ nodeOcc t, q.1 % 2 = 0

  def DepthAtMostOne (t : Tree) : Prop := ∀ q ∈ nodeOcc t, q.2.length ≤ 1

  def SmallTree (t : Tree) : Prop := nodeCount t ≤ 10000

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  /-- Let s be the mathematical integer represented by the returned I64 r. The function returns a result r, and s is the sum, over all node occurrences x in root that have a grandparent g whose value is even (g.value mod 2 = 0), of x.value. Here the grandparent of x is the parent of the parent of x, so x must be at depth at least 2 when the depth of the root is 0; if x has no grandparent it is not included. If no node occurrence has an even-valued grandparent, s = 0. Node occurrences are counted individually, even when their values coincide.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_1 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r ∧
        r.val = grandparentSum root := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r ∧
          r.val = grandparentSum root) := by
    sorry

  /-- For every root satisfying the preconditions, the function returns a result r (Result.ok of some I64); it does not fail, panic, or overflow.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_2 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, the mathematical integer s represented by r satisfies s >= 0.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_3 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, the mathematical integer s represented by r is at most the sum of the values of all node occurrences in root.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_4 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        r.val ≤ sumAll root := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          r.val ≤ sumAll root) := by
    sorry

  /-- The function returns a result r, and the mathematical integer s represented by r is 0.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, every node value v satisfies 1 <= v <= 100, and every node occurrence in root has depth at most 1. -/
  theorem spec_5 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (hdepth : DepthAtMostOne root) :
      ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r ∧
        r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (hdepth : DepthAtMostOne root), ∃ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r ∧
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, the mathematical integer s represented by r equals the sum of the values of all node occurrences in root whose depth is at least 2.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, every node occurrence has a value v with 1 <= v <= 100, and every node occurrence has an even value (v mod 2 = 0). -/
  theorem spec_6 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (heven : ValuesEven root) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        r.val = sumAtDepthAtLeast root 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (heven : ValuesEven root), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          r.val = sumAtDepthAtLeast root 2) := by
    sorry

  /-- Whenever the function returns a result r, if the mathematical integer s represented by r is nonzero, then there exists at least one node occurrence x in root that has a grandparent g with even value.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_7 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        r.val ≠ 0 → ∃ q ∈ nodeOcc root, HasEvenGrandparent q := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          r.val ≠ 0 → ∃ q ∈ nodeOcc root, HasEvenGrandparent q) := by
    sorry

  /-- Whenever the function returns a result r, for every node occurrence x in root that has a grandparent g with even value, the mathematical integer s represented by r satisfies s >= x.value.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, and for every node occurrence in root its stored value v is an integer with 1 <= v <= 100. -/
  theorem spec_8 (root : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        ∀ q ∈ nodeOcc root, HasEvenGrandparent q → q.1 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          ∀ q ∈ nodeOcc root, HasEvenGrandparent q → q.1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, the mathematical integer s represented by r is at least the sum of the values of all node occurrences in root whose depth is exactly 2.
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, every node value v satisfies 1 <= v <= 100, and root = Node(v, L, R) with v even (v mod 2 = 0). -/
  theorem spec_9 (root L R : Tree) (v : Std.I64)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (hroot : root = Tree.Node v L R)
      (hveven : v.val % 2 = 0) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        sumAtDepth root 2 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root L R : Tree) (v : Std.I64)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (hroot : root = Tree.Node v L R)
        (hveven : v.val % 2 = 0), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          sumAtDepth root 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, the mathematical integer s represented by r equals A(L) + A(R) + (if v is even then C(L) + C(R) else 0), where for any tree T, A(T) is the sum of the values of all node occurrences in T that have an even-valued grandparent located inside T (with T considered as a separate tree and A(Null) = 0), and C(T) is the sum of the values of the immediate children of the root of T (with C(Null) = 0).
    Preconditions: root is a finite non-empty binary tree with at most 10,000 node occurrences, every node value v satisfies 1 <= v <= 100, and root = Node(v, L, R). -/
  theorem spec_10 (root L R : Tree) (v : Std.I64)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (hroot : root = Tree.Node v L R) :
      ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        r.val = A L + A R + (if v.val % 2 = 0 then C L + C R else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root L R : Tree) (v : Std.I64)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (hroot : root = Tree.Node v L R), ∀ r : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          r.val = A L + A R + (if v.val % 2 = 0 then C L + C R else 0)) := by
    sorry

  /-- Whenever the function returns a result r for root and a result r2 for root2, the mathematical integers s and s2 represented by r and r2 satisfy s2 = s + D, where D is the sum of the values of all node occurrences in root whose depth is exactly 2.
    Preconditions: root = Node(v, L, R) and root2 = Node(v2, L, R) are finite non-empty binary trees with at most 10,000 node occurrences, every node occurrence in both trees has value w with 1 <= w <= 100, v is odd (v mod 2 = 1), and v2 is even (v2 mod 2 = 0). -/
  theorem spec_11 (root root2 L R : Tree) (v v2 : Std.I64)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (hne2 : root2 ≠ Tree.Null)
      (hsize2 : SmallTree root2)
      (hval2 : ValuesInRange root2)
      (hroot : root = Tree.Node v L R)
      (hroot2 : root2 = Tree.Node v2 L R)
      (hvodd : v.val % 2 = 1)
      (hveven : v2.val % 2 = 0) :
      ∀ r r2 : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        Aegis.SumEvenGrandparent.sum_even_grandparent root2 = Result.ok r2 →
          r2.val = r.val + sumAtDepth root 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root root2 L R : Tree) (v v2 : Std.I64)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (hne2 : root2 ≠ Tree.Null)
        (hsize2 : SmallTree root2)
        (hval2 : ValuesInRange root2)
        (hroot : root = Tree.Node v L R)
        (hroot2 : root2 = Tree.Node v2 L R)
        (hvodd : v.val % 2 = 1)
        (hveven : v2.val % 2 = 0), ∀ r r2 : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          Aegis.SumEvenGrandparent.sum_even_grandparent root2 = Result.ok r2 →
            r2.val = r.val + sumAtDepth root 2) := by
    sorry

  /-- Whenever the function returns a result r for root and a result r2 for root2, the mathematical integers s and s2 represented by r and r2 are equal.
    Preconditions: root and root2 are finite non-empty binary trees with at most 10,000 node occurrences, every node occurrence in both trees has value w with 1 <= w <= 100, and root2 is obtained from root by recursively swapping the left and right subtrees at every node while keeping all stored values the same. -/
  theorem spec_12 (root root2 : Tree)
      (hne : root ≠ Tree.Null)
      (hsize : SmallTree root)
      (hval : ValuesInRange root)
      (hne2 : root2 ≠ Tree.Null)
      (hsize2 : SmallTree root2)
      (hval2 : ValuesInRange root2)
      (hmirror : root2 = mirror root) :
      ∀ r r2 : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
        Aegis.SumEvenGrandparent.sum_even_grandparent root2 = Result.ok r2 → r2.val = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (root root2 : Tree)
        (hne : root ≠ Tree.Null)
        (hsize : SmallTree root)
        (hval : ValuesInRange root)
        (hne2 : root2 ≠ Tree.Null)
        (hsize2 : SmallTree root2)
        (hval2 : ValuesInRange root2)
        (hmirror : root2 = mirror root), ∀ r r2 : Std.I64, Aegis.SumEvenGrandparent.sum_even_grandparent root = Result.ok r →
          Aegis.SumEvenGrandparent.sum_even_grandparent root2 = Result.ok r2 → r2.val = r.val) := by
    sorry

  end AegisSpec.SumEvenGrandparent
