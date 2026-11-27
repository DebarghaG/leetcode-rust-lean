import Aegis.SortedListToBst.Code.Funs

/-!
# Specifications of `Aegis.SortedListToBst.sorted_list_to_bst`

LeetCode problem `convert-sorted-list-to-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortedListToBst

  def listLen : Aegis.SortedListToBst.List → Nat
    | Aegis.SortedListToBst.List.Nil => 0
    | Aegis.SortedListToBst.List.Cons _ next => listLen next + 1

  def vals : Aegis.SortedListToBst.List → List Int
    | Aegis.SortedListToBst.List.Nil => []
    | Aegis.SortedListToBst.List.Cons v next => v.val :: vals next

  def inorder : Aegis.SortedListToBst.Tree → List Int
    | Aegis.SortedListToBst.Tree.Null => []
    | Aegis.SortedListToBst.Tree.Node x l r => inorder l ++ [x.val] ++ inorder r

  def height : Aegis.SortedListToBst.Tree → Nat
    | Aegis.SortedListToBst.Tree.Null => 0
    | Aegis.SortedListToBst.Tree.Node _ l r => 1 + max (height l) (height r)

  def isBST : Aegis.SortedListToBst.Tree → Prop
    | Aegis.SortedListToBst.Tree.Null => True
    | Aegis.SortedListToBst.Tree.Node x l r =>
      (∀ y ∈ inorder l, y ≤ x.val) ∧ (∀ y ∈ inorder r, x.val ≤ y) ∧
        isBST l ∧ isBST r

  def isHeightBalanced : Aegis.SortedListToBst.Tree → Prop
    | Aegis.SortedListToBst.Tree.Null => True
    | Aegis.SortedListToBst.Tree.Node _ l r =>
      (height l ≤ height r + 1 ∧ height r ≤ height l + 1) ∧
        isHeightBalanced l ∧ isHeightBalanced r

  def Sorted (l : List Int) : Prop := l.Pairwise (· ≤ ·)

  def InBounds (l : List Int) : Prop := ∀ v ∈ l, -100000 ≤ v ∧ v ≤ 100000

  def LenLe (head : Aegis.SortedListToBst.List) : Prop := listLen head ≤ 20000

  /-- Whenever sorted_list_to_bst head = Result.ok T, the tree T is a height-balanced binary search tree whose in-order traversal equals vals(head). Define inorder(Tree.Null)=[] and inorder(Tree.Node(x,L,R))=inorder(L)++[x]++inorder(R). T is a binary search tree iff for every subtree Tree.Node(x,L,R) occurring in T, every element of inorder(L) is <= x and every element of inorder(R) is >= x. Define height(Tree.Null)=0 and height(Tree.Node(_,L,R))=1+max(height(L),height(R)). T is height-balanced iff for every subtree Tree.Node(_,L,R) occurring in T, |height(L)-height(R)| <= 1.
    Preconditions: Let len(head) be the number of nodes in the linked list head. Let vals(head) be the sequence of values of head read from the first node to the last. The list head satisfies: 0 <= len(head) <= 20000; every value in vals(head) is in [-100000, 100000]; and vals(head) is non-decreasing (sorted in ascending order, duplicates allowed). -/
  theorem spec_1 (head : Aegis.SortedListToBst.List)
      (hlen : LenLe head)
      (hbounds : InBounds (vals head))
      (hsorted : Sorted (vals head))
      {T : Aegis.SortedListToBst.Tree}
      (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T) :
      isBST T ∧ isHeightBalanced T ∧ inorder T = vals head := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.SortedListToBst.List)
        (hlen : LenLe head)
        (hbounds : InBounds (vals head))
        (hsorted : Sorted (vals head))
        {T : Aegis.SortedListToBst.Tree}
        (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T), isBST T ∧ isHeightBalanced T ∧ inorder T = vals head) := by
    sorry

  /-- For every head satisfying the preconditions, there exists a tree r such that sorted_list_to_bst head = Result.ok r (i.e., the function does not return Result.fail).
    Preconditions: Let len(head) be the number of nodes in the linked list head. Let vals(head) be the sequence of values of head read from the first node to the last. The list head satisfies: 0 <= len(head) <= 20000; every value in vals(head) is in [-100000, 100000]; and vals(head) is non-decreasing (sorted in ascending order, duplicates allowed). -/
  theorem spec_2 (head : Aegis.SortedListToBst.List)
      (hlen : LenLe head)
      (hbounds : InBounds (vals head))
      (hsorted : Sorted (vals head)) :
      ∃ r : Aegis.SortedListToBst.Tree,
        Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.SortedListToBst.List)
        (hlen : LenLe head)
        (hbounds : InBounds (vals head))
        (hsorted : Sorted (vals head)), ∃ r : Aegis.SortedListToBst.Tree,
          Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok r) := by
    sorry

  /-- Whenever sorted_list_to_bst head = Result.ok T, inorder(T) = vals(head), where inorder(Tree.Null)=[] and inorder(Tree.Node(x,L,R))=inorder(L)++[x]++inorder(R).
    Preconditions: Let len(head) be the number of nodes in the linked list head. Let vals(head) be the sequence of values of head read from the first node to the last. The list head satisfies: 0 <= len(head) <= 20000; every value in vals(head) is in [-100000, 100000]; and vals(head) is non-decreasing (sorted in ascending order, duplicates allowed). -/
  theorem spec_3 (head : Aegis.SortedListToBst.List)
      (hlen : LenLe head)
      (hbounds : InBounds (vals head))
      (hsorted : Sorted (vals head))
      {T : Aegis.SortedListToBst.Tree}
      (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T) :
      inorder T = vals head := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.SortedListToBst.List)
        (hlen : LenLe head)
        (hbounds : InBounds (vals head))
        (hsorted : Sorted (vals head))
        {T : Aegis.SortedListToBst.Tree}
        (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T), inorder T = vals head) := by
    sorry

  /-- Whenever sorted_list_to_bst head = Result.ok T, T is a binary search tree: for every subtree Tree.Node(x,L,R) occurring in T, every element of inorder(L) is <= x and every element of inorder(R) is >= x, where inorder(Tree.Null)=[] and inorder(Tree.Node(y,L,R))=inorder(L)++[y]++inorder(R).
    Preconditions: Let len(head) be the number of nodes in the linked list head. Let vals(head) be the sequence of values of head read from the first node to the last. The list head satisfies: 0 <= len(head) <= 20000; every value in vals(head) is in [-100000, 100000]; and vals(head) is non-decreasing (sorted in ascending order, duplicates allowed). -/
  theorem spec_4 (head : Aegis.SortedListToBst.List)
      (hlen : LenLe head)
      (hbounds : InBounds (vals head))
      (hsorted : Sorted (vals head))
      {T : Aegis.SortedListToBst.Tree}
      (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T) :
      isBST T := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.SortedListToBst.List)
        (hlen : LenLe head)
        (hbounds : InBounds (vals head))
        (hsorted : Sorted (vals head))
        {T : Aegis.SortedListToBst.Tree}
        (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T), isBST T) := by
    sorry

  /-- Whenever sorted_list_to_bst head = Result.ok T, T is height-balanced: for every subtree Tree.Node(_,L,R) occurring in T, |height(L)-height(R)| <= 1, where height(Tree.Null)=0 and height(Tree.Node(_,L,R))=1+max(height(L),height(R)).
    Preconditions: Let len(head) be the number of nodes in the linked list head. Let vals(head) be the sequence of values of head read from the first node to the last. The list head satisfies: 0 <= len(head) <= 20000; every value in vals(head) is in [-100000, 100000]; and vals(head) is non-decreasing (sorted in ascending order, duplicates allowed). -/
  theorem spec_5 (head : Aegis.SortedListToBst.List)
      (hlen : LenLe head)
      (hbounds : InBounds (vals head))
      (hsorted : Sorted (vals head))
      {T : Aegis.SortedListToBst.Tree}
      (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T) :
      isHeightBalanced T := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.SortedListToBst.List)
        (hlen : LenLe head)
        (hbounds : InBounds (vals head))
        (hsorted : Sorted (vals head))
        {T : Aegis.SortedListToBst.Tree}
        (hT : Aegis.SortedListToBst.sorted_list_to_bst head = Result.ok T), isHeightBalanced T) := by
    sorry

  end AegisSpec.SortedListToBst
