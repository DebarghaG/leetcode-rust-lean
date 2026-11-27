import Aegis.SortedArrayToBst.Code.Funs

/-!
# Specifications of `Aegis.SortedArrayToBst.sorted_array_to_bst`

LeetCode problem `convert-sorted-array-to-binary-search-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortedArrayToBst

  open Aegis.SortedArrayToBst (Tree sorted_array_to_bst)

  def LengthInRange (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 10000

  def ValuesInRange (nums : Slice Std.I64) : Prop :=
    ∀ (i : Nat) (hi : i < nums.val.length), -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000

  def StrictlyIncreasing (nums : Slice Std.I64) : Prop :=
    ∀ (i : Nat) (hi : i + 1 < nums.val.length), (nums.val[i]).val < (nums.val[i + 1]).val

  def InputOk (nums : Slice Std.I64) : Prop :=
    LengthInRange nums ∧ ValuesInRange nums ∧ StrictlyIncreasing nums

  def Height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (Height l) (Height r)

  def Inorder : Tree → List Std.I64
    | Tree.Null => []
    | Tree.Node v l r => Inorder l ++ [v] ++ Inorder r

  def Occurs (x : Int) : Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => v.val = x ∨ Occurs x l ∨ Occurs x r

  def HeightClose (l r : Tree) : Prop :=
    Height l ≤ Height r + 1 ∧ Height r ≤ Height l + 1

  def Balanced : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => Balanced l ∧ Balanced r ∧ HeightClose l r

  def AllNodesHeightClose : Tree → Prop
    | Tree.Null => True
    | Tree.Node _ l r => AllNodesHeightClose l ∧ AllNodesHeightClose r ∧ HeightClose l r

  def IsBst : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        IsBst l ∧ IsBst r ∧ (∀ x : Int, Occurs x l → x < v.val) ∧
          (∀ x : Int, Occurs x r → v.val < x)

  /-- The function returns a result r (it does not fail), and r is a height-balanced binary search tree whose inorder traversal is exactly nums. Concretely: define height(Null)=0 and height(Node(v,l,rr))=1+max(height(l),height(rr)); say a tree is height-balanced if every node t=Node(v,l,rr) satisfies balanced(l), balanced(rr), and |height(l)-height(rr)| <= 1, with Null balanced. Define inorder(Null)=[] and inorder(Node(v,l,rr))=inorder(l) ++ [v] ++ inorder(rr). Say a tree is a BST if for every node t=Node(v,l,rr), every value occurring in l is strictly less than v and every value occurring in rr is strictly greater than v. Then r is height-balanced, r is a BST, and inorder(r)=nums.
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_1 (nums : Slice Std.I64) (h : InputOk nums) :
      ∃ r : Tree, sorted_array_to_bst nums = ok r ∧ Balanced r ∧ IsBst r ∧ Inorder r = nums.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums), ∃ r : Tree, sorted_array_to_bst nums = ok r ∧ Balanced r ∧ IsBst r ∧ Inorder r = nums.val) := by
    sorry

  /-- The function returns a result r on every input satisfying the preconditions; no failure (panic, out-of-bounds access, or arithmetic overflow) occurs.
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_2 (nums : Slice Std.I64) (h : InputOk nums) :
      ∃ r : Tree, sorted_array_to_bst nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums), ∃ r : Tree, sorted_array_to_bst nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the inorder traversal of r is exactly nums: define inorder(Null)=[] and inorder(Node(v,l,rr))=inorder(l) ++ [v] ++ inorder(rr); then inorder(r)=nums.
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_3 (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
      (hr : sorted_array_to_bst nums = ok r) : Inorder r = nums.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
        (hr : sorted_array_to_bst nums = ok r), Inorder r = nums.val) := by
    sorry

  /-- Whenever the function returns a result r, r satisfies the binary-search-tree order: for every node t=Node(v,l,rr) of r, every value occurring in l is strictly less than v, and every value occurring in rr is strictly greater than v.
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_4 (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
      (hr : sorted_array_to_bst nums = ok r) : IsBst r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
        (hr : sorted_array_to_bst nums = ok r), IsBst r) := by
    sorry

  /-- Whenever the function returns a result r, r is height-balanced: with height(Null)=0 and height(Node(v,l,rr))=1+max(height(l),height(rr)), every node t=Node(v,l,rr) of r satisfies |height(l)-height(rr)| <= 1.
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_5 (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
      (hr : sorted_array_to_bst nums = ok r) : AllNodesHeightClose r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
        (hr : sorted_array_to_bst nums = ok r), AllNodesHeightClose r) := by
    sorry

  /-- Whenever the function returns a result r, r = Node(nums[0], Null, Null).
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. Additionally, len(nums)=1. -/
  theorem spec_6 (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 1)
      (r : Tree) (hr : sorted_array_to_bst nums = ok r) :
      r = Tree.Node (nums.val[0]) Tree.Null Tree.Null := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 1)
        (r : Tree) (hr : sorted_array_to_bst nums = ok r), r = Tree.Node (nums.val[0]) Tree.Null Tree.Null) := by
    sorry

  /-- Whenever the function returns a result r, either r = Node(nums[0], Null, Node(nums[1], Null, Null)) or r = Node(nums[1], Node(nums[0], Null, Null), Null).
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. Additionally, len(nums)=2. -/
  theorem spec_7 (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 2)
      (r : Tree) (hr : sorted_array_to_bst nums = ok r) :
      r = Tree.Node (nums.val[0]) Tree.Null (Tree.Node (nums.val[1]) Tree.Null Tree.Null) ∨
        r = Tree.Node (nums.val[1]) (Tree.Node (nums.val[0]) Tree.Null Tree.Null) Tree.Null := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 2)
        (r : Tree) (hr : sorted_array_to_bst nums = ok r), r = Tree.Node (nums.val[0]) Tree.Null (Tree.Node (nums.val[1]) Tree.Null Tree.Null) ∨
          r = Tree.Node (nums.val[1]) (Tree.Node (nums.val[0]) Tree.Null Tree.Null) Tree.Null) := by
    sorry

  /-- Whenever the function returns a result r, r = Node(nums[1], Node(nums[0], Null, Null), Node(nums[2], Null, Null)).
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. Additionally, len(nums)=3. -/
  theorem spec_8 (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 3)
      (r : Tree) (hr : sorted_array_to_bst nums = ok r) :
      r = Tree.Node (nums.val[1]) (Tree.Node (nums.val[0]) Tree.Null Tree.Null)
        (Tree.Node (nums.val[2]) Tree.Null Tree.Null) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (hlen : nums.val.length = 3)
        (r : Tree) (hr : sorted_array_to_bst nums = ok r), r = Tree.Node (nums.val[1]) (Tree.Node (nums.val[0]) Tree.Null Tree.Null)
          (Tree.Node (nums.val[2]) Tree.Null Tree.Null)) := by
    sorry

  /-- Whenever the function returns a result r, r is not Null; write r = Node(v,l,rr). Then there exists an index k with 0 <= k < len(nums) such that v = nums[k], inorder(l) = [nums[0],...,nums[k-1]] (empty if k=0), and inorder(rr) = [nums[k+1],...,nums[len(nums)-1]] (empty if k=len(nums)-1), where inorder(Null)=[] and inorder(Node(x,a,b))=inorder(a) ++ [x] ++ inorder(b).
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. -/
  theorem spec_9 (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
      (hr : sorted_array_to_bst nums = ok r) :
      ∃ (k : Nat) (hk : k < nums.val.length) (v : Std.I64) (l rr : Tree),
        r = Tree.Node v l rr ∧ v = nums.val[k] ∧ Inorder l = nums.val.take k ∧
          Inorder rr = nums.val.drop (k + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (r : Tree)
        (hr : sorted_array_to_bst nums = ok r), ∃ (k : Nat) (hk : k < nums.val.length) (v : Std.I64) (l rr : Tree),
          r = Tree.Node v l rr ∧ v = nums.val[k] ∧ Inorder l = nums.val.take k ∧
            Inorder rr = nums.val.drop (k + 1)) := by
    sorry

  /-- Whenever the function returns a result r, writing r = Node(v,l,rr), the root value v is neither nums[0] nor nums[len(nums)-1].
    Preconditions: nums is a slice of 64-bit integers satisfying the problem constraints: 1 <= len(nums) <= 10000; -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums); and nums[i] < nums[i+1] for every i with 0 <= i < len(nums)-1, so nums is strictly increasing. Additionally, len(nums) >= 3. -/
  theorem spec_10 (nums : Slice Std.I64) (h : InputOk nums) (hlen : 3 ≤ nums.val.length)
      (r : Tree) (hr : sorted_array_to_bst nums = ok r) :
      ∀ (v : Std.I64) (l rr : Tree), r = Tree.Node v l rr →
        v ≠ nums.val[0] ∧ v ≠ nums.val[nums.val.length - 1] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : InputOk nums) (hlen : 3 ≤ nums.val.length)
        (r : Tree) (hr : sorted_array_to_bst nums = ok r), ∀ (v : Std.I64) (l rr : Tree), r = Tree.Node v l rr →
          v ≠ nums.val[0] ∧ v ≠ nums.val[nums.val.length - 1]) := by
    sorry

  end AegisSpec.SortedArrayToBst
