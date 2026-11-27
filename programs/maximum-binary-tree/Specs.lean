import Aegis.ConstructMaximumBinaryTree.Code.Funs

/-!
# Specifications of `Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree`

LeetCode problem `maximum-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.ConstructMaximumBinaryTree

  open Aegis.ConstructMaximumBinaryTree

  def treeValues : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (treeValues l ++ treeValues r)

  def rootValue : Tree → Option ℤ
    | Tree.Null => none
    | Tree.Node v _ _ => some v.val

  def countNodes : Tree → ℕ
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + countNodes l + countNodes r

  def inorder : Tree → List Std.I64
    | Tree.Null => []
    | Tree.Node v l r => inorder l ++ v :: inorder r

  def height : Tree → ℕ
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + max (height l) (height r)

  def subtrees : Tree → List Tree
    | Tree.Null => []
    | Tree.Node v l r => Tree.Node v l r :: (subtrees l ++ subtrees r)

  def findNode : Tree → ℤ → Option Tree
    | Tree.Null, _ => none
    | Tree.Node v l r, x =>
        if v.val = x then some (Tree.Node v l r)
        else (match findNode l x with
              | some t => some t
              | none => findNode r x)

  def leftChildOf (t : Tree) (x : ℤ) : Option Tree :=
    (findNode t x).bind (fun n =>
      match n with
      | Tree.Null => none
      | Tree.Node _ l _ => some l)

  def rightChildOf (t : Tree) (x : ℤ) : Option Tree :=
    (findNode t x).bind (fun n =>
      match n with
      | Tree.Null => none
      | Tree.Node _ _ r => some r)

  def IsMaxHeap : Tree → Prop
    | Tree.Null => True
    | Tree.Node v l r =>
        (∀ w ∈ treeValues l, w < v.val) ∧ (∀ w ∈ treeValues r, w < v.val) ∧
          IsMaxHeap l ∧ IsMaxHeap r

  def ParentValue : Tree → ℤ → ℤ → Prop
    | Tree.Null, _, _ => False
    | Tree.Node v l r, c, p =>
        ParentValue l c p ∨ ParentValue r c p ∨
          (v.val = p ∧ (rootValue l = some c ∨ rootValue r = some c))

  def valAt (l : List Std.I64) (i : ℕ) : ℤ := ((l[i]?).map (fun x => x.val)).getD 0

  def subList {α : Type} (l : List α) (a b : ℕ) : List α := (l.drop a).take (b - a)

  def maxVal (l : List Std.I64) : ℤ := ((l.map (fun x => x.val)).max?).getD 0

  def IsLastGreaterIdx (l : List Std.I64) (i j : ℕ) : Prop :=
    j < i ∧ valAt l i < valAt l j ∧ ∀ j', j < j' → j' < i → ¬ (valAt l i < valAt l j')

  def IsFirstGreaterIdx (l : List Std.I64) (i j : ℕ) : Prop :=
    i < j ∧ j < l.length ∧ valAt l i < valAt l j ∧
      ∀ j', i < j' → j' < j → ¬ (valAt l i < valAt l j')

  def argmaxIdx? : (l : List Std.I64) → Option { i : ℕ // i < l.length }
    | [] => none
    | x :: xs =>
        match argmaxIdx? xs with
        | none => some ⟨0, by simp⟩
        | some ik =>
            if (xs[ik.1]'ik.2).val > x.val then
              some ⟨ik.1 + 1, by have := ik.2; simp only [List.length_cons]; omega⟩
            else some ⟨0, by simp⟩

  def M (xs : List Std.I64) : Tree :=
    match argmaxIdx? xs with
    | none => Tree.Null
    | some k => Tree.Node (xs[k.1]'k.2) (M (xs.take k.1)) (M (xs.drop (k.1 + 1)))
  termination_by xs.length
  decreasing_by
    · simp only [List.length_take]; have := k.2; omega
    · simp only [List.length_drop]; have := k.2; omega

  /-- Define M for any list xs of pairwise distinct integers by: M([]) = Null; if xs is nonempty, let k be the unique index with 0 <= k < len(xs) and xs[k] = max(xs), and set M(xs) = Node(xs[k], M(xs[0..k)), M(xs[k+1..len(xs)))). Here xs[a..b) is the sublist of elements at indices a through b-1. Whenever construct_maximum_binary_tree(nums) returns a result r, r = M(nums).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        r = M nums.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          r = M nums.val) := by
    sorry

  /-- For every input satisfying the preconditions, construct_maximum_binary_tree(nums) returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∃ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∃ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, there exist v, L, and R such that r = Node(v, L, R), and v = max(nums[0], ..., nums[len(nums)-1]).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∃ (v : Std.I64) (L R : Tree), r = Tree.Node v L R ∧ v.val = maxVal nums.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∃ (v : Std.I64) (L R : Tree), r = Tree.Node v L R ∧ v.val = maxVal nums.val) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, count_nodes(r) = len(nums), where count_nodes(Null) = 0 and count_nodes(Node(v, L, R)) = 1 + count_nodes(L) + count_nodes(R).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        countNodes r = nums.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          countNodes r = nums.val.length) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, inorder(r) = [nums[0], nums[1], ..., nums[len(nums)-1]], where inorder(Null) = [] and inorder(Node(v, L, R)) = inorder(L) ++ [v] ++ inorder(R).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        inorder r = nums.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          inorder r = nums.val) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every node u of r with value v, every node value w occurring in the left subtree of u or in the right subtree of u satisfies w < v. Occurrence in a subtree is defined recursively through child subtrees.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        IsMaxHeap r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          IsMaxHeap r) := by
    sorry

  /-- Let k be the unique index with 0 <= k < len(nums) and nums[k] = max(nums). Whenever construct_maximum_binary_tree(nums) returns a result r, r = Node(nums[k], L, R) for some L and R, and the values occurring in L are exactly the values nums[i] with 0 <= i < k, each occurring exactly once; the values occurring in R are exactly the values nums[i] with k < i < len(nums), each occurring exactly once.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (k : ℕ) (hk : k < nums.val.length)
      (hmax : (nums.val[k]'hk).val = maxVal nums.val) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∃ L R : Tree, r = Tree.Node (nums.val[k]'hk) L R ∧
          (treeValues L).Nodup ∧
          (treeValues L).Perm ((nums.val.take k).map (fun x => x.val)) ∧
          (treeValues R).Nodup ∧
          (treeValues R).Perm ((nums.val.drop (k + 1)).map (fun x => x.val)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (k : ℕ) (hk : k < nums.val.length)
        (hmax : (nums.val[k]'hk).val = maxVal nums.val), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∃ L R : Tree, r = Tree.Node (nums.val[k]'hk) L R ∧
            (treeValues L).Nodup ∧
            (treeValues L).Perm ((nums.val.take k).map (fun x => x.val)) ∧
            (treeValues R).Nodup ∧
            (treeValues R).Perm ((nums.val.drop (k + 1)).map (fun x => x.val))) := by
    sorry

  /-- Let k be the unique index with 0 <= k < len(nums) and nums[k] = max(nums). Whenever construct_maximum_binary_tree(nums) returns a result r = Node(v, L, R), count_nodes(L) = k and count_nodes(R) = len(nums) - 1 - k, where count_nodes(Null) = 0 and count_nodes(Node(w, A, B)) = 1 + count_nodes(A) + count_nodes(B).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (k : ℕ) (hk : k < nums.val.length)
      (hmax : (nums.val[k]'hk).val = maxVal nums.val) :
      ∀ (r : Tree) (v : Std.I64) (L R : Tree),
        Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        r = Tree.Node v L R →
        countNodes L = k ∧ countNodes R = nums.val.length - 1 - k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (k : ℕ) (hk : k < nums.val.length)
        (hmax : (nums.val[k]'hk).val = maxVal nums.val), ∀ (r : Tree) (v : Std.I64) (L R : Tree),
          Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          r = Tree.Node v L R →
          countNodes L = k ∧ countNodes R = nums.val.length - 1 - k) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every node u of r, if s is the list of values in the subtree rooted at u in inorder (left subtree, then the value of u, then right subtree), then there exist integers a and b with 0 <= a <= b <= len(nums) such that s = [nums[a], nums[a+1], ..., nums[b-1]]. Here the list is empty when a = b.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ u ∈ subtrees r, ∃ a b : ℕ,
          a ≤ b ∧ b ≤ nums.val.length ∧ inorder u = subList nums.val a b := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ u ∈ subtrees r, ∃ a b : ℕ,
            a ≤ b ∧ b ≤ nums.val.length ∧ inorder u = subList nums.val a b) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, the following holds for every index i with 0 <= i < len(nums) for which nums[i] is not the maximum value of nums. Let jL be the largest index j < i with nums[j] > nums[i], if such an index exists, and let jR be the smallest index j > i with nums[j] > nums[i], if such an index exists. At least one of jL and jR exists. Let p be nums[jL] if only jL exists, nums[jR] if only jR exists, and min(nums[jL], nums[jR]) if both exist. Then in r the node with value nums[i] has a parent with value p; that is, the node with value p has as a left child or a right child the node with value nums[i].
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        (∀ i (_ : i < nums.val.length), valAt nums.val i ≠ maxVal nums.val →
          (∃ j, j < i ∧ valAt nums.val i < valAt nums.val j) ∨
          (∃ j, i < j ∧ j < nums.val.length ∧ valAt nums.val i < valAt nums.val j)) ∧
        (∀ i (_ : i < nums.val.length), valAt nums.val i ≠ maxVal nums.val →
          ∃ p : ℤ, ParentValue r (valAt nums.val i) p ∧
            (((∃ jL, IsLastGreaterIdx nums.val i jL ∧ p = valAt nums.val jL) ∧
                (∀ jR, ¬ IsFirstGreaterIdx nums.val i jR)) ∨
             ((∃ jR, IsFirstGreaterIdx nums.val i jR ∧ p = valAt nums.val jR) ∧
                (∀ jL, ¬ IsLastGreaterIdx nums.val i jL)) ∨
             (∃ jL jR, IsLastGreaterIdx nums.val i jL ∧ IsFirstGreaterIdx nums.val i jR ∧
                p = min (valAt nums.val jL) (valAt nums.val jR)))) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          (∀ i (_ : i < nums.val.length), valAt nums.val i ≠ maxVal nums.val →
            (∃ j, j < i ∧ valAt nums.val i < valAt nums.val j) ∨
            (∃ j, i < j ∧ j < nums.val.length ∧ valAt nums.val i < valAt nums.val j)) ∧
          (∀ i (_ : i < nums.val.length), valAt nums.val i ≠ maxVal nums.val →
            ∃ p : ℤ, ParentValue r (valAt nums.val i) p ∧
              (((∃ jL, IsLastGreaterIdx nums.val i jL ∧ p = valAt nums.val jL) ∧
                  (∀ jR, ¬ IsFirstGreaterIdx nums.val i jR)) ∨
               ((∃ jR, IsFirstGreaterIdx nums.val i jR ∧ p = valAt nums.val jR) ∧
                  (∀ jL, ¬ IsLastGreaterIdx nums.val i jL)) ∨
               (∃ jL jR, IsLastGreaterIdx nums.val i jL ∧ IsFirstGreaterIdx nums.val i jR ∧
                  p = min (valAt nums.val jL) (valAt nums.val jR))))) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every integer x, x occurs as the value of some node of r if and only if there exists an index i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ x : ℤ, x ∈ treeValues r ↔ x ∈ nums.val.map (fun y => y.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ x : ℤ, x ∈ treeValues r ↔ x ∈ nums.val.map (fun y => y.val)) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, height(r) <= len(nums) <= 1000, where height(Null) = 0 and height(Node(v, L, R)) = 1 + max(height(L), height(R)).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        height r ≤ nums.val.length ∧ nums.val.length ≤ 1000 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          height r ≤ nums.val.length ∧ nums.val.length ≤ 1000) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, r = Node(nums[0], Null, Null).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. Additionally n = 1. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (hlength : nums.val.length = 1) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        r = Tree.Node (nums.val[0]'(by omega)) Tree.Null Tree.Null := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (hlength : nums.val.length = 1), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          r = Tree.Node (nums.val[0]'(by omega)) Tree.Null Tree.Null) := by
    sorry

  /-- Let k be the unique index with 0 <= k < len(nums) and nums[k] = max(nums). Whenever construct_maximum_binary_tree(nums) returns a result r, write r = Node(v, L, R). Then L = Null if and only if k = 0.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (k : ℕ) (hk : k < nums.val.length)
      (hmax : (nums.val[k]'hk).val = maxVal nums.val) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∃ (v : Std.I64) (L R : Tree), r = Tree.Node v L R ∧ (L = Tree.Null ↔ k = 0) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (k : ℕ) (hk : k < nums.val.length)
        (hmax : (nums.val[k]'hk).val = maxVal nums.val), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∃ (v : Std.I64) (L R : Tree), r = Tree.Node v L R ∧ (L = Tree.Null ↔ k = 0)) := by
    sorry

  /-- Let k be the unique index with 0 <= k < len(nums) and nums[k] = max(nums). Whenever construct_maximum_binary_tree(nums) returns a result r, write r = Node(v, L, R). Then R = Null if and only if k = len(nums) - 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. -/
  theorem spec_15 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (k : ℕ) (hk : k < nums.val.length)
      (hmax : (nums.val[k]'hk).val = maxVal nums.val) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∃ (v : Std.I64) (L R : Tree),
          r = Tree.Node v L R ∧ (R = Tree.Null ↔ k = nums.val.length - 1) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (k : ℕ) (hk : k < nums.val.length)
        (hmax : (nums.val[k]'hk).val = maxVal nums.val), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∃ (v : Std.I64) (L R : Tree),
            r = Tree.Node v L R ∧ (R = Tree.Null ↔ k = nums.val.length - 1)) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every index j with 0 <= j < len(nums), the node with value nums[j] has right child Null; its left child is Null when j = 0 and is the node with value nums[j-1] when j > 0.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. Additionally, for every i with 0 <= i < n - 1, nums[i] < nums[i+1]. -/
  theorem spec_16 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (hincr : ∀ i (hi : i < nums.val.length - 1),
        (nums.val[i]'(by omega)).val < (nums.val[i + 1]'(by omega)).val) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ j (_ : j < nums.val.length),
          rightChildOf r (valAt nums.val j) = some Tree.Null ∧
          (j = 0 → leftChildOf r (valAt nums.val j) = some Tree.Null) ∧
          (0 < j → ∃ t : Tree, findNode r (valAt nums.val (j - 1)) = some t ∧
            leftChildOf r (valAt nums.val j) = some t) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (hincr : ∀ i (hi : i < nums.val.length - 1),
          (nums.val[i]'(by omega)).val < (nums.val[i + 1]'(by omega)).val), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ j (_ : j < nums.val.length),
            rightChildOf r (valAt nums.val j) = some Tree.Null ∧
            (j = 0 → leftChildOf r (valAt nums.val j) = some Tree.Null) ∧
            (0 < j → ∃ t : Tree, findNode r (valAt nums.val (j - 1)) = some t ∧
              leftChildOf r (valAt nums.val j) = some t)) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every index j with 0 <= j < len(nums), the node with value nums[j] has left child Null; its right child is Null when j = len(nums) - 1 and is the node with value nums[j+1] when j < len(nums) - 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and nums[0], ..., nums[n-1] are pairwise distinct. Additionally, for every i with 0 <= i < n - 1, nums[i] > nums[i+1]. -/
  theorem spec_17 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup)
      (hdecr : ∀ i (hi : i < nums.val.length - 1),
        (nums.val[i + 1]'(by omega)).val < (nums.val[i]'(by omega)).val) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ j (_ : j < nums.val.length),
          leftChildOf r (valAt nums.val j) = some Tree.Null ∧
          (j = nums.val.length - 1 → rightChildOf r (valAt nums.val j) = some Tree.Null) ∧
          (j < nums.val.length - 1 → ∃ t : Tree, findNode r (valAt nums.val (j + 1)) = some t ∧
            rightChildOf r (valAt nums.val j) = some t) := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup)
        (hdecr : ∀ i (hi : i < nums.val.length - 1),
          (nums.val[i + 1]'(by omega)).val < (nums.val[i]'(by omega)).val), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ j (_ : j < nums.val.length),
            leftChildOf r (valAt nums.val j) = some Tree.Null ∧
            (j = nums.val.length - 1 → rightChildOf r (valAt nums.val j) = some Tree.Null) ∧
            (j < nums.val.length - 1 → ∃ t : Tree, findNode r (valAt nums.val (j + 1)) = some t ∧
              rightChildOf r (valAt nums.val j) = some t)) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, r is the unique binary tree such that inorder(r) = [nums[0],...,nums[n-1]] and every node's value is strictly greater than every value in its left and right subtrees. (This makes explicit that the combination of spec_4, spec_5 and spec_6 already pins down the answer uniquely, so no other tree could also be returned.)
    Preconditions: Let n = len(nums). 1 <= n <= 1000; for every i, 0 <= nums[i] <= 1000; nums[0],...,nums[n-1] are pairwise distinct. -/
  theorem spec_18 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        (inorder r = nums.val ∧ IsMaxHeap r) ∧
          ∀ t : Tree, inorder t = nums.val → IsMaxHeap t → t = r := by
    sorry

  theorem spec_18_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          (inorder r = nums.val ∧ IsMaxHeap r) ∧
            ∀ t : Tree, inorder t = nums.val → IsMaxHeap t → t = r) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, for every node u of r let [a,b) be the contiguous index range whose inorder values are the values of u's subtree (as in spec_9); then the subtree rooted at u equals M(nums[a..b)), where M is the function defined in spec_1. This strengthens S9 from a mere contiguity/inorder statement to a full structural statement at every node.
    Preconditions: Let n = len(nums). 1 <= n <= 1000; for every i, 0 <= nums[i] <= 1000; nums[0],...,nums[n-1] are pairwise distinct. -/
  theorem spec_19 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ u ∈ subtrees r, ∃ a b : ℕ,
          a ≤ b ∧ b ≤ nums.val.length ∧ inorder u = subList nums.val a b ∧
            u = M (subList nums.val a b) := by
    sorry

  theorem spec_19_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ u ∈ subtrees r, ∃ a b : ℕ,
            a ≤ b ∧ b ≤ nums.val.length ∧ inorder u = subList nums.val a b ∧
              u = M (subList nums.val a b)) := by
    sorry

  /-- Whenever construct_maximum_binary_tree(nums) returns a result r, no value is duplicated: for every integer x, the number of nodes of r whose value is x equals 1 if there is an index i with nums[i] = x, and equals 0 otherwise. (S11 only gives set membership; this states the exact multiplicity, which together with no extra nodes forbids any repeated or spurious node.)
    Preconditions: Let n = len(nums). 1 <= n <= 1000; for every i, 0 <= nums[i] <= 1000; nums[0],...,nums[n-1] are pairwise distinct. -/
  theorem spec_20 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
      (hbound : ∀ i (hi : i < nums.val.length),
        0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
      (hdist : (nums.val.map (fun x => x.val)).Nodup) :
      ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
        ∀ x : ℤ, (treeValues r).count x =
          if x ∈ nums.val.map (fun y => y.val) then 1 else 0 := by
    sorry

  theorem spec_20_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 1000)
        (hbound : ∀ i (hi : i < nums.val.length),
          0 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000)
        (hdist : (nums.val.map (fun x => x.val)).Nodup), ∀ r, Aegis.ConstructMaximumBinaryTree.construct_maximum_binary_tree nums = ok r →
          ∀ x : ℤ, (treeValues r).count x =
            if x ∈ nums.val.map (fun y => y.val) then 1 else 0) := by
    sorry

  end AegisSpec.ConstructMaximumBinaryTree
