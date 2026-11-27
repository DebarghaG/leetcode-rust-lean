import Aegis.ConstructFromPrePost.Code.Funs

/-!
# Specifications of `Aegis.ConstructFromPrePost.construct_from_pre_post`

LeetCode problem `construct-binary-tree-from-preorder-and-postorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConstructFromPrePost

  open Aegis.ConstructFromPrePost (Tree construct_from_pre_post)

  def pre : Tree → List Aeneas.Std.I64
    | Tree.Null => []
    | Tree.Node v l r => [v] ++ pre l ++ pre r

  def post : Tree → List Aeneas.Std.I64
    | Tree.Null => []
    | Tree.Node v l r => post l ++ post r ++ [v]

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def nullCount : Tree → Nat
    | Tree.Null => 1
    | Tree.Node _ l r => nullCount l + nullCount r

  def nodeValues : Tree → List Aeneas.Std.I64
    | Tree.Null => []
    | Tree.Node v l r => v :: (nodeValues l ++ nodeValues r)

  def listSlice {α : Type} (xs : List α) (a b : Nat) : List α := (xs.drop a).take (b - a)

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, the value r is a Tree satisfying pre(r)=preorder and post(r)=postorder.
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_1 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        pre r = preorder.val ∧ post r = postorder.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          pre r = preorder.val ∧ post r = postorder.val) := by
    sorry

  /-- construct_from_pre_post(preorder, postorder) returns a result r (an Ok value, not Err); equivalently, on every valid input it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_2 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∃ r : Tree, construct_from_pre_post preorder postorder = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∃ r : Tree, construct_from_pre_post preorder postorder = ok r) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, r is not Null, and if r=Node(v,L,R) then v=preorder[0].
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_3 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        r ≠ Tree.Null ∧
        ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
          v = preorder.val[0]'(by omega) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          r ≠ Tree.Null ∧
          ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
            v = preorder.val[0]'(by omega)) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, r is not Null, and if r=Node(v,L,R) then v=postorder[len(postorder)-1].
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_4 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        r ≠ Tree.Null ∧
        ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
          v = postorder.val[postorder.val.length - 1]'(by omega) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          r ≠ Tree.Null ∧
          ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
            v = postorder.val[postorder.val.length - 1]'(by omega)) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, the number of Node constructors occurring in r is exactly len(preorder).
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_5 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        nodeCount r = preorder.val.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          nodeCount r = preorder.val.length) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, define nullCount(Null)=1 and nullCount(Node(_,L,R))=nullCount(L)+nullCount(R); then nullCount(r)=len(preorder)+1.
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_6 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        nullCount r = preorder.val.length + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          nullCount r = preorder.val.length + 1) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r, the set of values v for which some Node(v,L,R) occurs in r is exactly the set of values occurring in preorder. Equivalently, every value of preorder occurs exactly once as a Node value in r, and no other i64 value occurs as a Node value in r.
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_7 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        (nodeValues r).Nodup ∧ ∀ x : Std.I64, x ∈ nodeValues r ↔ x ∈ preorder.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          (nodeValues r).Nodup ∧ ∀ x : Std.I64, x ∈ nodeValues r ↔ x ∈ preorder.val) := by
    sorry

  /-- Whenever construct_from_pre_post(preorder, postorder) returns a result r and r=Node(v,L,R), let n=len(preorder), let m=nodeCount(L) where nodeCount(Null)=0 and nodeCount(Node(_,A,B))=1+nodeCount(A)+nodeCount(B), and let xs[a..b] denote the contiguous slice of xs consisting of indices i with a <= i < b. Then 0 <= m <= n-1, pre(L)=preorder[1..m+1], pre(R)=preorder[m+1..n], post(L)=postorder[0..m], and post(R)=postorder[m..n-1].
    Preconditions: Write pre(Null)=[] and pre(Node(v,L,R))=[v] ++ pre(L) ++ pre(R), and post(Null)=[] and post(Node(v,L,R))=post(L) ++ post(R) ++ [v]. The slices preorder and postorder of Std.I64 are valid inputs: 1 <= len(preorder) <= 30; len(postorder)=len(preorder); all values of preorder are distinct; all values of postorder are distinct; every value of preorder and every value of postorder lies in [1, len(preorder)]; and there exists a finite Tree W such that pre(W)=preorder and post(W)=postorder. -/
  theorem spec_8 (preorder postorder : Slice Std.I64)
      (hpre_len : 1 ≤ preorder.val.length)
      (hpre_len_le : preorder.val.length ≤ 30)
      (hpost_len : postorder.val.length = preorder.val.length)
      (hpre_nodup : preorder.val.Nodup)
      (hpost_nodup : postorder.val.Nodup)
      (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
      (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val) :
      ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
        ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
          nodeCount L ≤ preorder.val.length - 1 ∧
          pre L = listSlice preorder.val 1 (nodeCount L + 1) ∧
          pre R = listSlice preorder.val (nodeCount L + 1) preorder.val.length ∧
          post L = listSlice postorder.val 0 (nodeCount L) ∧
          post R = listSlice postorder.val (nodeCount L) (postorder.val.length - 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (preorder postorder : Slice Std.I64)
        (hpre_len : 1 ≤ preorder.val.length)
        (hpre_len_le : preorder.val.length ≤ 30)
        (hpost_len : postorder.val.length = preorder.val.length)
        (hpre_nodup : preorder.val.Nodup)
        (hpost_nodup : postorder.val.Nodup)
        (hpre_bounds : ∀ x ∈ preorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (hpost_bounds : ∀ x ∈ postorder.val, 1 ≤ x.val ∧ x.val ≤ (preorder.val.length : Int))
        (h_exists : ∃ W : Tree, pre W = preorder.val ∧ post W = postorder.val), ∀ r : Tree, construct_from_pre_post preorder postorder = ok r →
          ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
            nodeCount L ≤ preorder.val.length - 1 ∧
            pre L = listSlice preorder.val 1 (nodeCount L + 1) ∧
            pre R = listSlice preorder.val (nodeCount L + 1) preorder.val.length ∧
            post L = listSlice postorder.val 0 (nodeCount L) ∧
            post R = listSlice postorder.val (nodeCount L) (postorder.val.length - 1)) := by
    sorry

  end AegisSpec.ConstructFromPrePost
