import Aegis.BuildTree.Code.Funs

/-!
# Specifications of `Aegis.BuildTree.build_tree`

LeetCode problem `construct-binary-tree-from-inorder-and-postorder-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BuildTree

open Aeneas Aeneas.Std Aeneas.Std.Result Aegis.BuildTree

def inorder_traversal : Tree → List Std.I64
  | Tree.Null => []
  | Tree.Node v l r => inorder_traversal l ++ [v] ++ inorder_traversal r

def postorder_traversal : Tree → List Std.I64
  | Tree.Null => []
  | Tree.Node v l r => postorder_traversal l ++ postorder_traversal r ++ [v]

def node_count : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + node_count l + node_count r

def occurs (v : Std.I64) : Tree → Prop
  | Tree.Null => False
  | Tree.Node w l r => w = v ∨ occurs v l ∨ occurs v r

def label_count (v : Int) : Tree → Nat
  | Tree.Null => 0
  | Tree.Node w l r => (if w.val = v then 1 else 0) + label_count v l + label_count v r

def is_subtree (S : Tree) : Tree → Prop
  | Tree.Null => False
  | Tree.Node v l r => S = Tree.Node v l r ∨ is_subtree S l ∨ is_subtree S r

def postorder_root (postorder : Slice Std.I64) : Option Std.I64 :=
  postorder.val.getLast?

def is_root_index (inorder postorder : Slice Std.I64) (k : Nat) : Prop :=
  k < inorder.val.length ∧ inorder.val[k]? = postorder_root postorder

/-- The function returns a result r and inorder_traversal(r)=inorder and postorder_traversal(r)=postorder.
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_1 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val) :
    ∃ r : Tree, build_tree inorder postorder = ok r ∧
      inorder_traversal r = inorder.val ∧ postorder_traversal r = postorder.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val), ∃ r : Tree, build_tree inorder postorder = ok r ∧
      inorder_traversal r = inorder.val ∧ postorder_traversal r = postorder.val) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; in particular it does not fail, panic, or overflow.
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_2 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val) :
    ∃ r : Tree, build_tree inorder postorder = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val), ∃ r : Tree, build_tree inorder postorder = ok r) := by
  sorry

/-- Whenever the function returns a result r, node_count(r)=len(inorder), where node_count(Null)=0 and node_count(Node(v,L,R))=1+node_count(L)+node_count(R).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_3 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    node_count r = inorder.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), node_count r = inorder.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of nodes of r whose label is v equals the number of indices i with 0 <= i < len(inorder) and inorder[i]=v.
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_4 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ v : Int, label_count v r = (inorder.val.filter (fun x => x.val = v)).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ v : Int, label_count v r = (inorder.val.filter (fun x => x.val = v)).length) := by
  sorry

/-- Whenever the function returns a result r, r is not Null, and if r=Node(v,L,R), then v=postorder[len(postorder)-1].
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_5 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    r ≠ Tree.Null ∧
      ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R → postorder_root postorder = some v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), r ≠ Tree.Null ∧
      ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R → postorder_root postorder = some v) := by
  sorry

/-- Let k be the unique index with 0 <= k < len(inorder) and inorder[k]=postorder[len(postorder)-1]. Whenever the function returns a result r=Node(v,L,R), inorder_traversal(L) is the prefix of inorder of length k, namely [inorder[0],...,inorder[k-1]] (empty when k=0).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_6 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R → inorder_traversal L = inorder.val.take k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R → inorder_traversal L = inorder.val.take k) := by
  sorry

/-- Let k be the unique index with 0 <= k < len(inorder) and inorder[k]=postorder[len(postorder)-1]. Whenever the function returns a result r=Node(v,L,R), inorder_traversal(R) is the suffix of inorder beginning at index k+1, namely [inorder[k+1],...,inorder[len(inorder)-1]] (empty when k+1=len(inorder)).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_7 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      inorder_traversal R = inorder.val.drop (k + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      inorder_traversal R = inorder.val.drop (k + 1)) := by
  sorry

/-- Let k be the unique index with 0 <= k < len(inorder) and inorder[k]=postorder[len(postorder)-1]. Whenever the function returns a result r=Node(v,L,R), postorder_traversal(L) is the prefix of postorder of length k, namely [postorder[0],...,postorder[k-1]] (empty when k=0).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_8 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      postorder_traversal L = postorder.val.take k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      postorder_traversal L = postorder.val.take k) := by
  sorry

/-- Let k be the unique index with 0 <= k < len(inorder) and inorder[k]=postorder[len(postorder)-1]. Whenever the function returns a result r=Node(v,L,R), postorder_traversal(R) is the slice of postorder from index k up to but excluding index len(postorder)-1, namely [postorder[k],...,postorder[len(postorder)-2]] (empty when k=len(postorder)-1).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_9 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      postorder_traversal R = (postorder.val.drop k).dropLast := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      postorder_traversal R = (postorder.val.drop k).dropLast) := by
  sorry

/-- Let k be the unique index with 0 <= k < len(inorder) and inorder[k]=postorder[len(postorder)-1]. Whenever the function returns a result r=Node(v,L,R), node_count(L)=k and node_count(R)=len(inorder)-k-1, where node_count(Null)=0 and node_count(Node(v,L2,R2))=1+node_count(L2)+node_count(R2).
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_10 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      node_count L = k ∧ node_count R = inorder.val.length - k - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (k : Nat) (hk : is_root_index inorder postorder k)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ (v : Std.I64) (L R : Tree), r = Tree.Node v L R →
      node_count L = k ∧ node_count R = inorder.val.length - k - 1) := by
  sorry

/-- Whenever the function returns a result r, for every Tree t, if inorder_traversal(t)=inorder and postorder_traversal(t)=postorder, then t=r, where equality of trees is structural equality of the Null and Node constructors.
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_11 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ t : Tree, inorder_traversal t = inorder.val → postorder_traversal t = postorder.val →
      t = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ t : Tree, inorder_traversal t = inorder.val → postorder_traversal t = postorder.val →
      t = r) := by
  sorry

/-- Whenever the function returns a result r, every node label v occurring in r satisfies -3000 <= v <= 3000.
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_12 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ v : Std.I64, occurs v r → -3000 ≤ v.val ∧ v.val ≤ 3000 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ v : Std.I64, occurs v r → -3000 ≤ v.val ∧ v.val ≤ 3000) := by
  sorry

/-- Whenever the function returns a result r, for every node occurrence u of r, if S is the subtree of r rooted at u, then there exist integers a,b with 0 <= a <= b < len(inorder) such that inorder_traversal(S)=[inorder[a],...,inorder[b]], and there exist integers c,d with 0 <= c <= d < len(postorder) such that postorder_traversal(S)=[postorder[c],...,postorder[d]].
  Preconditions: inorder and postorder are slices with len(inorder)=len(postorder), 1 <= len(inorder) <= 3000, every entry of both slices lies in [-3000,3000], entries of inorder are pairwise distinct, entries of postorder are pairwise distinct, and there exists a Tree T with inorder_traversal(T)=inorder and postorder_traversal(T)=postorder. Here inorder_traversal(Null)=[] and inorder_traversal(Node(v,L,R))=inorder_traversal(L) ++ [v] ++ inorder_traversal(R); postorder_traversal(Null)=[] and postorder_traversal(Node(v,L,R))=postorder_traversal(L) ++ postorder_traversal(R) ++ [v]. -/
theorem spec_13 (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r) :
    ∀ S : Tree, is_subtree S r →
      (∃ a b : Nat, a ≤ b ∧ b < inorder.val.length ∧
        inorder_traversal S = (inorder.val.drop a).take (b - a + 1)) ∧
      (∃ c d : Nat, c ≤ d ∧ d < postorder.val.length ∧
        postorder_traversal S = (postorder.val.drop c).take (d - c + 1)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (inorder postorder : Slice Std.I64)
    (hlen : inorder.val.length = postorder.val.length)
    (hpos : 1 ≤ inorder.val.length) (hle : inorder.val.length ≤ 3000)
    (hin_bounds : ∀ x ∈ inorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hpost_bounds : ∀ x ∈ postorder.val, -3000 ≤ x.val ∧ x.val ≤ 3000)
    (hin_nodup : inorder.val.Nodup) (hpost_nodup : postorder.val.Nodup)
    (hex : ∃ T : Tree,
      inorder_traversal T = inorder.val ∧ postorder_traversal T = postorder.val)
    (r : Tree) (hr : build_tree inorder postorder = ok r), ∀ S : Tree, is_subtree S r →
      (∃ a b : Nat, a ≤ b ∧ b < inorder.val.length ∧
        inorder_traversal S = (inorder.val.drop a).take (b - a + 1)) ∧
      (∃ c d : Nat, c ≤ d ∧ d < postorder.val.length ∧
        postorder_traversal S = (postorder.val.drop c).take (d - c + 1))) := by
  sorry

end AegisSpec.BuildTree
