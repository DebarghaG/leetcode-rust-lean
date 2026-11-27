import Aegis.IsSameTree.Code.Funs

/-!
# Specifications of `Aegis.IsSameTree.is_same_tree`

LeetCode problem `same-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsSameTree

open Aegis.IsSameTree

def nodes : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + nodes l + nodes r

def valsWithin : Tree → Prop
  | .Null => True
  | .Node v l r => (-10000 : ℤ) ≤ v.val ∧ v.val ≤ 10000 ∧ valsWithin l ∧ valsWithin r

def Same : Tree → Tree → Bool
  | .Null, .Null => true
  | .Node vp lp rp, .Node vq lq rq => (vp = vq) && Same lp lq && Same rp rq
  | _, _ => false

def SameShape : Tree → Tree → Bool
  | .Null, .Null => true
  | .Node _ lp rp, .Node _ lq rq => SameShape lp lq && SameShape rp rq
  | _, _ => false

inductive Dir where
  | L
  | R

def valueAt : Tree → List Dir → Option Std.I64
  | .Null, [] => none
  | .Node v _ _, [] => some v
  | .Null, _ :: _ => none
  | .Node _ l _, Dir.L :: rest => valueAt l rest
  | .Node _ _ r, Dir.R :: rest => valueAt r rest

/-- Let Same(p,q) be the recursive predicate: Same(Null,Null)=true; Same(Node(vp,lp,rp), Node(vq,lq,rq)) = (vp=vq and Same(lp,lq) and Same(rp,rq)); Same(p,q)=false in every other constructor case. Then is_same_tree p q returns Ok b for some Boolean b, and b=true exactly when Same(p,q) holds. Equivalently, the returned Boolean is true if and only if the two trees have identical structure and equal values at every corresponding node.
  Preconditions: p and q are finite binary trees satisfying the LeetCode constraints: nodes(p) <= 100, nodes(q) <= 100, and every node value of p or q lies in [-10000,10000], where nodes(Null)=0 and nodes(Node(v,l,r))=1+nodes(l)+nodes(r). -/
theorem spec_1 (p q : Tree) (hp : nodes p ≤ 100) (hq : nodes q ≤ 100)
    (hvp : valsWithin p) (hvq : valsWithin q) :
    ∃ b : Bool, is_same_tree p q = ok b ∧ (b = true ↔ Same p q = true) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (p q : Tree) (hp : nodes p ≤ 100) (hq : nodes q ≤ 100)
    (hvp : valsWithin p) (hvq : valsWithin q), ∃ b : Bool, is_same_tree p q = ok b ∧ (b = true ↔ Same p q = true)) := by
  sorry

/-- For every p and q, is_same_tree p q returns Ok b for some Boolean b; it never returns Err. In particular, the call cannot fail by arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: None: p and q are arbitrary finite values of the inductive type Tree. -/
theorem spec_2 (p q : Tree) :
    (∃ b : Bool, is_same_tree p q = ok b) ∧
      (∀ e : Aeneas.Std.Error, is_same_tree p q ≠ Aeneas.Std.Result.fail e) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (p q : Tree), (∃ b : Bool, is_same_tree p q = ok b) ∧
      (∀ e : Aeneas.Std.Error, is_same_tree p q ≠ Aeneas.Std.Result.fail e)) := by
  sorry

/-- is_same_tree Null Null = Ok true.
  Preconditions: None (Null satisfies the LeetCode node-count and value bounds vacuously). -/
theorem spec_3 : is_same_tree Tree.Null Tree.Null = ok true := by
  sorry

theorem spec_3_neg :
    ¬ (is_same_tree Tree.Null Tree.Null = ok true) := by
  sorry

/-- For every v,l,r, is_same_tree Null (Node(v,l,r)) = Ok false and is_same_tree (Node(v,l,r)) Null = Ok false.
  Preconditions: v is any 64-bit integer and l,r are finite Tree values; under the LeetCode constraints one may additionally require -10000 <= v <= 10000 and at most 100 nodes, but the statement holds without those restrictions. -/
theorem spec_4 (v : Std.I64) (l r : Tree) :
    (is_same_tree Tree.Null (Tree.Node v l r) = ok false) ∧
      (is_same_tree (Tree.Node v l r) Tree.Null = ok false) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (v : Std.I64) (l r : Tree), (is_same_tree Tree.Null (Tree.Node v l r) = ok false) ∧
      (is_same_tree (Tree.Node v l r) Tree.Null = ok false)) := by
  sorry

/-- For every a,b, is_same_tree (Node(a,Null,Null)) (Node(b,Null,Null)) returns Ok true exactly when a=b, and returns Ok false exactly when a!=b.
  Preconditions: a and b are 64-bit integers; under the LeetCode constraints they lie in [-10000,10000], but the statement holds for all 64-bit integers. -/
theorem spec_5 (a b : Std.I64) :
    ((is_same_tree (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null) =
          ok true) ↔ a = b) ∧
      ((is_same_tree (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null) =
          ok false) ↔ ¬ a = b) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : Std.I64), ((is_same_tree (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null) =
          ok true) ↔ a = b) ∧
      ((is_same_tree (Tree.Node a Tree.Null Tree.Null) (Tree.Node b Tree.Null Tree.Null) =
          ok false) ↔ ¬ a = b)) := by
  sorry

/-- For every such v1,v2,l1,r1,l2,r2, is_same_tree (Node(v1,l1,r1)) (Node(v2,l2,r2)) = Ok false.
  Preconditions: v1 and v2 are 64-bit integers with v1 != v2; l1,r1,l2,r2 are finite Tree values. Under LeetCode constraints the values lie in [-10000,10000], but the statement holds without that restriction. -/
theorem spec_6 (v1 v2 : Std.I64) (l1 r1 l2 r2 : Tree) (hv : v1 ≠ v2) :
    is_same_tree (Tree.Node v1 l1 r1) (Tree.Node v2 l2 r2) = ok false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (v1 v2 : Std.I64) (l1 r1 l2 r2 : Tree) (hv : v1 ≠ v2), is_same_tree (Tree.Node v1 l1 r1) (Tree.Node v2 l2 r2) = ok false) := by
  sorry

/-- For every p,q, whenever is_same_tree p q returns Ok b, the call is_same_tree q p returns Ok b with the same Boolean b.
  Preconditions: p and q are finite Tree values. -/
theorem spec_7 (p q : Tree) (b : Bool) (h : is_same_tree p q = ok b) :
    is_same_tree q p = ok b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (p q : Tree) (b : Bool) (h : is_same_tree p q = ok b), is_same_tree q p = ok b) := by
  sorry

/-- For every p, is_same_tree p p = Ok true.
  Preconditions: p is a finite Tree value. -/
theorem spec_8 (p : Tree) : is_same_tree p p = ok true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (p : Tree), is_same_tree p p = ok true) := by
  sorry

/-- For every such v,l1,r1,l2,r2, if is_same_tree l1 l2 = Ok false, then is_same_tree (Node(v,l1,r1)) (Node(v,l2,r2)) = Ok false.
  Preconditions: v is a 64-bit integer; l1,r1,l2,r2 are finite Tree values. -/
theorem spec_9 (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree l1 l2 = ok false) :
    is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok false := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree l1 l2 = ok false), is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok false) := by
  sorry

/-- For every such v,l1,r1,l2,r2, if is_same_tree r1 r2 = Ok false, then is_same_tree (Node(v,l1,r1)) (Node(v,l2,r2)) = Ok false.
  Preconditions: v is a 64-bit integer; l1,r1,l2,r2 are finite Tree values. -/
theorem spec_10 (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree r1 r2 = ok false) :
    is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree r1 r2 = ok false), is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok false) := by
  sorry

/-- For every such v,l1,r1,l2,r2, if is_same_tree l1 l2 = Ok true and is_same_tree r1 r2 = Ok true, then is_same_tree (Node(v,l1,r1)) (Node(v,l2,r2)) = Ok true.
  Preconditions: v is a 64-bit integer; l1,r1,l2,r2 are finite Tree values. -/
theorem spec_11 (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (hl : is_same_tree l1 l2 = ok true) (hr : is_same_tree r1 r2 = ok true) :
    is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (v : Std.I64) (l1 r1 l2 r2 : Tree)
    (hl : is_same_tree l1 l2 = ok true) (hr : is_same_tree r1 r2 = ok true), is_same_tree (Tree.Node v l1 r1) (Tree.Node v l2 r2) = ok true) := by
  sorry

/-- For every such values, if is_same_tree (Node(v1,l1,r1)) (Node(v2,l2,r2)) returns Ok true, then v1=v2, is_same_tree l1 l2 = Ok true, and is_same_tree r1 r2 = Ok true.
  Preconditions: v1,v2 are 64-bit integers; l1,r1,l2,r2 are finite Tree values. -/
theorem spec_12 (v1 v2 : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree (Tree.Node v1 l1 r1) (Tree.Node v2 l2 r2) = ok true) :
    v1 = v2 ∧ is_same_tree l1 l2 = ok true ∧ is_same_tree r1 r2 = ok true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (v1 v2 : Std.I64) (l1 r1 l2 r2 : Tree)
    (h : is_same_tree (Tree.Node v1 l1 r1) (Tree.Node v2 l2 r2) = ok true), v1 = v2 ∧ is_same_tree l1 l2 = ok true ∧ is_same_tree r1 r2 = ok true) := by
  sorry

/-- Define SameShape(p,q) recursively by SameShape(Null,Null)=true; SameShape(Node(u,lp,rp),Node(w,lq,rq)) = (SameShape(lp,lq) and SameShape(rp,rq)); and SameShape(p,q)=false in all other constructor cases. Whenever is_same_tree p q returns Ok true, SameShape(p,q) holds.
  Preconditions: p and q are finite Tree values. -/
theorem spec_13 (p q : Tree) (h : is_same_tree p q = ok true) : SameShape p q = true := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (p q : Tree) (h : is_same_tree p q = ok true), SameShape p q = true) := by
  sorry

/-- Define nodes(Null)=0 and nodes(Node(v,l,r))=1+nodes(l)+nodes(r). Whenever is_same_tree p q returns Ok true, nodes(p)=nodes(q).
  Preconditions: p and q are finite Tree values. -/
theorem spec_14 (p q : Tree) (h : is_same_tree p q = ok true) : nodes p = nodes q := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (p q : Tree) (h : is_same_tree p q = ok true), nodes p = nodes q) := by
  sorry

/-- For a finite path whose elements are L or R, define at(t,[]) to be none if t=Null and some v if t=Node(v,l,r); define at(Null,d::rest)=none; define at(Node(v,l,r),L::rest)=at(l,rest); define at(Node(v,l,r),R::rest)=at(r,rest). Whenever is_same_tree p q returns Ok false, there exists a finite path such that at(p,path) != at(q,path) as values of type Option i64.
  Preconditions: p and q are finite Tree values; path ranges over finite sequences of directions L and R. -/
theorem spec_15 (p q : Tree) (h : is_same_tree p q = ok false) :
    ∃ path : List Dir, valueAt p path ≠ valueAt q path := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (p q : Tree) (h : is_same_tree p q = ok false), ∃ path : List Dir, valueAt p path ≠ valueAt q path) := by
  sorry

end AegisSpec.IsSameTree
