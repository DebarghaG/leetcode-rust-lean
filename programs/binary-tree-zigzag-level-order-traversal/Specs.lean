import Aegis.ZigzagLevelOrder.Code.Funs

/-!
# Specifications of `Aegis.ZigzagLevelOrder.zigzag_level_order`

LeetCode problem `binary-tree-zigzag-level-order-traversal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ZigzagLevelOrder

  open Aegis.ZigzagLevelOrder (Tree zigzag_level_order)

  def nodeCount : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

  def height : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + Nat.max (height l) (height r)

  def levelVals : Tree → Nat → List Int
    | Tree.Null, _ => []
    | Tree.Node v _ _, 0 => [v.val]
    | Tree.Node _ l r, d + 1 => levelVals l d ++ levelVals r d

  def nodesAtDepth : Tree → Nat → List Tree
    | Tree.Null, _ => []
    | Tree.Node v l r, 0 => [Tree.Node v l r]
    | Tree.Node _ l r, d + 1 => nodesAtDepth l d ++ nodesAtDepth r d

  def HasValue : Tree → Std.I64 → Prop
    | Tree.Null, _ => False
    | Tree.Node v l r, w => w = v ∨ HasValue l w ∨ HasValue r w

  def allValues : Tree → List Int
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (allValues l ++ allValues r)

  def occCount (x : Int) : List Int → Nat
    | [] => 0
    | y :: ys => (if y = x then 1 else 0) + occCount x ys

  def rowVals (row : alloc.vec.Vec Std.I64) : List Int := row.val.map (fun x => x.val)

  def levelOrder (root : Tree) : List (List Int) :=
    (List.range (height root)).map (levelVals root)

  /-- Whenever the function returns a result r : Vec (Vec i64), r is exactly the zigzag level order of root. Define L(t,d) for t : Tree and d >= 0 by L(Null,d)=[]; L(Node(v,l,r),0)=[v]; and for d>0, L(Node(v,l,r),d)=L(l,d-1) ++ L(r,d-1). Define H(Null)=0 and H(Node(v,l,r))=1+max(H(l),H(r)). Then len(r)=H(root), and for every d with 0 <= d < len(r), r[d] = L(root,d) if d is even, and r[d] = reverse(L(root,d)) if d is odd. Here reverse is list reversal and ++ is list concatenation.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_1
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      r.val.length = height root ∧
        ∀ (d : Nat) (hd : d < r.val.length),
          rowVals (r.val[d]'hd) =
            (if d % 2 = 0 then levelVals root d else (levelVals root d).reverse) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), r.val.length = height root ∧
          ∀ (d : Nat) (hd : d < r.val.length),
            rowVals (r.val[d]'hd) =
              (if d % 2 = 0 then levelVals root d else (levelVals root d).reverse)) := by
    sorry

  /-- Whenever the function returns r, len(r) equals H(root), where H(Null)=0 and H(Node(v,l,r))=1+max(H(l),H(r)); equivalently, r has exactly one row for each depth d from 0 through the maximum node depth of root, and no rows beyond that.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_2
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      r.val.length = height root := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), r.val.length = height root) := by
    sorry

  /-- Whenever the function returns r, for every d with 0 <= d < len(r), len(r[d]) equals the number of nodes of root at depth d. Equivalently, len(r[d]) = len(L(root,d)), where L(Null,d)=[]; L(Node(v,l,r),0)=[v]; and L(Node(v,l,r),d+1)=L(l,d) ++ L(r,d).
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_3
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ (d : Nat) (hd : d < r.val.length),
        (r.val[d]'hd).val.length = (levelVals root d).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ (d : Nat) (hd : d < r.val.length),
          (r.val[d]'hd).val.length = (levelVals root d).length) := by
    sorry

  /-- Whenever the function returns r, for every d with 0 <= d < len(r) and every j with 0 <= j < len(r[d]), there exists a node x of root at depth d whose value is r[d][j].
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_4
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ (d : Nat) (hd : d < r.val.length) (j : Nat) (hj : j < (rowVals (r.val[d]'hd)).length),
        ∃ (v : Std.I64) (l rr : Tree),
          Tree.Node v l rr ∈ nodesAtDepth root d ∧ (rowVals (r.val[d]'hd))[j]'hj = v.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ (d : Nat) (hd : d < r.val.length) (j : Nat) (hj : j < (rowVals (r.val[d]'hd)).length),
          ∃ (v : Std.I64) (l rr : Tree),
            Tree.Node v l rr ∈ nodesAtDepth root d ∧ (rowVals (r.val[d]'hd))[j]'hj = v.val) := by
    sorry

  /-- Whenever the function returns r, for every d with 0 <= d < len(r) and every integer x, the number of indices j with 0 <= j < len(r[d]) and r[d][j] = x equals the number of nodes of root at depth d whose value is x.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_5
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ (d : Nat) (hd : d < r.val.length) (x : Int),
        occCount x (rowVals (r.val[d]'hd)) = occCount x (levelVals root d) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ (d : Nat) (hd : d < r.val.length) (x : Int),
          occCount x (rowVals (r.val[d]'hd)) = occCount x (levelVals root d)) := by
    sorry

  /-- Whenever the function returns r, for every integer x, the total number of occurrences of x in the concatenation of all rows r[0] ++ r[1] ++ ... ++ r[len(r)-1] equals the number of nodes of root whose value is x. If len(r)=0, that concatenation is empty.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_6
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ x : Int,
        occCount x (r.val.map rowVals).flatten = occCount x (allValues root) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ x : Int,
          occCount x (r.val.map rowVals).flatten = occCount x (allValues root)) := by
    sorry

  /-- Whenever the function returns r, if root = Null then len(r)=0; if root is not Null then 1 <= len(r) <= n(root). In particular, under the precondition n(root) <= 2000, len(r) <= 2000.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_7
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      (root = Tree.Null → r.val.length = 0) ∧
        (root ≠ Tree.Null → 1 ≤ r.val.length ∧ r.val.length ≤ nodeCount root) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), (root = Tree.Null → r.val.length = 0) ∧
          (root ≠ Tree.Null → 1 ≤ r.val.length ∧ r.val.length ≤ nodeCount root)) := by
    sorry

  /-- Whenever the function returns r, for every d with 0 <= d < len(r) and every j with 0 <= j < len(r[d]), -100 <= r[d][j] <= 100.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_8
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ (d : Nat) (hd : d < r.val.length) (j : Nat) (hj : j < (rowVals (r.val[d]'hd)).length),
        -100 ≤ (rowVals (r.val[d]'hd))[j]'hj ∧ (rowVals (r.val[d]'hd))[j]'hj ≤ 100 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ (d : Nat) (hd : d < r.val.length) (j : Nat) (hj : j < (rowVals (r.val[d]'hd)).length),
          -100 ≤ (rowVals (r.val[d]'hd))[j]'hj ∧ (rowVals (r.val[d]'hd))[j]'hj ≤ 100) := by
    sorry

  /-- Define L(Null,d)=[]; L(Node(v,l,r),0)=[v]; L(Node(v,l,r),d+1)=L(l,d) ++ L(r,d); and H(Null)=0, H(Node(v,l,r))=1+max(H(l),H(r)). Let B(root) be the ordinary left-to-right level-order traversal, so len(B(root))=H(root) and B(root)[d]=L(root,d) for every d < H(root). Whenever the function returns r, len(r)=len(B(root)), and for every d with 0 <= d < len(r), r[d] = B(root)[d] if d is even, and r[d] = reverse(B(root)[d]) if d is odd.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_9
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      r.val.length = (levelOrder root).length ∧
        ∀ d, d < r.val.length →
          (r.val[d]?).map rowVals =
            (levelOrder root)[d]?.map (fun l => if d % 2 = 0 then l else l.reverse) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), r.val.length = (levelOrder root).length ∧
          ∀ d, d < r.val.length →
            (r.val[d]?).map rowVals =
              (levelOrder root)[d]?.map (fun l => if d % 2 = 0 then l else l.reverse)) := by
    sorry

  /-- Whenever the function returns r, for every d with 0 <= d < len(r), len(r[d]) > 0.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_10
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hret : zigzag_level_order root = ok r) :
      ∀ (d : Nat) (hd : d < r.val.length), 0 < (r.val[d]'hd).val.length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hret : zigzag_level_order root = ok r), ∀ (d : Nat) (hd : d < r.val.length), 0 < (r.val[d]'hd).val.length) := by
    sorry

  /-- The function returns a result r : Vec (Vec i64); it does not fail with overflow, out-of-bounds, or panic on any tree satisfying the preconditions.
    Preconditions: Let n(root) be the number of Node constructors in root. The tree satisfies 0 <= n(root) <= 2000, and every node value v of root satisfies -100 <= v <= 100. -/
  theorem spec_11
      (root : Tree)
      (hcount : nodeCount root ≤ 2000)
      (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), zigzag_level_order root = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree)
        (hcount : nodeCount root ≤ 2000)
        (hval : ∀ v : Std.I64, HasValue root v → -100 ≤ v.val ∧ v.val ≤ 100), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), zigzag_level_order root = ok r) := by
    sorry

  end AegisSpec.ZigzagLevelOrder
