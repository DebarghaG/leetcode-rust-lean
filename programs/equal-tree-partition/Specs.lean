import Aegis.CheckEqualTree.Code.Funs

/-!
# Specifications of `Aegis.CheckEqualTree.check_equal_tree`

LeetCode problem `equal-tree-partition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckEqualTree

  open Aegis.CheckEqualTree

  def size : Tree → Nat
    | Tree.Null => 0
    | Tree.Node _ l r => 1 + size l + size r

  def values : Tree → List ℤ
    | Tree.Null => []
    | Tree.Node v l r => v.val :: (values l ++ values r)

  def sum : Tree → ℤ
    | Tree.Null => 0
    | Tree.Node v l r => v.val + (sum l + sum r)

  def NodeCountBounded (t : Tree) : Prop := 1 ≤ size t ∧ size t ≤ 10000

  def ValuesBounded (t : Tree) : Prop := ∀ x ∈ values t, -100000 ≤ x ∧ x ≤ 100000

  def NodeOccursIn (u : Tree) : Tree → Prop
    | Tree.Null => False
    | Tree.Node v l r => u = Tree.Node v l r ∨ NodeOccursIn u l ∨ NodeOccursIn u r

  def NonRootNodeOccurs (u : Tree) : Tree → Prop
    | Tree.Null => False
    | Tree.Node _ l r => NodeOccursIn u l ∨ NodeOccursIn u r

  def mkI64 (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

  def neg : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node (mkI64 (-v.val)) (neg l) (neg r)

  def mirror : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

  def scale (c : ℤ) : Tree → Tree
    | Tree.Null => Tree.Null
    | Tree.Node v l r => Tree.Node (mkI64 (c * v.val)) (scale c l) (scale c r)

  def nodeAt : Tree → List Bool → Option Tree
    | t, [] => some t
    | Tree.Null, _ :: _ => none
    | Tree.Node _ l _, true :: rest => nodeAt l rest
    | Tree.Node _ _ r, false :: rest => nodeAt r rest

  def replaceAt : Tree → List Bool → Tree → Tree
    | _, [], new => new
    | Tree.Null, _ :: _, _ => Tree.Null
    | Tree.Node v l r, true :: rest, new => Tree.Node v (replaceAt l rest new) r
    | Tree.Node v l r, false :: rest, new => Tree.Node v l (replaceAt r rest new)

  def swapChildrenAt (t : Tree) (path : List Bool) : Tree :=
    match nodeAt t path with
    | some (Tree.Node v l r) => replaceAt t path (Tree.Node v r l)
    | _ => t

  /-- Whenever check_equal_tree(root) returns a result r, r = true if and only if there exists a non-root Node occurrence u in root such that 2 * sum(u) = sum(root).
    Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10^4, and every Node value v satisfies -10^5 <= v <= 10^5. For a Tree t, sum(t) is the sum of values of all Node occurrences in t, with sum(Null)=0. A non-root Node occurrence is any Node occurrence that is the left or right child of some Node occurrence in root. -/
  theorem spec_1 (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
      (r : Bool) (hres : check_equal_tree root = ok r) :
      (r = true ↔ ∃ u : Tree, NonRootNodeOccurs u root ∧ 2 * sum u = sum root) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
        (r : Bool) (hres : check_equal_tree root = ok r), (r = true ↔ ∃ u : Tree, NonRootNodeOccurs u root ∧ 2 * sum u = sum root)) := by
    sorry

  /-- check_equal_tree(root) returns a result, either true or false; it does not fail, panic, or overflow.
    Preconditions: root is a finite Tree with 1 <= number of Node occurrences <= 10^4, and every Node value v satisfies -10^5 <= v <= 10^5. -/
  theorem spec_2 (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root) :
      ∃ r : Bool, check_equal_tree root = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root), ∃ r : Bool, check_equal_tree root = ok r) := by
    sorry

  /-- Whenever check_equal_tree(root) returns a result r, r = false.
    Preconditions: root = Node(v, Null, Null) for some integer v with -10^5 <= v <= 10^5, so root has exactly one node. -/
  theorem spec_3 (v : Std.I64) (hv : -100000 ≤ v.val ∧ v.val ≤ 100000) (r : Bool)
      (hres : check_equal_tree (Tree.Node v Tree.Null Tree.Null) = ok r) : r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (v : Std.I64) (hv : -100000 ≤ v.val ∧ v.val ≤ 100000) (r : Bool)
        (hres : check_equal_tree (Tree.Node v Tree.Null Tree.Null) = ok r), r = false) := by
    sorry

  /-- Whenever check_equal_tree(root) returns a result r, r = true if and only if there exists a non-root Node occurrence u in root with sum(u)=0.
    Preconditions: root has 1 <= number of Node occurrences <= 10^4 and every Node value v satisfies -10^5 <= v <= 10^5. Let sum(t) be the sum of values of all Node occurrences in t, with sum(Null)=0. Assume sum(root)=0. A non-root Node occurrence is any Node occurrence that is the left or right child of some Node occurrence in root. -/
  theorem spec_4 (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
      (hsum : sum root = 0) (r : Bool) (hres : check_equal_tree root = ok r) :
      (r = true ↔ ∃ u : Tree, NonRootNodeOccurs u root ∧ sum u = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
        (hsum : sum root = 0) (r : Bool) (hres : check_equal_tree root = ok r), (r = true ↔ ∃ u : Tree, NonRootNodeOccurs u root ∧ sum u = 0)) := by
    sorry

  /-- Whenever check_equal_tree(root) returns a result r, r = true if and only if a = b.
    Preconditions: root is either Node(a, Node(b, Null, Null), Null) or Node(a, Null, Node(b, Null, Null)), with -10^5 <= a <= 10^5 and -10^5 <= b <= 10^5. Thus root has exactly two nodes: value a at the root and value b at its only child. -/
  theorem spec_5 (root : Tree) (a b : Std.I64)
      (hroot : root = Tree.Node a (Tree.Node b Tree.Null Tree.Null) Tree.Null ∨
        root = Tree.Node a Tree.Null (Tree.Node b Tree.Null Tree.Null))
      (ha : -100000 ≤ a.val ∧ a.val ≤ 100000) (hb : -100000 ≤ b.val ∧ b.val ≤ 100000)
      (r : Bool) (hres : check_equal_tree root = ok r) : (r = true ↔ a.val = b.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (root : Tree) (a b : Std.I64)
        (hroot : root = Tree.Node a (Tree.Node b Tree.Null Tree.Null) Tree.Null ∨
          root = Tree.Node a Tree.Null (Tree.Node b Tree.Null Tree.Null))
        (ha : -100000 ≤ a.val ∧ a.val ≤ 100000) (hb : -100000 ≤ b.val ∧ b.val ≤ 100000)
        (r : Bool) (hres : check_equal_tree root = ok r), (r = true ↔ a.val = b.val)) := by
    sorry

  /-- Whenever check_equal_tree(root) returns a result r, r = true if and only if (b = a + c or c = a + b).
    Preconditions: root = Node(a, Node(b, Null, Null), Node(c, Null, Null)) with -10^5 <= a,b,c <= 10^5. Thus root has exactly three nodes: root value a, left child value b, and right child value c. -/
  theorem spec_6 (a b c : Std.I64)
      (ha : -100000 ≤ a.val ∧ a.val ≤ 100000) (hb : -100000 ≤ b.val ∧ b.val ≤ 100000)
      (hc : -100000 ≤ c.val ∧ c.val ≤ 100000) (r : Bool)
      (hres : check_equal_tree (Tree.Node a (Tree.Node b Tree.Null Tree.Null)
        (Tree.Node c Tree.Null Tree.Null)) = ok r) :
      (r = true ↔ (b.val = a.val + c.val ∨ c.val = a.val + b.val)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c : Std.I64)
        (ha : -100000 ≤ a.val ∧ a.val ≤ 100000) (hb : -100000 ≤ b.val ∧ b.val ≤ 100000)
        (hc : -100000 ≤ c.val ∧ c.val ≤ 100000) (r : Bool)
        (hres : check_equal_tree (Tree.Node a (Tree.Node b Tree.Null Tree.Null)
          (Tree.Node c Tree.Null Tree.Null)) = ok r), (r = true ↔ (b.val = a.val + c.val ∨ c.val = a.val + b.val))) := by
    sorry

  /-- Whenever check_equal_tree(root) returns a result r, r = true.
    Preconditions: root is either Node(a, u, Null) with u a non-null Tree, or Node(a, Null, u) with u a non-null Tree. All Node values are in [-10^5, 10^5] and the total number of nodes is at most 10^4. Let sum(t) be the sum of values of all Node occurrences in t, with sum(Null)=0. Assume a = sum(u). -/
  theorem spec_7 (root u : Tree) (a : Std.I64)
      (hroot : root = Tree.Node a u Tree.Null ∨ root = Tree.Node a Tree.Null u)
      (hnonnull : u ≠ Tree.Null) (hcount : size root ≤ 10000) (hbounds : ValuesBounded root)
      (ha : a.val = sum u) (r : Bool) (hres : check_equal_tree root = ok r) : r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (root u : Tree) (a : Std.I64)
        (hroot : root = Tree.Node a u Tree.Null ∨ root = Tree.Node a Tree.Null u)
        (hnonnull : u ≠ Tree.Null) (hcount : size root ≤ 10000) (hbounds : ValuesBounded root)
        (ha : a.val = sum u) (r : Bool) (hres : check_equal_tree root = ok r), r = true) := by
    sorry

  /-- Whenever check_equal_tree(root) returns r and check_equal_tree(neg(root)) returns r', we have r = r'.
    Preconditions: root has 1 <= number of Node occurrences <= 10^4 and every Node value v satisfies -10^5 <= v <= 10^5. Let neg(root) be the Tree obtained by replacing every Node value v by -v; neg(root) also satisfies the value bounds. -/
  theorem spec_8 (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
      (r r' : Bool) (hres : check_equal_tree root = ok r)
      (hres' : check_equal_tree (neg root) = ok r') : r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
        (r r' : Bool) (hres : check_equal_tree root = ok r)
        (hres' : check_equal_tree (neg root) = ok r'), r = r') := by
    sorry

  /-- Whenever check_equal_tree(root) returns r and check_equal_tree(mirror(root)) returns r', we have r = r'.
    Preconditions: root has 1 <= number of Node occurrences <= 10^4 and every Node value v satisfies -10^5 <= v <= 10^5. Let mirror(root) be defined recursively by mirror(Null)=Null and mirror(Node(v,l,r))=Node(v,mirror(r),mirror(l)). -/
  theorem spec_9 (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
      (r r' : Bool) (hres : check_equal_tree root = ok r)
      (hres' : check_equal_tree (mirror root) = ok r') : r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (root : Tree) (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
        (r r' : Bool) (hres : check_equal_tree root = ok r)
        (hres' : check_equal_tree (mirror root) = ok r'), r = r') := by
    sorry

  /-- Whenever check_equal_tree(root) returns r and check_equal_tree(scale(root,c)) returns r', we have r = r'.
    Preconditions: root has 1 <= number of Node occurrences <= 10^4 and every Node value v satisfies -10^5 <= v <= 10^5. Let c be any nonzero integer such that c*v is within the i64 range for every Node value v in root, and let scale(root,c) be the Tree obtained by replacing every Node value v by c*v. -/
  theorem spec_10 (root : Tree) (c : ℤ) (hcount : NodeCountBounded root)
      (hbounds : ValuesBounded root) (hc : c ≠ 0)
      (hrange : ∀ x ∈ values root,
        -9223372036854775808 ≤ c * x ∧ c * x ≤ 9223372036854775807)
      (r r' : Bool) (hres : check_equal_tree root = ok r)
      (hres' : check_equal_tree (scale c root) = ok r') : r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (root : Tree) (c : ℤ) (hcount : NodeCountBounded root)
        (hbounds : ValuesBounded root) (hc : c ≠ 0)
        (hrange : ∀ x ∈ values root,
          -9223372036854775808 ≤ c * x ∧ c * x ≤ 9223372036854775807)
        (r r' : Bool) (hres : check_equal_tree root = ok r)
        (hres' : check_equal_tree (scale c root) = ok r'), r = r') := by
    sorry

  /-- Whenever check_equal_tree(root) returns r and check_equal_tree(swap_children(root,p)) returns r', we have r = r'.
    Preconditions: root has 1 <= number of Node occurrences <= 10^4 and every Node value v satisfies -10^5 <= v <= 10^5. Let p be any Node occurrence in root. Let swap_children(root,p) be the Tree obtained by interchanging the left and right subtrees of p, leaving all other nodes and values unchanged. -/
  theorem spec_11 (root : Tree) (path : List Bool) (p : Tree)
      (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
      (hp : nodeAt root path = some p) (hpnode : ∃ (v : Std.I64) (l r : Tree), p = Tree.Node v l r)
      (r r' : Bool) (hres : check_equal_tree root = ok r)
      (hres' : check_equal_tree (swapChildrenAt root path) = ok r') : r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (root : Tree) (path : List Bool) (p : Tree)
        (hcount : NodeCountBounded root) (hbounds : ValuesBounded root)
        (hp : nodeAt root path = some p) (hpnode : ∃ (v : Std.I64) (l r : Tree), p = Tree.Node v l r)
        (r r' : Bool) (hres : check_equal_tree root = ok r)
        (hres' : check_equal_tree (swapChildrenAt root path) = ok r'), r = r') := by
    sorry

  end AegisSpec.CheckEqualTree
