import Aegis.VerticalTraversal.Code.Funs

/-!
# Specifications of `Aegis.VerticalTraversal.vertical_traversal`

LeetCode problem `vertical-order-traversal-of-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.VerticalTraversal

open Aegis.VerticalTraversal

structure VNode where

  row : Int

  col : Int

  value : Int

def nodesAt : Tree → Int → Int → List VNode
  | Tree.Null, _, _ => []
  | Tree.Node v l r, row, col =>
      ⟨row, col, v.val⟩ ::
        (nodesAt l (row + 1) (col - 1) ++ nodesAt r (row + 1) (col + 1))

def nodes (t : Tree) : List VNode := nodesAt t 0 0

def nodeCount (t : Tree) : Nat := (nodes t).length

def nodeValues (t : Tree) : List Int := (nodes t).map (fun x => x.value)

def nodeCols (t : Tree) : List Int := (nodes t).map (fun x => x.col)

def colMin (t : Tree) : Int := (nodeCols t).min?.getD 0

def colMax (t : Tree) : Int := (nodeCols t).max?.getD 0

def colNodesMul (t : Tree) (c : Int) : List VNode :=
  (nodes t).filter (fun x => x.col == c)

def colNodes (t : Tree) (c : Int) : List VNode :=
  (colNodesMul t c).mergeSort
    (fun a b => decide (a.row < b.row) || (a.row == b.row && decide (a.value ≤ b.value)))

def colValuesMul (t : Tree) (c : Int) : List Int :=
  (colNodesMul t c).map (fun x => x.value)

def colValues (t : Tree) (c : Int) : List Int :=
  (colNodes t c).map (fun x => x.value)

def outer (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
  r.val.map (fun g => g.val.map (fun x => x.val))

def group (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  (outer r)[i]?.getD []

def rootValue : Tree → Int
  | Tree.Null => 0
  | Tree.Node v _ _ => v.val

def noRightChild : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => r = Tree.Null ∧ noRightChild l

def chainValues : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l _ => v.val :: chainValues l

def noLeftChild : Tree → Prop
  | Tree.Null => True
  | Tree.Node _ l r => l = Tree.Null ∧ noLeftChild r

def rightChainValues : Tree → List Int
  | Tree.Null => []
  | Tree.Node v _ r => v.val :: rightChainValues r

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

/-- The function returns a result r and r is exactly the vertical order traversal of root. Define row(x) and col(x) recursively: row(root)=0 and col(root)=0; if y is the left child of x then row(y)=row(x)+1 and col(y)=col(x)-1; if z is the right child of x then row(z)=row(x)+1 and col(z)=col(x)+1. Let cmin and cmax be the minimum and maximum of col(x) over all nodes x of root. Then len(r)=cmax-cmin+1. For every integer c with cmin <= c <= cmax, let L=r[c-cmin], and let N_c be the nodes x of root with col(x)=c ordered by increasing row(x) and, for nodes with equal row(x), by increasing value(x), with arbitrary order among equal values. Then len(L)=len(N_c) and for every j with 0 <= j < len(L), L[j] equals the value of N_c[j].
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_1 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r ∧
        (r.val.length : Int) = colMax root - colMin root + 1 ∧
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            group r (c - colMin root).toNat = colValues root c := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r ∧
        (r.val.length : Int) = colMax root - colMin root + 1 ∧
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            group r (c - colMin root).toNat = colValues root c) := by
  sorry

/-- Whenever root satisfies the preconditions, vertical_traversal returns a result r; it does not overflow, panic, go out of bounds, or fail. Nothing else about r is claimed by this specification.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_2 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), vertical_traversal root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), vertical_traversal root = ok r) := by
  sorry

/-- Whenever the function returns a result r, let cmin and cmax be the minimum and maximum column of any node of root, where the column of a node is defined recursively from the root at column 0, a left child decreasing the column by 1 and a right child increasing the column by 1. Then len(r) = cmax - cmin + 1.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_3 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        (r.val.length : Int) = colMax root - colMin root + 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        (r.val.length : Int) = colMax root - colMin root + 1) := by
  sorry

/-- Whenever the function returns a result r, len(r) > 0 and every inner list is nonempty: for every i with 0 <= i < len(r), len(r[i]) > 0.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_4 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        0 < r.val.length ∧ ∀ i : Nat, i < r.val.length → 0 < (group r i).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        0 < r.val.length ∧ ∀ i : Nat, i < r.val.length → 0 < (group r i).length) := by
  sorry

/-- Whenever the function returns a result r, the sum of the lengths of all inner lists equals the number of nodes of root: sum_{i=0}^{len(r)-1} len(r[i]) = number_of_nodes(root), where number_of_nodes(root) is the number of Node constructors in root.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_5 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ((outer r).map (fun l => l.length)).sum = nodeCount root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ((outer r).map (fun l => l.length)).sum = nodeCount root) := by
  sorry

/-- Whenever the function returns a result r, define col(x) recursively by col(root)=0, the left child of x has column col(x)-1, and the right child of x has column col(x)+1. Let cmin and cmax be the minimum and maximum col(x) over all nodes x of root. For every integer column c with cmin <= c <= cmax, the multiset of values in r[c-cmin] equals the multiset of values value(x) over all nodes x of root with col(x)=c.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_6 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ i : Nat, i < r.val.length →
          List.Perm (group r i) (colValuesMul root (colMin root + (i : Int))) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ i : Nat, i < r.val.length →
          List.Perm (group r i) (colValuesMul root (colMin root + (i : Int)))) := by
  sorry

/-- Whenever the function returns a result r, define row(x) and col(x) recursively from root with row(root)=0 and col(root)=0, a left child increasing row by 1 and decreasing column by 1, and a right child increasing row by 1 and increasing column by 1. Let cmin and cmax be the minimum and maximum col(x) over all nodes x of root. For every integer column c with cmin <= c <= cmax, there exists a bijection phi from the index set {j | 0 <= j < len(r[c-cmin])} to the set of nodes x of root with col(x)=c such that r[c-cmin][j] equals value(phi(j)) for every j, and for all j,k with 0 <= j < k < len(r[c-cmin]), row(phi(j)) <= row(phi(k)).
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_7 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            ∃ ns : List VNode,
              ns.Perm (colNodesMul root c) ∧
                ns.map (fun x => x.value) = group r (c - colMin root).toNat ∧
                  ∀ (j k : Nat), j < k → ∀ (hj : j < ns.length) (hk : k < ns.length),
                    (ns.get ⟨j, hj⟩).row ≤ (ns.get ⟨k, hk⟩).row := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            ∃ ns : List VNode,
              ns.Perm (colNodesMul root c) ∧
                ns.map (fun x => x.value) = group r (c - colMin root).toNat ∧
                  ∀ (j k : Nat), j < k → ∀ (hj : j < ns.length) (hk : k < ns.length),
                    (ns.get ⟨j, hj⟩).row ≤ (ns.get ⟨k, hk⟩).row) := by
  sorry

/-- Whenever the function returns a result r, define row(x) and col(x) recursively from root with row(root)=0 and col(root)=0, a left child increasing row by 1 and decreasing column by 1, and a right child increasing row by 1 and increasing column by 1. Let cmin and cmax be the minimum and maximum col(x) over all nodes x of root. For every integer column c with cmin <= c <= cmax, there exists a bijection phi from the index set {j | 0 <= j < len(r[c-cmin])} to the set of nodes x of root with col(x)=c such that r[c-cmin][j] equals value(phi(j)) for every j, and for all j,k with 0 <= j < k < len(r[c-cmin]) and row(phi(j)) = row(phi(k)), value(phi(j)) <= value(phi(k)).
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_8 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            ∃ ns : List VNode,
              ns.Perm (colNodesMul root c) ∧
                ns.map (fun x => x.value) = group r (c - colMin root).toNat ∧
                  ∀ (j k : Nat), j < k → ∀ (hj : j < ns.length) (hk : k < ns.length),
                    (ns.get ⟨j, hj⟩).row = (ns.get ⟨k, hk⟩).row →
                      (ns.get ⟨j, hj⟩).value ≤ (ns.get ⟨k, hk⟩).value := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ c : Int, colMin root ≤ c → c ≤ colMax root →
          (c - colMin root).toNat < r.val.length ∧
            ∃ ns : List VNode,
              ns.Perm (colNodesMul root c) ∧
                ns.map (fun x => x.value) = group r (c - colMin root).toNat ∧
                  ∀ (j k : Nat), j < k → ∀ (hj : j < ns.length) (hk : k < ns.length),
                    (ns.get ⟨j, hj⟩).row = (ns.get ⟨k, hk⟩).row →
                      (ns.get ⟨j, hj⟩).value ≤ (ns.get ⟨k, hk⟩).value) := by
  sorry

/-- Whenever the function returns a result r, define col(x) recursively by col(root)=0, the left child of x has column col(x)-1, and the right child of x has column col(x)+1. Let cmin be the minimum col(x) over all nodes x of root. Then 0 <= -cmin < len(r), the inner list r[-cmin] is nonempty, and its first entry equals the value of root: r[-cmin][0] = value(root).
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_9 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        0 ≤ -colMin root ∧
          (-colMin root).toNat < r.val.length ∧
            0 < (group r (-colMin root).toNat).length ∧
              (group r (-colMin root).toNat).head? = some (rootValue root) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        0 ≤ -colMin root ∧
          (-colMin root).toNat < r.val.length ∧
            0 < (group r (-colMin root).toNat).length ∧
              (group r (-colMin root).toNat).head? = some (rootValue root)) := by
  sorry

/-- Whenever the function returns a result r, r has exactly one inner list and that inner list has exactly one entry, equal to v.
  Preconditions: root = Node(v, Null, Null) for some integer v with 0 <= v <= 1000. -/
theorem spec_10 (v : Std.I64) (hv : 0 ≤ v.val ∧ v.val ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal (Tree.Node v Tree.Null Tree.Null) = ok r →
        r.val.length = 1 ∧ group r 0 = [v.val] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (v : Std.I64) (hv : 0 ≤ v.val ∧ v.val ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal (Tree.Node v Tree.Null Tree.Null) = ok r →
        r.val.length = 1 ∧ group r 0 = [v.val]) := by
  sorry

/-- Whenever the function returns a result r, len(r)=n and for every i with 0 <= i < n, r[i] is the singleton list whose only entry is v_{n-1-i}. Equivalently, r is [[v_{n-1}], [v_{n-2}], ..., [v1], [v0]].
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, every node value lies in [0,1000], and no node has a right child. Thus the nodes form a single left-descending chain; let v0, v1, ..., v_{n-1} be the node values from the root downward, where n is the number of nodes. -/
theorem spec_11 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000)
    (hnr : noRightChild root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        r.val.length = nodeCount root ∧
          outer r = (chainValues root).reverse.map (fun x => [x]) ∧
            ∀ i : Nat, i < r.val.length →
              group r i = ((chainValues root).reverse[i]?).toList := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000)
    (hnr : noRightChild root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        r.val.length = nodeCount root ∧
          outer r = (chainValues root).reverse.map (fun x => [x]) ∧
            ∀ i : Nat, i < r.val.length →
              group r i = ((chainValues root).reverse[i]?).toList) := by
  sorry

/-- Whenever the function returns a result r, len(r)=n and for every i with 0 <= i < n, r[i] is the singleton list whose only entry is v_i. Equivalently, r is [[v0], [v1], ..., [v_{n-1}]].
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, every node value lies in [0,1000], and no node has a left child. Thus the nodes form a single right-descending chain; let v0, v1, ..., v_{n-1} be the node values from the root downward, where n is the number of nodes. -/
theorem spec_12 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000)
    (hnl : noLeftChild root) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        r.val.length = nodeCount root ∧
          outer r = (rightChainValues root).map (fun x => [x]) ∧
            ∀ i : Nat, i < r.val.length →
              group r i = ((rightChainValues root)[i]?).toList := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000)
    (hnl : noLeftChild root), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        r.val.length = nodeCount root ∧
          outer r = (rightChainValues root).map (fun x => [x]) ∧
            ∀ i : Nat, i < r.val.length →
              group r i = ((rightChainValues root)[i]?).toList) := by
  sorry

/-- Define mirror(root) recursively by mirror(Null)=Null and mirror(Node(v,L,R))=Node(v, mirror(R), mirror(L)). Whenever vertical_traversal(root) returns r and vertical_traversal(mirror(root)) returns r', we have len(r') = len(r) and for every i with 0 <= i < len(r), r'[i] = r[len(r)-1-i].
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_13 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      vertical_traversal root = ok r →
        vertical_traversal (mirror root) = ok r' →
          r'.val.length = r.val.length ∧
            ∀ i : Nat, i < r.val.length →
              group r' i = group r (r.val.length - 1 - i) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64)),
      vertical_traversal root = ok r →
        vertical_traversal (mirror root) = ok r' →
          r'.val.length = r.val.length ∧
            ∀ i : Nat, i < r.val.length →
              group r' i = group r (r.val.length - 1 - i)) := by
  sorry

/-- Whenever the function returns a result r, every entry of every inner list lies between 0 and 1000 inclusive: for all i,j with 0 <= i < len(r) and 0 <= j < len(r[i]), 0 <= r[i][j] <= 1000.
  Preconditions: root is a finite binary tree with between 1 and 1000 nodes inclusive, and every node value v satisfies 0 <= v <= 1000. -/
theorem spec_14 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < (group r i).length),
          0 ≤ (group r i).get ⟨j, hj⟩ ∧ (group r i).get ⟨j, hj⟩ ≤ 1000 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hle : nodeCount root ≤ 1000)
    (hval : ∀ v ∈ nodeValues root, 0 ≤ v ∧ v ≤ 1000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      vertical_traversal root = ok r →
        ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < (group r i).length),
          0 ≤ (group r i).get ⟨j, hj⟩ ∧ (group r i).get ⟨j, hj⟩ ≤ 1000) := by
  sorry

end AegisSpec.VerticalTraversal
