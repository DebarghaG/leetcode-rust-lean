import Aegis.SumNumbers.Code.Funs

/-!
# Specifications of `Aegis.SumNumbers.sum_numbers`

LeetCode problem `sum-root-to-leaf-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumNumbers

open Aegis.SumNumbers (Tree sum_numbers)

def nodeValue : Tree → Int
  | Tree.Null => 0
  | Tree.Node v _ _ => v.val

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def leafCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ Tree.Null Tree.Null => 1
  | Tree.Node _ l r => leafCount l + leafCount r

def extendWith (n : Tree) (ps : List (List Tree)) : List (List Tree) :=
  ps.map (fun p => n :: p)

def rootLeafPaths : Tree → List (List Tree)
  | Tree.Null => []
  | Tree.Node v Tree.Null Tree.Null => [[Tree.Node v Tree.Null Tree.Null]]
  | Tree.Node v l Tree.Null => extendWith (Tree.Node v l Tree.Null) (rootLeafPaths l)
  | Tree.Node v Tree.Null r => extendWith (Tree.Node v Tree.Null r) (rootLeafPaths r)
  | Tree.Node v l r =>
      extendWith (Tree.Node v l r) (rootLeafPaths l) ++
        extendWith (Tree.Node v l r) (rootLeafPaths r)

def pathValue (p : List Tree) : Int :=
  p.foldl (fun acc n => acc * 10 + nodeValue n) 0

def totalValue (t : Tree) : Int :=
  (rootLeafPaths t).foldl (fun acc p => acc + pathValue p) 0

def prefixValue (t : Tree) (d : Int) : Int :=
  (rootLeafPaths t).foldl (fun acc p => acc + (d * 10 ^ p.length + pathValue p)) 0

def rootLeafTerm (d : Int) : Tree → Tree → Int
  | Tree.Null, Tree.Null => d
  | _, _ => 0

def digitsOK : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => 0 ≤ v.val ∧ v.val ≤ 9 ∧ digitsOK l ∧ digitsOK r

def allZero : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => v.val = 0 ∧ allZero l ∧ allZero r

def pathLengthOK (t : Tree) : Prop := ∀ p, p ∈ rootLeafPaths t → p.length ≤ 10

def nodeCountOK (t : Tree) : Prop := 1 ≤ nodeCount t ∧ nodeCount t ≤ 1000

def sumFitsI32 (t : Tree) : Prop :=
  -(2 : Int) ^ 31 ≤ totalValue t ∧ totalValue t < (2 : Int) ^ 31

def Mirror : Tree → Tree → Prop
  | Tree.Null, Tree.Null => True
  | Tree.Node v l r, Tree.Node v' l' r' =>
      v = v' ∧ ((Mirror l l' ∧ Mirror r r') ∨ (Mirror l r' ∧ Mirror r l'))
  | _, _ => False

/-- Define a root-to-leaf path of root as a sequence of nodes n0,...,nk such that n0 is the root of root, for each i<k the node n_{i+1} is either the left child or the right child of n_i, and nk is a leaf (its left and right children are both Null). For such a path let value(n0,...,nk) = Σ_{i=0}^{k} v(n_i) * 10^{k-i}, where v(n) is the integer stored in node n. Whenever sum_numbers(root) returns a result r, r is exactly the sum of value(P) over all root-to-leaf paths P of root, with each root-to-leaf path counted once.
  Preconditions: root is a non-null binary tree (root ≠ Null); every Node value is an integer in the range 0..9; the number of nodes of root is in [1,1000]; every root-to-leaf path of root has at most 10 nodes; and the sum of the numbers represented by all root-to-leaf paths of root fits in the signed 32-bit integer range. -/
theorem spec_1 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r) :
    r.val = totalValue root := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r), r.val = totalValue root) := by
  sorry

/-- sum_numbers(root) returns Ok(r) for some r : Std.I64; equivalently, it does not return Err, panic, access an out-of-bounds part of the tree, or overflow an i64.
  Preconditions: root is a non-null binary tree (root ≠ Null); every Node value is an integer in the range 0..9; the number of nodes of root is in [1,1000]; every root-to-leaf path of root has at most 10 nodes; and the sum of the numbers represented by all root-to-leaf paths of root fits in the signed 32-bit integer range. -/
theorem spec_2 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root) :
    ∃ r : I64, sum_numbers root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root), ∃ r : I64, sum_numbers root = ok r) := by
  sorry

/-- Whenever sum_numbers(root) returns r, 0 ≤ r < 10^13.
  Preconditions: root is a non-null binary tree (root ≠ Null); every Node value is an integer in the range 0..9; the number of nodes of root is in [1,1000]; every root-to-leaf path of root has at most 10 nodes; and the sum of the numbers represented by all root-to-leaf paths of root fits in the signed 32-bit integer range. -/
theorem spec_3 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r) :
    0 ≤ r.val ∧ r.val < (10 : Int) ^ 13 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r), 0 ≤ r.val ∧ r.val < (10 : Int) ^ 13) := by
  sorry

/-- Whenever sum_numbers(root) returns r, if L is the number of leaf nodes of root, then 0 ≤ r ≤ L * (10^10 - 1).
  Preconditions: root is a non-null binary tree (root ≠ Null); every Node value is an integer in the range 0..9; the number of nodes of root is in [1,1000]; every root-to-leaf path of root has at most 10 nodes; and the sum of the numbers represented by all root-to-leaf paths of root fits in the signed 32-bit integer range. -/
theorem spec_4 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r) :
    0 ≤ r.val ∧ r.val ≤ (leafCount root : Int) * ((10 : Int) ^ 10 - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hr : sum_numbers root = ok r), 0 ≤ r.val ∧ r.val ≤ (leafCount root : Int) * ((10 : Int) ^ 10 - 1)) := by
  sorry

/-- Whenever sum_numbers(root) returns r, r = d.
  Preconditions: root = Node(d, Null, Null) for some integer d with 0 ≤ d ≤ 9. -/
theorem spec_5 (root : Tree) (d : I64) (r : I64)
    (hroot : root = Tree.Node d Tree.Null Tree.Null)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (hr : sum_numbers root = ok r) :
    r.val = d.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (d : I64) (r : I64)
    (hroot : root = Tree.Node d Tree.Null Tree.Null)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (hr : sum_numbers root = ok r), r.val = d.val) := by
  sorry

/-- Whenever sum_numbers(root) returns r, r = 10*d + e.
  Preconditions: root is either Node(d, Node(e, Null, Null), Null) or Node(d, Null, Node(e, Null, Null)) for integers d and e with 0 ≤ d ≤ 9 and 0 ≤ e ≤ 9. -/
theorem spec_6 (root : Tree) (d e : I64) (r : I64)
    (hroot : root = Tree.Node d (Tree.Node e Tree.Null Tree.Null) Tree.Null ∨
      root = Tree.Node d Tree.Null (Tree.Node e Tree.Null Tree.Null))
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (he : 0 ≤ e.val ∧ e.val ≤ 9)
    (hr : sum_numbers root = ok r) :
    r.val = 10 * d.val + e.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (d e : I64) (r : I64)
    (hroot : root = Tree.Node d (Tree.Node e Tree.Null Tree.Null) Tree.Null ∨
      root = Tree.Node d Tree.Null (Tree.Node e Tree.Null Tree.Null))
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (he : 0 ≤ e.val ∧ e.val ≤ 9)
    (hr : sum_numbers root = ok r), r.val = 10 * d.val + e.val) := by
  sorry

/-- Whenever sum_numbers(root) returns r, r = 0.
  Preconditions: root is a non-null binary tree, every Node value is 0, the number of nodes is in [1,1000], and every root-to-leaf path has at most 10 nodes. -/
theorem spec_7 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hzero : allZero root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hr : sum_numbers root = ok r) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hzero : allZero root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hr : sum_numbers root = ok r), r.val = 0) := by
  sorry

/-- Define, for a non-null tree T, len(Q) and value(Q) for a root-to-leaf path Q = q0,...,qm of T by len(Q)=m+1 and value(Q)=Σ_{i=0}^{m} v(q_i)*10^{m-i}, where v(q) is the integer stored at q. For a tree U (possibly Null) and integer d, define S(U,d)=0 if U=Null, and otherwise S(U,d)=Σ_{Q} (d*10^(len(Q)) + value(Q)) over all root-to-leaf paths Q of U. Whenever sum_numbers(root) returns r, r = (if L=Null and R=Null then d else 0) + S(L,d) + S(R,d).
  Preconditions: root = Node(d, L, R) for some integer d with 0 ≤ d ≤ 9; every node value in L and R is in 0..9; the tree has 1..1000 nodes; every root-to-leaf path of root has at most 10 nodes; the total sum fits in the signed 32-bit integer range. -/
theorem spec_8 (d : I64) (L R : Tree) (r : I64)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (hdigits : digitsOK L ∧ digitsOK R)
    (hcount : nodeCountOK (Tree.Node d L R))
    (hpaths : pathLengthOK (Tree.Node d L R))
    (hsum : sumFitsI32 (Tree.Node d L R))
    (hr : sum_numbers (Tree.Node d L R) = ok r) :
    r.val = rootLeafTerm d.val L R + prefixValue L d.val + prefixValue R d.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (d : I64) (L R : Tree) (r : I64)
    (hd : 0 ≤ d.val ∧ d.val ≤ 9)
    (hdigits : digitsOK L ∧ digitsOK R)
    (hcount : nodeCountOK (Tree.Node d L R))
    (hpaths : pathLengthOK (Tree.Node d L R))
    (hsum : sumFitsI32 (Tree.Node d L R))
    (hr : sum_numbers (Tree.Node d L R) = ok r), r.val = rootLeafTerm d.val L R + prefixValue L d.val + prefixValue R d.val) := by
  sorry

/-- Whenever sum_numbers(root) returns r and sum_numbers(root') returns r', r = r'.
  Preconditions: root is a non-null binary tree satisfying the usual constraints (values in 0..9, 1..1000 nodes, every root-to-leaf path at most 10 nodes, sum fits in signed 32-bit integer). root' is obtained from root by exchanging the left and right children of any collection of its nodes, leaving all node values unchanged. -/
theorem spec_9 (root root' : Tree) (r r' : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hmirror : Mirror root root')
    (hr : sum_numbers root = ok r)
    (hr' : sum_numbers root' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root root' : Tree) (r r' : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hmirror : Mirror root root')
    (hr : sum_numbers root = ok r)
    (hr' : sum_numbers root' = ok r'), r.val = r'.val) := by
  sorry

/-- Let P be the unique root-to-leaf path of root, and let value(P) be the integer represented by the sequence of node values along P. Whenever sum_numbers(root) returns r, r = value(P).
  Preconditions: root is a non-null binary tree satisfying the usual constraints (values in 0..9, 1..1000 nodes, every root-to-leaf path at most 10 nodes, sum fits in signed 32-bit integer), and root has exactly one leaf node. -/
theorem spec_10 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hleaves : leafCount root = 1)
    (hr : sum_numbers root = ok r) :
    ∃ P : List Tree, rootLeafPaths root = [P] ∧ r.val = pathValue P := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hleaves : leafCount root = 1)
    (hr : sum_numbers root = ok r), ∃ P : List Tree, rootLeafPaths root = [P] ∧ r.val = pathValue P) := by
  sorry

/-- Let P and Q be the two root-to-leaf paths of root, and let value(P) and value(Q) be the integers represented by their node-value sequences. Whenever sum_numbers(root) returns r, r = value(P) + value(Q).
  Preconditions: root is a non-null binary tree satisfying the usual constraints (values in 0..9, 1..1000 nodes, every root-to-leaf path at most 10 nodes, sum fits in signed 32-bit integer), and root has exactly two leaf nodes. -/
theorem spec_11 (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hleaves : leafCount root = 2)
    (hr : sum_numbers root = ok r) :
    ∃ P Q : List Tree, rootLeafPaths root = [P, Q] ∧ r.val = pathValue P + pathValue Q := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (r : I64)
    (hne : root ≠ Tree.Null)
    (hdigits : digitsOK root)
    (hcount : nodeCountOK root)
    (hpaths : pathLengthOK root)
    (hsum : sumFitsI32 root)
    (hleaves : leafCount root = 2)
    (hr : sum_numbers root = ok r), ∃ P Q : List Tree, rootLeafPaths root = [P, Q] ∧ r.val = pathValue P + pathValue Q) := by
  sorry

end AegisSpec.SumNumbers
