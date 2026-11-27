import Aegis.MaxPathSum.Code.Funs

/-!
# Specifications of `Aegis.MaxPathSum.max_path_sum`

LeetCode problem `binary-tree-maximum-path-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPathSum

open Aegis.MaxPathSum

def nodeVal : Tree → Int
  | .Null => 0
  | .Node v _ _ => v.val

def nodeVals : Tree → List Int
  | .Null => []
  | .Node v l r => v.val :: (nodeVals l ++ nodeVals r)

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodeCount l + nodeCount r + 1

def SizeOk (t : Tree) : Prop := 1 ≤ nodeCount t ∧ nodeCount t ≤ 30000

def ValsInRange (t : Tree) : Prop := ∀ x ∈ nodeVals t, -1000 ≤ x ∧ x ≤ 1000

def ValsNonneg (t : Tree) : Prop := ∀ x ∈ nodeVals t, 0 ≤ x

def ValsNonpos (t : Tree) : Prop := ∀ x ∈ nodeVals t, x ≤ 0

def ValsEq (t : Tree) (c : Int) : Prop := ∀ x ∈ nodeVals t, x = c

def sumVals (t : Tree) : Int := (nodeVals t).sum

def sumPosVals (t : Tree) : Int := ((nodeVals t).filter (fun x => decide (0 < x))).sum

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def maxNodeVal (t : Tree) : Int := listMax (nodeVals t)

def mirror : Tree → Tree
  | .Null => .Null
  | .Node v l r => .Node v (mirror r) (mirror l)

def IsChain : Tree → Prop
  | .Null => True
  | .Node _ l r => (l = .Null ∨ r = .Null) ∧ IsChain l ∧ IsChain r

def chainVals : Tree → List Int
  | .Null => []
  | .Node v .Null r => v.val :: chainVals r
  | .Node v l _ => v.val :: chainVals l

inductive DownChain : Tree → List Tree → Prop where
  | null : DownChain .Null []
  | left {v : I64} {l r : Tree} {rest : List Tree} :
      DownChain l rest → DownChain (.Node v l r) (.Node v l r :: rest)
  | right {v : I64} {l r : Tree} {rest : List Tree} :
      DownChain r rest → DownChain (.Node v l r) (.Node v l r :: rest)

inductive IsSimplePath : Tree → List Tree → Prop where
  | left {v : I64} {l r : Tree} {p : List Tree} :
      IsSimplePath l p → IsSimplePath (.Node v l r) p
  | right {v : I64} {l r : Tree} {p : List Tree} :
      IsSimplePath r p → IsSimplePath (.Node v l r) p
  | through {v : I64} {l r : Tree} {L R : List Tree} :
      DownChain l L → DownChain r R →
      IsSimplePath (.Node v l r) (L.reverse ++ .Node v l r :: R)

def pathSum (p : List Tree) : Int := (p.map nodeVal).sum

def IsMaxPathSum (t : Tree) (s : Int) : Prop :=
  (∃ p, IsSimplePath t p ∧ pathSum p = s) ∧ ∀ p, IsSimplePath t p → pathSum p ≤ s

def nodeAt : Tree → List Bool → Option Tree
  | .Null, _ => none
  | .Node v l r, [] => some (.Node v l r)
  | .Node _ l _, false :: rest => nodeAt l rest
  | .Node _ _ r, true :: rest => nodeAt r rest

def swapAt : Tree → List Bool → Tree
  | .Null, _ => .Null
  | .Node v l r, [] => .Node v r l
  | .Node v l r, false :: rest => .Node v (swapAt l rest) r
  | .Node v l r, true :: rest => .Node v l (swapAt r rest)

def IsSwapOf (root root' : Tree) : Prop :=
  ∃ pos : List Bool, (∃ u : Tree, nodeAt root pos = some u) ∧ swapAt root pos = root'

def SameShape : Tree → Tree → Prop
  | .Null, .Null => True
  | .Node _ l r, .Node _ l' r' => SameShape l l' ∧ SameShape r r'
  | _, _ => False

def PointwiseLE : Tree → Tree → Prop
  | .Null, .Null => True
  | .Node v l r, .Node v' l' r' => v.val ≤ v'.val ∧ PointwiseLE l l' ∧ PointwiseLE r r'
  | _, _ => False

def height : Tree → Nat
  | .Null => 0
  | .Node _ l r => max (height l) (height r) + 1

def maxPathLen : Tree → Nat
  | .Null => 0
  | .Node _ l r => max (max (maxPathLen l) (maxPathLen r)) (height l + height r + 1)

def segSums (l : List Int) : List Int :=
  (List.range l.length).flatMap fun i =>
    (List.range (l.length - i)).map fun k => ((l.drop i).take (k + 1)).sum

def maxSegSum (l : List Int) : Int := listMax (segSums l)

def T1 (v : Int) (t : Tree) : Prop :=
  ∃ w : I64, w.val = v ∧ t = .Node w .Null .Null

def T2a (a b : Int) (t : Tree) : Prop :=
  ∃ wa wb : I64, wa.val = a ∧ wb.val = b ∧ t = .Node wa (.Node wb .Null .Null) .Null

def T2b (a b : Int) (t : Tree) : Prop :=
  ∃ wa wb : I64, wa.val = a ∧ wb.val = b ∧ t = .Node wa .Null (.Node wb .Null .Null)

def T3 (a b c : Int) (t : Tree) : Prop :=
  ∃ wa wb wc : I64,
    wa.val = a ∧ wb.val = b ∧ wc.val = c ∧
      t = .Node wa (.Node wb .Null .Null) (.Node wc .Null .Null)

/-- The function returns a result r (it does not fail), and r is the maximum path sum of root. The maximum path sum is defined as follows: a non-empty simple path is a finite sequence p_0,...,p_k with k >= 0 of pairwise distinct nodes of root such that for every i with 0 <= i < k, p_i and p_{i+1} are a parent and a child in root in either order; its sum is val(p_0)+...+val(p_k), where val(n) is the integer stored at node n. The maximum is taken over all such non-empty simple paths in root. Single-node paths are allowed, paths need not pass through the designated root, and empty paths are not allowed.
  Preconditions: root is a finite binary tree (Tree) with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. -/
theorem spec_1 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∃ r : I64, max_path_sum root = ok r ∧ IsMaxPathSum root r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∃ r : I64, max_path_sum root = ok r ∧ IsMaxPathSum root r.val) := by
  sorry

/-- For every such root, the function returns a result (a successful Result carrying an i64); it never fails by overflow, by panic, by an out-of-bounds access, or by returning an error.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. -/
theorem spec_2 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∃ r : I64, max_path_sum root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∃ r : I64, max_path_sum root = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists a non-empty simple path P in root whose node-value sum is r. Here a simple path is a finite sequence p_0,...,p_k with k >= 0 of pairwise distinct nodes of root such that for every i with 0 <= i < k, p_i and p_{i+1} are a parent and a child in root in either order; its node-value sum is val(p_0)+...+val(p_k).
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. -/
theorem spec_3 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∀ r : I64, max_path_sum root = ok r → ∃ p : List Tree, IsSimplePath root p ∧ pathSum p = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∀ r : I64, max_path_sum root = ok r → ∃ p : List Tree, IsSimplePath root p ∧ pathSum p = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every non-empty simple path P in root, the sum of val(n) over all nodes n on P is at most r. Here a simple path is a finite sequence p_0,...,p_k with k >= 0 of pairwise distinct nodes of root such that for every i with 0 <= i < k, p_i and p_{i+1} are a parent and a child in root in either order.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. -/
theorem spec_4 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∀ r : I64, max_path_sum root = ok r → ∀ p : List Tree, IsSimplePath root p → pathSum p ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∀ r : I64, max_path_sum root = ok r → ∀ p : List Tree, IsSimplePath root p → pathSum p ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r is at most the sum of val(n) over all nodes n of root whose value is positive (this sum is 0 if root has no positive-valued node).
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. -/
theorem spec_5 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∀ r : I64, max_path_sum root = ok r → r.val ≤ sumPosVals root := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∀ r : I64, max_path_sum root = ok r → r.val ≤ sumPosVals root) := by
  sorry

/-- The function returns a result r and r = v.
  Preconditions: root is exactly Node(v, Null, Null) for some integer v with -1000 <= v <= 1000. -/
theorem spec_6 (root : Tree) (v : Int) (hvlo : -1000 ≤ v) (hvhi : v ≤ 1000)
    (hroot : T1 v root) :
    ∃ r : I64, max_path_sum root = ok r ∧ r.val = v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (v : Int) (hvlo : -1000 ≤ v) (hvhi : v ≤ 1000)
    (hroot : T1 v root), ∃ r : I64, max_path_sum root = ok r ∧ r.val = v) := by
  sorry

/-- Whenever the function returns a result r, r = max(a, b, a+b), where max is the maximum of the three mathematical integers.
  Preconditions: root is either Node(a, Node(b, Null, Null), Null) or Node(a, Null, Node(b, Null, Null)), where -1000 <= a <= 1000 and -1000 <= b <= 1000. -/
theorem spec_7 (root : Tree) (a b : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hroot : T2a a b root ∨ T2b a b root) :
    ∀ r : I64, max_path_sum root = ok r → r.val = max a (max b (a + b)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (a b : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hroot : T2a a b root ∨ T2b a b root), ∀ r : I64, max_path_sum root = ok r → r.val = max a (max b (a + b))) := by
  sorry

/-- Whenever the function returns a result r, r = max(a, b, c, a+b, a+c, a+b+c), where max is over the six listed mathematical integers.
  Preconditions: root is exactly Node(a, Node(b, Null, Null), Node(c, Null, Null)) for integers a,b,c in [-1000, 1000]. -/
theorem spec_8 (root : Tree) (a b c : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hclo : -1000 ≤ c) (hchi : c ≤ 1000) (hroot : T3 a b c root) :
    ∀ r : I64, max_path_sum root = ok r →
      r.val = max a (max b (max c (max (a + b) (max (a + c) (a + b + c))))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (a b c : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hclo : -1000 ≤ c) (hchi : c ≤ 1000) (hroot : T3 a b c root), ∀ r : I64, max_path_sum root = ok r →
      r.val = max a (max b (max c (max (a + b) (max (a + c) (a + b + c)))))) := by
  sorry

/-- Whenever the function returns a result r, r equals the maximum of val(n) over all nodes n of root.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, every node value is in [-1000, 1000], and every node value is at most 0. -/
theorem spec_9 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hnonpos : ValsNonpos root) :
    ∀ r : I64, max_path_sum root = ok r → r.val = maxNodeVal root := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hnonpos : ValsNonpos root), ∀ r : I64, max_path_sum root = ok r → r.val = maxNodeVal root) := by
  sorry

/-- The function returns a result r and r equals the sum of val(n) over all nodes n of root.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, every node value is in [-1000, 1000], every node value is at least 0, and root is a chain: every node has at most one non-Null child. -/
theorem spec_10 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hnonneg : ValsNonneg root) (hchain : IsChain root) :
    ∃ r : I64, max_path_sum root = ok r ∧ r.val = sumVals root := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hnonneg : ValsNonneg root) (hchain : IsChain root), ∃ r : I64, max_path_sum root = ok r ∧ r.val = sumVals root) := by
  sorry

/-- Whenever max_path_sum(root) returns a result r and max_path_sum(mirror(root)) returns a result r', we have r = r'.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and every node value is an integer in [-1000, 1000]. Define mirror(root) recursively by mirror(Null) = Null and mirror(Node(v,l,r)) = Node(v,mirror(r),mirror(l)). -/
theorem spec_11 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root) :
    ∀ r r' : I64, max_path_sum root = ok r → max_path_sum (mirror root) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root), ∀ r r' : I64, max_path_sum root = ok r → max_path_sum (mirror root) = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever max_path_sum(root) returns a result r and max_path_sum(root') returns a result r', we have r = r'.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, every node value is in [-1000, 1000], and root' is any tree obtained from root by choosing one node u of root and swapping its left and right subtrees, with all other nodes and edges unchanged. -/
theorem spec_12 (root root' : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hswap : IsSwapOf root root') :
    ∀ r r' : I64, max_path_sum root = ok r → max_path_sum root' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root root' : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hswap : IsSwapOf root root'), ∀ r r' : I64, max_path_sum root = ok r → max_path_sum root' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = max(a, b, c, a+b, b+c, a+b+c), where max is over the six listed mathematical integers.
  Preconditions: root is a chain with exactly three nodes, and a,b,c are its node values in top-to-bottom order, with -1000 <= a <= 1000, -1000 <= b <= 1000, and -1000 <= c <= 1000. -/
theorem spec_13 (root : Tree) (a b c : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hclo : -1000 ≤ c) (hchi : c ≤ 1000)
    (hchain : IsChain root) (hcount : nodeCount root = 3)
    (hvals : chainVals root = [a, b, c]) :
    ∀ r : I64, max_path_sum root = ok r →
      r.val = max a (max b (max c (max (a + b) (max (b + c) (a + b + c))))) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (root : Tree) (a b c : Int)
    (halo : -1000 ≤ a) (hahi : a ≤ 1000) (hblo : -1000 ≤ b) (hbhi : b ≤ 1000)
    (hclo : -1000 ≤ c) (hchi : c ≤ 1000)
    (hchain : IsChain root) (hcount : nodeCount root = 3)
    (hvals : chainVals root = [a, b, c]), ∀ r : I64, max_path_sum root = ok r →
      r.val = max a (max b (max c (max (a + b) (max (b + c) (a + b + c)))))) := by
  sorry

/-- Whenever the function returns a result r, r = c * L, where L is the maximum number of nodes in a non-empty simple path in root. Here a simple path is a finite sequence p_0,...,p_k with k >= 0 of pairwise distinct nodes of root such that consecutive nodes are parent and child in either order.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, and there is an integer c with 1 <= c <= 1000 such that every node value equals c. -/
theorem spec_14 (root : Tree) (c : Int) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 1000) (hconst : ValsEq root c) :
    ∀ r : I64, max_path_sum root = ok r → r.val = c * (maxPathLen root : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (root : Tree) (c : Int) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 1000) (hconst : ValsEq root c), ∀ r : I64, max_path_sum root = ok r → r.val = c * (maxPathLen root : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = max_{1 <= i <= j <= n} (a_i + ... + a_j), the maximum over all non-empty contiguous segments of the chain, computed as mathematical integers.
  Preconditions: root is a finite binary tree with at least one node and at most 30000 nodes, every node value is in [-1000, 1000], and root is a chain. Let a_1,...,a_n be the node values in top-to-bottom order (n >= 1). -/
theorem spec_15 (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hchain : IsChain root) :
    ∀ r : I64, max_path_sum root = ok r → r.val = maxSegSum (chainVals root) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (root : Tree) (hsize : SizeOk root) (hvals : ValsInRange root)
    (hchain : IsChain root), ∀ r : I64, max_path_sum root = ok r → r.val = maxSegSum (chainVals root)) := by
  sorry

/-- Whenever max_path_sum(root) returns a result r and max_path_sum(root') returns a result r', we have r <= r'.
  Preconditions: root and root' are finite binary trees with the same shape (the same Null/Node structure), each has at least one node and at most 30000 nodes, every node value in both trees is in [-1000, 1000], and for every node n of root with corresponding node n' of root', val(n) <= val(n'). -/
theorem spec_16 (root root' : Tree)
    (hsize : SizeOk root) (hvals : ValsInRange root)
    (hsize' : SizeOk root') (hvals' : ValsInRange root')
    (hshape : SameShape root root') (hle : PointwiseLE root root') :
    ∀ r r' : I64, max_path_sum root = ok r → max_path_sum root' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (root root' : Tree)
    (hsize : SizeOk root) (hvals : ValsInRange root)
    (hsize' : SizeOk root') (hvals' : ValsInRange root')
    (hshape : SameShape root root') (hle : PointwiseLE root root'), ∀ r r' : I64, max_path_sum root = ok r → max_path_sum root' = ok r' →
      r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxPathSum
