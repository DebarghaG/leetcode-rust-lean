import Aegis.LongestUnivaluePath.Code.Funs

/-!
# Specifications of `Aegis.LongestUnivaluePath.longest_univalue_path`

LeetCode problem `longest-univalue-path`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.LongestUnivaluePath

open Aegis.LongestUnivaluePath

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodeCount l + nodeCount r + 1

def depth : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + max (depth l) (depth r)

def rootVal : Tree → Option Int
  | .Null => none
  | .Node v _ _ => some v.val

def occursIn : Tree → Int → Prop
  | .Null, _ => False
  | .Node v l r, x => v.val = x ∨ occursIn l x ∨ occursIn r x

def allValsIn : Tree → (Int → Prop) → Prop
  | .Null, _ => True
  | .Node v l r, p => p v.val ∧ allValsIn l p ∧ allValsIn r p

def inBounds (t : Tree) : Prop := allValsIn t (fun v => -1000 ≤ v ∧ v ≤ 1000)

def hasSameValEdge : Tree → Prop
  | .Null => False
  | .Node v l r => rootVal l = some v.val ∨ rootVal r = some v.val
      ∨ hasSameValEdge l ∨ hasSameValEdge r

inductive DownAny : Tree → Nat → Prop where
  | zero {v : Std.I64} {l r : Tree} : DownAny (.Node v l r) 0
  | left {v : Std.I64} {l r : Tree} {k : Nat} :
      DownAny l k → DownAny (.Node v l r) (k + 1)
  | right {v : Std.I64} {l r : Tree} {k : Nat} :
      DownAny r k → DownAny (.Node v l r) (k + 1)

inductive AnyPath : Tree → Nat → Prop where
  | single {v : Std.I64} {l r : Tree} : AnyPath (.Node v l r) 0
  | downLeft {v : Std.I64} {l r : Tree} {k : Nat} :
      DownAny l k → AnyPath (.Node v l r) (k + 1)
  | downRight {v : Std.I64} {l r : Tree} {k : Nat} :
      DownAny r k → AnyPath (.Node v l r) (k + 1)
  | throughRoot {v : Std.I64} {l r : Tree} {a b : Nat} :
      DownAny l a → DownAny r b → AnyPath (.Node v l r) (a + b + 2)
  | insideLeft {v : Std.I64} {l r : Tree} {k : Nat} :
      AnyPath l k → AnyPath (.Node v l r) k
  | insideRight {v : Std.I64} {l r : Tree} {k : Nat} :
      AnyPath r k → AnyPath (.Node v l r) k

inductive DownPath : Tree → Int → Nat → Prop where
  | zero {v : Std.I64} {l r : Tree} : DownPath (.Node v l r) v.val 0
  | left {v : Std.I64} {l r : Tree} {k : Nat} :
      DownPath l v.val k → DownPath (.Node v l r) v.val (k + 1)
  | right {v : Std.I64} {l r : Tree} {k : Nat} :
      DownPath r v.val k → DownPath (.Node v l r) v.val (k + 1)

inductive UPath : Tree → Int → Nat → Prop where
  | single {v : Std.I64} {l r : Tree} : UPath (.Node v l r) v.val 0
  | downLeft {v : Std.I64} {l r : Tree} {k : Nat} :
      DownPath l v.val k → UPath (.Node v l r) v.val (k + 1)
  | downRight {v : Std.I64} {l r : Tree} {k : Nat} :
      DownPath r v.val k → UPath (.Node v l r) v.val (k + 1)
  | throughRoot {v : Std.I64} {l r : Tree} {a b : Nat} :
      DownPath l v.val a → DownPath r v.val b → UPath (.Node v l r) v.val (a + b + 2)
  | insideLeft {v : Std.I64} {l r : Tree} {x : Int} {k : Nat} :
      UPath l x k → UPath (.Node v l r) x k
  | insideRight {v : Std.I64} {l r : Tree} {x : Int} {k : Nat} :
      UPath r x k → UPath (.Node v l r) x k

def hasUPath (t : Tree) (k : Nat) : Prop := ∃ x : Int, UPath t x k

noncomputable def univalueMax (t : Tree) : Nat := by
  classical
  exact Nat.findGreatest (hasUPath t) (nodeCount t)

noncomputable def treeDiameter (t : Tree) : Nat := by
  classical
  exact Nat.findGreatest (AnyPath t) (nodeCount t)

def armTo : Int → Tree → Nat
  | _, .Null => 0
  | x, .Node v l r => if v.val = x then 1 + max (armTo x l) (armTo x r) else 0

def down : Tree → Nat
  | .Null => 0
  | .Node v l r => max (armTo v.val l) (armTo v.val r)

def mirror : Tree → Tree
  | .Null => .Null
  | .Node v l r => .Node v (mirror r) (mirror l)

inductive MapsBy (g : Int → Int) : Tree → Tree → Prop where
  | null : MapsBy g .Null .Null
  | node {v w : Std.I64} {l r l' r' : Tree} : w.val = g v.val →
      MapsBy g l l' → MapsBy g r r' → MapsBy g (.Node v l r) (.Node w l' r')

def childResult (t : Tree) (r : Std.I64) : Prop :=
  (t = .Null ∧ r = 0#i64) ∨ longest_univalue_path t = ok r

/-- The function returns a result r (Ok r) and r is exactly the maximum, over all pairs of nodes u and v of root (including u = v), of the number of edges on the unique simple path from u to v, restricted to those paths on which every node has the same value as u; a single-node path has length 0. If root is Null (n = 0), the returned value is r = 0.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. Here a node means an occurrence of the Node constructor. -/
theorem spec_1 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) :
    ∃ r : Std.I64, longest_univalue_path root = ok r ∧ r.val = (univalueMax root : Int) ∧
      (root = .Null → r.val = 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root), ∃ r : Std.I64, longest_univalue_path root = ok r ∧ r.val = (univalueMax root : Int) ∧
      (root = .Null → r.val = 0)) := by
  sorry

/-- For every root satisfying the preconditions, the function returns a result r and does not fail: there is no overflow, out-of-bounds access, or panic.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. -/
theorem spec_2 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) :
    ∃ r : Std.I64, longest_univalue_path root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root), ∃ r : Std.I64, longest_univalue_path root = ok r) := by
  sorry

/-- Whenever the function returns r on root, 0 <= r <= max(0, n - 1), where n is the number of nodes of root.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. -/
theorem spec_3 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r) :
    0 ≤ r.val ∧ r.val ≤ max 0 ((n : Int) - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r), 0 ≤ r.val ∧ r.val ≤ max 0 ((n : Int) - 1)) := by
  sorry

/-- Whenever the function returns r on root, if root is nonempty then there exist nodes u and v of root (possibly u = v) such that the unique simple path from u to v has exactly r edges and every node on that path has the same value; if root is Null then r = 0.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. -/
theorem spec_4 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r) :
    (root = .Null → r.val = 0) ∧
      (root ≠ .Null → ∃ (x : Int) (k : Nat), UPath root x k ∧ (k : Int) = r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r), (root = .Null → r.val = 0) ∧
      (root ≠ .Null → ∃ (x : Int) (k : Nat), UPath root x k ∧ (k : Int) = r.val)) := by
  sorry

/-- Whenever the function returns r on root, every simple path between two nodes of root whose nodes all have the same value has length at most r edges.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. -/
theorem spec_5 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r) :
    ∀ (x : Int) (k : Nat), UPath root x k → (k : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r), ∀ (x : Int) (k : Nat), UPath root x k → (k : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns r on root, r equals the maximum, over all pairs of nodes u and v of root, of the number of edges on the unique simple path from u to v; equivalently, r is the diameter of root measured in edges.
  Preconditions: root is nonempty and every node of root has the same value x, with -1000 <= x <= 1000 and 1 <= n <= 10000, where n is the number of nodes in root; the depth of root is at most 1000. -/
theorem spec_6 (root : Tree) (x : Std.I64) (n : Nat) (hn : nodeCount root = n)
    (hnpos : 1 ≤ n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000) (hne : root ≠ .Null)
    (hval : allValsIn root (fun v => v = x.val)) (hx : -1000 ≤ x.val ∧ x.val ≤ 1000) :
    ∀ r : Std.I64,
      longest_univalue_path root = ok r → r.val = (treeDiameter root : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (x : Std.I64) (n : Nat) (hn : nodeCount root = n)
    (hnpos : 1 ≤ n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000) (hne : root ≠ .Null)
    (hval : allValsIn root (fun v => v = x.val)) (hx : -1000 ≤ x.val ∧ x.val ≤ 1000), ∀ r : Std.I64,
      longest_univalue_path root = ok r → r.val = (treeDiameter root : Int)) := by
  sorry

/-- Whenever the function returns r on root, r = 0 if and only if every parent-child edge of root joins two nodes with different values; equivalently, r > 0 if and only if there is at least one parent-child edge whose two endpoint values are equal.
  Preconditions: root is a Tree with n nodes, where 0 <= n <= 10000; the depth of root is at most 1000; every node value is an integer in [-1000, 1000]. -/
theorem spec_7 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r) :
    (r.val = 0 ↔ ¬ hasSameValEdge root) ∧ (0 < r.val ↔ hasSameValEdge root) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (r : Std.I64)
    (hr : longest_univalue_path root = ok r), (r.val = 0 ↔ ¬ hasSameValEdge root) ∧ (0 < r.val ↔ hasSameValEdge root)) := by
  sorry

/-- Whenever the function returns r on root, and rL is the result returned by the function on L when L is non-Null (with rL = 0 when L = Null), and rR is the result returned by the function on R when R is non-Null (with rR = 0 when R = Null), then r >= rL and r >= rR.
  Preconditions: root is a Tree of the form Node(x, L, R), with 0 <= n <= 10000 nodes, depth at most 1000, and every node value in [-1000, 1000]; L is the left subtree and R is the right subtree. -/
theorem spec_8 (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (r : Std.I64) (hr : longest_univalue_path root = ok r) :
    ∀ (rL rR : Std.I64),
      childResult L rL → childResult R rR → rL.val ≤ r.val ∧ rR.val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (r : Std.I64) (hr : longest_univalue_path root = ok r), ∀ (rL rR : Std.I64),
      childResult L rL → childResult R rR → rL.val ≤ r.val ∧ rR.val ≤ r.val) := by
  sorry

/-- Let mirror(root) be the tree obtained from root by recursively replacing every Node(x, L, R) with Node(x, mirror(R), mirror(L)) and leaving Null unchanged. Whenever the function returns r on root and r_m on mirror(root), r = r_m.
  Preconditions: root is a Tree with 0 <= n <= 10000 nodes, depth at most 1000, and every node value in [-1000, 1000]. -/
theorem spec_9 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) :
    ∀ (r rm : Std.I64), longest_univalue_path root = ok r →
      longest_univalue_path (mirror root) = ok rm → r.val = rm.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root), ∀ (r rm : Std.I64), longest_univalue_path root = ok r →
      longest_univalue_path (mirror root) = ok rm → r.val = rm.val) := by
  sorry

/-- Whenever the function returns r on root and r_f on T_f(root), r = r_f.
  Preconditions: root is a Tree with 0 <= n <= 10000 nodes, depth at most 1000, and every node value in [-1000, 1000]. Let S be the set of values occurring in root. Let f be any function from S into [-1000, 1000] that is injective on S. Let T_f(root) be the tree obtained by replacing each node value v by f(v). -/
theorem spec_10 (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (g : Int → Int)
    (hg : ∀ v : Int, occursIn root v → -1000 ≤ g v ∧ g v ≤ 1000)
    (hinj : ∀ a b : Int, occursIn root a → occursIn root b → g a = g b → a = b) :
    ∀ (tf : Tree) (r rf : Std.I64), MapsBy g root tf → longest_univalue_path root = ok r →
      longest_univalue_path tf = ok rf → r.val = rf.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (n : Nat) (hn : nodeCount root = n) (hnle : n ≤ 10000)
    (hdepth : depth root ≤ 1000) (hbounds : inBounds root) (g : Int → Int)
    (hg : ∀ v : Int, occursIn root v → -1000 ≤ g v ∧ g v ≤ 1000)
    (hinj : ∀ a b : Int, occursIn root a → occursIn root b → g a = g b → a = b), ∀ (tf : Tree) (r rf : Std.I64), MapsBy g root tf → longest_univalue_path root = ok r →
      longest_univalue_path tf = ok rf → r.val = rf.val) := by
  sorry

/-- Whenever the function returns r on root, and rL is the result returned by the function on L when L is non-Null (with rL = 0 when L = Null), and rR is the result returned by the function on R when R is non-Null (with rR = 0 when R = Null), then r = max(rL, rR).
  Preconditions: root is a Tree of the form Node(x, L, R), with 0 <= n <= 10000 nodes, depth at most 1000, and every node value in [-1000, 1000]; L is the left subtree and R is the right subtree; every non-null child of root has a root value different from x. -/
theorem spec_11 (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (hchildL : rootVal L ≠ some x.val)
    (hchildR : rootVal R ≠ some x.val) (r : Std.I64)
    (hr : longest_univalue_path root = ok r) :
    ∀ (rL rR : Std.I64),
      childResult L rL → childResult R rR → r.val = max rL.val rR.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (hchildL : rootVal L ≠ some x.val)
    (hchildR : rootVal R ≠ some x.val) (r : Std.I64)
    (hr : longest_univalue_path root = ok r), ∀ (rL rR : Std.I64),
      childResult L rL → childResult R rR → r.val = max rL.val rR.val) := by
  sorry

/-- If the function returns r on root, then r = max(rL, rR, armL + armR). Thus every longest univalue path is either wholly contained in one child subtree or is formed by joining through root the longest equal-valued downward arms in the left and right subtrees.
  Preconditions: root = Node(x, L, R) with 0 <= n <= 10000 nodes, depth at most 1000, and every node value in [-1000, 1000]; L and R are the left and right subtrees. For a nonempty tree w, define down(w) as the maximum number of edges on a downward path starting at w and following only child edges, all of whose nodes have the same value as the root of w; a single-node downward path has length 0. Let rL and rR be the function results on L and R when non-Null, and 0 when Null. Let armL = 0 if L = Null or root(L) has value different from x, otherwise armL = 1 + down(L); define armR similarly. -/
theorem spec_12 (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (r : Std.I64) (hr : longest_univalue_path root = ok r) :
    ∀ (rL rR : Std.I64), childResult L rL → childResult R rR →
      r.val = max (max rL.val rR.val) ((armTo x.val L : Int) + (armTo x.val R : Int)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root L R : Tree) (x : Std.I64) (n : Nat) (hroot : root = .Node x L R)
    (hn : nodeCount root = n) (hnle : n ≤ 10000) (hdepth : depth root ≤ 1000)
    (hbounds : inBounds root) (r : Std.I64) (hr : longest_univalue_path root = ok r), ∀ (rL rR : Std.I64), childResult L rL → childResult R rR →
      r.val = max (max rL.val rR.val) ((armTo x.val L : Int) + (armTo x.val R : Int))) := by
  sorry

end AegisSpec.LongestUnivaluePath
