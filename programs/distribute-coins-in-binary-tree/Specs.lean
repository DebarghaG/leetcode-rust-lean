import Aegis.DistributeCoins.Code.Funs

/-!
# Specifications of `Aegis.DistributeCoins.distribute_coins`

LeetCode problem `distribute-coins-in-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistributeCoins

open Aegis.DistributeCoins

def iabs (x : Int) : Int := if x < 0 then -x else x

def size : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + size l + size r

def csum : Tree → Int
  | Tree.Null => 0
  | Tree.Node v l r => v.val + csum l + csum r

def imbalance (t : Tree) : Int := iabs (csum t - (size t : Int))

def inner : Tree → Int
  | Tree.Null => 0
  | Tree.Node _ l r => inner l + inner r + imbalance l + imbalance r

def valuesBounded (t : Tree) (n : Nat) : Prop :=
  match t with
  | Tree.Null => True
  | Tree.Node v l r =>
      (0 ≤ v.val ∧ v.val ≤ (n : Int)) ∧ valuesBounded l n ∧ valuesBounded r n

def allOnes : Tree → Prop
  | Tree.Null => True
  | Tree.Node v l r => v.val = 1 ∧ allOnes l ∧ allOnes r

def subtreeAt : Tree → List Bool → Option Tree
  | Tree.Null, _ => none
  | Tree.Node v l r, [] => some (Tree.Node v l r)
  | Tree.Node _ l _, false :: p => subtreeAt l p
  | Tree.Node _ _ r, true :: p => subtreeAt r p

def valAt : Tree → List Bool → Option Int
  | Tree.Null, _ => none
  | Tree.Node v _ _, [] => some v.val
  | Tree.Node _ l _, false :: p => valAt l p
  | Tree.Node _ _ r, true :: p => valAt r p

def occurs (t : Tree) (p : List Bool) : Prop := ∃ s, subtreeAt t p = some s

def depthSum : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => depthSum l + size l + (depthSum r + size r)

def marked : Tree → List Bool → Option (Nat × Nat × Nat)
  | Tree.Null, _ => none
  | Tree.Node _ l r, [] =>
      some (1 + size l + size r, 0, depthSum l + size l + (depthSum r + size r))
  | Tree.Node _ l r, false :: p =>
      match marked l p with
      | none => none
      | some (sl, dl, ml) =>
          some (1 + sl + size r, dl + 1,
            ml + (dl + 1) + (size r * (dl + 2) + depthSum r))
  | Tree.Node _ l r, true :: p =>
      match marked r p with
      | none => none
      | some (sr, dr, mr) =>
          some (1 + size l + sr, dr + 1,
            mr + (dr + 1) + (size l * (dr + 2) + depthSum l))

def distSumFrom (t : Tree) (p : List Bool) : Nat :=
  match marked t p with
  | none => 0
  | some (_, _, m) => m

inductive Mirrors : Tree → Tree → Prop where
  | null : Mirrors Tree.Null Tree.Null
  | node {v l r l' r'} :
      Mirrors l l' → Mirrors r r' → Mirrors (Tree.Node v l r) (Tree.Node v l' r')
  | swap {v l r l' r'} :
      Mirrors r l' → Mirrors l r' → Mirrors (Tree.Node v l r) (Tree.Node v l' r')

def Coins : Type := List Bool → Nat

def sharesPath (a b : List Bool) : Prop :=
  (∃ c : Bool, b = a ++ [c]) ∨ (∃ c : Bool, a = b ++ [c])

def adjacent (t : Tree) (a b : List Bool) : Prop :=
  occurs t a ∧ occurs t b ∧ sharesPath a b

def transfer (c : Coins) (a b : List Bool) : Coins :=
  fun x => if x = a then c a - 1 else if x = b then c b + 1 else c x

inductive ReachIn (t : Tree) : Coins → Coins → Nat → Prop where
  | refl (c : Coins) : ReachIn t c c 0
  | step {c c' : Coins} {k : Nat} {a b : List Bool} :
      adjacent t a b → 0 < c a → ReachIn t (transfer c a b) c' k →
        ReachIn t c c' (k + 1)

def initCoins (t : Tree) : Coins :=
  fun p => match valAt t p with
    | none => 0
    | some v => v.toNat

def oneCoinEach (t : Tree) (c : Coins) : Prop := ∀ p, occurs t p → c p = 1

/-- The function returns a result r, and r equals the sum, over every node v other than the root, of |coins(v) - size(v)|, where size(v) is the number of nodes in the subtree rooted at v and coins(v) is the sum of the node values in that same subtree. For a node v, its subtree consists of v and all of its descendants. The root itself is excluded from the sum.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_1 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∃ r : Std.I64,
      Aegis.DistributeCoins.distribute_coins root = ok r ∧ r.val = inner root := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∃ r : Std.I64,
      Aegis.DistributeCoins.distribute_coins root = ok r ∧ r.val = inner root) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r of type Std.I64; it does not fail, panic, or overflow. In particular, r is a well-defined 64-bit integer within the representable range.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_2 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∃ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∃ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_3 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (n-1)*(n-1).
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_4 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val ≤ ((n : Int) - 1) * ((n : Int) - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val ≤ ((n : Int) - 1) * ((n : Int) - 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if every node of root has value exactly 1.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_5 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      (r.val = 0 ↔ allOnes root) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      (r.val = 0 ↔ allOnes root)) := by
  sorry

/-- Whenever the function returns a result r, r = |root_value - 1|, where root_value is the value at the root node. Equivalently, r = |child_value - 1| for the unique child's value.
  Preconditions: The input satisfies the problem constraints, and root has exactly two nodes: the root Node and one child, either left or right, with no grandchildren. Thus n=2 and the sum of the two node values is 2. -/
theorem spec_6 (root : Tree) (n : Nat) (a : Std.I64) (L R : Tree)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hroot : root = Tree.Node a L R) (hn : n = 2)
    (hshape :
      (L = Tree.Null ∧ ∃ c : Std.I64, R = Tree.Node c Tree.Null Tree.Null) ∨
        (R = Tree.Null ∧ ∃ c : Std.I64, L = Tree.Node c Tree.Null Tree.Null)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = iabs (a.val - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (n : Nat) (a : Std.I64) (L R : Tree)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hroot : root = Tree.Node a L R) (hn : n = 2)
    (hshape :
      (L = Tree.Null ∧ ∃ c : Std.I64, R = Tree.Node c Tree.Null Tree.Null) ∨
        (R = Tree.Null ∧ ∃ c : Std.I64, L = Tree.Node c Tree.Null Tree.Null)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = iabs (a.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, r equals the sum of dist(p,v) over all nodes v of root with v != p, where dist(p,v) is the number of edges on the unique path from p to v in the tree.
  Preconditions: The input satisfies the problem constraints. There is a node p in root with value n, and every node other than p has value 0, where n is the total number of nodes in root. -/
theorem spec_7 (root : Tree) (n : Nat) (p : List Bool)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hpval : valAt root p = some (n : Int))
    (hzero : ∀ (q : List Bool) (v : Int), q ≠ p → valAt root q = some v → v = 0) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = (distSumFrom root p : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (n : Nat) (p : List Bool)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hpval : valAt root p = some (n : Int))
    (hzero : ∀ (q : List Bool) (v : Int), q ≠ p → valAt root q = some v → v = 0), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = (distSumFrom root p : Int)) := by
  sorry

/-- Whenever the function returns r on root and r' on root', we have r = r'.
  Preconditions: Let root satisfy the problem constraints. Let root' be any tree obtained from root by independently swapping the left and right child subtrees at zero or more nodes, without changing any node values. Then root' has the same number n of nodes and the same node values as root, only with left/right order changed, so it also satisfies the constraints. -/
theorem spec_8 (root root' : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hmirror : Mirrors root root') :
    ∀ r r' : Std.I64,
      Aegis.DistributeCoins.distribute_coins root = ok r →
        Aegis.DistributeCoins.distribute_coins root' = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root' : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hmirror : Mirrors root root'), ∀ r r' : Std.I64,
      Aegis.DistributeCoins.distribute_coins root = ok r →
        Aegis.DistributeCoins.distribute_coins root' = ok r' → r = r') := by
  sorry

/-- Suppose root is a Node with value a, left subtree L, and right subtree R. For any possibly-Null tree C, let N(C) be its number of nodes and Csum(C) be the sum of its node values, with N(Null)=0 and Csum(Null)=0. Let inner(C) be the sum, over every node v of C other than the top node of C if C is non-Null, of |coins_C(v) - size_C(v)|, where size_C and coins_C are computed inside C; set inner(Null)=0. Whenever the function returns r on root, r = inner(L) + inner(R) + |Csum(L)-N(L)| + |Csum(R)-N(R)|.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_9 (root : Tree) (n : Nat) (a : Std.I64) (L R : Tree)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hroot : root = Tree.Node a L R) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = inner L + inner R + iabs (csum L - (size L : Int)) +
        iabs (csum R - (size R : Int)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (n : Nat) (a : Std.I64) (L R : Tree)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int))
    (hroot : root = Tree.Node a L R), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      r.val = inner L + inner R + iabs (csum L - (size L : Int)) +
        iabs (csum R - (size R : Int))) := by
  sorry

/-- Whenever the function returns a result r, for every node v other than the root, r >= |coins(v) - size(v)|, where size(v) is the number of nodes in the subtree rooted at v and coins(v) is the sum of values in that subtree.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_10 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∀ (p : List Bool), p ≠ [] → ∀ s : Tree, subtreeAt root p = some s → imbalance s ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∀ (p : List Bool), p ≠ [] → ∀ s : Tree, subtreeAt root p = some s → imbalance s ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a finite sequence of exactly r moves, each move taking one coin between two adjacent nodes, such that after all moves every node has exactly one coin.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_11 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∃ k : Nat, (k : Int) = r.val ∧
        ∃ c : Coins, ReachIn root (initCoins root) c k ∧ oneCoinEach root c := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∃ k : Nat, (k : Int) = r.val ∧
        ∃ c : Coins, ReachIn root (initCoins root) c k ∧ oneCoinEach root c) := by
  sorry

/-- Whenever the function returns a result r, there is no finite sequence of fewer than r moves, each move taking one coin between two adjacent nodes, such that after all moves every node has exactly one coin.
  Preconditions: Let n be the number of Node constructors reachable in root. The input satisfies the problem constraints: root is not Null, 1 <= n <= 100, every node value is an integer with 0 <= value <= n, and the sum of all node values is n. -/
theorem spec_12 (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)) :
    ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∀ (k : Nat) (c : Coins), ReachIn root (initCoins root) c k → oneCoinEach root c →
        r.val ≤ (k : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (root : Tree) (n : Nat)
    (hne : root ≠ Tree.Null) (hsize : size root = n) (h1 : 1 ≤ n) (h100 : n ≤ 100)
    (hbounded : valuesBounded root n) (hsum : csum root = (n : Int)), ∀ r : Std.I64, Aegis.DistributeCoins.distribute_coins root = ok r →
      ∀ (k : Nat) (c : Coins), ReachIn root (initCoins root) c k → oneCoinEach root c →
        r.val ≤ (k : Int)) := by
  sorry

end AegisSpec.DistributeCoins
