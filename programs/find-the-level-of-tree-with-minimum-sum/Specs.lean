import Aegis.MinimumLevel.Code.Funs

/-!
# Specifications of `Aegis.MinimumLevel.minimum_level`

LeetCode problem `find-the-level-of-tree-with-minimum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumLevel

open Aegis.MinimumLevel (Tree)

def nodeCount : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + nodeCount l + nodeCount r

def boundedValues : Tree → Prop
  | .Null => True
  | .Node v l r => 1 ≤ v.val ∧ v.val ≤ 1000000000 ∧ boundedValues l ∧ boundedValues r

def height : Tree → Nat
  | .Null => 0
  | .Node _ l r => 1 + max (height l) (height r)

def levelSum : Tree → Nat → ℤ
  | .Null, _ => 0
  | .Node _ _ _, 0 => 0
  | .Node v _ _, 1 => v.val
  | .Node _ l r, (k + 2) => levelSum l (k + 1) + levelSum r (k + 1)

def SameUpToSwap : Tree → Tree → Prop
  | .Null, .Null => True
  | .Null, .Node _ _ _ => False
  | .Node _ _ _, .Null => False
  | .Node v l r, .Node v' l' r' =>
      v.val = v'.val ∧
        ((SameUpToSwap l l' ∧ SameUpToSwap r r') ∨
         (SameUpToSwap l r' ∧ SameUpToSwap r l'))

/-- Let height(root) be the largest level index of any node, with the root at level 1, and for 1 <= k <= height(root) let S(root,k) be the sum of the values of all nodes at level k. Whenever minimum_level(root) returns a result r, r is the unique level index such that 1 <= r <= height(root), S(root,r) is the minimum of S(root,k) over all 1 <= k <= height(root), and r is the smallest level index attaining that minimum; equivalently, for every k with 1 <= k <= height(root), S(root,r) <= S(root,k), and for every k with 1 <= k < r, S(root,k) > S(root,r).
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_1 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (height root : ℤ) ∧
          (∀ k : Nat, 1 ≤ k → k ≤ height root → levelSum root r.val.toNat ≤ levelSum root k) ∧
          (∀ k : Nat, 1 ≤ k → k < r.val.toNat → levelSum root r.val.toNat < levelSum root k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000), ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (height root : ℤ) ∧
          (∀ k : Nat, 1 ≤ k → k ≤ height root → levelSum root r.val.toNat ≤ levelSum root k) ∧
          (∀ k : Nat, 1 ≤ k → k < r.val.toNat → levelSum root r.val.toNat < levelSum root k)) := by
  sorry

/-- minimum_level(root) returns a result; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_2 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000) :
    ∃ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000), ∃ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r) := by
  sorry

/-- Whenever minimum_level(root) returns a result r, 1 <= r <= height(root), where height(root) is the largest level index containing a node. In particular, the returned level actually exists and contains at least one node.
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_3 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (height root : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000), ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (height root : ℤ)) := by
  sorry

/-- Whenever minimum_level(root) returns a result r, r = 1.
  Preconditions: root = Node(v, Null, Null) for some integer v with 1 <= v <= 10^9. -/
theorem spec_4 (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level (Tree.Node v Tree.Null Tree.Null) = ok r → r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (v : Std.I64) (hv1 : 1 ≤ v.val) (hv2 : v.val ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level (Tree.Node v Tree.Null Tree.Null) = ok r → r.val = 1) := by
  sorry

/-- Let S1 = S(root,1) and S2 = S(root,2). Whenever minimum_level(root) returns a result r, r = 1 if S1 <= S2, and r = 2 if S2 < S1.
  Preconditions: root is a Tree satisfying the problem constraints and height(root) = 2. -/
theorem spec_5 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hheight : height root = 2) :
    ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        (levelSum root 1 ≤ levelSum root 2 → r.val = 1) ∧
          (levelSum root 2 < levelSum root 1 → r.val = 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hheight : height root = 2), ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        (levelSum root 1 ≤ levelSum root 2 → r.val = 1) ∧
          (levelSum root 2 < levelSum root 1 → r.val = 2)) := by
  sorry

/-- If S(root,1) <= S(root,k) for every k with 1 <= k <= height(root), then whenever minimum_level(root) returns a result r, r = 1.
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_6 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hmin : ∀ k : Nat, 1 ≤ k → k ≤ height root → levelSum root 1 ≤ levelSum root k) :
    ∀ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hmin : ∀ k : Nat, 1 ≤ k → k ≤ height root → levelSum root 1 ≤ levelSum root k), ∀ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r → r.val = 1) := by
  sorry

/-- If there is a level m with 1 <= m <= height(root) such that S(root,m) < S(root,k) for every k with 1 <= k <= height(root) and k != m, then whenever minimum_level(root) returns a result r, r = m.
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_7 (root : Tree) (m : Nat)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hm1 : 1 ≤ m) (hm2 : m ≤ height root)
    (hmin : ∀ k : Nat, 1 ≤ k → k ≤ height root → k ≠ m → levelSum root m < levelSum root k) :
    ∀ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r → r.val = (m : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (m : Nat)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hm1 : 1 ≤ m) (hm2 : m ≤ height root)
    (hmin : ∀ k : Nat, 1 ≤ k → k ≤ height root → k ≠ m → levelSum root m < levelSum root k), ∀ r : Std.I64, Aegis.MinimumLevel.minimum_level root = ok r → r.val = (m : ℤ)) := by
  sorry

/-- Whenever minimum_level(root) returns r and minimum_level(root') returns r', we have r = r'.
  Preconditions: root and root' are Trees satisfying the problem constraints, and root' is obtained from root by arbitrarily swapping the left and right children of any nodes. -/
theorem spec_8 (root root' : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hne' : 1 ≤ nodeCount root') (hval' : boundedValues root')
    (hsize' : nodeCount root' ≤ 100000)
    (hswap : SameUpToSwap root root') :
    ∀ r r' : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        Aegis.MinimumLevel.minimum_level root' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root root' : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000)
    (hne' : 1 ≤ nodeCount root') (hval' : boundedValues root')
    (hsize' : nodeCount root' ≤ 100000)
    (hswap : SameUpToSwap root root'), ∀ r r' : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        Aegis.MinimumLevel.minimum_level root' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever minimum_level(root) returns a result r, 1 <= r <= n, where n is the number of nodes of root; in particular 1 <= r <= 10^5, so the returned Std.I64 value is small and positive.
  Preconditions: root is a Tree satisfying the problem constraints: it contains at least one node, every node value v satisfies 1 <= v <= 10^9, and the total number of nodes is at most 10^5. -/
theorem spec_9 (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ) ∧ r.val ≤ 100000 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree)
    (hne : 1 ≤ nodeCount root) (hval : boundedValues root) (hsize : nodeCount root ≤ 100000), ∀ r : Std.I64,
      Aegis.MinimumLevel.minimum_level root = ok r →
        1 ≤ r.val ∧ r.val ≤ (nodeCount root : ℤ) ∧ r.val ≤ 100000) := by
  sorry

end AegisSpec.MinimumLevel
