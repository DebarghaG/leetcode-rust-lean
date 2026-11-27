import Aegis.BtreeGameWinningMove.Code.Funs

/-!
# Specifications of `Aegis.BtreeGameWinningMove.btree_game_winning_move`

LeetCode problem `binary-tree-coloring-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.BtreeGameWinningMove

namespace AegisSpec.BtreeGameWinningMove

def values : Tree → List Int
  | Tree.Null => []
  | Tree.Node v l r => values l ++ [v.val] ++ values r

def nodeCount : Tree → Nat
  | Tree.Null => 0
  | Tree.Node _ l r => nodeCount l + 1 + nodeCount r

def occurs (a : Int) (t : Tree) : Prop := a ∈ values t

def Adj : Tree → Int → Int → Prop
  | Tree.Null, _, _ => False
  | Tree.Node v l r, a, b =>
      (v.val = a ∧ (b ∈ values l ∨ b ∈ values r)) ∨
      (v.val = b ∧ (a ∈ values l ∨ a ∈ values r)) ∨
      Adj l a b ∨ Adj r a b

def connectedAvoiding (t : Tree) (z a b : Int) : Prop :=
  Relation.ReflTransGen (fun u v => Adj t u v ∧ u ≠ z ∧ v ≠ z) a b

noncomputable def componentSize (t : Tree) (z y : Int) : Nat := by
  classical
  exact ((values t).toFinset.filter (fun w => w ≠ z ∧ connectedAvoiding t z y w)).card

def childSizes : Tree → Int → Option (Nat × Nat)
  | Tree.Null, _ => none
  | Tree.Node v l r, x =>
      if v.val = x then some (nodeCount l, nodeCount r)
      else
        match childSizes l x with
        | some s => some s
        | none => childSizes r x

def leftSize (t : Tree) (x : Int) : Nat := ((childSizes t x).map (fun s => s.1)).getD 0

def rightSize (t : Tree) (x : Int) : Nat := ((childSizes t x).map (fun s => s.2)).getD 0

def parentSize (t : Tree) (n : Nat) (x : Int) : Nat := n - 1 - leftSize t x - rightSize t x

def swapAt (x : Int) : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r =>
      if v.val = x then Tree.Node v r l else Tree.Node v (swapAt x l) (swapAt x r)

def mirror : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirror r) (mirror l)

/-- The function returns a result r and r = true if and only if L > n/2 or R > n/2 or P > n/2, where L is the number of nodes in the left child subtree of the node with value x (0 if that node has no left child), R is the number of nodes in its right child subtree (0 if it has no right child), and P = n - 1 - L - R. Equivalently, since n is odd, r = true if and only if 2*L > n or 2*R > n or 2*P > n.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_1 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∃ r : Bool,
      btree_game_winning_move root n x = ok r ∧
        (r = true ↔
          (leftSize root x.val > n.val.toNat / 2 ∨
            rightSize root x.val > n.val.toNat / 2 ∨
            parentSize root n.val.toNat x.val > n.val.toNat / 2)) ∧
        (r = true ↔
          (2 * leftSize root x.val > n.val.toNat ∨
            2 * rightSize root x.val > n.val.toNat ∨
            2 * parentSize root n.val.toNat x.val > n.val.toNat)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∃ r : Bool,
      btree_game_winning_move root n x = ok r ∧
        (r = true ↔
          (leftSize root x.val > n.val.toNat / 2 ∨
            rightSize root x.val > n.val.toNat / 2 ∨
            parentSize root n.val.toNat x.val > n.val.toNat / 2)) ∧
        (r = true ↔
          (2 * leftSize root x.val > n.val.toNat ∨
            2 * rightSize root x.val > n.val.toNat ∨
            2 * parentSize root n.val.toNat x.val > n.val.toNat))) := by
  sorry

/-- The function returns a result r (a Bool) and does not fail for every input satisfying the preconditions.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_2 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∃ r : Bool, btree_game_winning_move root n x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∃ r : Bool, btree_game_winning_move root n x = ok r) := by
  sorry

/-- Whenever the function returns true, max(L, R, P) >= (n+1)/2, where L is the number of nodes in the left child subtree of the node with value x, R is the number of nodes in its right child subtree, and P = n - 1 - L - R.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_3 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = true →
        max (leftSize root x.val)
            (max (rightSize root x.val) (parentSize root n.val.toNat x.val)) ≥
          (n.val.toNat + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = true →
        max (leftSize root x.val)
            (max (rightSize root x.val) (parentSize root n.val.toNat x.val)) ≥
          (n.val.toNat + 1) / 2) := by
  sorry

/-- Whenever the function returns false, max(L, R, P) <= (n-1)/2, where L is the number of nodes in the left child subtree of the node with value x, R is the number of nodes in its right child subtree, and P = n - 1 - L - R.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_4 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = false →
        max (leftSize root x.val)
            (max (rightSize root x.val) (parentSize root n.val.toNat x.val)) ≤
          (n.val.toNat - 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = false →
        max (leftSize root x.val)
            (max (rightSize root x.val) (parentSize root n.val.toNat x.val)) ≤
          (n.val.toNat - 1) / 2) := by
  sorry

/-- Whenever the function returns true, there exists a node y in root with value y != x such that y is adjacent to the node with value x and the connected component containing y after deleting the node with value x from the tree has size > n/2.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_5 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = true →
        ∃ y : Std.I64,
          occurs y.val root ∧ y.val ≠ x.val ∧ Adj root x.val y.val ∧
            componentSize root x.val y.val > n.val.toNat / 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∀ r : Bool,
      btree_game_winning_move root n x = ok r → r = true →
        ∃ y : Std.I64,
          occurs y.val root ∧ y.val ≠ x.val ∧ Adj root x.val y.val ∧
            componentSize root x.val y.val > n.val.toNat / 2) := by
  sorry

/-- If the node with value x has a neighbor y such that the connected component containing y after deleting the node with value x from the tree has size > n/2, then the function returns a result r and r = true.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_6 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    (∃ y : Std.I64,
        occurs y.val root ∧ y.val ≠ x.val ∧ Adj root x.val y.val ∧
          componentSize root x.val y.val > n.val.toNat / 2) →
      ∃ r : Bool, btree_game_winning_move root n x = ok r ∧ r = true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), (∃ y : Std.I64,
        occurs y.val root ∧ y.val ≠ x.val ∧ Adj root x.val y.val ∧
          componentSize root x.val y.val > n.val.toNat / 2) →
      ∃ r : Bool, btree_game_winning_move root n x = ok r ∧ r = true) := by
  sorry

/-- Let root' be the tree obtained from root by swapping the left and right child subtrees of the node with value x, leaving all other nodes and values unchanged. Then both calls btree_game_winning_move(root, n, x) and btree_game_winning_move(root', n, x) return results, and the returned Bools are equal.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_7 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∃ r r' : Bool,
      btree_game_winning_move root n x = ok r ∧
        btree_game_winning_move (swapAt x.val root) n x = ok r' ∧ r = r' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∃ r r' : Bool,
      btree_game_winning_move root n x = ok r ∧
        btree_game_winning_move (swapAt x.val root) n x = ok r' ∧ r = r') := by
  sorry

/-- Let root' be the mirror image of root, defined by recursively swapping the left and right child of every node. Then both calls btree_game_winning_move(root, n, x) and btree_game_winning_move(root', n, x) return results, and the returned Bools are equal.
  Preconditions: root is a binary tree with exactly n nodes; n is odd and 1 <= n <= 100; the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in root. -/
theorem spec_8 (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    ∃ r r' : Bool,
      btree_game_winning_move root n x = ok r ∧
        btree_game_winning_move (mirror root) n x = ok r' ∧ r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (n x : Std.I64)
    (hsize : nodeCount root = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup : (values root).Nodup)
    (hvalues : ∀ a : Int, a ∈ values root ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), ∃ r r' : Bool,
      btree_game_winning_move root n x = ok r ∧
        btree_game_winning_move (mirror root) n x = ok r' ∧ r = r') := by
  sorry

/-- If the node with value x has left-subtree size L and right-subtree size R in both root1 and root2, then both calls btree_game_winning_move(root1, n, x) and btree_game_winning_move(root2, n, x) return results, and the returned Bools are equal.
  Preconditions: root1 and root2 are binary trees, each with exactly n nodes; n is odd and 1 <= n <= 100; in each tree the node values are pairwise distinct and are exactly the integers 1,2,...,n; 1 <= x <= n, so the node whose value is x exists in each tree. -/
theorem spec_9 (root1 root2 : Tree) (n x : Std.I64)
    (hsize1 : nodeCount root1 = n.val.toNat)
    (hsize2 : nodeCount root2 = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup1 : (values root1).Nodup)
    (hvalues1 : ∀ a : Int, a ∈ values root1 ↔ 1 ≤ a ∧ a ≤ n.val)
    (hnodup2 : (values root2).Nodup)
    (hvalues2 : ∀ a : Int, a ∈ values root2 ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val) :
    leftSize root1 x.val = leftSize root2 x.val →
      rightSize root1 x.val = rightSize root2 x.val →
        ∃ r1 r2 : Bool,
          btree_game_winning_move root1 n x = ok r1 ∧
            btree_game_winning_move root2 n x = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root1 root2 : Tree) (n x : Std.I64)
    (hsize1 : nodeCount root1 = n.val.toNat)
    (hsize2 : nodeCount root2 = n.val.toNat)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100) (hn_odd : Odd n.val)
    (hnodup1 : (values root1).Nodup)
    (hvalues1 : ∀ a : Int, a ∈ values root1 ↔ 1 ≤ a ∧ a ≤ n.val)
    (hnodup2 : (values root2).Nodup)
    (hvalues2 : ∀ a : Int, a ∈ values root2 ↔ 1 ≤ a ∧ a ≤ n.val)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ n.val), leftSize root1 x.val = leftSize root2 x.val →
      rightSize root1 x.val = rightSize root2 x.val →
        ∃ r1 r2 : Bool,
          btree_game_winning_move root1 n x = ok r1 ∧
            btree_game_winning_move root2 n x = ok r2 ∧ r1 = r2) := by
  sorry

end AegisSpec.BtreeGameWinningMove
