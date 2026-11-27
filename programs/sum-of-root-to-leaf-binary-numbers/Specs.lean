import Aegis.SumRootToLeaf.Code.Funs

/-!
# Specifications of `Aegis.SumRootToLeaf.sum_root_to_leaf`

LeetCode problem `sum-of-root-to-leaf-binary-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SumRootToLeaf

namespace AegisSpec.SumRootToLeaf

def nodes : Tree → Nat
  | .Null => 0
  | .Node _ l r => nodes l + nodes r + 1

def valuesAreBits : Tree → Prop
  | .Null => True
  | .Node v l r => (v.val = 0 ∨ v.val = 1) ∧ valuesAreBits l ∧ valuesAreBits r

def valuesAllZeros : Tree → Prop
  | .Null => True
  | .Node v l r => v.val = 0 ∧ valuesAllZeros l ∧ valuesAllZeros r

def valuesAllOnes : Tree → Prop
  | .Null => True
  | .Node v l r => v.val = 1 ∧ valuesAllOnes l ∧ valuesAllOnes r

def paths : Tree → List (List ℤ)
  | .Null => []
  | .Node v .Null .Null => [[v.val]]
  | .Node v l r =>
    (paths l).map (fun p => v.val :: p) ++ (paths r).map (fun p => v.val :: p)

def bitsToInt : List ℤ → ℤ
  | [] => 0
  | b :: bs => b * (2:ℤ) ^ bs.length + bitsToInt bs

def ans (t : Tree) : ℤ := ((paths t).map bitsToInt).sum

def W (t : Tree) : ℤ := ((paths t).map (fun p => (2:ℤ) ^ (p.length - 1))).sum

def numLeaves (t : Tree) : Nat := (paths t).length

def allLeavesAtDepth : Tree → Nat → Prop
  | .Null, _ => True
  | .Node _ .Null .Null, d => d = 1
  | .Node _ l r, d => 1 ≤ d ∧ allLeavesAtDepth l (d - 1) ∧ allLeavesAtDepth r (d - 1)

def sumOverNodes : Tree → ℤ
  | .Null => 0
  | .Node v l r => v.val * W (.Node v l r) + sumOverNodes l + sumOverNodes r

def fitsI32 (z : ℤ) : Prop := -((2:ℤ) ^ 31) ≤ z ∧ z ≤ (2:ℤ) ^ 31 - 1

/-- For a leaf L of root, let P(L) be the integer whose binary digits are the sequence of node values on the path from the root to L, with the root value as the most significant bit; leading zeros are allowed and do not change the integer. Whenever sum_root_to_leaf(root) returns a result r, r equals the sum of P(L) over all leaves L of root, where a leaf is a node whose left and right children are both Null.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical sum defined in the statement is between 0 and 2^31 - 1. -/
theorem spec_1 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : 0 ≤ ans root ∧ ans root ≤ (2:ℤ) ^ 31 - 1)
    (hret : sum_root_to_leaf root = ok r) :
    r.val = ans root := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : 0 ≤ ans root ∧ ans root ≤ (2:ℤ) ^ 31 - 1)
    (hret : sum_root_to_leaf root = ok r), r.val = ans root) := by
  sorry

/-- sum_root_to_leaf(root) returns a result r; it does not fail.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical sum of the root-to-leaf binary numbers of root is between 0 and 2^31 - 1. -/
theorem spec_2 (root : Tree)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : 0 ≤ ans root ∧ ans root ≤ (2:ℤ) ^ 31 - 1) :
    ∃ r : Std.I64, sum_root_to_leaf root = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : 0 ≤ ans root ∧ ans root ≤ (2:ℤ) ^ 31 - 1), ∃ r : Std.I64, sum_root_to_leaf root = ok r) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, 0 <= r.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_3 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), 0 ≤ r.val) := by
  sorry

/-- Let n be the number of nodes of root. Whenever sum_root_to_leaf(root) returns a result r, r <= n * (2^n - 1).
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_4 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val ≤ (nodes root : ℤ) * ((2:ℤ) ^ nodes root - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val ≤ (nodes root : ℤ) * ((2:ℤ) ^ nodes root - 1)) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = v.
  Preconditions: root = Node(v, Null, Null) for some v with v = 0 or v = 1; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_5 (v : Std.I64) (r : Std.I64)
    (hv : v.val = 0 ∨ v.val = 1)
    (hfit : fitsI32 (ans (Tree.Node v Tree.Null Tree.Null)))
    (hret : sum_root_to_leaf (Tree.Node v Tree.Null Tree.Null) = ok r) :
    r.val = v.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (v : Std.I64) (r : Std.I64)
    (hv : v.val = 0 ∨ v.val = 1)
    (hfit : fitsI32 (ans (Tree.Node v Tree.Null Tree.Null)))
    (hret : sum_root_to_leaf (Tree.Node v Tree.Null Tree.Null) = ok r), r.val = v.val) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = 0.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_6 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hzero : valuesAllZeros root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hzero : valuesAllZeros root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val = 0) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = m * (2^d - 1).
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 1; there is an integer d >= 1 such that every leaf of root has exactly d nodes on its path from the root; let m be the number of leaves; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_7 (root : Tree) (r : Std.I64) (d : Nat)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hone : valuesAllOnes root)
    (hd : 1 ≤ d)
    (hdepth : allLeavesAtDepth root d)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val = (numLeaves root : ℤ) * ((2:ℤ) ^ d - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (r : Std.I64) (d : Nat)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hone : valuesAllOnes root)
    (hd : 1 ≤ d)
    (hdepth : allLeavesAtDepth root d)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val = (numLeaves root : ℤ) * ((2:ℤ) ^ d - 1)) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = sum_{i=0}^{d-1} v_i * 2^{d-1-i}.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; root has exactly one leaf L. Let v_0, ..., v_{d-1} be the sequence of node values on the unique path from the root to L, where v_0 is the root, v_{d-1} is L, and d >= 1 is the number of nodes on the path; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_8 (root : Tree) (r : Std.I64) (vs : List ℤ) (d : Nat)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hpath : paths root = [vs])
    (hd : vs.length = d)
    (hd1 : 1 ≤ d)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val = ((List.range d).map (fun i => vs.getD i 0 * (2:ℤ) ^ (d - 1 - i))).sum := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (r : Std.I64) (vs : List ℤ) (d : Nat)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hpath : paths root = [vs])
    (hd : vs.length = d)
    (hd1 : 1 ≤ d)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val = ((List.range d).map (fun i => vs.getD i 0 * (2:ℤ) ^ (d - 1 - i))).sum) := by
  sorry

/-- Define ans(Null) = 0, and for any non-empty subtree S let ans(S) be the sum over leaves M of S of the integer represented by the bits on the path from the root of S to M. Whenever sum_root_to_leaf(root) returns a result r, r = ans(L) + ans(R).
  Preconditions: root = Node(0, L, R), where L and R are Trees, possibly Null; root has between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer for root fits in a 32-bit signed integer. -/
theorem spec_9 (L R : Tree) (r : Std.I64)
    (hsize : 1 ≤ nodes (Tree.Node 0#i64 L R) ∧ nodes (Tree.Node 0#i64 L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node 0#i64 L R))
    (hfit : fitsI32 (ans (Tree.Node 0#i64 L R)))
    (hret : sum_root_to_leaf (Tree.Node 0#i64 L R) = ok r) :
    r.val = ans L + ans R := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (L R : Tree) (r : Std.I64)
    (hsize : 1 ≤ nodes (Tree.Node 0#i64 L R) ∧ nodes (Tree.Node 0#i64 L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node 0#i64 L R))
    (hfit : fitsI32 (ans (Tree.Node 0#i64 L R)))
    (hret : sum_root_to_leaf (Tree.Node 0#i64 L R) = ok r), r.val = ans L + ans R) := by
  sorry

/-- Define ans(Null) = 0 and W(Null) = 0. For any non-empty subtree S, let ans(S) be the sum over leaves M of S of the integer represented by the bits on the path from the root of S to M, and let W(S) be the sum over leaves M of S of 2^{dist(S,M)}, where dist(S,M) is the number of edges from the root of S to M. Whenever sum_root_to_leaf(root) returns a result r, r = ans(L) + ans(R) + 2 * W(L) + 2 * W(R).
  Preconditions: root = Node(1, L, R), where L and R are Trees, possibly Null, and at least one of L, R is non-Null (so the root is not a leaf); root has between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer for root fits in a 32-bit signed integer. -/
theorem spec_10 (L R : Tree) (r : Std.I64)
    (hnl : L ≠ Tree.Null ∨ R ≠ Tree.Null)
    (hsize : 1 ≤ nodes (Tree.Node 1#i64 L R) ∧ nodes (Tree.Node 1#i64 L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node 1#i64 L R))
    (hfit : fitsI32 (ans (Tree.Node 1#i64 L R)))
    (hret : sum_root_to_leaf (Tree.Node 1#i64 L R) = ok r) :
    r.val = ans L + ans R + 2 * W L + 2 * W R := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (L R : Tree) (r : Std.I64)
    (hnl : L ≠ Tree.Null ∨ R ≠ Tree.Null)
    (hsize : 1 ≤ nodes (Tree.Node 1#i64 L R) ∧ nodes (Tree.Node 1#i64 L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node 1#i64 L R))
    (hfit : fitsI32 (ans (Tree.Node 1#i64 L R)))
    (hret : sum_root_to_leaf (Tree.Node 1#i64 L R) = ok r), r.val = ans L + ans R + 2 * W L + 2 * W R) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = sum over every node u of root of value(u) * (sum over leaves L in the subtree rooted at u of 2^{dist(u,L)}), where value(u) is the 0 or 1 stored at u and dist(u,L) is the number of edges from u to L. If u is itself a leaf, the inner sum is 1 because the empty path contributes 2^0.
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_11 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val = sumOverNodes root := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val = sumOverNodes root) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = 22.
  Preconditions: root = Node(1, Node(0, Node(0, Null, Null), Node(1, Null, Null)), Node(1, Node(0, Null, Null), Node(1, Null, Null))). -/
theorem spec_12 (r : Std.I64)
    (hret : sum_root_to_leaf
      (Tree.Node 1#i64
        (Tree.Node 0#i64 (Tree.Node 0#i64 Tree.Null Tree.Null)
          (Tree.Node 1#i64 Tree.Null Tree.Null))
        (Tree.Node 1#i64 (Tree.Node 0#i64 Tree.Null Tree.Null)
          (Tree.Node 1#i64 Tree.Null Tree.Null))) = ok r) :
    r.val = 22 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (r : Std.I64)
    (hret : sum_root_to_leaf
      (Tree.Node 1#i64
        (Tree.Node 0#i64 (Tree.Node 0#i64 Tree.Null Tree.Null)
          (Tree.Node 1#i64 Tree.Null Tree.Null))
        (Tree.Node 1#i64 (Tree.Node 0#i64 Tree.Null Tree.Null)
          (Tree.Node 1#i64 Tree.Null Tree.Null))) = ok r), r.val = 22) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r = 6.
  Preconditions: root = Node(1, Node(1, Null, Null), Node(1, Null, Null)). -/
theorem spec_13 (r : Std.I64)
    (hret : sum_root_to_leaf
      (Tree.Node 1#i64 (Tree.Node 1#i64 Tree.Null Tree.Null)
        (Tree.Node 1#i64 Tree.Null Tree.Null)) = ok r) :
    r.val = 6 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (r : Std.I64)
    (hret : sum_root_to_leaf
      (Tree.Node 1#i64 (Tree.Node 1#i64 Tree.Null Tree.Null)
        (Tree.Node 1#i64 Tree.Null Tree.Null)) = ok r), r.val = 6) := by
  sorry

/-- Define ans(Null) = 0 and W(Null) = 0; for a non-empty subtree S, ans(S) is the sum over leaves M of S of the integer represented by the bits on the path from the root of S to M, and W(S) is the sum over leaves M of S of 2^{dist(S,M)} with dist counted in edges. If L and R are both Null (root is a leaf), then whenever sum_root_to_leaf(root) returns a result r, r = v. If at least one of L, R is non-Null, then whenever sum_root_to_leaf(root) returns a result r, r = ans(L) + ans(R) + 2*v*(W(L) + W(R)).
  Preconditions: root = Node(v, L, R) where v = 0 or v = 1 and L, R are Trees, possibly Null; root has between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer for root fits in a 32-bit signed integer. -/
theorem spec_14 (v : Std.I64) (L R : Tree) (r : Std.I64)
    (hv : v.val = 0 ∨ v.val = 1)
    (hsize : 1 ≤ nodes (Tree.Node v L R) ∧ nodes (Tree.Node v L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node v L R))
    (hfit : fitsI32 (ans (Tree.Node v L R)))
    (hret : sum_root_to_leaf (Tree.Node v L R) = ok r) :
    ((L = Tree.Null ∧ R = Tree.Null) → r.val = v.val) ∧
      ((L ≠ Tree.Null ∨ R ≠ Tree.Null) →
        r.val = ans L + ans R + 2 * v.val * (W L + W R)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (v : Std.I64) (L R : Tree) (r : Std.I64)
    (hv : v.val = 0 ∨ v.val = 1)
    (hsize : 1 ≤ nodes (Tree.Node v L R) ∧ nodes (Tree.Node v L R) ≤ 1000)
    (hbits : valuesAreBits (Tree.Node v L R))
    (hfit : fitsI32 (ans (Tree.Node v L R)))
    (hret : sum_root_to_leaf (Tree.Node v L R) = ok r), ((L = Tree.Null ∧ R = Tree.Null) → r.val = v.val) ∧
      ((L ≠ Tree.Null ∨ R ≠ Tree.Null) →
        r.val = ans L + ans R + 2 * v.val * (W L + W R))) := by
  sorry

/-- Whenever sum_root_to_leaf(root) returns a result r, r <= 2^31 - 1, i.e. the returned value stays within the range the problem guarantees (and hence within i64).
  Preconditions: root is a non-empty finite Tree with between 1 and 1000 nodes; every node value is 0 or 1; the mathematical answer fits in a 32-bit signed integer. -/
theorem spec_15 (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r) :
    r.val ≤ (2:ℤ) ^ 31 - 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (root : Tree) (r : Std.I64)
    (hne : root ≠ Tree.Null)
    (hsize : 1 ≤ nodes root ∧ nodes root ≤ 1000)
    (hbits : valuesAreBits root)
    (hfit : fitsI32 (ans root))
    (hret : sum_root_to_leaf root = ok r), r.val ≤ (2:ℤ) ^ 31 - 1) := by
  sorry

end AegisSpec.SumRootToLeaf
