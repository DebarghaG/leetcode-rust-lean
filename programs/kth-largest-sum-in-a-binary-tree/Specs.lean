import Aegis.KthLargestLevelSum.Code.Funs

/-!
# Specifications of `Aegis.KthLargestLevelSum.kth_largest_level_sum`

LeetCode problem `kth-largest-sum-in-a-binary-tree`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.KthLargestLevelSum

namespace AegisSpec.KthLargestLevelSum

def addLists : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | xs, [] => xs
  | a :: xs, b :: bs => (a + b) :: addLists xs bs

def levelSumsWith (f : ℤ → ℤ) : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => f v.val :: addLists (levelSumsWith f l) (levelSumsWith f r)

def levelSums (t : Tree) : List ℤ := levelSumsWith (fun x => x) t

def levelSum (t : Tree) (d : ℕ) : ℤ := (levelSums t).getD d 0

def numLevels (t : Tree) : ℕ := (levelSums t).length

def absLevelSums (t : Tree) : List ℤ := levelSumsWith (fun x => |x|) t

def absLevelSum (t : Tree) (d : ℕ) : ℤ := (absLevelSums t).getD d 0

def AbsLevelBound (t : Tree) : Prop := ∀ d : ℕ, d < numLevels t → absLevelSum t d ≤ 2 ^ 63 - 1

def nodeCount : Tree → ℕ
  | Tree.Null => 0
  | Tree.Node _ l r => 1 + nodeCount l + nodeCount r

def nodeValues : Tree → List ℤ
  | Tree.Null => []
  | Tree.Node v l r => v.val :: (nodeValues l ++ nodeValues r)

def mirrorTree : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node v (mirrorTree r) (mirrorTree l)

def IsNonIncreasing (l : List ℤ) : Prop := l.Pairwise (fun a b => b ≤ a)

def IsKthLargest (t : Tree) (k : ℕ) (r : ℤ) : Prop :=
  ∃ T : List ℤ, T.Perm (levelSums t) ∧ IsNonIncreasing T ∧ T[k - 1]? = some r

def countAbove (r : ℤ) : List ℤ → ℕ
  | [] => 0
  | s :: ss => (if r < s then 1 else 0) + countAbove r ss

def countAtLeast (r : ℤ) : List ℤ → ℕ
  | [] => 0
  | s :: ss => (if r ≤ s then 1 else 0) + countAtLeast r ss

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldr max x

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldr min x

abbrev i64Range (x : ℤ) : Prop :=
  IScalar.cMin IScalarTy.I64 ≤ x ∧ x ≤ IScalar.cMax IScalarTy.I64

def scaleVal (c : ℤ) (v : Std.I64) : Std.I64 :=
  if h : i64Range (c * v.val) then IScalar.ofInt (c * v.val) h else v

def scaleTree (c : ℤ) : Tree → Tree
  | Tree.Null => Tree.Null
  | Tree.Node v l r => Tree.Node (scaleVal c v) (scaleTree c l) (scaleTree c r)

/-- Let H be the number of non-empty depths in root, and for 0 <= d < H let S_d be the sum of the values of all nodes at depth d. The function returns Result.ok r, where: if k > H then r = -1; if 1 <= k <= H then r is the k-th largest element of the multiset {S_d | 0 <= d < H}, with duplicates counted (equivalently, if T_0 >= T_1 >= ... >= T_{H-1} is the non-increasing ordering of this multiset, then r = T_{k-1}).
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node (root has depth 0, children have depth one greater), the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1. -/
theorem spec_1 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ((numLevels root : ℤ) < k.val → r.val = -1) ∧
      (k.val ≤ (numLevels root : ℤ) → IsKthLargest root k.val.toNat r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ((numLevels root : ℤ) < k.val → r.val = -1) ∧
      (k.val ≤ (numLevels root : ℤ) → IsKthLargest root k.val.toNat r.val)) := by
  sorry

/-- The function returns a result Result.ok r for some i64 value r; it does not fail by arithmetic overflow, panic, or out-of-bounds access.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1. -/
theorem spec_2 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r) := by
  sorry

/-- Let S_d be the sum of node values at depth d, for 0 <= d < H. The function returns Result.ok r, and min_{0 <= d < H} S_d <= r <= max_{0 <= d < H} S_d.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; let H be the number of non-empty depths in root; k <= H. -/
theorem spec_3 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      listMin (levelSums root) ≤ r.val ∧
      r.val ≤ listMax (levelSums root) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      listMin (levelSums root) ≤ r.val ∧
      r.val ≤ listMax (levelSums root)) := by
  sorry

/-- Let S_d be the sum of node values at depth d, for 0 <= d < H. The function returns Result.ok r, and there exists an integer d with 0 <= d < H such that r = S_d.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; let H be the number of non-empty depths in root; k <= H. -/
theorem spec_4 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ∃ d : ℕ, d < numLevels root ∧ levelSum root d = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ∃ d : ℕ, d < numLevels root ∧ levelSum root d = r.val) := by
  sorry

/-- Let S_d be the sum of node values at depth d, for 0 <= d < H. The function returns Result.ok r, and the number of depths d with 0 <= d < H and S_d > r is at most k - 1.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; let H be the number of non-empty depths in root; k <= H. -/
theorem spec_5 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ((countAbove r.val (levelSums root) : ℤ) ≤ k.val - 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      ((countAbove r.val (levelSums root) : ℤ) ≤ k.val - 1)) := by
  sorry

/-- Let S_d be the sum of node values at depth d, for 0 <= d < H. The function returns Result.ok r, and the number of depths d with 0 <= d < H and S_d >= r is at least k.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; 1 <= k <= n; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; let H be the number of non-empty depths in root; k <= H. -/
theorem spec_6 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      (k.val ≤ (countAtLeast r.val (levelSums root) : ℤ)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hkH : k.val ≤ (numLevels root : ℤ)), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      (k.val ≤ (countAtLeast r.val (levelSums root) : ℤ))) := by
  sorry

/-- Let r1 be the Result.ok value returned for kth_largest_level_sum(root, k1) and let r2 be the Result.ok value returned for kth_largest_level_sum(root, k2). Then r1 >= r2.
  Preconditions: root is not Tree.Null; n(root) <= 10^5; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; k1 and k2 are integers with 1 <= k1 <= k2 <= H(root), where H(root) is the number of non-empty depths in root. -/
theorem spec_7 (root : Tree) (k1 k2 : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (numLevels root : ℤ)) :
    ∀ r1 r2 : Std.I64, kth_largest_level_sum root k1 = ok r1 →
      kth_largest_level_sum root k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (root : Tree) (k1 k2 : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (numLevels root : ℤ)), ∀ r1 r2 : Std.I64, kth_largest_level_sum root k1 = ok r1 →
      kth_largest_level_sum root k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Let mirror(root) be the tree obtained from root by recursively swapping the left and right child of every node, with Null unchanged. Let r be the Result.ok value returned for (root, k) and let r' be the Result.ok value returned for (mirror(root), k). Then r = r'.
  Preconditions: root is not Tree.Null; n(root) <= 10^5; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; 1 <= k <= n(root). -/
theorem spec_8 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)) :
    ∀ r r' : Std.I64, kth_largest_level_sum root k = ok r →
      kth_largest_level_sum (mirrorTree root) k = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)), ∀ r r' : Std.I64, kth_largest_level_sum root k = ok r →
      kth_largest_level_sum (mirrorTree root) k = ok r' → r = r') := by
  sorry

/-- Let H be the number of non-empty depths in root, which equals the number of non-empty depths in c*root. If k > H, the function returns Result.ok (-1) for both root and c*root. If k <= H, the function returns Result.ok r for (root, k) and Result.ok r_c for (c*root, k), and r_c = c * r.
  Preconditions: root is not Tree.Null; n(root) <= 10^5; for every depth d that contains at least one node in root, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; 1 <= k <= n(root); c is a nonnegative integer; the tree c*root, obtained by replacing every node value v by c*v, has all node values in the i64 range and satisfies, for every depth d that contains at least one node in c*root, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1. -/
theorem spec_9 (root : Tree) (k : Std.I64) (c : ℤ)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hc : 0 ≤ c)
    (hrange : ∀ v ∈ nodeValues root, i64Range (c * v))
    (hcbound : AbsLevelBound (scaleTree c root)) :
    (((numLevels root : ℤ) < k.val) →
        ∃ r rc : Std.I64, kth_largest_level_sum root k = ok r ∧ r.val = -1 ∧
          kth_largest_level_sum (scaleTree c root) k = ok rc ∧ rc.val = -1) ∧
      (k.val ≤ (numLevels root : ℤ) →
        ∃ r rc : Std.I64, kth_largest_level_sum root k = ok r ∧
          kth_largest_level_sum (scaleTree c root) k = ok rc ∧ rc.val = c * r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (c : ℤ)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hc : 0 ≤ c)
    (hrange : ∀ v ∈ nodeValues root, i64Range (c * v))
    (hcbound : AbsLevelBound (scaleTree c root)), (((numLevels root : ℤ) < k.val) →
        ∃ r rc : Std.I64, kth_largest_level_sum root k = ok r ∧ r.val = -1 ∧
          kth_largest_level_sum (scaleTree c root) k = ok rc ∧ rc.val = -1) ∧
      (k.val ≤ (numLevels root : ℤ) →
        ∃ r rc : Std.I64, kth_largest_level_sum root k = ok r ∧
          kth_largest_level_sum (scaleTree c root) k = ok rc ∧ rc.val = c * r.val)) := by
  sorry

/-- The function returns Result.ok r, and if k <= H then r = C; if k > H then r = -1.
  Preconditions: root is not Tree.Null; let n be the number of nodes in root; n <= 10^5; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; 1 <= k <= n; let H be the number of non-empty depths in root; there exists an integer C such that for every depth d with 0 <= d < H, the sum S_d of values of nodes at depth d equals C. -/
theorem spec_10 (root : Tree) (k : Std.I64) (C : ℤ)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hC : ∀ d : ℕ, d < numLevels root → levelSum root d = C) :
    ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      (k.val ≤ (numLevels root : ℤ) → r.val = C) ∧
      ((numLevels root : ℤ) < k.val → r.val = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (root : Tree) (k : Std.I64) (C : ℤ)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ))
    (hC : ∀ d : ℕ, d < numLevels root → levelSum root d = C), ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧
      (k.val ≤ (numLevels root : ℤ) → r.val = C) ∧
      ((numLevels root : ℤ) < k.val → r.val = -1)) := by
  sorry

/-- Let H be the number of non-empty depths in root. If k <= H then the function returns Result.ok r with r >= 0; if k > H then the function returns Result.ok (-1).
  Preconditions: root is not Tree.Null; n(root) <= 10^5; for every depth d that contains at least one node, the sum of |value(v)| over all nodes v at depth d is at most 2^63 - 1; every node value in root is nonnegative; 1 <= k <= n(root). -/
theorem spec_11 (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hnonneg : ∀ v ∈ nodeValues root, 0 ≤ v)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)) :
    (k.val ≤ (numLevels root : ℤ) →
        ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧ 0 ≤ r.val) ∧
      ((numLevels root : ℤ) < k.val →
        ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧ r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (root : Tree) (k : Std.I64)
    (hroot : root ≠ Tree.Null) (hn : nodeCount root ≤ 10 ^ 5)
    (hbound : AbsLevelBound root)
    (hnonneg : ∀ v ∈ nodeValues root, 0 ≤ v)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (nodeCount root : ℤ)), (k.val ≤ (numLevels root : ℤ) →
        ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧ 0 ≤ r.val) ∧
      ((numLevels root : ℤ) < k.val →
        ∃ r : Std.I64, kth_largest_level_sum root k = ok r ∧ r.val = -1)) := by
  sorry

/-- Let r1 be the Result.ok value returned for (T1, k) and let r2 be the Result.ok value returned for (T2, k). Then r1 = r2.
  Preconditions: T1 and T2 are non-null trees; each has at most 10^5 nodes; for each tree and each depth d containing a node, the sum of |value(v)| over nodes at depth d is at most 2^63 - 1; H(T1) = H(T2) = H, where H(T) is the number of non-empty depths in T; for every d with 0 <= d < H, the sum of node values at depth d in T1 equals the corresponding sum at depth d in T2; k is an integer with 1 <= k <= min(n(T1), n(T2)). -/
theorem spec_12 (T1 T2 : Tree) (k : Std.I64) (H : ℕ)
    (hnull1 : T1 ≠ Tree.Null) (hnull2 : T2 ≠ Tree.Null)
    (hn1 : nodeCount T1 ≤ 10 ^ 5) (hn2 : nodeCount T2 ≤ 10 ^ 5)
    (hbound1 : AbsLevelBound T1) (hbound2 : AbsLevelBound T2)
    (hH1 : numLevels T1 = H) (hH2 : numLevels T2 = H)
    (hsame : ∀ d : ℕ, d < H → levelSum T1 d = levelSum T2 d)
    (hk1 : 1 ≤ k.val)
    (hkn : k.val ≤ ((min (nodeCount T1) (nodeCount T2) : ℕ) : ℤ)) :
    ∀ r1 r2 : Std.I64, kth_largest_level_sum T1 k = ok r1 →
      kth_largest_level_sum T2 k = ok r2 → r1 = r2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (T1 T2 : Tree) (k : Std.I64) (H : ℕ)
    (hnull1 : T1 ≠ Tree.Null) (hnull2 : T2 ≠ Tree.Null)
    (hn1 : nodeCount T1 ≤ 10 ^ 5) (hn2 : nodeCount T2 ≤ 10 ^ 5)
    (hbound1 : AbsLevelBound T1) (hbound2 : AbsLevelBound T2)
    (hH1 : numLevels T1 = H) (hH2 : numLevels T2 = H)
    (hsame : ∀ d : ℕ, d < H → levelSum T1 d = levelSum T2 d)
    (hk1 : 1 ≤ k.val)
    (hkn : k.val ≤ ((min (nodeCount T1) (nodeCount T2) : ℕ) : ℤ)), ∀ r1 r2 : Std.I64, kth_largest_level_sum T1 k = ok r1 →
      kth_largest_level_sum T2 k = ok r2 → r1 = r2) := by
  sorry

end AegisSpec.KthLargestLevelSum
