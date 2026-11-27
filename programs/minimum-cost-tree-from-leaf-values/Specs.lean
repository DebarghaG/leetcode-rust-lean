import Aegis.MctFromLeafValues.Code.Funs

/-!
# Specifications of `Aegis.MctFromLeafValues.mct_from_leaf_values`

LeetCode problem `minimum-cost-tree-from-leaf-values`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MctFromLeafValues

open Aegis.MctFromLeafValues (mct_from_leaf_values)

def vals (arr : Slice I64) : List ℤ := arr.val.map (fun x => x.val)

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl max x

def adjacentSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => match xs with
    | [] => 0
    | y :: _ => x * y + adjacentSum xs

def rightCombSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => match xs with
    | [] => 0
    | _ => x * listMax xs + rightCombSum xs

def leftCombSumAux (m : ℤ) : List ℤ → ℤ
  | [] => 0
  | x :: xs => m * x + leftCombSumAux (max m x) xs

def leftCombSum : List ℤ → ℤ
  | [] => 0
  | x :: xs => leftCombSumAux x xs

inductive MctTree where
  | leaf : ℤ → MctTree
  | node : MctTree → MctTree → MctTree

namespace MctTree

def leaves : MctTree → List ℤ
  | leaf x => [x]
  | node l r => leaves l ++ leaves r

def maxLeaf : MctTree → ℤ
  | leaf x => x
  | node l r => max (maxLeaf l) (maxLeaf r)

def nodeSum : MctTree → ℤ
  | leaf _ => 0
  | node l r => nodeSum l + nodeSum r + maxLeaf l * maxLeaf r

def rightComb : List ℤ → MctTree
  | [] => leaf 0
  | x :: xs => match xs with
    | [] => leaf x
    | _ => node (leaf x) (rightComb xs)

def leftCombAux : MctTree → List ℤ → MctTree
  | acc, [] => acc
  | acc, x :: xs => leftCombAux (node acc (leaf x)) xs

def leftComb : List ℤ → MctTree
  | [] => leaf 0
  | x :: xs => leftCombAux (leaf x) xs

end MctTree

def IsValidFor (t : MctTree) (arr : Slice I64) : Prop := t.leaves = vals arr

def IsRightComb (t : MctTree) : Prop := t = MctTree.rightComb t.leaves

def IsLeftComb (t : MctTree) : Prop := t = MctTree.leftComb t.leaves

def costSet (arr : Slice I64) : Set ℤ := {c : ℤ | ∃ t : MctTree, IsValidFor t arr ∧ t.nodeSum = c}

def IsAns (arr : Slice I64) (c : ℤ) : Prop := IsLeast (costSet arr) c

/-- The function returns a result r, and r = ans(arr), where ans(arr) is defined as follows. A valid tree for arr is a finite rooted ordered binary tree in which every node has either 0 or 2 children, whose leaves, read in in-order, have values arr[0], arr[1], ..., arr[n-1], and in which every internal (non-leaf) node has value (max of the leaf values in its left subtree) * (max of the leaf values in its right subtree). For such a tree T, let C(T) be the sum of the values of all internal nodes of T (leaves are not summed). Then ans(arr) = min { C(T) : T is a valid tree for arr }. Thus r is the smallest possible sum of non-leaf node values over all such trees.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. (The problem's guarantee that the answer fits in a 32-bit signed integer is automatic from these bounds.) -/
theorem spec_1 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    ∃ r : I64, mct_from_leaf_values arr = ok r ∧ IsAns arr r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), ∃ r : I64, mct_from_leaf_values arr = ok r ∧ IsAns arr r.val) := by
  sorry

/-- The function returns a result r for arr; it does not panic, fail, or overflow at any point.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_2 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    ∃ r : I64, mct_from_leaf_values arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), ∃ r : I64, mct_from_leaf_values arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= (n-1) * m * m, where n = len(arr) and m = min { arr[i] : 0 <= i < n }.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_3 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    ∀ r : I64, mct_from_leaf_values arr = ok r →
      ((n : ℤ) - 1) * listMin (vals arr) * listMin (vals arr) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), ∀ r : I64, mct_from_leaf_values arr = ok r →
      ((n : ℤ) - 1) * listMin (vals arr) * listMin (vals arr) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= (n-1) * M * M, where n = len(arr) and M = max { arr[i] : 0 <= i < n }.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_4 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    ∀ r : I64, mct_from_leaf_values arr = ok r →
      r.val ≤ ((n : ℤ) - 1) * listMax (vals arr) * listMax (vals arr) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), ∀ r : I64, mct_from_leaf_values arr = ok r →
      r.val ≤ ((n : ℤ) - 1) * listMax (vals arr) * listMax (vals arr)) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{n-2} arr[i] * arr[i+1].
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_5 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    ∀ r : I64, mct_from_leaf_values arr = ok r → adjacentSum (vals arr) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), ∀ r : I64, mct_from_leaf_values arr = ok r → adjacentSum (vals arr) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = arr[0] * arr[1].
  Preconditions: arr is a slice of i64 with n = len(arr), n = 2, and 1 <= arr[i] <= 15 for i = 0,1. -/
theorem spec_6 (arr : Slice I64) (a b : I64) (harr : arr.val = [a, b])
    (ha1 : 1 ≤ a.val) (ha15 : a.val ≤ 15) (hb1 : 1 ≤ b.val) (hb15 : b.val ≤ 15) :
    ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = a.val * b.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice I64) (a b : I64) (harr : arr.val = [a, b])
    (ha1 : 1 ≤ a.val) (ha15 : a.val ≤ 15) (hb1 : 1 ≤ b.val) (hb15 : b.val ≤ 15), ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = a.val * b.val) := by
  sorry

/-- Whenever the function returns a result r, r = min( arr[1]*arr[2] + arr[0]*max(arr[1], arr[2]), arr[0]*arr[1] + max(arr[0], arr[1])*arr[2] ).
  Preconditions: arr is a slice of i64 with n = len(arr), n = 3, and 1 <= arr[i] <= 15 for i = 0,1,2. -/
theorem spec_7 (arr : Slice I64) (a0 a1 a2 : I64) (harr : arr.val = [a0, a1, a2])
    (h01 : 1 ≤ a0.val) (h015 : a0.val ≤ 15) (h11 : 1 ≤ a1.val) (h115 : a1.val ≤ 15)
    (h21 : 1 ≤ a2.val) (h215 : a2.val ≤ 15) :
    ∀ r : I64, mct_from_leaf_values arr = ok r →
      r.val = min (a1.val * a2.val + a0.val * max a1.val a2.val)
        (a0.val * a1.val + max a0.val a1.val * a2.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice I64) (a0 a1 a2 : I64) (harr : arr.val = [a0, a1, a2])
    (h01 : 1 ≤ a0.val) (h015 : a0.val ≤ 15) (h11 : 1 ≤ a1.val) (h115 : a1.val ≤ 15)
    (h21 : 1 ≤ a2.val) (h215 : a2.val ≤ 15), ∀ r : I64, mct_from_leaf_values arr = ok r →
      r.val = min (a1.val * a2.val + a0.val * max a1.val a2.val)
        (a0.val * a1.val + max a0.val a1.val * a2.val)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-2} arr[i] * arr[i+1].
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i. Also arr is monotone: either arr[0] <= arr[1] <= ... <= arr[n-1], or arr[0] >= arr[1] >= ... >= arr[n-1]. -/
theorem spec_8 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hmono : (vals arr).Pairwise (· ≤ ·) ∨ (vals arr).Pairwise (· ≥ ·)) :
    ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = adjacentSum (vals arr) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hmono : (vals arr).Pairwise (· ≤ ·) ∨ (vals arr).Pairwise (· ≥ ·)), ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = adjacentSum (vals arr)) := by
  sorry

/-- Whenever the function returns a result r, r = (n-1) * x * x.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and there is an integer x with 1 <= x <= 15 such that arr[i] = x for every i with 0 <= i < n. -/
theorem spec_9 (arr : Slice I64) (n : ℕ) (x : ℤ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hx1 : 1 ≤ x) (hx15 : x ≤ 15)
    (hall : ∀ y ∈ vals arr, y = x) :
    ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = ((n : ℤ) - 1) * x * x := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (x : ℤ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hx1 : 1 ≤ x) (hx15 : x ≤ 15)
    (hall : ∀ y ∈ vals arr, y = x), ∀ r : I64, mct_from_leaf_values arr = ok r → r.val = ((n : ℤ) - 1) * x * x) := by
  sorry

/-- Whenever mct_from_leaf_values(arr) returns r and mct_from_leaf_values(arr') returns r', we have r <= r'.
  Preconditions: arr and arr' are two slices of i64, both with length n, 2 <= n <= 40, and 1 <= arr[i], arr'[i] <= 15 for every i with 0 <= i < n. Moreover arr[i] <= arr'[i] for every i with 0 <= i < n. -/
theorem spec_10 (arr arr' : Slice I64) (n : ℕ) (hn : arr.val.length = n)
    (hn' : arr'.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hb' : ∀ x ∈ arr'.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hle : List.Forall₂ (· ≤ ·) (vals arr) (vals arr')) :
    ∀ r r' : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values arr' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr arr' : Slice I64) (n : ℕ) (hn : arr.val.length = n)
    (hn' : arr'.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hb' : ∀ x ∈ arr'.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hle : List.Forall₂ (· ≤ ·) (vals arr) (vals arr')), ∀ r r' : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values arr' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Whenever mct_from_leaf_values(arr) returns r and mct_from_leaf_values(rev(arr)) returns r_rev, we have r = r_rev.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i. Let rev(arr) be the slice of length n with rev(arr)[i] = arr[n-1-i]. -/
theorem spec_11 (arr rev : Slice I64) (n : ℕ) (hn : arr.val.length = n)
    (hnr : rev.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hb' : ∀ x ∈ rev.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hrev : rev.val = arr.val.reverse) :
    ∀ r rrev : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values rev = ok rrev →
      r.val = rrev.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr rev : Slice I64) (n : ℕ) (hn : arr.val.length = n)
    (hnr : rev.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hb' : ∀ x ∈ rev.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hrev : rev.val = arr.val.reverse), ∀ r rrev : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values rev = ok rrev →
      r.val = rrev.val) := by
  sorry

/-- Whenever mct_from_leaf_values(arr) returns r and mct_from_leaf_values(c*arr) returns r_c, we have r_c = c * c * r.
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i. Let c be a positive integer such that 1 <= c * arr[i] <= 15 for every i. Define c*arr by (c*arr)[i] = c * arr[i]. -/
theorem spec_12 (arr scaled : Slice I64) (n c : ℕ) (hn : arr.val.length = n)
    (hns : scaled.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40) (hc : 1 ≤ c)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hbc : ∀ x ∈ vals arr, 1 ≤ (c : ℤ) * x ∧ (c : ℤ) * x ≤ 15)
    (hbs : ∀ x ∈ scaled.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hscale : List.Forall₂ (fun x y => y = (c : ℤ) * x) (vals arr) (vals scaled)) :
    ∀ r rc : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values scaled = ok rc →
      rc.val = (c : ℤ) * (c : ℤ) * r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr scaled : Slice I64) (n c : ℕ) (hn : arr.val.length = n)
    (hns : scaled.val.length = n) (hn2 : 2 ≤ n) (hn40 : n ≤ 40) (hc : 1 ≤ c)
    (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hbc : ∀ x ∈ vals arr, 1 ≤ (c : ℤ) * x ∧ (c : ℤ) * x ≤ 15)
    (hbs : ∀ x ∈ scaled.val, 1 ≤ x.val ∧ x.val ≤ 15)
    (hscale : List.Forall₂ (fun x y => y = (c : ℤ) * x) (vals arr) (vals scaled)), ∀ r rc : I64, mct_from_leaf_values arr = ok r → mct_from_leaf_values scaled = ok rc →
      rc.val = (c : ℤ) * (c : ℤ) * r.val) := by
  sorry

/-- There exists a valid right-comb tree for arr whose non-leaf-node sum is R(arr) = sum_{i=0}^{n-2} ( arr[i] * max { arr[j] : i+1 <= j <= n-1 } ). Whenever the function returns a result r, r <= R(arr).
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_13 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    (∃ t : MctTree, IsRightComb t ∧ IsValidFor t arr ∧ t.nodeSum = rightCombSum (vals arr)) ∧
      ∀ r : I64, mct_from_leaf_values arr = ok r → r.val ≤ rightCombSum (vals arr) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), (∃ t : MctTree, IsRightComb t ∧ IsValidFor t arr ∧ t.nodeSum = rightCombSum (vals arr)) ∧
      ∀ r : I64, mct_from_leaf_values arr = ok r → r.val ≤ rightCombSum (vals arr)) := by
  sorry

/-- There exists a valid left-comb tree for arr whose non-leaf-node sum is L(arr) = sum_{i=1}^{n-1} ( max { arr[j] : 0 <= j <= i-1 } * arr[i] ). Whenever the function returns a result r, r <= L(arr).
  Preconditions: arr is a slice of i64 with n = len(arr), 2 <= n <= 40, and 1 <= arr[i] <= 15 for every i with 0 <= i < n. -/
theorem spec_14 (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15) :
    (∃ t : MctTree, IsLeftComb t ∧ IsValidFor t arr ∧ t.nodeSum = leftCombSum (vals arr)) ∧
      ∀ r : I64, mct_from_leaf_values arr = ok r → r.val ≤ leftCombSum (vals arr) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice I64) (n : ℕ) (hn : arr.val.length = n) (hn2 : 2 ≤ n)
    (hn40 : n ≤ 40) (hb : ∀ x ∈ arr.val, 1 ≤ x.val ∧ x.val ≤ 15), (∃ t : MctTree, IsLeftComb t ∧ IsValidFor t arr ∧ t.nodeSum = leftCombSum (vals arr)) ∧
      ∀ r : I64, mct_from_leaf_values arr = ok r → r.val ≤ leftCombSum (vals arr)) := by
  sorry

end AegisSpec.MctFromLeafValues
