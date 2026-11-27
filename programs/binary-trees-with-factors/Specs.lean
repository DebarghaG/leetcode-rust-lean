import Aegis.NumFactoredBinaryTrees.Code.Funs

/-!
# Specifications of `Aegis.NumFactoredBinaryTrees.num_factored_binary_trees`

LeetCode problem `binary-trees-with-factors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumFactoredBinaryTrees

  def modulus : Int := 1000000007

  def maxValue : Int := 10 ^ 9

  def contents (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

  def EntriesDistinct (l : List Std.I64) : Prop :=
    ∀ (i j : Nat) (x y : Std.I64), l[i]? = some x → l[j]? = some y → x.val = y.val → i = j

  def Pre (arr : Slice Std.I64) : Prop :=
    1 ≤ arr.val.length ∧
    arr.val.length ≤ 1000 ∧
    (∀ x ∈ arr.val, 2 ≤ x.val ∧ x.val ≤ maxValue) ∧
    EntriesDistinct arr.val

  def IsPrimeInt (v : Int) : Prop := Nat.Prime v.natAbs

  inductive ValidTree (a : List Int) : Int → Type
    | leaf (v : Int) (hv : v ∈ a) : ValidTree a v
    | node (v l r : Int) (hv : v ∈ a) (hmul : v = l * r)
        (hl : ValidTree a l) (hr : ValidTree a r) : ValidTree a v

  noncomputable def treeCount (a : List Int) (v : Int) : Nat := Nat.card (ValidTree a v)

  noncomputable def totalCount (a : List Int) : Nat := Nat.card (Sigma fun v : Int => ValidTree a v)

  def InternalTree (a : List Int) (v l r : Int) : Type :=
    { t : ValidTree a v //
        ∃ (hv : v ∈ a) (hmul : v = l * r) (L : ValidTree a l) (R : ValidTree a r),
          t = ValidTree.node v l r hv hmul L R }

  noncomputable def internalCount (a : List Int) (v l r : Int) : Nat :=
    Nat.card (InternalTree a v l r)

  /-- Let M = 10^9+7. Call a non-empty finite ordered binary tree valid for arr if: every node label is an element of arr; every leaf has no children; every internal node has exactly two children, and if its label is w and the root labels of its left and right children are a and b respectively, then w = a*b. Let N(arr) be the total number of valid trees for arr. Whenever num_factored_binary_trees(arr) returns a result r, r = N(arr) mod M.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct (for every i,j, if 0 <= i < len(arr), 0 <= j < len(arr), and arr[i] = arr[j], then i = j). -/
  theorem spec_1 (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) :
      r.val = ((totalCount (contents arr) : Nat) : Int) % modulus := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r), r.val = ((totalCount (contents arr) : Nat) : Int) % modulus) := by
    sorry

  /-- For every arr satisfying the preconditions, num_factored_binary_trees(arr) returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct (for every i,j, if 0 <= i < len(arr), 0 <= j < len(arr), and arr[i] = arr[j], then i = j). -/
  theorem spec_2 (arr : Slice Std.I64) (hpre : Pre arr) :
      ∃ r : Std.I64, Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr), ∃ r : Std.I64, Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) := by
    sorry

  /-- Whenever num_factored_binary_trees(arr) returns a result r, 0 <= r <= 10^9+6.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct (for every i,j, if 0 <= i < len(arr), 0 <= j < len(arr), and arr[i] = arr[j], then i = j). -/
  theorem spec_3 (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) :
      0 ≤ r.val ∧ r.val ≤ 10 ^ 9 + 6 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r), 0 ≤ r.val ∧ r.val ≤ 10 ^ 9 + 6) := by
    sorry

  /-- Let a tree be valid for arr if it is a non-empty finite ordered binary tree with labels in arr, leaves childless, and every internal node with label w and child root labels a,b satisfies w = a*b. For v in arr, let T(v) be the number of valid trees for arr rooted at v. Let N(arr) be the total number of valid trees for arr. Then N(arr) = sum over v in arr of T(v). Consequently, whenever num_factored_binary_trees(arr) returns r, r = (sum over v in arr of T(v)) mod (10^9+7).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct (for every i,j, if 0 <= i < len(arr), 0 <= j < len(arr), and arr[i] = arr[j], then i = j). -/
  theorem spec_4 (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) :
      totalCount (contents arr) = ∑ v ∈ (contents arr).toFinset, treeCount (contents arr) v ∧
      r.val = ((∑ v ∈ (contents arr).toFinset,
        treeCount (contents arr) v : Nat) : Int) % modulus := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr) (r : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r), totalCount (contents arr) = ∑ v ∈ (contents arr).toFinset, treeCount (contents arr) v ∧
        r.val = ((∑ v ∈ (contents arr).toFinset,
          treeCount (contents arr) v : Nat) : Int) % modulus) := by
    sorry

  /-- If num_factored_binary_trees(arr) returns r and num_factored_binary_trees(arr') returns r', then r = r'.
    Preconditions: arr and arr' each satisfy: 1 <= len <= 1000; all entries in [2,10^9]; all entries distinct. Also, for every integer x, x is an element of arr if and only if x is an element of arr'. -/
  theorem spec_5 (arr arr' : Slice Std.I64) (hpre : Pre arr) (hpre' : Pre arr')
      (hset : ∀ x : Int, x ∈ contents arr ↔ x ∈ contents arr')
      (r r' : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r)
      (hres' : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr' = ok r') :
      r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr arr' : Slice Std.I64) (hpre : Pre arr) (hpre' : Pre arr')
        (hset : ∀ x : Int, x ∈ contents arr ↔ x ∈ contents arr')
        (r r' : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r)
        (hres' : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr' = ok r'), r = r') := by
    sorry

  /-- Whenever num_factored_binary_trees(arr) returns r, r = len(arr) mod (10^9+7). Since len(arr) <= 1000 < 10^9+7, this means r = len(arr).
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct; len(arr) >= 2; and for every a,b,v in arr, a*b != v. -/
  theorem spec_6 (arr : Slice Std.I64) (hpre : Pre arr) (hlen : 2 ≤ arr.val.length)
      (hnoprod : ∀ a ∈ contents arr, ∀ b ∈ contents arr, ∀ v ∈ contents arr, a * b ≠ v)
      (r : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) :
      r.val = ((arr.val.length : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr) (hlen : 2 ≤ arr.val.length)
        (hnoprod : ∀ a ∈ contents arr, ∀ b ∈ contents arr, ∀ v ∈ contents arr, a * b ≠ v)
        (r : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r), r.val = ((arr.val.length : Nat) : Int)) := by
    sorry

  /-- Whenever num_factored_binary_trees(arr) returns r, r = 1.
    Preconditions: 1 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 2 <= arr[i] <= 10^9; all entries of arr are distinct; len(arr) = 1. -/
  theorem spec_7 (arr : Slice Std.I64) (hpre : Pre arr) (hlen : arr.val.length = 1)
      (r : Std.I64)
      (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r) :
      r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (hpre : Pre arr) (hlen : arr.val.length = 1)
        (r : Std.I64)
        (hres : Aegis.NumFactoredBinaryTrees.num_factored_binary_trees arr = ok r), r.val = 1) := by
    sorry

  end AegisSpec.NumFactoredBinaryTrees
