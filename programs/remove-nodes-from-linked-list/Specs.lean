import Aegis.RemoveNodes.Code.Funs

/-!
# Specifications of `Aegis.RemoveNodes.remove_nodes`

LeetCode problem `remove-nodes-from-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RemoveNodes

  open Aegis.RemoveNodes (remove_nodes)

  abbrev RustList : Type := Aegis.RemoveNodes.List

  def values : RustList → List Int
    | .Nil => []
    | .Cons v next => v.val :: values next

  def IsSuffixMaxIndex (xs : List Int) (i : Nat) : Prop :=
    match xs.drop i with
    | [] => False
    | v :: t => ∀ y ∈ t, y ≤ v

  def isSuffixMaxIndex (xs : List Int) (i : Nat) : Bool :=
    match xs.drop i with
    | [] => false
    | v :: t => t.all (fun y => decide (y ≤ v))

  def suffixMaxIndices (xs : List Int) : List Nat :=
    (List.range xs.length).filter (fun i => isSuffixMaxIndex xs i)

  def suffixMaxValues (xs : List Int) : List Int :=
    (suffixMaxIndices xs).map (fun i => (xs.drop i).headD 0)

  def sel (xs : List Int) (idx : List Nat) : List Int :=
    idx.map (fun i => xs.getD i 0)

  def countOf (v : Int) (xs : List Int) : Nat :=
    (xs.filter (fun x => x = v)).length

  def IsMaxOf (M : Int) (xs : List Int) : Prop :=
    M ∈ xs ∧ ∀ x ∈ xs, x ≤ M

  def NonIncreasing (xs : List Int) : Prop :=
    ∀ (i : Nat) (hi : i + 1 < xs.length), xs[i + 1]'hi ≤ xs[i]'(by omega)

  def NonDecreasing (xs : List Int) : Prop :=
    ∀ (i : Nat) (hi : i + 1 < xs.length), xs[i]'(by omega) ≤ xs[i + 1]'hi

  def minValue : List Int → Option Int
    | [] => none
    | x :: t => some (t.foldr min x)

  /-- The function returns a result r. Let ys be the value sequence of r. Let I be the set of all indices i with 0 <= i < n such that for every j with i < j < n, xs[j] <= xs[i]. Let i_0 < i_1 < ... < i_{m-1} be the elements of I in increasing order. Then m = len(ys) and ys[k] = xs[i_k] for every 0 <= k < m. Equivalently, ys is obtained from xs by deleting exactly those entries xs[i] for which there exists j with i < j < n and xs[j] > xs[i], while preserving the relative order of the remaining entries.
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_1 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∃ r, remove_nodes head = ok r ∧ values r = suffixMaxValues xs := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∃ r, remove_nodes head = ok r ∧ values r = suffixMaxValues xs) := by
    sorry

  /-- The function returns a result r for every head satisfying the preconditions; it does not panic, overflow, or otherwise fail.
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_2 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∃ r, remove_nodes head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∃ r, remove_nodes head = ok r) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, 1 <= len(ys) <= n.
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_3 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r → 1 ≤ (values r).length ∧ (values r).length ≤ xs.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r → 1 ≤ (values r).length ∧ (values r).length ≤ xs.length) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, len(ys) >= 1 and ys[len(ys)-1] = xs[n-1].
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_4 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r → 1 ≤ (values r).length ∧ (values r).getLast? = xs.getLast? := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r → 1 ≤ (values r).length ∧ (values r).getLast? = xs.getLast?) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, ys is an order-preserving subsequence of xs: there exist indices 0 <= i_0 < i_1 < ... < i_{len(ys)-1} < n such that ys[k] = xs[i_k] for every 0 <= k < len(ys).
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_5 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r →
        ∃ idx : List Nat, idx.Pairwise (· < ·) ∧ (∀ i ∈ idx, i < xs.length) ∧
          sel xs idx = values r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r →
          ∃ idx : List Nat, idx.Pairwise (· < ·) ∧ (∀ i ∈ idx, i < xs.length) ∧
            sel xs idx = values r) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, ys is non-increasing: for every k with 0 <= k < len(ys)-1, ys[k] >= ys[k+1].
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_6 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r → NonIncreasing (values r) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r → NonIncreasing (values r)) := by
    sorry

  /-- Let M be the maximum value of xs and let c be the number of indices i with xs[i] = M. Whenever the function returns a result r, letting ys be its value sequence, len(ys) >= c; for every k with 0 <= k < c, ys[k] = M; and for every k with c <= k < len(ys), ys[k] < M.
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_7 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ (r : RustList) (M : Int), remove_nodes head = ok r → IsMaxOf M xs →
        countOf M xs ≤ (values r).length ∧
        (∀ k (hk : k < (values r).length), k < countOf M xs → (values r)[k]'hk = M) ∧
        (∀ k (hk : k < (values r).length), countOf M xs ≤ k → (values r)[k]'hk < M) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ (r : RustList) (M : Int), remove_nodes head = ok r → IsMaxOf M xs →
          countOf M xs ≤ (values r).length ∧
          (∀ k (hk : k < (values r).length), k < countOf M xs → (values r)[k]'hk = M) ∧
          (∀ k (hk : k < (values r).length), countOf M xs ≤ k → (values r)[k]'hk < M)) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, ys = xs if and only if xs is non-increasing, meaning that for every i with 0 <= i < n-1, xs[i] >= xs[i+1].
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_8 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r → (values r = xs ↔ NonIncreasing xs) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r → (values r = xs ↔ NonIncreasing xs)) := by
    sorry

  /-- If xs is non-decreasing, meaning that for every i with 0 <= i < n-1, xs[i] <= xs[i+1], then whenever the function returns a result r, letting ys be its value sequence, ys consists exactly of all occurrences of M = xs[n-1]: if c is the number of indices i with xs[i] = M, then len(ys) = c and ys[k] = M for every 0 <= k < c.
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_9 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000)
      (hmono : NonDecreasing xs) :
      ∀ (r : RustList) (M : Int), remove_nodes head = ok r → xs.getLast? = some M →
        (values r).length = countOf M xs ∧
        (∀ k (hk : k < (values r).length), k < countOf M xs → (values r)[k]'hk = M) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000)
        (hmono : NonDecreasing xs), ∀ (r : RustList) (M : Int), remove_nodes head = ok r → xs.getLast? = some M →
          (values r).length = countOf M xs ∧
          (∀ k (hk : k < (values r).length), k < countOf M xs → (values r)[k]'hk = M)) := by
    sorry

  /-- Whenever the function returns a result r, let ys be its value sequence and match each position k of ys to the unique original index i_k selected by the exact suffix-maximum characterization, so ys[k] = xs[i_k] and the i_k are exactly the indices i with 0 <= i < n and xs[j] <= xs[i] for every j with i < j < n. For every original index i not among these selected indices, there exists a selected index p such that i < p < n and xs[p] > xs[i].
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_10 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r →
        values r = suffixMaxValues xs ∧
        (∀ i, i < xs.length → (i ∈ suffixMaxIndices xs ↔ IsSuffixMaxIndex xs i)) ∧
        (∀ (i : Nat) (hi : i < xs.length), ¬ IsSuffixMaxIndex xs i →
          ∃ (p : Nat) (hp : p < xs.length), i < p ∧ IsSuffixMaxIndex xs p ∧
            xs[i]'hi < xs[p]'hp) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r →
          values r = suffixMaxValues xs ∧
          (∀ i, i < xs.length → (i ∈ suffixMaxIndices xs ↔ IsSuffixMaxIndex xs i)) ∧
          (∀ (i : Nat) (hi : i < xs.length), ¬ IsSuffixMaxIndex xs i →
            ∃ (p : Nat) (hp : p < xs.length), i < p ∧ IsSuffixMaxIndex xs p ∧
              xs[i]'hi < xs[p]'hp)) := by
    sorry

  /-- Whenever the function returns a result r, letting ys be its value sequence, min{ys[k] | 0 <= k < len(ys)} = xs[n-1].
    Preconditions: Let xs be the value sequence of head from left to right and n = len(xs). Assume 1 <= n <= 100000 and 1 <= xs[i] <= 100000 for every 0 <= i < n. -/
  theorem spec_11 (head : RustList) (xs : List Int) (hvals : values head = xs)
      (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
      (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000) :
      ∀ r, remove_nodes head = ok r → minValue (values r) = xs.getLast? := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (head : RustList) (xs : List Int) (hvals : values head = xs)
        (hn : 1 ≤ xs.length) (hnb : xs.length ≤ 100000)
        (hrange : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000), ∀ r, remove_nodes head = ok r → minValue (values r) = xs.getLast?) := by
    sorry

  end AegisSpec.RemoveNodes
