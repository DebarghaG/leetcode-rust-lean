import Aegis.NextLargerNodes.Code.Funs

/-!
# Specifications of `Aegis.NextLargerNodes.next_larger_nodes`

LeetCode problem `next-greater-node-in-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NextLargerNodes (next_larger_nodes)

  namespace AegisSpec.NextLargerNodes

  def nodeVals : Aegis.NextLargerNodes.List → List Std.I64
    | .Nil => []
    | .Cons v next => v :: nodeVals next

  def nth : List Std.I64 → Nat → Int
    | [], _ => 0
    | v :: _, 0 => v.val
    | _ :: vs, i + 1 => nth vs i

  def IsNextLarger (xs : List Std.I64) (i m : Nat) : Prop :=
    i < m ∧ m < xs.length ∧ nth xs i < nth xs m ∧
      ∀ k, i < k → k < m → nth xs k ≤ nth xs i

  def StrictlyIncreasing (xs : List Std.I64) : Prop :=
    ∀ i, i < xs.length - 1 → nth xs i < nth xs (i + 1)

  def StrictlyDecreasing (xs : List Std.I64) : Prop :=
    ∀ i, i < xs.length - 1 → nth xs (i + 1) < nth xs i

  /-- The function returns a result r, len(r) = n, and for every i with 0 <= i < n: if there exists j with i < j < n and xs[j] > xs[i], then r[i] = xs[m] where m is the least j with i < j < n and xs[j] > xs[i]; otherwise r[i] = 0.
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, so xs[0] is the first node value and xs[n-1] is the last node value, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_1 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        next_larger_nodes head = ok r ∧
        r.val.length = xs.length ∧
        ∀ i, i < xs.length →
          (∃ m, IsNextLarger xs i m ∧ nth r.val i = nth xs m) ∨
          ((∀ j, i < j → j < xs.length → nth xs j ≤ nth xs i) ∧ nth r.val i = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          next_larger_nodes head = ok r ∧
          r.val.length = xs.length ∧
          ∀ i, i < xs.length →
            (∃ m, IsNextLarger xs i m ∧ nth r.val i = nth xs m) ∨
            ((∀ j, i < j → j < xs.length → nth xs j ≤ nth xs i) ∧ nth r.val i = 0)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_2 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, next_larger_nodes head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, next_larger_nodes head = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n.
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_3 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      r.val.length = xs.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), r.val.length = xs.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i] <= 1000000000.
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_4 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < r.val.length → 0 ≤ nth r.val i ∧ nth r.val i ≤ 1000000000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < r.val.length → 0 ≤ nth r.val i ∧ nth r.val i ≤ 1000000000) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and i < len(r), if r[i] != 0 then r[i] > xs[i].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_5 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < xs.length → i < r.val.length → nth r.val i ≠ 0 → nth xs i < nth r.val i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < xs.length → i < r.val.length → nth r.val i ≠ 0 → nth xs i < nth r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and i < len(r), r[i] = 0 if and only if for every j with i < j < n, xs[j] <= xs[i].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_6 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < xs.length → i < r.val.length →
        (nth r.val i = 0 ↔ ∀ j, i < j → j < xs.length → nth xs j ≤ nth xs i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < xs.length → i < r.val.length →
          (nth r.val i = 0 ↔ ∀ j, i < j → j < xs.length → nth xs j ≤ nth xs i)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n and i < len(r), if r[i] != 0 then there exists j with i < j < n such that xs[j] = r[i], xs[j] > xs[i], and for every k with i < k < j, xs[k] <= xs[i].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_7 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < xs.length → i < r.val.length → nth r.val i ≠ 0 →
        ∃ j, i < j ∧ j < xs.length ∧ nth xs j = nth r.val i ∧ nth xs i < nth xs j ∧
          ∀ k, i < k → k < j → nth xs k ≤ nth xs i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < xs.length → i < r.val.length → nth r.val i ≠ 0 →
          ∃ j, i < j ∧ j < xs.length ∧ nth xs j = nth r.val i ∧ nth xs i < nth xs j ∧
            ∀ k, i < k → k < j → nth xs k ≤ nth xs i) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i < j < n and i < len(r), if xs[j] > xs[i] and for every k with i < k < j, xs[k] <= xs[i], then r[i] = xs[j].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_8 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i j, i < j → j < xs.length → i < r.val.length →
        nth xs i < nth xs j → (∀ k, i < k → k < j → nth xs k ≤ nth xs i) →
        nth r.val i = nth xs j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i j, i < j → j < xs.length → i < r.val.length →
          nth xs i < nth xs j → (∀ k, i < k → k < j → nth xs k ≤ nth xs i) →
          nth r.val i = nth xs j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n - 1 and i < len(r), if xs[i+1] > xs[i], then r[i] = xs[i+1].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_9 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < xs.length - 1 → i < r.val.length →
        nth xs i < nth xs (i + 1) → nth r.val i = nth xs (i + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < xs.length - 1 → i < r.val.length →
          nth xs i < nth xs (i + 1) → nth r.val i = nth xs (i + 1)) := by
    sorry

  /-- Whenever the function returns a result r and n = 1, len(r) = 1 and r[0] = 0.
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_10 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
      (hone : xs.length = 1) :
      r.val.length = 1 ∧ nth r.val 0 = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
        (hone : xs.length = 1), r.val.length = 1 ∧ nth r.val 0 = 0) := by
    sorry

  /-- Whenever the function returns a result r and xs is strictly increasing (that is, xs[i] < xs[i+1] for every i with 0 <= i < n - 1), len(r) = n, r[i] = xs[i+1] for every i with 0 <= i < n - 1, and r[n-1] = 0.
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_11 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
      (hinc : StrictlyIncreasing xs) :
      r.val.length = xs.length ∧
        (∀ i, i < xs.length - 1 → nth r.val i = nth xs (i + 1)) ∧
        nth r.val (xs.length - 1) = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
        (hinc : StrictlyIncreasing xs), r.val.length = xs.length ∧
          (∀ i, i < xs.length - 1 → nth r.val i = nth xs (i + 1)) ∧
          nth r.val (xs.length - 1) = 0) := by
    sorry

  /-- Whenever the function returns a result r and xs is strictly decreasing (that is, xs[i] > xs[i+1] for every i with 0 <= i < n - 1), r[i] = 0 for every i with 0 <= i < n and i < len(r).
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_12 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
      (hdec : StrictlyDecreasing xs) :
      ∀ i, i < xs.length → i < r.val.length → nth r.val i = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
        (hdec : StrictlyDecreasing xs), ∀ i, i < xs.length → i < r.val.length → nth r.val i = 0) := by
    sorry

  /-- Whenever the function returns a result r and all node values are equal (that is, xs[i] = xs[0] for every i with 0 <= i < n), r[i] = 0 for every i with 0 <= i < n and i < len(r).
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_13 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
      (heq : ∀ i, i < xs.length → nth xs i = nth xs 0) :
      ∀ i, i < xs.length → i < r.val.length → nth r.val i = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r)
        (heq : ∀ i, i < xs.length → nth xs i = nth xs 0), ∀ i, i < xs.length → i < r.val.length → nth r.val i = 0) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(r) and r[i] != 0 if and only if there exist indices p and q with 0 <= p < q < n and xs[p] < xs[q].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_14 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      (∃ i, i < r.val.length ∧ nth r.val i ≠ 0) ↔
        (∃ p, ∃ q, p < q ∧ q < xs.length ∧ nth xs p < nth xs q) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), (∃ i, i < r.val.length ∧ nth r.val i ≠ 0) ↔
          (∃ p, ∃ q, p < q ∧ q < xs.length ∧ nth xs p < nth xs q)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n - 1 and i + 1 < len(r), if xs[i] = xs[i+1], then r[i] = r[i+1].
    Preconditions: Let xs be the sequence of node values of head, read from the outermost Cons to Nil, and let n = len(xs). Assume n >= 1, n <= 10000, and 1 <= xs[i] <= 1000000000 for every i with 0 <= i < n. -/
  theorem spec_15 (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
      (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
      (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
      (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r) :
      ∀ i, i < xs.length - 1 → i + 1 < r.val.length →
        nth xs i = nth xs (i + 1) → nth r.val i = nth r.val (i + 1) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (head : Aegis.NextLargerNodes.List) (xs : List Std.I64)
        (hxs : xs = nodeVals head) (hn_pos : 1 ≤ xs.length) (hn_max : xs.length ≤ 10000)
        (hval : ∀ i, i < xs.length → 1 ≤ nth xs i ∧ nth xs i ≤ 1000000000)
        (r : alloc.vec.Vec Std.I64) (hres : next_larger_nodes head = ok r), ∀ i, i < xs.length - 1 → i + 1 < r.val.length →
          nth xs i = nth xs (i + 1) → nth r.val i = nth r.val (i + 1)) := by
    sorry

  end AegisSpec.NextLargerNodes
