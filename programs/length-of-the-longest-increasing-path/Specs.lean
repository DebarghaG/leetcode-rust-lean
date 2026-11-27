import Aegis.MaxPathLength.Code.Funs

/-!
# Specifications of `Aegis.MaxPathLength.max_path_length`

LeetCode problem `length-of-the-longest-increasing-path`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MaxPathLength

namespace AegisSpec.MaxPathLength

def rows (coordinates : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  coordinates.val.map (fun v => v.val.map (fun z => z.val))

def row (coordinates : Slice (alloc.vec.Vec I64)) (i : Nat) : List Int :=
  (rows coordinates).getD i []

def pt (coordinates : Slice (alloc.vec.Vec I64)) (i : Nat) : Int × Int :=
  match row coordinates i with
  | [x, y] => (x, y)
  | _ => (0, 0)

def X (coordinates : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (pt coordinates i).1

def Y (coordinates : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
  (pt coordinates i).2

def InBounds (p : Int × Int) : Prop :=
  0 ≤ p.1 ∧ p.1 ≤ 10 ^ 9 ∧ 0 ≤ p.2 ∧ p.2 ≤ 10 ^ 9

def IsPath (coordinates : Slice (alloc.vec.Vec I64)) (js : List Nat) : Prop :=
  js ≠ [] ∧
    (∀ j ∈ js, j < coordinates.val.length) ∧
      (∀ t, t + 1 < js.length →
        X coordinates (js.getD t 0) < X coordinates (js.getD (t + 1) 0) ∧
          Y coordinates (js.getD t 0) < Y coordinates (js.getD (t + 1) 0))

def pathLengthsThrough (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Set Nat :=
  {m | ∃ js : List Nat, IsPath coordinates js ∧ k ∈ js ∧ js.length = m}

noncomputable def maxPathLengthThrough
    (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Nat :=
  sSup (pathLengthsThrough coordinates k)

def pathLengthsEndingAt (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Set Nat :=
  {m | ∃ js : List Nat, IsPath coordinates js ∧ js.getLast? = some k ∧ js.length = m}

noncomputable def maxPathLengthEndingAt
    (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Nat :=
  sSup (pathLengthsEndingAt coordinates k)

def pathLengthsStartingAt (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Set Nat :=
  {m | ∃ js : List Nat, IsPath coordinates js ∧ js.head? = some k ∧ js.length = m}

noncomputable def maxPathLengthStartingAt
    (coordinates : Slice (alloc.vec.Vec I64)) (k : Nat) : Nat :=
  sSup (pathLengthsStartingAt coordinates k)

/-- For every input satisfying the preconditions, the function returns a result r and r equals the maximum length of an increasing path that contains k. Write coordinates[i] = (X_i, Y_i). An increasing path is a sequence of indices i_0, i_1, ..., i_{m-1} with m >= 1 such that 0 <= i_j < n for all j and, for every j with 0 <= j < m-1, X_{i_j} < X_{i_{j+1}} and Y_{i_j} < Y_{i_{j+1}}. The path contains k if some i_j = k, and its length is m. The maximum is over all such paths; it is well defined because the one-point path [k] is allowed.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_1
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int)) :
    ∃ r : I64, max_path_length coordinates k = ok r ∧
      r.val = (maxPathLengthThrough coordinates k.val.toNat : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int)), ∃ r : I64, max_path_length coordinates k = ok r ∧
      r.val = (maxPathLengthThrough coordinates k.val.toNat : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r. Equivalently, it does not fail, panic, overflow, underflow, or access a coordinate out of bounds on this constrained input domain.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_2
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int)) :
    ∃ r : I64, max_path_length coordinates k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int)), ∃ r : I64, max_path_length coordinates k = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, 1 <= r <= n, where n = len(coordinates).
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_3
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    1 ≤ r.val ∧ r.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), 1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). Whenever the function returns a result r on an input satisfying the preconditions, r = 1 if and only if for every index i with 0 <= i < n and i != k, neither (X_i < X_k and Y_i < Y_k) nor (X_k < X_i and Y_k < Y_i) holds.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_4
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    (r.val = 1 ↔
      ∀ i, i < n → i ≠ k.val.toNat →
        ¬ (X coordinates i < X coordinates k.val.toNat ∧
            Y coordinates i < Y coordinates k.val.toNat) ∧
          ¬ (X coordinates k.val.toNat < X coordinates i ∧
              Y coordinates k.val.toNat < Y coordinates i)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), (r.val = 1 ↔
      ∀ i, i < n → i ≠ k.val.toNat →
        ¬ (X coordinates i < X coordinates k.val.toNat ∧
            Y coordinates i < Y coordinates k.val.toNat) ∧
          ¬ (X coordinates k.val.toNat < X coordinates i ∧
              Y coordinates k.val.toNat < Y coordinates i))) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). Whenever the function returns a result r on an input satisfying the preconditions, if there exist indices a and b with 0 <= a,b < n such that X_a < X_k < X_b and Y_a < Y_k < Y_b, then r >= 3.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_5
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r)
    (h_between : ∃ a b, a < n ∧ b < n ∧
      X coordinates a < X coordinates k.val.toNat ∧
        X coordinates k.val.toNat < X coordinates b ∧
          Y coordinates a < Y coordinates k.val.toNat ∧
            Y coordinates k.val.toNat < Y coordinates b) :
    3 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r)
    (h_between : ∃ a b, a < n ∧ b < n ∧
      X coordinates a < X coordinates k.val.toNat ∧
        X coordinates k.val.toNat < X coordinates b ∧
          Y coordinates a < Y coordinates k.val.toNat ∧
            Y coordinates k.val.toNat < Y coordinates b), 3 ≤ r.val) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). Whenever the function returns a result r on an input satisfying the preconditions, r = n if and only if for every pair of distinct indices i,j with 0 <= i,j < n, either (X_i < X_j and Y_i < Y_j) or (X_j < X_i and Y_j < Y_i).
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_6
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    (r.val = (n : Int) ↔
      ∀ i j, i < n → j < n → i ≠ j →
        (X coordinates i < X coordinates j ∧ Y coordinates i < Y coordinates j) ∨
          (X coordinates j < X coordinates i ∧ Y coordinates j < Y coordinates i)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), (r.val = (n : Int) ↔
      ∀ i j, i < n → j < n → i ≠ j →
        (X coordinates i < X coordinates j ∧ Y coordinates i < Y coordinates j) ∨
          (X coordinates j < X coordinates i ∧ Y coordinates j < Y coordinates i))) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). An increasing path is a sequence of indices with strictly increasing X and Y coordinates for every consecutive pair; its length is the number of indices. Whenever the function returns a result r on an input satisfying the preconditions, let A be the maximum length of an increasing path whose last index is k, and let B be the maximum length of an increasing path whose first index is k. Then r = A + B - 1.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_7
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    r.val = (maxPathLengthEndingAt coordinates k.val.toNat : Int) +
        (maxPathLengthStartingAt coordinates k.val.toNat : Int) - 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), r.val = (maxPathLengthEndingAt coordinates k.val.toNat : Int) +
        (maxPathLengthStartingAt coordinates k.val.toNat : Int) - 1) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). Whenever the function returns a result r on an input satisfying the preconditions, there exists an increasing path containing k whose length is exactly r, where an increasing path is a sequence of indices i_0, i_1, ..., i_{m-1} with m >= 1, 0 <= i_j < n, and X_{i_j} < X_{i_{j+1}} and Y_{i_j} < Y_{i_{j+1}} for all consecutive j; the length is m.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_8
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    ∃ js : List Nat, IsPath coordinates js ∧ k.val.toNat ∈ js ∧
      (js.length : Int) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), ∃ js : List Nat, IsPath coordinates js ∧ k.val.toNat ∈ js ∧
      (js.length : Int) = r.val) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). Whenever the function returns a result r on an input satisfying the preconditions, every increasing path containing k has length at most r. Here an increasing path is a sequence of indices i_0, i_1, ..., i_{m-1} with m >= 1, 0 <= i_j < n, and X_{i_j} < X_{i_{j+1}} and Y_{i_j} < Y_{i_{j+1}} for all consecutive j; its length is m.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_9
    (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r) :
    ∀ js : List Nat, IsPath coordinates js → k.val.toNat ∈ js →
      (js.length : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (coordinates : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))
    (r : I64) (hr : max_path_length coordinates k = ok r), ∀ js : List Nat, IsPath coordinates js → k.val.toNat ∈ js →
      (js.length : Int) ≤ r.val) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). For every input satisfying the preconditions, let coordinates' be the slice of length n with coordinates'[i] = (Y_i, X_i) for 0 <= i < n. If the function returns r on (coordinates,k) and returns r' on (coordinates',k), then r' = r.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_10
    (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (hn' : n = coordinates'.val.length)
    (h_swap : ∀ i, i < n →
      pt coordinates' i = (Y coordinates i, X coordinates i))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r') :
    r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (hn' : n = coordinates'.val.length)
    (h_swap : ∀ i, i < n →
      pt coordinates' i = (Y coordinates i, X coordinates i))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r'), r' = r) := by
  sorry

/-- For every input satisfying the preconditions and every permutation π of {0,1,...,n-1}, define coordinates' by coordinates'[i] = coordinates[π(i)] for 0 <= i < n, and let k' be the unique index with π(k') = k. If the function returns r on (coordinates,k) and returns r' on (coordinates',k'), then r' = r.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_11
    (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (π : Nat → Nat) (k' : Nat)
    (hπ_lt : ∀ i, i < n → π i < n)
    (hπ_inj : ∀ i j, i < n → j < n → π i = π j → i = j)
    (hk' : k' < n) (hπ_k : π k' = k.val.toNat)

    (hn' : n = coordinates'.val.length)
    (h_perm : ∀ i, i < n → pt coordinates' i = pt coordinates (π i))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r') :
    r' = r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (π : Nat → Nat) (k' : Nat)
    (hπ_lt : ∀ i, i < n → π i < n)
    (hπ_inj : ∀ i j, i < n → j < n → π i = π j → i = j)
    (hk' : k' < n) (hπ_k : π k' = k.val.toNat)

    (hn' : n = coordinates'.val.length)
    (h_perm : ∀ i, i < n → pt coordinates' i = pt coordinates (π i))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r'), r' = r) := by
  sorry

/-- Write coordinates[i] = (X_i, Y_i). For every input satisfying the preconditions and every pair of integers a,b such that 0 <= X_i + a <= 10^9 and 0 <= Y_i + b <= 10^9 for all i, let coordinates'[i] = (X_i + a, Y_i + b). If the function returns r on (coordinates,k) and returns r' on (coordinates',k), then r' = r.
  Preconditions: n = len(coordinates); 1 <= n <= 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_12
    (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (a b : Int)
    (h_a : ∀ i, i < n → 0 ≤ X coordinates i + a ∧ X coordinates i + a ≤ 10 ^ 9)
    (h_b : ∀ i, i < n → 0 ≤ Y coordinates i + b ∧ Y coordinates i + b ≤ 10 ^ 9)

    (hn' : n = coordinates'.val.length)
    (h_trans : ∀ i, i < n →
      pt coordinates' i = (X coordinates i + a, Y coordinates i + b))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r') :
    r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (a b : Int)
    (h_a : ∀ i, i < n → 0 ≤ X coordinates i + a ∧ X coordinates i + a ≤ 10 ^ 9)
    (h_b : ∀ i, i < n → 0 ≤ Y coordinates i + b ∧ Y coordinates i + b ≤ 10 ^ 9)

    (hn' : n = coordinates'.val.length)
    (h_trans : ∀ i, i < n →
      pt coordinates' i = (X coordinates i + a, Y coordinates i + b))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r'), r' = r) := by
  sorry

/-- For every input satisfying the preconditions and every point p = (x,y) with 0 <= x,y <= 10^9 that is distinct from all coordinates[i], let coordinates' be coordinates with p appended at index n. If the function returns r on (coordinates,k) and returns r' on (coordinates',k), then r' >= r.
  Preconditions: n = len(coordinates); 1 <= n < 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_13
    (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_lt : n < 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (x y : Int)
    (h_p_bnd : InBounds (x, y))
    (h_p_dist : ∀ i, i < n → (x, y) ≠ pt coordinates i)

    (hn' : n + 1 = coordinates'.val.length)
    (h_prefix : ∀ i, i < n → pt coordinates' i = pt coordinates i)
    (h_last : pt coordinates' n = (x, y))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_lt : n < 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (x y : Int)
    (h_p_bnd : InBounds (x, y))
    (h_p_dist : ∀ i, i < n → (x, y) ≠ pt coordinates i)

    (hn' : n + 1 = coordinates'.val.length)
    (h_prefix : ∀ i, i < n → pt coordinates' i = pt coordinates i)
    (h_last : pt coordinates' n = (x, y))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r'), r.val ≤ r'.val) := by
  sorry

/-- For every input satisfying the preconditions and every point p = (x,y) with 0 <= x,y <= 10^9 that is distinct from all coordinates[i], let coordinates' be coordinates with p appended at index n. If the function returns r on (coordinates,k) and returns r' on (coordinates',k), then r' <= r + 1.
  Preconditions: n = len(coordinates); 1 <= n < 10^5; for every i with 0 <= i < n, coordinates[i] has length 2; for every i with 0 <= i < n, 0 <= coordinates[i][0] <= 10^9 and 0 <= coordinates[i][1] <= 10^9; all points are distinct, i.e. coordinates[i] != coordinates[j] for 0 <= i < j < n; and 0 <= k < n. -/
theorem spec_14
    (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_lt : n < 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (x y : Int)
    (h_p_bnd : InBounds (x, y))
    (h_p_dist : ∀ i, i < n → (x, y) ≠ pt coordinates i)

    (hn' : n + 1 = coordinates'.val.length)
    (h_prefix : ∀ i, i < n → pt coordinates' i = pt coordinates i)
    (h_last : pt coordinates' n = (x, y))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r') :
    r'.val ≤ r.val + 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (coordinates coordinates' : Slice (alloc.vec.Vec I64)) (k : I64) (n : Nat)
    (hn : n = coordinates.val.length)
    (hn_pos : 1 ≤ n) (hn_lt : n < 10 ^ 5)
    (h_row : ∀ i, i < n → (row coordinates i).length = 2)
    (h_bnd : ∀ i, i < n → InBounds (pt coordinates i))
    (h_dist : ∀ i j, i < j → j < n → pt coordinates i ≠ pt coordinates j)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val < (n : Int))

    (x y : Int)
    (h_p_bnd : InBounds (x, y))
    (h_p_dist : ∀ i, i < n → (x, y) ≠ pt coordinates i)

    (hn' : n + 1 = coordinates'.val.length)
    (h_prefix : ∀ i, i < n → pt coordinates' i = pt coordinates i)
    (h_last : pt coordinates' n = (x, y))
    (r r' : I64) (hr : max_path_length coordinates k = ok r)
    (hr' : max_path_length coordinates' k = ok r'), r'.val ≤ r.val + 1) := by
  sorry

end AegisSpec.MaxPathLength
