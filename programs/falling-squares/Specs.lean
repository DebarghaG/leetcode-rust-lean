import Aegis.FallingSquares.Code.Funs

/-!
# Specifications of `Aegis.FallingSquares.falling_squares`

LeetCode problem `falling-squares`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FallingSquares

namespace AegisSpec.FallingSquares

def rowsOf (positions : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  positions.val.map (fun row => row.val.map (fun x => x.val))

def nRows (positions : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (rowsOf positions).length

def leftOf (rows : List (List Int)) (i : Nat) : Int :=
  (rows.getD i []).getD 0 0

def sideOf (rows : List (List Int)) (i : Nat) : Int :=
  (rows.getD i []).getD 1 0

def rightOf (rows : List (List Int)) (i : Nat) : Int :=
  leftOf rows i + sideOf rows i

abbrev overlaps (rows : List (List Int)) (j k : Nat) : Prop :=
  leftOf rows j < rightOf rows k ∧ leftOf rows k < rightOf rows j

def bottomFromTops (rows : List (List Int)) (prev : List Int) (k : Nat) : Int :=
  match (List.range k).filterMap
    (fun j => if overlaps rows j k then some (prev.getD j 0) else none) with
  | [] => 0
  | t :: ts => ts.foldr max t

def topsPrefix (rows : List (List Int)) : Nat → List Int
  | 0 => []
  | k + 1 =>
      topsPrefix rows k ++ [bottomFromTops rows (topsPrefix rows k) k + sideOf rows k]

def bottomOf (rows : List (List Int)) (k : Nat) : Int :=
  bottomFromTops rows (topsPrefix rows k) k

def topOf (rows : List (List Int)) (k : Nat) : Int :=
  bottomOf rows k + sideOf rows k

def maxTopUpTo (rows : List (List Int)) (i : Nat) : Int :=
  match (List.range (i + 1)).map (topOf rows) with
  | [] => 0
  | t :: ts => ts.foldr max t

def maxSideUpTo (rows : List (List Int)) (i : Nat) : Int :=
  match (List.range (i + 1)).map (sideOf rows) with
  | [] => 0
  | t :: ts => ts.foldr max t

def sumSideUpTo (rows : List (List Int)) (i : Nat) : Int :=
  ((List.range (i + 1)).map (sideOf rows)).foldr (· + ·) 0

def outVals (r : alloc.vec.Vec Std.I64) : List Int :=
  r.val.map (fun x => x.val)

def outAt (r : alloc.vec.Vec Std.I64) (i : Nat) : Int :=
  (outVals r).getD i 0

def obstacleMax (rows : List (List Int)) (k : Nat) (keep : Nat → Prop) [DecidablePred keep] :
    Int :=
  match (List.range k).filterMap
    (fun j => if overlaps rows j k ∧ keep j then some (topOf rows j) else none) with
  | [] => 0
  | t :: ts => ts.foldr max t

def takePrefix (positions : Slice (alloc.vec.Vec Std.I64)) (m : Nat) :
    Slice (alloc.vec.Vec Std.I64) where
  leng := (positions.val.take m).length
  list := Aeneas.Data.ListN.ListN.fromList (positions.val.take m)
  bound := by
    have hlen : positions.val.length = positions.leng :=
      Aeneas.Data.ListN.ListN_length positions.list
    have htake : (positions.val.take m).length ≤ positions.val.length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    have hbound : positions.leng ≤ Usize.max := positions.bound
    omega

def prefixUpTo (positions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) :
    Slice (alloc.vec.Vec Std.I64) :=
  takePrefix positions (i + 1)

/-- Whenever falling_squares returns a result r, len(r) = n and, for every i with 0 <= i < n, r[i] = max_{0 <= k <= i} T_k, where for each k with 0 <= k < n we define L_k = positions[k][0], S_k = positions[k][1], R_k = L_k + S_k; J_k = {j | 0 <= j < k and L_j < R_k and L_k < R_j}; B_k = 0 if J_k is empty, and B_k = max_{j in J_k} T_j otherwise; and T_k = B_k + S_k. Here B_k is the y-coordinate of the bottom edge of square k after it lands and T_k is the y-coordinate of its top edge. The condition L_j < R_k and L_k < R_j means the two squares' horizontal interiors overlap, so touching only at an endpoint is not an overlap. The answer is 0-indexed: r[0] is the height after the first drop.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_1 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      (outVals r).length = nRows positions ∧
      (∀ i, i < nRows positions → outAt r i = maxTopUpTo (rowsOf positions) i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      (outVals r).length = nRows positions ∧
      (∀ i, i < nRows positions → outAt r i = maxTopUpTo (rowsOf positions) i)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, access a vector out of bounds, or overflow i64 arithmetic.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_2 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∃ r, falling_squares positions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∃ r, falling_squares positions = ok r) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n - 1, r[i] <= r[i + 1]. The recorded tallest-stack height never decreases as more squares are dropped.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_3 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i + 1 < nRows positions → outAt r i ≤ outAt r (i + 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i + 1 < nRows positions → outAt r i ≤ outAt r (i + 1)) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, r[i] >= max_{0 <= k <= i} positions[k][1]. In particular r[i] >= positions[i][1].
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_4 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        outAt r i ≥ maxSideUpTo (rowsOf positions) i ∧
        outAt r i ≥ sideOf (rowsOf positions) i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        outAt r i ≥ maxSideUpTo (rowsOf positions) i ∧
        outAt r i ≥ sideOf (rowsOf positions) i) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, r[i] <= sum_{k = 0}^{i} positions[k][1]. No stack using the first i+1 squares can have height exceeding the sum of their side lengths.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_5 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → outAt r i ≤ sumSideUpTo (rowsOf positions) i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → outAt r i ≤ sumSideUpTo (rowsOf positions) i) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, 1 <= r[i] <= 1000000000. All recorded heights are positive and fit comfortably in i64.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_6 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → 1 ≤ outAt r i ∧ outAt r i ≤ 1000000000 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → 1 ≤ outAt r i ∧ outAt r i ≤ 1000000000) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, r[i] = T_i if i = 0, and r[i] = max(r[i - 1], T_i) if i > 0, where T_i is the top height of square i defined by the landing recurrence: L_m = positions[m][0], S_m = positions[m][1], R_m = L_m + S_m, and T_m = S_m + B_m with B_m = 0 if no j < m has L_j < R_m and L_m < R_j, otherwise B_m = max{T_j | 0 <= j < m, L_j < R_m, L_m < R_j}. This says each output is the running maximum of the newly landed square's top and the previous output.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_7 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        outAt r i = if i = 0 then topOf (rowsOf positions) i
                    else max (outAt r (i - 1)) (topOf (rowsOf positions) i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        outAt r i = if i = 0 then topOf (rowsOf positions) i
                    else max (outAt r (i - 1)) (topOf (rowsOf positions) i)) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, there exists k with 0 <= k <= i such that r[i] = T_k, where T_k is the top height of square k after it lands. Thus the tallest-stack height after i drops is attained by the top of one of the squares dropped so far. Here T_k = B_k + S_k, with B_k defined by the landing recurrence as in spec_1.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_8 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        ∃ k, k ≤ i ∧ outAt r i = topOf (rowsOf positions) k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        ∃ k, k ≤ i ∧ outAt r i = topOf (rowsOf positions) k) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n and every k with 0 <= k <= i, r[i] >= T_k, where T_k is the top height of square k after it lands. Thus r[i] is an upper bound for every top height produced by the first i+1 drops. Here T_k = B_k + S_k, with B_k defined by the landing recurrence as in spec_1.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_9 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → ∀ k, k ≤ i →
        outAt r i ≥ topOf (rowsOf positions) k := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions → ∀ k, k ≤ i →
        outAt r i ≥ topOf (rowsOf positions) k) := by
  sorry

/-- Whenever falling_squares returns a result r, for every i with 0 <= i < n, let p be the prefix slice positions[0..i] consisting of entries 0 through i inclusive. If falling_squares(p) returns r_p, then len(r_p) = i + 1 and r_p[i] = r[i]. Equivalently, the height recorded after drop i is determined only by the first i+1 input squares and is unaffected by any later squares.
  Preconditions: Let n = len(positions). 1 <= n <= 1000. For every i with 0 <= i < n, positions[i] has length 2, and writing L_i = positions[i][0] and S_i = positions[i][1], we have 1 <= L_i <= 100000000 and 1 <= S_i <= 1000000. -/
theorem spec_10 (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000) :
    ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        ∀ rp, falling_squares (prefixUpTo positions i) = ok rp →
          (outVals rp).length = i + 1 ∧ outAt rp i = outAt r i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (positions : Slice (alloc.vec.Vec Std.I64))
    (hpos : 1 ≤ nRows positions)
    (hlen : nRows positions ≤ 1000)
    (hrow : ∀ i, i < nRows positions → ((rowsOf positions).getD i []).length = 2)
    (hleft : ∀ i, i < nRows positions →
      1 ≤ leftOf (rowsOf positions) i ∧ leftOf (rowsOf positions) i ≤ 100000000)
    (hside : ∀ i, i < nRows positions →
      1 ≤ sideOf (rowsOf positions) i ∧ sideOf (rowsOf positions) i ≤ 1000000), ∀ r, falling_squares positions = ok r →
      ∀ i, i < nRows positions →
        ∀ rp, falling_squares (prefixUpTo positions i) = ok rp →
          (outVals rp).length = i + 1 ∧ outAt rp i = outAt r i) := by
  sorry

end AegisSpec.FallingSquares
