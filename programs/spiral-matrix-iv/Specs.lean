import Aegis.SpiralMatrix.Code.Funs

/-!
# Specifications of `Aegis.SpiralMatrix.spiral_matrix`

LeetCode problem `spiral-matrix-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SpiralMatrix

def nth? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: tl, k + 1 => nth? tl k

def listLen : Aegis.SpiralMatrix.List → Nat
  | Aegis.SpiralMatrix.List.Nil => 0
  | Aegis.SpiralMatrix.List.Cons _ tl => 1 + listLen tl

def listVals : Aegis.SpiralMatrix.List → List Int
  | Aegis.SpiralMatrix.List.Nil => []
  | Aegis.SpiralMatrix.List.Cons v tl => v.val :: listVals tl

def spiralBoundaryCells : Nat → Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _, _ => []
  | fuel + 1, top, bottom, left, right =>
    if top > bottom ∨ left > right then
      []
    else if top = bottom then
      (List.range (right + 1 - left)).map (fun d => (top, left + d))
    else if left = right then
      (List.range (bottom + 1 - top)).map (fun d => (top + d, left))
    else
      (List.range (right + 1 - left)).map (fun d => (top, left + d))
        ++ (List.range (bottom - top)).map (fun d => (top + 1 + d, right))
        ++ (List.range (right - left)).map (fun d => (bottom, right - 1 - d))
        ++ (List.range (bottom - top - 1)).map (fun d => (bottom - 1 - d, left))
        ++ spiralBoundaryCells fuel (top + 1) (bottom - 1) (left + 1) (right - 1)

def spiralOrder (rows cols : Nat) : List (Nat × Nat) :=
  spiralBoundaryCells (rows * cols) 0 (rows - 1) 0 (cols - 1)

def cellValue? (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (p : Nat × Nat) : Option Int :=
  (nth? r.val p.1).bind (fun row => (nth? row.val p.2).map (fun v => v.val))

/-- Whenever spiral_matrix m n head returns a result r, r is exactly the m by n matrix defined as follows. len(r) = m, and for every i with 0 <= i < m, len(r[i]) = n, with rows indexed 0..m-1 and columns indexed 0..n-1. Let the clockwise spiral order of an m by n matrix be the sequence of all m*n cells obtained by repeatedly traversing the current outer boundary of the not-yet-visited cells: left-to-right along the top row, top-to-bottom along the right column, right-to-left along the bottom row, and bottom-to-top along the left column, then moving inward; if only one row or one column remains, it is traversed in the only direction that continues the spiral. For every k with 0 <= k < m*n, if (i,j) is the k-th cell in this clockwise spiral order (0-indexed), then r[i][j] is the value of the k-th node of head if k < L, and r[i][j] = -1 if k >= L.
  Preconditions: Let L be the number of nodes (Cons cells) in head. The inputs satisfy the problem constraints: m and n are integers with 1 <= m, 1 <= n, and m*n <= 100000; 1 <= L <= m*n; and every node value v of head satisfies 0 <= v <= 1000. -/
theorem spec_1 (m n : Std.I64) (head : Aegis.SpiralMatrix.List)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ m.val) (hn : 1 ≤ n.val) (hmn : m.val * n.val ≤ 100000)
    (hL_pos : 1 ≤ (listLen head : Int)) (hL_le : (listLen head : Int) ≤ m.val * n.val)
    (hval : ∀ v, v ∈ listVals head → 0 ≤ v ∧ v ≤ 1000)
    (hres : Aegis.SpiralMatrix.spiral_matrix m n head = ok r) :
    r.val.length = m.val.toNat ∧
      (∀ row, row ∈ r.val → row.val.length = n.val.toNat) ∧
      (spiralOrder m.val.toNat n.val.toNat).length = m.val.toNat * n.val.toNat ∧
      (∀ (k : Nat) (p : Nat × Nat), k < m.val.toNat * n.val.toNat →
        nth? (spiralOrder m.val.toNat n.val.toNat) k = some p → k < listLen head →
        ∃ v, nth? (listVals head) k = some v ∧ cellValue? r p = some v) ∧
      (∀ (k : Nat) (p : Nat × Nat), k < m.val.toNat * n.val.toNat →
        nth? (spiralOrder m.val.toNat n.val.toNat) k = some p → listLen head ≤ k →
        cellValue? r p = some (-1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : Std.I64) (head : Aegis.SpiralMatrix.List)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ m.val) (hn : 1 ≤ n.val) (hmn : m.val * n.val ≤ 100000)
    (hL_pos : 1 ≤ (listLen head : Int)) (hL_le : (listLen head : Int) ≤ m.val * n.val)
    (hval : ∀ v, v ∈ listVals head → 0 ≤ v ∧ v ≤ 1000)
    (hres : Aegis.SpiralMatrix.spiral_matrix m n head = ok r), r.val.length = m.val.toNat ∧
      (∀ row, row ∈ r.val → row.val.length = n.val.toNat) ∧
      (spiralOrder m.val.toNat n.val.toNat).length = m.val.toNat * n.val.toNat ∧
      (∀ (k : Nat) (p : Nat × Nat), k < m.val.toNat * n.val.toNat →
        nth? (spiralOrder m.val.toNat n.val.toNat) k = some p → k < listLen head →
        ∃ v, nth? (listVals head) k = some v ∧ cellValue? r p = some v) ∧
      (∀ (k : Nat) (p : Nat × Nat), k < m.val.toNat * n.val.toNat →
        nth? (spiralOrder m.val.toNat n.val.toNat) k = some p → listLen head ≤ k →
        cellValue? r p = some (-1))) := by
  sorry

/-- For every m, n, and head satisfying the preconditions, spiral_matrix m n head returns a result r; it does not panic, fail an overflow check, or access an out-of-bounds index.
  Preconditions: Let L be the number of nodes (Cons cells) in head. The inputs satisfy the problem constraints: m and n are integers with 1 <= m, 1 <= n, and m*n <= 100000; 1 <= L <= m*n; and every node value v of head satisfies 0 <= v <= 1000. -/
theorem spec_2 (m n : Std.I64) (head : Aegis.SpiralMatrix.List)
    (hm : 1 ≤ m.val) (hn : 1 ≤ n.val) (hmn : m.val * n.val ≤ 100000)
    (hL_pos : 1 ≤ (listLen head : Int)) (hL_le : (listLen head : Int) ≤ m.val * n.val)
    (hval : ∀ v, v ∈ listVals head → 0 ≤ v ∧ v ≤ 1000) :
    ∃ r, Aegis.SpiralMatrix.spiral_matrix m n head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : Std.I64) (head : Aegis.SpiralMatrix.List)
    (hm : 1 ≤ m.val) (hn : 1 ≤ n.val) (hmn : m.val * n.val ≤ 100000)
    (hL_pos : 1 ≤ (listLen head : Int)) (hL_le : (listLen head : Int) ≤ m.val * n.val)
    (hval : ∀ v, v ∈ listVals head → 0 ≤ v ∧ v ≤ 1000), ∃ r, Aegis.SpiralMatrix.spiral_matrix m n head = ok r) := by
  sorry

end AegisSpec.SpiralMatrix
