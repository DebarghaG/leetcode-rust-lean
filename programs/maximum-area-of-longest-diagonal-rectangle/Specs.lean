import Aegis.AreaOfMaxDiagonal.Code.Funs

/-!
# Specifications of `Aegis.AreaOfMaxDiagonal.area_of_max_diagonal`

LeetCode problem `maximum-area-of-longest-diagonal-rectangle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AreaOfMaxDiagonal

def rowPair (dimensions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option (Int × Int) :=
  match dimensions.val[i]? with
  | none => none
  | some row =>
    match row.val with
    | [x, y] => some (x.val, y.val)
    | _ => none

def diag2 (dimensions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  match rowPair dimensions i with
  | some (a, b) => a * a + b * b
  | none => 0

def area (dimensions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Int :=
  match rowPair dimensions i with
  | some (a, b) => a * b
  | none => 0

def IsMaxDiag (dimensions : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
  i < dimensions.val.length ∧
    ∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions i

def maxDiag (dimensions : Slice (alloc.vec.Vec Std.I64)) : Int :=
  ((List.range dimensions.val.length).map (diag2 dimensions)).foldr max 0

def IsPerm (n : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i, i < n → σ i < n) ∧
    (∀ i, i < n → ∀ j, j < n → σ i = σ j → i = j) ∧
      (∀ j, j < n → ∃ i, i < n ∧ σ i = j)

def AppendedRow (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64)) (a b : Int) : Prop :=
  dimensions'.val.length = dimensions.val.length + 1 ∧
    (∀ i, i < dimensions.val.length → rowPair dimensions' i = rowPair dimensions i) ∧
      rowPair dimensions' dimensions.val.length = some (a, b)

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] and area(i) = dimensions[i][0] * dimensions[i][1] for 0 <= i < len(dimensions). The function returns a result r, and there exists an index k with 0 <= k < len(dimensions) such that r = area(k), for every i with 0 <= i < len(dimensions) we have diag2(i) <= diag2(k), and for every i with 0 <= i < len(dimensions) and diag2(i) = diag2(k) we have area(i) <= r.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_1 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∃ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r ∧
      ∃ k, IsMaxDiag dimensions k ∧ r.val = area dimensions k ∧
        ∀ i, i < dimensions.val.length → diag2 dimensions i = diag2 dimensions k →
          area dimensions i ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∃ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r ∧
      ∃ k, IsMaxDiag dimensions k ∧ r.val = area dimensions k ∧
        ∀ i, i < dimensions.val.length → diag2 dimensions i = diag2 dimensions k →
          area dimensions i ≤ r.val) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_2 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∃ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∃ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r <= 10000.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_3 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      1 ≤ r.val ∧ r.val ≤ 10000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      1 ≤ r.val ∧ r.val ≤ 10000) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] and area(i) = dimensions[i][0] * dimensions[i][1] for 0 <= i < len(dimensions). Whenever the function returns a result r, there exists an index i with 0 <= i < len(dimensions) such that r = area(i) and for every j with 0 <= j < len(dimensions), diag2(j) <= diag2(i).
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_4 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∃ i, i < dimensions.val.length ∧ r.val = area dimensions i ∧
        ∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∃ i, i < dimensions.val.length ∧ r.val = area dimensions i ∧
        ∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions i) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] and area(i) = dimensions[i][0] * dimensions[i][1] for 0 <= i < len(dimensions). Whenever the function returns a result r, for every i with 0 <= i < len(dimensions), if for every j with 0 <= j < len(dimensions) we have diag2(j) <= diag2(i), then area(i) <= r.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_5 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ i, i < dimensions.val.length →
        (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions i) →
          area dimensions i ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ i, i < dimensions.val.length →
        (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions i) →
          area dimensions i ≤ r.val) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] and area(i) = dimensions[i][0] * dimensions[i][1] for 0 <= i < len(dimensions). Whenever the function returns a result r, if there is exactly one index m with 0 <= m < len(dimensions) such that for every j with 0 <= j < len(dimensions), diag2(j) <= diag2(m), then r = area(m).
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_6 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ m, IsMaxDiag dimensions m →
        (∀ m', IsMaxDiag dimensions m' → m' = m) → r.val = area dimensions m := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ m, IsMaxDiag dimensions m →
        (∀ m', IsMaxDiag dimensions m' → m' = m) → r.val = area dimensions m) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] and area(i) = dimensions[i][0] * dimensions[i][1] for 0 <= i < len(dimensions). Whenever the function returns a result r, if there exist distinct indices p and q with 0 <= p < q < len(dimensions) such that for every j with 0 <= j < len(dimensions), diag2(j) <= diag2(p) and diag2(j) <= diag2(q), then there exists an index m with 0 <= m < len(dimensions) such that diag2(m) = diag2(p), r = area(m), and for every i with 0 <= i < len(dimensions) and diag2(i) = diag2(p), area(i) <= r.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_7 (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100) :
    ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ p q, p < q → q < dimensions.val.length →
        (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions p) →
          (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions q) →
            ∃ m, m < dimensions.val.length ∧ diag2 dimensions m = diag2 dimensions p ∧
              r.val = area dimensions m ∧
                ∀ i, i < dimensions.val.length → diag2 dimensions i = diag2 dimensions p →
                  area dimensions i ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (dimensions : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100), ∀ r, Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      ∀ p q, p < q → q < dimensions.val.length →
        (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions p) →
          (∀ j, j < dimensions.val.length → diag2 dimensions j ≤ diag2 dimensions q) →
            ∃ m, m < dimensions.val.length ∧ diag2 dimensions m = diag2 dimensions p ∧
              r.val = area dimensions m ∧
                ∀ i, i < dimensions.val.length → diag2 dimensions i = diag2 dimensions p →
                  area dimensions i ≤ r.val) := by
  sorry

/-- Let dimensions' be any slice with len(dimensions') = len(dimensions) and, for every i with 0 <= i < len(dimensions), len(dimensions'[i]) = 2, dimensions'[i][0] = dimensions[i][1], and dimensions'[i][1] = dimensions[i][0]. Whenever area_of_max_diagonal(dimensions) returns r and area_of_max_diagonal(dimensions') returns r', we have r = r'.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_8 (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100)
    (h_len' : dimensions'.val.length = dimensions.val.length)
    (h_swap : ∀ i, i < dimensions.val.length →
      rowPair dimensions' i = (rowPair dimensions i).map (fun p => (p.2, p.1))) :
    ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100)
    (h_len' : dimensions'.val.length = dimensions.val.length)
    (h_swap : ∀ i, i < dimensions.val.length →
      rowPair dimensions' i = (rowPair dimensions i).map (fun p => (p.2, p.1))), ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r.val = r'.val) := by
  sorry

/-- Let dimensions' be any slice with len(dimensions') = len(dimensions) for which there exists a bijection sigma on {0, ..., len(dimensions)-1} such that dimensions'[i] = dimensions[sigma(i)] for every i with 0 <= i < len(dimensions). Whenever area_of_max_diagonal(dimensions) returns r and area_of_max_diagonal(dimensions') returns r', we have r = r'.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_9 (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100)
    (h_len' : dimensions'.val.length = dimensions.val.length)
    (h_perm : ∃ σ, IsPerm dimensions.val.length σ ∧
      ∀ i, i < dimensions.val.length → rowPair dimensions' i = rowPair dimensions (σ i)) :
    ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64))
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ a b, rowPair dimensions i = some (a, b) ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100)
    (h_len' : dimensions'.val.length = dimensions.val.length)
    (h_perm : ∃ σ, IsPerm dimensions.val.length σ ∧
      ∀ i, i < dimensions.val.length → rowPair dimensions' i = rowPair dimensions (σ i)), ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r.val = r'.val) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] for 0 <= i < len(dimensions), and let M be the maximum of diag2(i) over 0 <= i < len(dimensions). If len(dimensions) < 100, a and b are integers with 1 <= a <= 100 and 1 <= b <= 100, a*a + b*b < M, and dimensions' is the slice obtained by appending the row [a,b] to dimensions, then whenever area_of_max_diagonal(dimensions) returns r and area_of_max_diagonal(dimensions') returns r', we have r' = r.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_10 (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ x y, rowPair dimensions i = some (x, y) ∧ 1 ≤ x ∧ x ≤ 100 ∧ 1 ≤ y ∧ y ≤ 100)
    (h_len_lt : dimensions.val.length < 100)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100) (hb_lo : 1 ≤ b) (hb_hi : b ≤ 100)
    (h_diag_lt : a * a + b * b < maxDiag dimensions)
    (h_app : AppendedRow dimensions dimensions' a b) :
    ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ x y, rowPair dimensions i = some (x, y) ∧ 1 ≤ x ∧ x ≤ 100 ∧ 1 ≤ y ∧ y ≤ 100)
    (h_len_lt : dimensions.val.length < 100)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100) (hb_lo : 1 ≤ b) (hb_hi : b ≤ 100)
    (h_diag_lt : a * a + b * b < maxDiag dimensions)
    (h_app : AppendedRow dimensions dimensions' a b), ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' → r'.val = r.val) := by
  sorry

/-- Let diag2(i) = dimensions[i][0] * dimensions[i][0] + dimensions[i][1] * dimensions[i][1] for 0 <= i < len(dimensions), and let M be the maximum of diag2(i) over 0 <= i < len(dimensions). Whenever area_of_max_diagonal(dimensions) returns r and area_of_max_diagonal(dimensions') returns r', if len(dimensions) < 100, 1 <= a <= 100, 1 <= b <= 100, a*a + b*b = M, a*b <= r, and dimensions' is the slice obtained by appending the row [a,b] to dimensions, then r' = r.
  Preconditions: 1 <= len(dimensions) <= 100; for every i with 0 <= i < len(dimensions), len(dimensions[i]) = 2, 1 <= dimensions[i][0] <= 100, and 1 <= dimensions[i][1] <= 100. -/
theorem spec_11 (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ x y, rowPair dimensions i = some (x, y) ∧ 1 ≤ x ∧ x ≤ 100 ∧ 1 ≤ y ∧ y ≤ 100)
    (h_len_lt : dimensions.val.length < 100)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100) (hb_lo : 1 ≤ b) (hb_hi : b ≤ 100)
    (h_diag_eq : a * a + b * b = maxDiag dimensions)
    (h_app : AppendedRow dimensions dimensions' a b) :
    ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' →
        a * b ≤ r.val → r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (dimensions dimensions' : Slice (alloc.vec.Vec Std.I64)) (a b : Int)
    (h_len_lo : 1 ≤ dimensions.val.length)
    (h_len_hi : dimensions.val.length ≤ 100)
    (h_rows : ∀ i, i < dimensions.val.length →
      ∃ x y, rowPair dimensions i = some (x, y) ∧ 1 ≤ x ∧ x ≤ 100 ∧ 1 ≤ y ∧ y ≤ 100)
    (h_len_lt : dimensions.val.length < 100)
    (ha_lo : 1 ≤ a) (ha_hi : a ≤ 100) (hb_lo : 1 ≤ b) (hb_hi : b ≤ 100)
    (h_diag_eq : a * a + b * b = maxDiag dimensions)
    (h_app : AppendedRow dimensions dimensions' a b), ∀ r r', Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions = ok r →
      Aegis.AreaOfMaxDiagonal.area_of_max_diagonal dimensions' = ok r' →
        a * b ≤ r.val → r'.val = r.val) := by
  sorry

end AegisSpec.AreaOfMaxDiagonal
