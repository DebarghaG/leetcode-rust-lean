import Aegis.CountBlackBlocks.Code.Funs

/-!
# Specifications of `Aegis.CountBlackBlocks.count_black_blocks`

LeetCode problem `number-of-black-blocks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountBlackBlocks

def coordPairs (coordinates : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  coordinates.val.map (fun v => v.val.map (fun x => x.val))

def vecEntry (v : alloc.vec.Vec Std.I64) (t : ℕ) : Option ℤ :=
  (v.val[t]?).map (fun x => x.val)

def IsBlack (coordinates : Slice (alloc.vec.Vec Std.I64)) (x y : ℤ) : Prop :=
  [x, y] ∈ coordPairs coordinates

instance decidableIsBlack (coordinates : Slice (alloc.vec.Vec Std.I64)) (x y : ℤ) :
    Decidable (IsBlack coordinates x y) :=
  inferInstanceAs (Decidable ([x, y] ∈ coordPairs coordinates))

def blockBlackCount (coordinates : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℕ :=
  (((Finset.range 2) ×ˢ (Finset.range 2)).filter
      (fun p : ℕ × ℕ =>
        IsBlack coordinates ((i : ℤ) + (p.1 : ℤ)) ((j : ℤ) + (p.2 : ℤ)))).card

def blockCount (m n : ℤ) (coordinates : Slice (alloc.vec.Vec Std.I64)) (t : ℕ) : ℕ :=
  (((Finset.range (m - 1).toNat) ×ˢ (Finset.range (n - 1).toNat)).filter
      (fun p : ℕ × ℕ => blockBlackCount coordinates p.1 p.2 = t)).card

def fd (d p : ℤ) : ℤ := if p = 0 ∨ p = d - 1 then 1 else 2

def pairWeight (m n : ℤ) (c : List ℤ) : ℤ :=
  match c with
  | [x, y] => fd m x * fd n y
  | _ => 0

def ValidInput (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  2 ≤ m.val ∧ m.val ≤ 100000 ∧ 2 ≤ n.val ∧ n.val ≤ 100000 ∧
  coordinates.val.length ≤ 10000 ∧
  (∀ v : alloc.vec.Vec Std.I64, v ∈ coordinates.val → v.val.length = 2) ∧
  (∀ c : List ℤ, c ∈ coordPairs coordinates →
    ∃ x y : ℤ, c = [x, y] ∧ 0 ≤ x ∧ x < m.val ∧ 0 ≤ y ∧ y < n.val) ∧
  (coordPairs coordinates).Nodup

def IsTranspose (coordinates coordinates' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  coordPairs coordinates' = (coordPairs coordinates).map (fun c => c.reverse)

def IsPermutationOf (coordinates coordinates' : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  coordinates'.val.Perm coordinates.val

/-- The function returns a result r such that len(r) = 5 and, for every t with 0 <= t <= 4, r[t] equals the number of pairs (i,j) with 0 <= i < m-1 and 0 <= j < n-1 for which exactly t of the four cells (i,j), (i+1,j), (i,j+1), (i+1,j+1) are black. A cell (x,y) with 0 <= x < m and 0 <= y < n is black iff there exists k with 0 <= k < len(coordinates), coordinates[k][0] = x, and coordinates[k][1] = y.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_1 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r ∧
      r.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 →
        vecEntry r t = some ((blockCount m.val n.val coordinates t : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r ∧
      r.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 →
        vecEntry r t = some ((blockCount m.val n.val coordinates t : ℕ) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail (no overflow, panic, out-of-bounds access, or allocation failure).
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_2 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 5.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_3 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r → r.val.length = 5 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r → r.val.length = 5) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t <= 4, r[t] >= 0.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_4 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 → ∃ c : ℤ, vecEntry r t = some c ∧ 0 ≤ c := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 → ∃ c : ℤ, vecEntry r t = some c ∧ 0 ≤ c) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t <= 4, r[t] <= (m-1)*(n-1).
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_5 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 →
        ∃ c : ℤ, vecEntry r t = some c ∧ c ≤ (m.val - 1) * (n.val - 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 →
        ∃ c : ℤ, vecEntry r t = some c ∧ c ≤ (m.val - 1) * (n.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, r[0] + r[1] + r[2] + r[3] + r[4] = (m-1)*(n-1).
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_6 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∃ a0 a1 a2 a3 a4 : ℤ,
        vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧ vecEntry r 2 = some a2 ∧
        vecEntry r 3 = some a3 ∧ vecEntry r 4 = some a4 ∧
        a0 + a1 + a2 + a3 + a4 = (m.val - 1) * (n.val - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∃ a0 a1 a2 a3 a4 : ℤ,
        vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧ vecEntry r 2 = some a2 ∧
        vecEntry r 3 = some a3 ∧ vecEntry r 4 = some a4 ∧
        a0 + a1 + a2 + a3 + a4 = (m.val - 1) * (n.val - 1)) := by
  sorry

/-- Whenever the function returns a result r, 0*r[0] + 1*r[1] + 2*r[2] + 3*r[3] + 4*r[4] = sum_{k=0}^{len(coordinates)-1} f_m(coordinates[k][0]) * f_n(coordinates[k][1]), where for d >= 2 and 0 <= p < d, f_d(p) = 1 if p = 0 or p = d-1, and f_d(p) = 2 otherwise.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_7 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∃ a0 a1 a2 a3 a4 : ℤ,
        vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧ vecEntry r 2 = some a2 ∧
        vecEntry r 3 = some a3 ∧ vecEntry r 4 = some a4 ∧
        0 * a0 + 1 * a1 + 2 * a2 + 3 * a3 + 4 * a4 =
          ((coordPairs coordinates).map (pairWeight m.val n.val)).sum := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∃ a0 a1 a2 a3 a4 : ℤ,
        vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧ vecEntry r 2 = some a2 ∧
        vecEntry r 3 = some a3 ∧ vecEntry r 4 = some a4 ∧
        0 * a0 + 1 * a1 + 2 * a2 + 3 * a3 + 4 * a4 =
          ((coordPairs coordinates).map (pairWeight m.val n.val)).sum) := by
  sorry

/-- Whenever the function returns a result r, r[0] = (m-1)*(n-1) and r[1] = r[2] = r[3] = r[4] = 0.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. Additionally, len(coordinates) = 0. -/
theorem spec_8 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (h0 : coordinates.val.length = 0) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      vecEntry r 0 = some ((m.val - 1) * (n.val - 1)) ∧
      vecEntry r 1 = some 0 ∧ vecEntry r 2 = some 0 ∧
      vecEntry r 3 = some 0 ∧ vecEntry r 4 = some 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (h0 : coordinates.val.length = 0), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      vecEntry r 0 = some ((m.val - 1) * (n.val - 1)) ∧
      vecEntry r 1 = some 0 ∧ vecEntry r 2 = some 0 ∧
      vecEntry r 3 = some 0 ∧ vecEntry r 4 = some 0) := by
  sorry

/-- Whenever the function returns a result r, letting x = coordinates[0][0] and y = coordinates[0][1], we have r[1] = f_m(x) * f_n(y), r[0] = (m-1)*(n-1) - r[1], and r[2] = r[3] = r[4] = 0, where for d >= 2 and 0 <= p < d, f_d(p) = 1 if p = 0 or p = d-1, and f_d(p) = 2 otherwise.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. Additionally, len(coordinates) = 1. -/
theorem spec_9 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (h1 : coordinates.val.length = 1) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ x y : ℤ, coordPairs coordinates = [[x, y]] →
        ∃ a0 a1 : ℤ,
          vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧
          a1 = fd m.val x * fd n.val y ∧
          a0 = (m.val - 1) * (n.val - 1) - a1 ∧
          vecEntry r 2 = some 0 ∧ vecEntry r 3 = some 0 ∧ vecEntry r 4 = some 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (h1 : coordinates.val.length = 1), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ x y : ℤ, coordPairs coordinates = [[x, y]] →
        ∃ a0 a1 : ℤ,
          vecEntry r 0 = some a0 ∧ vecEntry r 1 = some a1 ∧
          a1 = fd m.val x * fd n.val y ∧
          a0 = (m.val - 1) * (n.val - 1) - a1 ∧
          vecEntry r 2 = some 0 ∧ vecEntry r 3 = some 0 ∧ vecEntry r 4 = some 0) := by
  sorry

/-- Whenever the function returns a result r, for every integer t with 0 <= t <= 4 and t > len(coordinates), r[t] = 0.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. -/
theorem spec_10 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 → coordinates.val.length < t → vecEntry r t = some 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 → coordinates.val.length < t → vecEntry r t = some 0) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t <= 4, r[t] = 1 if t = len(coordinates), and r[t] = 0 otherwise.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. Additionally, m = 2 and n = 2. -/
theorem spec_11 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (hm : m.val = 2) (hn : n.val = 2) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 →
        vecEntry r t = some (if t = coordinates.val.length then (1 : ℤ) else (0 : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (hm : m.val = 2) (hn : n.val = 2), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      ∀ t : ℕ, t ≤ 4 →
        vecEntry r t = some (if t = coordinates.val.length then (1 : ℤ) else (0 : ℤ))) := by
  sorry

/-- For every valid input (m, n, coordinates) with result r, if coordinates' is obtained by replacing each coordinates[k] = [x, y] with [y, x] and the function returns r' on (n, m, coordinates'), then len(r) = len(r') = 5 and r[t] = r'[t] for every t with 0 <= t <= 4.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. The same preconditions are assumed for the transposed input (n, m, coordinates'), where coordinates' is obtained from coordinates by replacing each pair [x, y] with [y, x]. -/
theorem spec_12 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates)
    (coordinates' : Slice (alloc.vec.Vec Std.I64)) (h' : ValidInput n m coordinates')
    (htr : IsTranspose coordinates coordinates') :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      Aegis.CountBlackBlocks.count_black_blocks n m coordinates' = ok r' →
      r.val.length = 5 ∧ r'.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 → vecEntry r t = vecEntry r' t := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates)
    (coordinates' : Slice (alloc.vec.Vec Std.I64)) (h' : ValidInput n m coordinates')
    (htr : IsTranspose coordinates coordinates'), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      Aegis.CountBlackBlocks.count_black_blocks n m coordinates' = ok r' →
      r.val.length = 5 ∧ r'.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 → vecEntry r t = vecEntry r' t) := by
  sorry

/-- For every valid input (m, n, coordinates) with result r and every valid input (m, n, coordinates') with result r', where coordinates' is a permutation of coordinates, we have len(r) = len(r') = 5 and r[t] = r'[t] for every t with 0 <= t <= 4.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. coordinates' is a permutation of coordinates: it has the same length and there exists a bijection pi of {0, ..., len(coordinates)-1} such that coordinates'[k] = coordinates[pi(k)] for all k. -/
theorem spec_13 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates)
    (coordinates' : Slice (alloc.vec.Vec Std.I64)) (h' : ValidInput m n coordinates')
    (hperm : IsPermutationOf coordinates coordinates') :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates' = ok r' →
      r.val.length = 5 ∧ r'.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 → vecEntry r t = vecEntry r' t := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates)
    (coordinates' : Slice (alloc.vec.Vec Std.I64)) (h' : ValidInput m n coordinates')
    (hperm : IsPermutationOf coordinates coordinates'), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates' = ok r' →
      r.val.length = 5 ∧ r'.val.length = 5 ∧
      ∀ t : ℕ, t ≤ 4 → vecEntry r t = vecEntry r' t) := by
  sorry

/-- Whenever the function returns a result r, r[4] = (m-1)*(n-1) and r[0] = r[1] = r[2] = r[3] = 0.
  Preconditions: m and n are integers with 2 <= m <= 100000 and 2 <= n <= 100000. coordinates is a slice of vectors; for every k with 0 <= k < len(coordinates), len(coordinates[k]) = 2 and if coordinates[k] = [x, y] then 0 <= x < m and 0 <= y < n. len(coordinates) <= 10000. The pairs coordinates[k] are pairwise distinct: there is no k1 != k2 with coordinates[k1] = coordinates[k2]. Additionally, len(coordinates) = m*n, so every grid cell is black. -/
theorem spec_14 (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (hlen : (coordinates.val.length : ℤ) = m.val * n.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      vecEntry r 4 = some ((m.val - 1) * (n.val - 1)) ∧
      vecEntry r 0 = some 0 ∧ vecEntry r 1 = some 0 ∧
      vecEntry r 2 = some 0 ∧ vecEntry r 3 = some 0 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (m n : Std.I64) (coordinates : Slice (alloc.vec.Vec Std.I64))
    (h : ValidInput m n coordinates) (hlen : (coordinates.val.length : ℤ) = m.val * n.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.CountBlackBlocks.count_black_blocks m n coordinates = ok r →
      vecEntry r 4 = some ((m.val - 1) * (n.val - 1)) ∧
      vecEntry r 0 = some 0 ∧ vecEntry r 1 = some 0 ∧
      vecEntry r 2 = some 0 ∧ vecEntry r 3 = some 0) := by
  sorry

end AegisSpec.CountBlackBlocks
