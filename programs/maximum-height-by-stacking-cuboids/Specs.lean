import Aegis.MaxHeight.Code.Funs

/-!
# Specifications of `Aegis.MaxHeight.max_height`

LeetCode problem `maximum-height-by-stacking-cuboids`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxHeight

open Aegis.MaxHeight

def rows (cuboids : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  (cuboids.val).map (fun c => (c.val).map (fun x => x.val))

def row (cuboids : Slice (alloc.vec.Vec I64)) (i : ℕ) : List Int :=
  (rows cuboids).getD i []

def entry (cuboids : Slice (alloc.vec.Vec I64)) (i j : ℕ) : Int :=
  (row cuboids i).getD j 0

def max3 (x y z : Int) : Int := max x (max y z)

def maxDim (cuboids : Slice (alloc.vec.Vec I64)) (i : ℕ) : Int :=
  max3 (entry cuboids i 0) (entry cuboids i 1) (entry cuboids i 2)

def maxDimOver (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ) : Int :=
  ((List.range n).map (maxDim cuboids)).foldr max 0

def sumMaxDim (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ) : Int :=
  ((List.range n).map (maxDim cuboids)).sum

structure Box where

  w : Int

  l : Int

  h : Int

namespace Box

def IsOrient (b : Box) (row : List Int) : Prop :=
  [b.w, b.l, b.h].Perm row

end Box

def FitsOn (lower upper : Box) : Prop :=
  upper.w ≤ lower.w ∧ upper.l ≤ lower.l ∧ upper.h ≤ lower.h

def StackOK (rows : List (List Int)) (s : List (ℕ × Box)) : Prop :=
  (s.map Prod.fst).Nodup ∧
  (∀ p ∈ s, p.1 < rows.length ∧ p.2.IsOrient (rows.getD p.1 [])) ∧
  List.IsChain FitsOn (s.map Prod.snd)

def StackHeight (s : List (ℕ × Box)) : Int :=
  (s.map (fun p => p.2.h)).sum

def IsMaxStackHeight (rows : List (List Int)) (r : Int) : Prop :=
  (∃ s, s ≠ [] ∧ StackOK rows s ∧ StackHeight s = r) ∧
    (∀ s, s ≠ [] → StackOK rows s → StackHeight s ≤ r)

/-- The function returns a result r, and r is the maximum, over all nonempty finite sequences of distinct indices i_0, ..., i_{m-1} with 0 <= i_k < n and all choices of orientations (w_k, l_k, h_k) such that (w_k, l_k, h_k) is a permutation of the three entries of cuboids[i_k], satisfying w_{k+1} <= w_k, l_{k+1} <= l_k, and h_{k+1} <= h_k for every k with 0 <= k < m-1, of the total height h_0 + ... + h_{m-1}. Here i_0 is the bottom cuboid and i_{m-1} is the top cuboid.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_1 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∃ r, Aegis.MaxHeight.max_height cuboids = ok r ∧ IsMaxStackHeight (rows cuboids) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∃ r, Aegis.MaxHeight.max_height cuboids = ok r ∧ IsMaxStackHeight (rows cuboids) r.val) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_2 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∃ r, Aegis.MaxHeight.max_height cuboids = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∃ r, Aegis.MaxHeight.max_height cuboids = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= max_{0 <= i < n} max(cuboids[i][0], cuboids[i][1], cuboids[i][2]).
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_3 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r → maxDimOver cuboids n ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r → maxDimOver cuboids n ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} max(cuboids[i][0], cuboids[i][1], cuboids[i][2]).
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_4 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r → r.val ≤ sumMaxDim cuboids n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r → r.val ≤ sumMaxDim cuboids n) := by
  sorry

/-- Whenever the function returns a result r, there exist a nonempty sequence of distinct indices i_0, ..., i_{m-1} and orientations (w_k, l_k, h_k), each a permutation of cuboids[i_k]'s three entries, such that w_{k+1} <= w_k, l_{k+1} <= l_k, and h_{k+1} <= h_k for all 0 <= k < m-1, and h_0 + ... + h_{m-1} = r.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_5 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∃ s : List (ℕ × Box), s ≠ [] ∧ StackOK (rows cuboids) s ∧ StackHeight s = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∃ s : List (ℕ × Box), s ≠ [] ∧ StackOK (rows cuboids) s ∧ StackHeight s = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every nonempty sequence of distinct indices i_0, ..., i_{m-1} and orientations (w_k, l_k, h_k), each a permutation of cuboids[i_k]'s three entries, if w_{k+1} <= w_k, l_{k+1} <= l_k, and h_{k+1} <= h_k for all 0 <= k < m-1, then h_0 + ... + h_{m-1} <= r.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_6 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∀ s : List (ℕ × Box), s ≠ [] → StackOK (rows cuboids) s → StackHeight s ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∀ s : List (ℕ × Box), s ≠ [] → StackOK (rows cuboids) s → StackHeight s ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = max(cuboids[0][0], cuboids[0][1], cuboids[0][2]).
  Preconditions: Let n = len(cuboids). Assume n = 1, len(cuboids[0]) = 3, and 1 <= cuboids[0][0], cuboids[0][1], cuboids[0][2] <= 100. -/
theorem spec_7 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_one : n = 1)
    (h_row : (row cuboids 0).length = 3)
    (h_bounds : ∀ j, j < 3 → 1 ≤ entry cuboids 0 j ∧ entry cuboids 0 j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      r.val = max (entry cuboids 0 0) (max (entry cuboids 0 1) (entry cuboids 0 2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_one : n = 1)
    (h_row : (row cuboids 0).length = 3)
    (h_bounds : ∀ j, j < 3 → 1 ≤ entry cuboids 0 j ∧ entry cuboids 0 j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      r.val = max (entry cuboids 0 0) (max (entry cuboids 0 1) (entry cuboids 0 2))) := by
  sorry

/-- Whenever the function returns a result r, r = n * max(cuboids[0][0], cuboids[0][1], cuboids[0][2]).
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. Also assume that for every i with 0 <= i < n, the three entries of cuboids[i] are a permutation of cuboids[0][0], cuboids[0][1], cuboids[0][2]. -/
theorem spec_8 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_perm : ∀ i, i < n → (row cuboids i).Perm (row cuboids 0)) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      r.val = (n : Int) * max (entry cuboids 0 0) (max (entry cuboids 0 1) (entry cuboids 0 2)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_perm : ∀ i, i < n → (row cuboids i).Perm (row cuboids 0)), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      r.val = (n : Int) * max (entry cuboids 0 0) (max (entry cuboids 0 1) (entry cuboids 0 2))) := by
  sorry

/-- If the function returns r on input cuboids and r2 on input cuboids2, then r2 = r.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. Let cuboids2 be a slice of length n also satisfying the same constraints, and assume there is a bijection sigma on {0, ..., n-1} such that cuboids2[j] = cuboids[sigma(j)] for every j with 0 <= j < n. -/
theorem spec_9 (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_bij : ∃ sigma : Fin n → Fin n, Function.Bijective sigma ∧
      ∀ j : Fin n, row cuboids2 j.val = row cuboids (sigma j).val) :
    ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_bij : ∃ sigma : Fin n → Fin n, Function.Bijective sigma ∧
      ∀ j : Fin n, row cuboids2 j.val = row cuboids (sigma j).val), ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val = r.val) := by
  sorry

/-- If the function returns r on input cuboids and r2 on input cuboids2, then r2 = k * r.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. Let k be a positive integer, and let cuboids2 be a slice of length n satisfying the same constraints and such that cuboids2[i][j] = k * cuboids[i][j] for every i with 0 <= i < n and j in {0, 1, 2}. -/
theorem spec_10 (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n k : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_k : 0 < k)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_scale : ∀ i j, i < n → j < 3 →
      entry cuboids2 i j = (k : Int) * entry cuboids i j) :
    ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val = (k : Int) * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n k : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_k : 0 < k)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_scale : ∀ i j, i < n → j < 3 →
      entry cuboids2 i j = (k : Int) * entry cuboids i j), ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val = (k : Int) * r.val) := by
  sorry

/-- If the function returns r on input cuboids and r2 on input cuboids2, then r2 >= r.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. Let cuboids2 be a slice of length n+1 satisfying the same constraints, with cuboids2[i] = cuboids[i] for every i with 0 <= i < n. -/
theorem spec_11 (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n + 1)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_le2 : n + 1 ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n + 1 → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n + 1 → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_agree : ∀ i, i < n → row cuboids2 i = row cuboids i) :
    ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n + 1)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_le2 : n + 1 ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n + 1 → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n + 1 → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_agree : ∀ i, i < n → row cuboids2 i = row cuboids i), ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- If the function returns r on input cuboids and r2 on input cuboids2, then r2 <= r + M.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. Let cuboids2 be a slice of length n+1 satisfying the same constraints, with cuboids2[i] = cuboids[i] for every i with 0 <= i < n. Let M = max(cuboids2[n][0], cuboids2[n][1], cuboids2[n][2]). -/
theorem spec_12 (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ) (M : Int)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n + 1)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_le2 : n + 1 ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n + 1 → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n + 1 → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_agree : ∀ i, i < n → row cuboids2 i = row cuboids i)
    (h_M : M = max (entry cuboids2 n 0) (max (entry cuboids2 n 1) (entry cuboids2 n 2))) :
    ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val ≤ r.val + M := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cuboids cuboids2 : Slice (alloc.vec.Vec I64)) (n : ℕ) (M : Int)
    (h_n : (cuboids.val).length = n) (h_n2 : (cuboids2.val).length = n + 1)
    (h_pos : 1 ≤ n) (h_le : n ≤ 100) (h_le2 : n + 1 ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100)
    (h_row2 : ∀ i, i < n + 1 → (row cuboids2 i).length = 3)
    (h_bounds2 : ∀ i j, i < n + 1 → j < 3 → 1 ≤ entry cuboids2 i j ∧ entry cuboids2 i j ≤ 100)
    (h_agree : ∀ i, i < n → row cuboids2 i = row cuboids i)
    (h_M : M = max (entry cuboids2 n 0) (max (entry cuboids2 n 1) (entry cuboids2 n 2))), ∀ r r2, Aegis.MaxHeight.max_height cuboids = ok r →
      Aegis.MaxHeight.max_height cuboids2 = ok r2 → r2.val ≤ r.val + M) := by
  sorry

/-- Whenever the function returns a result r, there exist an integer m with 1 <= m <= n, distinct indices i_0, ..., i_{m-1} in {0, ..., n-1}, and for each k an integer d_k in {cuboids[i_k][0], cuboids[i_k][1], cuboids[i_k][2]}, such that r = d_0 + ... + d_{m-1}.
  Preconditions: Let n = len(cuboids). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, len(cuboids[i]) = 3 and 1 <= cuboids[i][0], cuboids[i][1], cuboids[i][2] <= 100. -/
theorem spec_13 (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100) :
    ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∃ (m : ℕ) (is : List ℕ) (ds : List Int),
        1 ≤ m ∧ m ≤ n ∧ is.length = m ∧ is.Nodup ∧ (∀ i ∈ is, i < n) ∧
          List.Forall₂ (fun i d =>
            d = entry cuboids i 0 ∨ d = entry cuboids i 1 ∨ d = entry cuboids i 2) is ds ∧
          r.val = ds.sum := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cuboids : Slice (alloc.vec.Vec I64)) (n : ℕ)
    (h_n : (cuboids.val).length = n) (h_pos : 1 ≤ n) (h_le : n ≤ 100)
    (h_row : ∀ i, i < n → (row cuboids i).length = 3)
    (h_bounds : ∀ i j, i < n → j < 3 → 1 ≤ entry cuboids i j ∧ entry cuboids i j ≤ 100), ∀ r, Aegis.MaxHeight.max_height cuboids = ok r →
      ∃ (m : ℕ) (is : List ℕ) (ds : List Int),
        1 ≤ m ∧ m ≤ n ∧ is.length = m ∧ is.Nodup ∧ (∀ i ∈ is, i < n) ∧
          List.Forall₂ (fun i d =>
            d = entry cuboids i 0 ∨ d = entry cuboids i 1 ∨ d = entry cuboids i 2) is ds ∧
          r.val = ds.sum) := by
  sorry

end AegisSpec.MaxHeight
