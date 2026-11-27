import Aegis.LastStoneWeightIi.Code.Funs

/-!
# Specifications of `Aegis.LastStoneWeightIi.last_stone_weight_ii`

LeetCode problem `last-stone-weight-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LastStoneWeightIi (last_stone_weight_ii)

namespace AegisSpec.LastStoneWeightIi

def totalSum (stones : Slice Std.I64) : ℤ :=
  (stones.val.map fun x => x.val).sum

def subsetSum (stones : Slice Std.I64) (A : Finset (Fin stones.val.length)) : ℤ :=
  ∑ i ∈ A, (stones.val.get i).val

def IsMaxFeasible (stones : Slice Std.I64) (M : ℤ) : Prop :=
  (∃ A : Finset (Fin stones.val.length),
      2 * subsetSum stones A ≤ totalSum stones ∧ subsetSum stones A = M) ∧
    ∀ A : Finset (Fin stones.val.length),
      2 * subsetSum stones A ≤ totalSum stones → subsetSum stones A ≤ M

def maxStone (stones : Slice Std.I64) : ℤ :=
  (stones.val.map fun x => x.val).foldr max 0

theorem val_length_le (stones : Slice Std.I64) : stones.val.length ≤ Usize.max := by
  have h : stones.val.length = stones.leng := Aeneas.Data.ListN.ListN_length stones.list
  rw [h]
  exact stones.bound

def swapStones (stones : Slice Std.I64) (i j : ℕ) : Slice Std.I64 :=
  Slice.mk (stones.val.swap i j).length
    (Aeneas.Data.ListN.ListN.fromList (stones.val.swap i j)) (by
      rw [List.length_swap]
      exact val_length_le stones)

@[simp]
theorem swapStones_val (stones : Slice Std.I64) (i j : ℕ) :
    (swapStones stones i j).val = stones.val.swap i j := by
  simp [swapStones, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- The function returns a result r, and r = T - 2*M, where T = sum_{i=0}^{len(stones)-1} stones[i] and M is the maximum, over all subsets A of {0,1,...,len(stones)-1}, of sum_{i in A} stones[i] subject to 2*(sum_{i in A} stones[i]) <= T. The empty subset is allowed in this maximum.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_1 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∃ r : Std.I64,
      last_stone_weight_ii stones = ok r ∧
        ∃ M : ℤ, IsMaxFeasible stones M ∧ r.val = totalSum stones - 2 * M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∃ r : Std.I64,
      last_stone_weight_ii stones = ok r ∧
        ∃ M : ℤ, IsMaxFeasible stones M ∧ r.val = totalSum stones - 2 * M) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_2 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∃ r : Std.I64, last_stone_weight_ii stones = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∃ r : Std.I64, last_stone_weight_ii stones = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= T, where T = sum_{i=0}^{len(stones)-1} stones[i].
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_3 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      0 ≤ r.val ∧ r.val ≤ totalSum stones := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      0 ≤ r.val ∧ r.val ≤ totalSum stones) := by
  sorry

/-- Whenever the function returns a result r, T - r is even, where T = sum_{i=0}^{len(stones)-1} stones[i]. Equivalently, r and T have the same parity.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_4 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      Even (totalSum stones - r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      Even (totalSum stones - r.val)) := by
  sorry

/-- Whenever the function returns a result r, r <= max_{0 <= i < len(stones)} stones[i].
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_5 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r → r.val ≤ maxStone stones := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r → r.val ≤ maxStone stones) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there exists a subset A of {0,1,...,len(stones)-1} such that 2*(sum_{i in A} stones[i]) = T, where T = sum_{i=0}^{len(stones)-1} stones[i].
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_6 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      (r.val = 0 ↔
        ∃ A : Finset (Fin stones.val.length), 2 * subsetSum stones A = totalSum stones) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      (r.val = 0 ↔
        ∃ A : Finset (Fin stones.val.length), 2 * subsetSum stones A = totalSum stones)) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset A of {0,1,...,len(stones)-1} such that 2*(sum_{i in A} stones[i]) = T - r, where T = sum_{i=0}^{len(stones)-1} stones[i]. Equivalently, sum_{i in A} stones[i] = (T-r)/2.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_7 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∃ A : Finset (Fin stones.val.length),
        2 * subsetSum stones A = totalSum stones - r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∃ A : Finset (Fin stones.val.length),
        2 * subsetSum stones A = totalSum stones - r.val) := by
  sorry

/-- Whenever the function returns a result r, for every subset A of {0,1,...,len(stones)-1}, |T - 2*(sum_{i in A} stones[i])| >= r, where T = sum_{i=0}^{len(stones)-1} stones[i].
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_8 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∀ A : Finset (Fin stones.val.length),
        |totalSum stones - 2 * subsetSum stones A| ≥ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∀ A : Finset (Fin stones.val.length),
        |totalSum stones - 2 * subsetSum stones A| ≥ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every index k with 0 <= k < len(stones) and 2*stones[k] >= T, we have r = 2*stones[k] - T, where T = sum_{i=0}^{len(stones)-1} stones[i].
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_9 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∀ (k : ℕ) (hk : k < stones.val.length),
        2 * (stones.val.get ⟨k, hk⟩).val ≥ totalSum stones →
          r.val = 2 * (stones.val.get ⟨k, hk⟩).val - totalSum stones := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      ∀ (k : ℕ) (hk : k < stones.val.length),
        2 * (stones.val.get ⟨k, hk⟩).val ≥ totalSum stones →
          r.val = 2 * (stones.val.get ⟨k, hk⟩).val - totalSum stones) := by
  sorry

/-- Whenever the function returns a result r, if len(stones) is odd then r = w, and if len(stones) is even then r = 0.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100; there exists w such that for every i with 0 <= i < len(stones), stones[i] = w. -/
theorem spec_10 (stones : Slice Std.I64) (w : Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100)
    (hconst : ∀ (i : ℕ) (h : i < stones.val.length),
      (stones.val.get ⟨i, h⟩).val = w.val) :
    ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      (Odd stones.val.length → r.val = w.val) ∧
        (Even stones.val.length → r.val = 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (stones : Slice Std.I64) (w : Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100)
    (hconst : ∀ (i : ℕ) (h : i < stones.val.length),
      (stones.val.get ⟨i, h⟩).val = w.val), ∀ r : Std.I64, last_stone_weight_ii stones = ok r →
      (Odd stones.val.length → r.val = w.val) ∧
        (Even stones.val.length → r.val = 0)) := by
  sorry

/-- For any indices i and j with 0 <= i < j < len(stones), let swapped be the slice obtained from stones by exchanging the values at positions i and j and leaving all other positions unchanged. Whenever the function returns r on stones and returns r_swapped on swapped, we have r_swapped = r.
  Preconditions: 1 <= len(stones) <= 30; for every index i with 0 <= i < len(stones), 1 <= stones[i] <= 100. -/
theorem spec_11 (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100)
    (i j : ℕ) (hi : i < stones.val.length) (hj : j < stones.val.length) (hij : i < j) :
    ∀ (r : Std.I64), last_stone_weight_ii stones = ok r →
      ∀ (r_swapped : Std.I64),
        last_stone_weight_ii (swapStones stones i j) = ok r_swapped →
          r_swapped.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (stones : Slice Std.I64)
    (hlen1 : 1 ≤ stones.val.length) (hlen30 : stones.val.length ≤ 30)
    (hpos : ∀ (i : ℕ) (h : i < stones.val.length), 1 ≤ (stones.val.get ⟨i, h⟩).val)
    (hle : ∀ (i : ℕ) (h : i < stones.val.length), (stones.val.get ⟨i, h⟩).val ≤ 100)
    (i j : ℕ) (hi : i < stones.val.length) (hj : j < stones.val.length) (hij : i < j), ∀ (r : Std.I64), last_stone_weight_ii stones = ok r →
      ∀ (r_swapped : Std.I64),
        last_stone_weight_ii (swapStones stones i j) = ok r_swapped →
          r_swapped.val = r.val) := by
  sorry

end AegisSpec.LastStoneWeightIi
