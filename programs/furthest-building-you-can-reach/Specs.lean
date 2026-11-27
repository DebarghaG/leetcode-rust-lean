import Aegis.FurthestBuilding.Code.Funs

/-!
# Specifications of `Aegis.FurthestBuilding.furthest_building`

LeetCode problem `furthest-building-you-can-reach`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FurthestBuilding

namespace AegisSpec.FurthestBuilding

def hlen (heights : Slice Std.I64) : ℕ :=
  heights.val.length

def hget (heights : Slice Std.I64) (i : ℕ) : ℤ :=
  match heights.val[i]? with
  | some x => x.val
  | none => 0

def upSteps (heights : Slice Std.I64) (k : ℕ) : Finset ℕ :=
  (Finset.range k).filter fun i => hget heights i < hget heights (i + 1)

def brickCost (heights : Slice Std.I64) (S : Finset ℕ) (k : ℕ) : ℤ :=
  ∑ i ∈ upSteps heights k \ S, (hget heights (i + 1) - hget heights i)

def Reachable (heights : Slice Std.I64) (bricks ladders : ℤ) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ upSteps heights k ∧ (S.card : ℤ) ≤ ladders ∧ brickCost heights S k ≤ bricks

def shiftI64 (x : Std.I64) (C : ℤ) (h : 1 ≤ x.val + C ∧ x.val + C ≤ 1000000) : Std.I64 :=
  IScalar.ofInt (ty := .I64) (x.val + C) (by
    have h1 := h.1
    have h2 := h.2
    show I64.rMin ≤ x.val + C ∧ x.val + C ≤ I64.rMax
    simp only [I64.rMin, I64.rMax]
    omega)

def listNOfList {α : Type} : (l : List α) → Aeneas.Data.ListN.ListN α l.length
  | [] => .nil
  | a :: l => .cons a (listNOfList l)

def shiftList (l : List Std.I64) (C : ℤ)
    (hC : ∀ x, x ∈ l → 1 ≤ x.val + C ∧ x.val + C ≤ 1000000) : List Std.I64 :=
  l.attach.map fun p => shiftI64 p.1 C (hC p.1 p.2)

theorem shiftList_length {l : List Std.I64} {C : ℤ}
    {hC : ∀ x, x ∈ l → 1 ≤ x.val + C ∧ x.val + C ≤ 1000000} :
    (shiftList l C hC).length = l.length := by
  simp [shiftList, List.length_map, List.length_attach]

theorem listN_toList_length {α : Type} {n : ℕ} (l : Aeneas.Data.ListN.ListN α n) :
    l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

theorem slice_val_length (s : Slice Std.I64) : s.val.length = s.leng :=
  listN_toList_length s.list

def shiftSlice (heights : Slice Std.I64) (C : ℤ)
    (hC : ∀ x, x ∈ heights.val → 1 ≤ x.val + C ∧ x.val + C ≤ 1000000) : Slice Std.I64 :=
  Slice.mk heights.leng
    (by
      have h1 : (shiftList heights.val C hC).length = heights.val.length := shiftList_length
      have h2 : heights.val.length = heights.leng := slice_val_length heights
      exact h1.trans h2 ▸ listNOfList (shiftList heights.val C hC))
    heights.bound

/-- Let n = len(heights). For 0 <= k < n, call k reachable if there exists a set S of indices i with 0 <= i < k and heights[i] < heights[i+1] such that |S| <= ladders and the sum, over all i with 0 <= i < k and heights[i] < heights[i+1] and i not in S, of (heights[i+1] - heights[i]) is at most bricks (empty sums are 0). The function returns a result r such that 0 <= r < n, r is reachable, and for every k with r < k < n, k is not reachable.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights). -/
theorem spec_1 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      Reachable heights bricks.val ladders.val r.val.toNat ∧
      (∀ k : ℕ, r.val < (k : ℤ) → (k : ℤ) < (hlen heights : ℤ) →
        ¬ Reachable heights bricks.val ladders.val k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      Reachable heights bricks.val ladders.val r.val.toNat ∧
      (∀ k : ℕ, r.val < (k : ℤ) → (k : ℤ) < (hlen heights : ℤ) →
        ¬ Reachable heights bricks.val ladders.val k)) := by
  sorry

/-- The function returns a result r and 0 <= r < len(heights).
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights). -/
theorem spec_2 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ)) := by
  sorry

/-- The function returns a result and does not fail for every heights, bricks, and ladders satisfying the preconditions.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights). -/
theorem spec_3 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64, furthest_building heights bricks ladders = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64, furthest_building heights bricks ladders = ok r) := by
  sorry

/-- The function returns 0.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights); len(heights) = 1. -/
theorem spec_4 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_len_one : hlen heights = 1) :
    furthest_building heights bricks ladders = ok 0#i64 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_len_one : hlen heights = 1), furthest_building heights bricks ladders = ok 0#i64) := by
  sorry

/-- The function returns len(heights)-1.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights); for every i with 0 <= i < len(heights)-1, heights[i] >= heights[i+1]. -/
theorem spec_5 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_nonincr : ∀ i : ℕ, i < hlen heights - 1 → hget heights i ≥ hget heights (i + 1)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧ r.val = (hlen heights : ℤ) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_nonincr : ∀ i : ℕ, i < hlen heights - 1 → hget heights i ≥ hget heights (i + 1)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧ r.val = (hlen heights : ℤ) - 1) := by
  sorry

/-- Let n = len(heights). The function returns r where: if there exists j with 0 <= j < n-1 and heights[j] < heights[j+1], then r is the least such j; otherwise r = n-1.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; bricks = 0; ladders = 0; 0 <= ladders <= len(heights). -/
theorem spec_6 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_zero : bricks.val = 0)
    (h_ladders_zero : ladders.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      ((∃ j : ℕ, j < hlen heights - 1 ∧ hget heights j < hget heights (j + 1)) →
        r.val.toNat < hlen heights - 1 ∧
        hget heights r.val.toNat < hget heights (r.val.toNat + 1) ∧
        (∀ j : ℕ, j < r.val.toNat → ¬ (hget heights j < hget heights (j + 1)))) ∧
      (¬ (∃ j : ℕ, j < hlen heights - 1 ∧ hget heights j < hget heights (j + 1)) →
        r.val = (hlen heights : ℤ) - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_zero : bricks.val = 0)
    (h_ladders_zero : ladders.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      ((∃ j : ℕ, j < hlen heights - 1 ∧ hget heights j < hget heights (j + 1)) →
        r.val.toNat < hlen heights - 1 ∧
        hget heights r.val.toNat < hget heights (r.val.toNat + 1) ∧
        (∀ j : ℕ, j < r.val.toNat → ¬ (hget heights j < hget heights (j + 1)))) ∧
      (¬ (∃ j : ℕ, j < hlen heights - 1 ∧ hget heights j < hget heights (j + 1)) →
        r.val = (hlen heights : ℤ) - 1)) := by
  sorry

/-- Let n = len(heights). The function returns the largest r with 0 <= r < n such that the number of indices i satisfying 0 <= i < r and heights[i] < heights[i+1] is at most ladders.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; bricks = 0; 0 <= ladders <= len(heights). -/
theorem spec_7 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_zero : bricks.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      ((upSteps heights r.val.toNat).card : ℤ) ≤ ladders.val ∧
      (∀ k : ℕ, (k : ℤ) < (hlen heights : ℤ) →
        ((upSteps heights k).card : ℤ) ≤ ladders.val → k ≤ r.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_zero : bricks.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      ((upSteps heights r.val.toNat).card : ℤ) ≤ ladders.val ∧
      (∀ k : ℕ, (k : ℤ) < (hlen heights : ℤ) →
        ((upSteps heights k).card : ℤ) ≤ ladders.val → k ≤ r.val.toNat)) := by
  sorry

/-- Let n = len(heights). The function returns the largest r with 0 <= r < n such that the sum, over all i with 0 <= i < r and heights[i] < heights[i+1], of (heights[i+1] - heights[i]) is at most bricks (empty sums are 0).
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; ladders = 0; 0 <= ladders <= len(heights). -/
theorem spec_8 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_zero : ladders.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      (∑ i ∈ upSteps heights r.val.toNat,
        (hget heights (i + 1) - hget heights i)) ≤ bricks.val ∧
      (∀ k : ℕ, (k : ℤ) < (hlen heights : ℤ) →
        (∑ i ∈ upSteps heights k, (hget heights (i + 1) - hget heights i)) ≤ bricks.val →
        k ≤ r.val.toNat) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_zero : ladders.val = 0)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∃ r : Std.I64,
      furthest_building heights bricks ladders = ok r ∧
      0 ≤ r.val ∧ r.val < (hlen heights : ℤ) ∧
      (∑ i ∈ upSteps heights r.val.toNat,
        (hget heights (i + 1) - hget heights i)) ≤ bricks.val ∧
      (∀ k : ℕ, (k : ℤ) < (hlen heights : ℤ) →
        (∑ i ∈ upSteps heights k, (hget heights (i + 1) - hget heights i)) ≤ bricks.val →
        k ≤ r.val.toNat)) := by
  sorry

/-- Let r1 be the result returned by furthest_building heights bricks1 ladders and let r2 be the result returned by furthest_building heights bricks2 ladders. Then r1 <= r2.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= ladders <= len(heights); 0 <= bricks1 <= bricks2 <= 1000000000. -/
theorem spec_9 (heights : Slice Std.I64) (bricks1 bricks2 ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_bricks1_lo : 0 ≤ bricks1.val)
    (h_bricks_le : bricks1.val ≤ bricks2.val)
    (h_bricks2_hi : bricks2.val ≤ 1000000000) :
    ∀ r1 r2 : Std.I64,
      furthest_building heights bricks1 ladders = ok r1 →
      furthest_building heights bricks2 ladders = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks1 bricks2 ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_bricks1_lo : 0 ≤ bricks1.val)
    (h_bricks_le : bricks1.val ≤ bricks2.val)
    (h_bricks2_hi : bricks2.val ≤ 1000000000), ∀ r1 r2 : Std.I64,
      furthest_building heights bricks1 ladders = ok r1 →
      furthest_building heights bricks2 ladders = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Let r1 be the result returned by furthest_building heights bricks ladders1 and let r2 be the result returned by furthest_building heights bricks ladders2. Then r1 <= r2.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders1 <= ladders2 <= len(heights). -/
theorem spec_10 (heights : Slice Std.I64) (bricks ladders1 ladders2 : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders1_lo : 0 ≤ ladders1.val)
    (h_ladders_le : ladders1.val ≤ ladders2.val)
    (h_ladders2_hi : ladders2.val ≤ (hlen heights : ℤ)) :
    ∀ r1 r2 : Std.I64,
      furthest_building heights bricks ladders1 = ok r1 →
      furthest_building heights bricks ladders2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders1 ladders2 : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders1_lo : 0 ≤ ladders1.val)
    (h_ladders_le : ladders1.val ≤ ladders2.val)
    (h_ladders2_hi : ladders2.val ≤ (hlen heights : ℤ)), ∀ r1 r2 : Std.I64,
      furthest_building heights bricks ladders1 = ok r1 →
      furthest_building heights bricks ladders2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r, then there exists a set S of indices i with 0 <= i < r and heights[i] < heights[i+1] such that |S| <= ladders and the sum, over all i with 0 <= i < r and heights[i] < heights[i+1] and i not in S, of (heights[i+1] - heights[i]) is at most bricks (empty sums are 0).
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights). -/
theorem spec_11 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      ∃ S : Finset ℕ,
        S ⊆ upSteps heights r.val.toNat ∧
        (S.card : ℤ) ≤ ladders.val ∧
        brickCost heights S r.val.toNat ≤ bricks.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      ∃ S : Finset ℕ,
        S ⊆ upSteps heights r.val.toNat ∧
        (S.card : ℤ) ≤ ladders.val ∧
        brickCost heights S r.val.toNat ≤ bricks.val) := by
  sorry

/-- If the function returns r and r < len(heights)-1, then building r+1 is not reachable; equivalently, for every set S of indices i with 0 <= i < r+1 and heights[i] < heights[i+1] such that |S| <= ladders, the sum, over all i with 0 <= i < r+1 and heights[i] < heights[i+1] and i not in S, of (heights[i+1] - heights[i]) is greater than bricks.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights). -/
theorem spec_12 (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)) :
    ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      r.val < (hlen heights : ℤ) - 1 →
      ∀ S : Finset ℕ,
        S ⊆ upSteps heights (r.val.toNat + 1) →
        (S.card : ℤ) ≤ ladders.val →
        bricks.val < brickCost heights S (r.val.toNat + 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ)), ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      r.val < (hlen heights : ℤ) - 1 →
      ∀ S : Finset ℕ,
        S ⊆ upSteps heights (r.val.toNat + 1) →
        (S.card : ℤ) ≤ ladders.val →
        bricks.val < brickCost heights S (r.val.toNat + 1)) := by
  sorry

/-- Let shifted be the slice of length len(heights) with shifted[i] = heights[i] + C for every i with 0 <= i < len(heights). If furthest_building heights bricks ladders returns r, then furthest_building shifted bricks ladders returns r.
  Preconditions: 1 <= len(heights) <= 100000; for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000; 0 <= bricks <= 1000000000; 0 <= ladders <= len(heights); C is an integer such that for every i with 0 <= i < len(heights), 1 <= heights[i] + C <= 1000000. -/
theorem spec_13 (heights : Slice Std.I64) (bricks ladders : Std.I64) (C : ℤ)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_shift : ∀ x : Std.I64, x ∈ heights.val → 1 ≤ x.val + C ∧ x.val + C ≤ 1000000) :
    ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      furthest_building (shiftSlice heights C h_shift) bricks ladders = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (heights : Slice Std.I64) (bricks ladders : Std.I64) (C : ℤ)
    (h_len_ge : 1 ≤ hlen heights) (h_len_le : hlen heights ≤ 100000)
    (h_heights : ∀ i : ℕ, i < hlen heights → 1 ≤ hget heights i ∧ hget heights i ≤ 1000000)
    (h_bricks_lo : 0 ≤ bricks.val) (h_bricks_hi : bricks.val ≤ 1000000000)
    (h_ladders_lo : 0 ≤ ladders.val) (h_ladders_hi : ladders.val ≤ (hlen heights : ℤ))
    (h_shift : ∀ x : Std.I64, x ∈ heights.val → 1 ≤ x.val + C ∧ x.val + C ≤ 1000000), ∀ r : Std.I64,
      furthest_building heights bricks ladders = ok r →
      furthest_building (shiftSlice heights C h_shift) bricks ladders = ok r) := by
  sorry

end AegisSpec.FurthestBuilding
