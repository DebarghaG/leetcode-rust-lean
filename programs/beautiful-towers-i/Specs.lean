import Aegis.MaximumSumOfHeights.Code.Funs

/-!
# Specifications of `Aegis.MaximumSumOfHeights.maximum_sum_of_heights`

LeetCode problem `beautiful-towers-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumSumOfHeights

def heightAt (heights : Slice Std.I64) (i : Nat) : ℤ := (heights.val.getD i default).val

def seqAt (b : List ℤ) (i : Nat) : ℤ := b.getD i 0

def IsMountain (b : List ℤ) : Prop :=
  ∃ p : Nat, p < b.length ∧
    (∀ i : Nat, i < p → seqAt b i ≤ seqAt b (i + 1)) ∧
    (∀ i : Nat, p ≤ i → i + 1 < b.length → seqAt b (i + 1) ≤ seqAt b i)

def IsBounded (heights : Slice Std.I64) (lo : ℤ) (b : List ℤ) : Prop :=
  b.length = heights.val.length ∧
    ∀ i : Nat, i < b.length → lo ≤ seqAt b i ∧ seqAt b i ≤ heightAt heights i

def heightsSum (heights : Slice Std.I64) : ℤ := (heights.val.map (fun x => x.val)).sum

def heightsMax (heights : Slice Std.I64) : ℤ :=
  ((heights.val.map (fun x => x.val)).max?).getD 0

def sliceOfList (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

def sliceRev (heights : Slice Std.I64) : Slice Std.I64 :=
  sliceOfList heights.val.reverse (by
    show heights.val.reverse.length ≤ Usize.max
    rw [List.length_reverse]
    simp only [Slice.val, Aeneas.Data.ListN.ListN_length]
    exact heights.bound)

theorem heightAt_eq (heights : Slice Std.I64) (i : Nat) (hi : i < heights.val.length) :
    heightAt heights i = (heights.val[i]'hi).val := by
  simp [heightAt, hi]

theorem seqAt_eq (b : List ℤ) (i : Nat) (hi : i < b.length) : seqAt b i = b[i]'hi := by
  simp [seqAt, hi]

theorem sliceRev_val (heights : Slice Std.I64) :
    (sliceRev heights).val = heights.val.reverse := by
  simp [sliceRev, sliceOfList, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

/-- The function returns a result r, and r is the maximum of the set of all sums Σ_{i=0}^{len(heights)-1} b[i], where b ranges over all integer sequences of length len(heights) satisfying: (a) 0 <= b[i] <= heights[i] for every i with 0 <= i < len(heights); and (b) b is mountain-shaped, meaning there exists an index p with 0 <= p < len(heights) such that b[0] <= b[1] <= ... <= b[p] and b[p] >= b[p+1] >= ... >= b[len(heights)-1].
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_1
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      (∀ b : List ℤ, IsBounded heights 0 b → IsMountain b → b.sum ≤ r.val) ∧
      (∃ b : List ℤ, IsBounded heights 0 b ∧ IsMountain b ∧ b.sum = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      (∀ b : List ℤ, IsBounded heights 0 b → IsMountain b → b.sum ≤ r.val) ∧
      (∃ b : List ℤ, IsBounded heights 0 b ∧ IsMountain b ∧ b.sum = r.val)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_2
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64, Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r) := by
  sorry

/-- The function returns a result r and r <= Σ_{i=0}^{len(heights)-1} heights[i].
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_3
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      r.val ≤ heightsSum heights := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      r.val ≤ heightsSum heights) := by
  sorry

/-- The function returns a result r and r >= max{ heights[i] | 0 <= i < len(heights) }.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_4
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      heightsMax heights ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      heightsMax heights ≤ r.val) := by
  sorry

/-- The function returns a result r and r >= len(heights).
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_5
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      (heights.val.length : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      (heights.val.length : ℤ) ≤ r.val) := by
  sorry

/-- For every input heights satisfying the preconditions, let r be the result returned on heights and let r_rev be the result returned on the reversed slice rev(heights), where rev(heights)[i] = heights[len(heights)-1-i] for 0 <= i < len(heights). Then both results exist and r = r_rev.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_6
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r r_rev : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights (sliceRev heights) = ok r_rev ∧
      r = r_rev := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r r_rev : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights (sliceRev heights) = ok r_rev ∧
      r = r_rev) := by
  sorry

/-- Let r be the result returned on heights and let r' be the result returned on heights'. Then both results exist and r <= r'.
  Preconditions: heights and heights' are non-empty slices of 64-bit integers with the same length n, n <= 1000, 1 <= heights[i] <= 1000000000 and 1 <= heights'[i] <= 1000000000 for every i with 0 <= i < n, and heights[i] <= heights'[i] for every i with 0 <= i < n. -/
theorem spec_7
    (heights heights' : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_len' : heights'.val.length ≤ 1000)
    (h_same : heights.val.length = heights'.val.length)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000)
    (h_bnd' : ∀ (i : Nat), i < heights'.val.length →
      1 ≤ heightAt heights' i ∧ heightAt heights' i ≤ 1000000000)
    (h_le : ∀ (i : Nat), i < heights.val.length →
      heightAt heights i ≤ heightAt heights' i) :
    ∃ r r' : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights' = ok r' ∧
      r.val ≤ r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (heights heights' : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_len' : heights'.val.length ≤ 1000)
    (h_same : heights.val.length = heights'.val.length)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000)
    (h_bnd' : ∀ (i : Nat), i < heights'.val.length →
      1 ≤ heightAt heights' i ∧ heightAt heights' i ≤ 1000000000)
    (h_le : ∀ (i : Nat), i < heights.val.length →
      heightAt heights i ≤ heightAt heights' i), ∃ r r' : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights' = ok r' ∧
      r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r, and there exists an integer sequence b of length len(heights) such that (a) 0 <= b[i] <= heights[i] for every i with 0 <= i < len(heights), (b) b is mountain-shaped, meaning there exists an index p with 0 <= p < len(heights) such that b[0] <= b[1] <= ... <= b[p] and b[p] >= b[p+1] >= ... >= b[len(heights)-1], and (c) Σ_{i=0}^{len(heights)-1} b[i] = r.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_8
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ b : List ℤ, IsBounded heights 0 b ∧ IsMountain b ∧ b.sum = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ b : List ℤ, IsBounded heights 0 b ∧ IsMountain b ∧ b.sum = r.val) := by
  sorry

/-- The function returns a result r, and for every integer sequence b of length len(heights) satisfying 0 <= b[i] <= heights[i] for every i and being mountain-shaped (there exists p with b[0] <= ... <= b[p] and b[p] >= ... >= b[len(heights)-1]), we have Σ_{i=0}^{len(heights)-1} b[i] <= r.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_9
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∀ b : List ℤ, IsBounded heights 0 b → IsMountain b → b.sum ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∀ b : List ℤ, IsBounded heights 0 b → IsMountain b → b.sum ≤ r.val) := by
  sorry

/-- The function returns a result r, and there exist an index p with 0 <= p < len(heights) and an integer sequence b of length len(heights) such that b is mountain-shaped, b[i] <= b[p] for every i with 0 <= i < len(heights), 0 <= b[i] <= heights[i] for every i, b[p] = heights[p], and Σ_{i=0}^{len(heights)-1} b[i] = r.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_10
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ (p : Nat) (b : List ℤ),
        p < heights.val.length ∧
        IsMountain b ∧
        (∀ i : Nat, i < heights.val.length → seqAt b i ≤ seqAt b p) ∧
        IsBounded heights 0 b ∧
        seqAt b p = heightAt heights p ∧
        b.sum = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ (p : Nat) (b : List ℤ),
        p < heights.val.length ∧
        IsMountain b ∧
        (∀ i : Nat, i < heights.val.length → seqAt b i ≤ seqAt b p) ∧
        IsBounded heights 0 b ∧
        seqAt b p = heightAt heights p ∧
        b.sum = r.val) := by
  sorry

/-- The function returns a result r, and there exists an integer sequence b of length len(heights) such that (a) 1 <= b[i] <= heights[i] for every i with 0 <= i < len(heights), (b) b is mountain-shaped, and (c) Σ_{i=0}^{len(heights)-1} b[i] = r.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_11
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ b : List ℤ, IsBounded heights 1 b ∧ IsMountain b ∧ b.sum = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      ∃ b : List ℤ, IsBounded heights 1 b ∧ IsMountain b ∧ b.sum = r.val) := by
  sorry

/-- The function returns a result r and r >= max{ heights[i] | 0 <= i < len(heights) } + len(heights) - 1.
  Preconditions: heights is a non-empty slice of 64-bit integers, len(heights) <= 1000, and for every i with 0 <= i < len(heights), 1 <= heights[i] <= 1000000000. -/
theorem spec_12
    (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      heightsMax heights + (heights.val.length : ℤ) - 1 ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (heights : Slice Std.I64)
    (h_pos : 0 < heights.val.length)
    (h_len : heights.val.length ≤ 1000)
    (h_bnd : ∀ (i : Nat), i < heights.val.length →
      1 ≤ heightAt heights i ∧ heightAt heights i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSumOfHeights.maximum_sum_of_heights heights = ok r ∧
      heightsMax heights + (heights.val.length : ℤ) - 1 ≤ r.val) := by
  sorry

end AegisSpec.MaximumSumOfHeights
