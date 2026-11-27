import Aegis.NumberOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPairs.number_of_pairs`

LeetCode problem `find-the-number-of-good-pairs-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfPairs

def ival (l : List I64) (i : ℕ) : ℤ := if h : i < l.length then (l[i]).val else 0

theorem ival_of_lt {l : List I64} {i : ℕ} (h : i < l.length) : ival l i = (l[i]).val := by
  simp [ival, h]

def divisibleInt (a b : ℤ) : Prop := ∃ q : ℤ, a = q * b

def pairCond (nums1 nums2 : Slice I64) (k : I64) (i j : ℕ) : Prop :=
  divisibleInt (ival nums1.val i) (ival nums2.val j * k.val)

theorem divisibleInt_iff_dvd (a b : ℤ) : divisibleInt a b ↔ b ∣ a := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, by rw [hq, mul_comm]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, mul_comm]⟩

theorem slice_len_val (s : Slice I64) : (Slice.len s).val = s.val.length := rfl

theorem number_of_pairs_unfold (nums1 nums2 : Slice I64) (k : I64) :
    Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k
      = Aegis.NumberOfPairs.number_of_pairs_loop0 nums1 nums2 k 0#i64
          (Slice.len nums1) (Slice.len nums2) 0#usize := rfl

noncomputable section

open Classical

def pairCount (nums1 nums2 : Slice I64) (k : I64) : ℕ :=
  ∑ i ∈ Finset.range nums1.val.length, ∑ j ∈ Finset.range nums2.val.length,
    if pairCond nums1 nums2 k i j then 1 else 0

def rowCount (nums1 nums2 : Slice I64) (k : I64) (i : ℕ) : ℕ :=
  ((Finset.range nums2.val.length).filter (fun j => pairCond nums1 nums2 k i j)).card

def colCount (nums1 nums2 : Slice I64) (k : I64) (j : ℕ) : ℕ :=
  ((Finset.range nums1.val.length).filter (fun i => pairCond nums1 nums2 k i j)).card

def rowSum (nums1 nums2 : Slice I64) (k : I64) : ℕ :=
  ∑ i ∈ Finset.range nums1.val.length, rowCount nums1 nums2 k i

def colSum (nums1 nums2 : Slice I64) (k : I64) : ℕ :=
  ∑ j ∈ Finset.range nums2.val.length, colCount nums1 nums2 k j

def listMax (l : List I64) : ℤ := l.foldr (fun x acc => max x.val acc) 0

def countMulLe (nums2 : Slice I64) (k : I64) (M : ℤ) : ℕ :=
  ((Finset.range nums2.val.length).filter (fun j => ival nums2.val j * k.val ≤ M)).card

def countKDvd (nums1 : Slice I64) (k : I64) : ℕ :=
  ((Finset.range nums1.val.length).filter
    (fun i => ∃ q : ℤ, ival nums1.val i = k.val * q)).card

def countOne (nums2 : Slice I64) : ℕ :=
  ((Finset.range nums2.val.length).filter (fun j => ival nums2.val j = 1)).card

/-- the function returns a result r and r equals the number of pairs (i, j) with 0 <= i < len(nums1) and 0 <= j < len(nums2) such that nums1[i] is divisible by nums2[j] * k (i.e., there exists an integer q with nums1[i] = q * (nums2[j] * k)).
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_1 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∃ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r ∧
      r.val = (pairCount nums1 nums2 k : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∃ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r ∧
      r.val = (pairCount nums1 nums2 k : ℤ)) := by
  sorry

/-- the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_2 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∃ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∃ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r) := by
  sorry

/-- whenever the function returns a result r, r >= 0.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_3 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r → 0 ≤ r.val) := by
  sorry

/-- whenever the function returns a result r, r <= len(nums1) * len(nums2).
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_4 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val ≤ (nums1.val.length : ℤ) * (nums2.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val ≤ (nums1.val.length : ℤ) * (nums2.val.length : ℤ)) := by
  sorry

/-- whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2), nums1[i] is not divisible by nums2[j] * k (i.e., there is no integer q with nums1[i] = q * (nums2[j] * k)).
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_5 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (r.val = 0 ↔ ∀ i : ℕ, i < nums1.val.length → ∀ j : ℕ, j < nums2.val.length →
        ¬ pairCond nums1 nums2 k i j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (r.val = 0 ↔ ∀ i : ℕ, i < nums1.val.length → ∀ j : ℕ, j < nums2.val.length →
        ¬ pairCond nums1 nums2 k i j)) := by
  sorry

/-- whenever the function returns a result r, r = len(nums1) * len(nums2) if and only if for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2), nums1[i] is divisible by nums2[j] * k.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_6 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (r.val = (nums1.val.length : ℤ) * (nums2.val.length : ℤ) ↔
        ∀ i : ℕ, i < nums1.val.length → ∀ j : ℕ, j < nums2.val.length →
          pairCond nums1 nums2 k i j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (r.val = (nums1.val.length : ℤ) * (nums2.val.length : ℤ) ↔
        ∀ i : ℕ, i < nums1.val.length → ∀ j : ℕ, j < nums2.val.length →
          pairCond nums1 nums2 k i j)) := by
  sorry

/-- whenever the function returns a result r, let c_i be the number of indices j with 0 <= j < len(nums2) such that nums1[i] is divisible by nums2[j] * k, for each i with 0 <= i < len(nums1); then r = c_0 + c_1 + ... + c_{len(nums1)-1}.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_7 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val = (rowSum nums1 nums2 k : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val = (rowSum nums1 nums2 k : ℤ)) := by
  sorry

/-- whenever the function returns a result r, let d_j be the number of indices i with 0 <= i < len(nums1) such that nums1[i] is divisible by nums2[j] * k, for each j with 0 <= j < len(nums2); then r = d_0 + d_1 + ... + d_{len(nums2)-1}.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_8 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val = (colSum nums1 nums2 k : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val = (colSum nums1 nums2 k : ℤ)) := by
  sorry

/-- whenever the function returns a result r, let M be the maximum value among nums1[0], nums1[1], ..., nums1[len(nums1)-1]. Then r <= len(nums1) * B where B is the number of indices j with 0 <= j < len(nums2) and nums2[j] * k <= M.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_9 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val ≤ (nums1.val.length : ℤ) * (countMulLe nums2 k (listMax nums1.val) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      r.val ≤ (nums1.val.length : ℤ) * (countMulLe nums2 k (listMax nums1.val) : ℤ)) := by
  sorry

/-- whenever the function returns a result r, let A be the number of indices i with 0 <= i < len(nums1) such that k divides nums1[i], and let B be the number of indices j with 0 <= j < len(nums2) such that nums2[j] = 1. Then r >= A * B.
  Preconditions: len(nums1) >= 1 and len(nums2) >= 1 and len(nums1) <= 50 and len(nums2) <= 50, and for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 50, and for every j with 0 <= j < len(nums2), 1 <= nums2[j] <= 50, and 1 <= k <= 50. -/
theorem spec_10 (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50) :
    ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (countKDvd nums1 k : ℤ) * (countOne nums2 : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (k : I64)
    (hn1 : 1 ≤ nums1.val.length) (hm1 : 1 ≤ nums2.val.length)
    (hn2 : nums1.val.length ≤ 50) (hm2 : nums2.val.length ≤ 50)
    (hb1 : ∀ i : ℕ, i < nums1.val.length →
      1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 50)
    (hb2 : ∀ j : ℕ, j < nums2.val.length →
      1 ≤ ival nums2.val j ∧ ival nums2.val j ≤ 50)
    (hk : 1 ≤ k.val ∧ k.val ≤ 50), ∀ r : I64, Aegis.NumberOfPairs.number_of_pairs nums1 nums2 k = ok r →
      (countKDvd nums1 k : ℤ) * (countOne nums2 : ℤ) ≤ r.val) := by
  sorry

end

end AegisSpec.NumberOfPairs
