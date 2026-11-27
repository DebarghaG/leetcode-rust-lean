import Aegis.NumberOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPairs.number_of_pairs`

LeetCode problem `find-the-number-of-good-pairs-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfPairs

open Aegis.NumberOfPairs

attribute [local instance] Classical.propDecidable

def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def DivisibleBy (a b : Int) : Prop := ∃ q : Int, a = b * q

theorem divisibleBy_iff_dvd (a b : Int) : DivisibleBy a b ↔ b ∣ a := Iff.rfl

def concat (a b : Slice Std.I64) (h : (a.val ++ b.val).length ≤ Usize.max) : Slice Std.I64 :=
  ⟨(a.val ++ b.val).length, Aeneas.Data.ListN.ListN.fromList (a.val ++ b.val), h⟩

theorem concat_val (a b : Slice Std.I64) (h : (a.val ++ b.val).length ≤ Usize.max) :
    (concat a b h).val = a.val ++ b.val := by
  simp [concat, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

noncomputable def countRow (nums2 : Slice Std.I64) (k : Std.I64) (a : Int) : Nat :=
  ((Finset.univ : Finset (Fin (vals nums2).length)).filter
    (fun j => DivisibleBy a ((vals nums2).get j * k.val))).card

noncomputable def countCol (nums1 : Slice Std.I64) (k : Std.I64) (b : Int) : Nat :=
  ((Finset.univ : Finset (Fin (vals nums1).length)).filter
    (fun i => DivisibleBy ((vals nums1).get i) (b * k.val))).card

noncomputable def pairCount (nums1 nums2 : Slice Std.I64) (k : Std.I64) : Nat :=
  ((Finset.univ :
      Finset (Fin (vals nums1).length × Fin (vals nums2).length)).filter
    (fun p =>
      DivisibleBy ((vals nums1).get p.1) ((vals nums2).get p.2 * k.val))).card

/-- The function returns a result r and r = |{(i,j) : 0 <= i < len(nums1), 0 <= j < len(nums2), and nums1[i] is divisible by nums2[j]*k}|. Here 'a is divisible by b' means there exists an integer q with a = b*q (equivalently, since b > 0, a mod b = 0).
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. All lists are 0-indexed. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∃ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r ∧ r.val = (pairCount nums1 nums2 k : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∃ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r ∧ r.val = (pairCount nums1 nums2 k : Int)) := by
  sorry

/-- Under these preconditions, the function returns a result r; it does not fail because of arithmetic overflow, division by zero, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∃ r : Std.I64, number_of_pairs nums1 nums2 k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∃ r : Std.I64, number_of_pairs nums1 nums2 k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums1)*len(nums2).
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums1.val.length : Int) * (nums2.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums1.val.length : Int) * (nums2.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j with 0 <= i < len(nums1) and 0 <= j < len(nums2) such that nums1[i] is divisible by nums2[j]*k (that is, there exists an integer q with nums1[i] = (nums2[j]*k)*q).
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        (0 < r.val ↔
          ∃ (i : Fin (vals nums1).length) (j : Fin (vals nums2).length),
            DivisibleBy ((vals nums1).get i) ((vals nums2).get j * k.val)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        (0 < r.val ↔
          ∃ (i : Fin (vals nums1).length) (j : Fin (vals nums2).length),
            DivisibleBy ((vals nums1).get i) ((vals nums2).get j * k.val))) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums1)-1} c_i, where for each i, c_i is the number of indices j with 0 <= j < len(nums2) such that nums1[i] is divisible by nums2[j]*k.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        r.val =
          ((Finset.univ : Finset (Fin (vals nums1).length)).sum
            (fun i => countRow nums2 k ((vals nums1).get i)) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        r.val =
          ((Finset.univ : Finset (Fin (vals nums1).length)).sum
            (fun i => countRow nums2 k ((vals nums1).get i)) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{j=0}^{len(nums2)-1} d_j, where for each j, d_j is the number of indices i with 0 <= i < len(nums1) such that nums1[i] is divisible by nums2[j]*k.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        r.val =
          ((Finset.univ : Finset (Fin (vals nums2).length)).sum
            (fun j => countCol nums1 k ((vals nums2).get j)) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Std.I64,
      number_of_pairs nums1 nums2 k = ok r →
        r.val =
          ((Finset.univ : Finset (Fin (vals nums2).length)).sum
            (fun j => countCol nums1 k ((vals nums2).get j)) : Int)) := by
  sorry

/-- Let a ++ b denote the concatenation of a and b. Whenever number_of_pairs(a ++ b, nums2, k), number_of_pairs(a, nums2, k), and number_of_pairs(b, nums2, k) all return results r, r_a, and r_b, then r = r_a + r_b.
  Preconditions: Let m = len(nums2). Assume 1 <= m <= 100000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. Let a and b be slices of i64 with lengths at least 1, with len(a)+len(b) <= 100000, and with every entry in [1,1000000]. -/
theorem spec_7 (nums2 a b : Slice Std.I64) (k : Std.I64)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
    (ha_pos : 1 ≤ a.val.length) (hb_pos : 1 ≤ b.val.length)
    (hab_len : a.val.length + b.val.length ≤ 100000)
    (ha : ∀ v ∈ a.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hb : ∀ v ∈ b.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000) :
    ∀ (r ra rb : Std.I64),
      number_of_pairs
          (concat a b (by
            have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
            rw [List.length_append]
            omega))
          nums2 k = ok r →
        number_of_pairs a nums2 k = ok ra →
          number_of_pairs b nums2 k = ok rb → r.val = ra.val + rb.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums2 a b : Slice Std.I64) (k : Std.I64)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
    (ha_pos : 1 ≤ a.val.length) (hb_pos : 1 ≤ b.val.length)
    (hab_len : a.val.length + b.val.length ≤ 100000)
    (ha : ∀ v ∈ a.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hb : ∀ v ∈ b.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000), ∀ (r ra rb : Std.I64),
      number_of_pairs
          (concat a b (by
            have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
            rw [List.length_append]
            omega))
          nums2 k = ok r →
        number_of_pairs a nums2 k = ok ra →
          number_of_pairs b nums2 k = ok rb → r.val = ra.val + rb.val) := by
  sorry

/-- Let b ++ c denote the concatenation of b and c. Whenever number_of_pairs(nums1, b ++ c, k), number_of_pairs(nums1, b, k), and number_of_pairs(nums1, c, k) all return results r, r_b, and r_c, then r = r_b + r_c.
  Preconditions: Let n = len(nums1). Assume 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, and 1 <= k <= 1000. Let b and c be slices of i64 with lengths at least 1, with len(b)+len(c) <= 100000, and with every entry in [1,1000000]. -/
theorem spec_8 (nums1 b c : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
    (hb_pos : 1 ≤ b.val.length) (hc_pos : 1 ≤ c.val.length)
    (hbc_len : b.val.length + c.val.length ≤ 100000)
    (hb : ∀ v ∈ b.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hc : ∀ v ∈ c.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000) :
    ∀ (r rb rc : Std.I64),
      number_of_pairs nums1
          (concat b c (by
            have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
            rw [List.length_append]
            omega))
          k = ok r →
        number_of_pairs nums1 b k = ok rb →
          number_of_pairs nums1 c k = ok rc → r.val = rb.val + rc.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 b c : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
    (hb_pos : 1 ≤ b.val.length) (hc_pos : 1 ≤ c.val.length)
    (hbc_len : b.val.length + c.val.length ≤ 100000)
    (hb : ∀ v ∈ b.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hc : ∀ v ∈ c.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000), ∀ (r rb rc : Std.I64),
      number_of_pairs nums1
          (concat b c (by
            have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
            rw [List.length_append]
            omega))
          k = ok r →
        number_of_pairs nums1 b k = ok rb →
          number_of_pairs nums1 c k = ok rc → r.val = rb.val + rc.val) := by
  sorry

/-- Whenever number_of_pairs(a, nums2, k) and number_of_pairs(nums1, nums2, k) return results r_a and r, r_a = r.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. Let p be a bijection from {0,...,len(nums1)-1} to itself and let a be a slice of length len(nums1) with a[i] = nums1[p(i)] for every i. -/
theorem spec_9 (nums1 nums2 a : Slice Std.I64) (k : Std.I64)
    (p : Equiv.Perm (Fin (vals nums1).length))
    (hla : (vals a).length = (vals nums1).length)
    (ha : ∀ i : Fin (vals a).length,
      (vals a).get i = (vals nums1).get (p (Fin.cast hla i)))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ (r ra : Std.I64),
      number_of_pairs a nums2 k = ok ra →
        number_of_pairs nums1 nums2 k = ok r → ra.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 a : Slice Std.I64) (k : Std.I64)
    (p : Equiv.Perm (Fin (vals nums1).length))
    (hla : (vals a).length = (vals nums1).length)
    (ha : ∀ i : Fin (vals a).length,
      (vals a).get i = (vals nums1).get (p (Fin.cast hla i)))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ (r ra : Std.I64),
      number_of_pairs a nums2 k = ok ra →
        number_of_pairs nums1 nums2 k = ok r → ra.val = r.val) := by
  sorry

/-- Whenever number_of_pairs(nums1, b, k) and number_of_pairs(nums1, nums2, k) return results r_b and r, r_b = r.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. Let p be a bijection from {0,...,len(nums2)-1} to itself and let b be a slice of length len(nums2) with b[j] = nums2[p(j)] for every j. -/
theorem spec_10 (nums1 nums2 b : Slice Std.I64) (k : Std.I64)
    (p : Equiv.Perm (Fin (vals nums2).length))
    (hlb : (vals b).length = (vals nums2).length)
    (hb : ∀ j : Fin (vals b).length,
      (vals b).get j = (vals nums2).get (p (Fin.cast hlb j)))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ (r rb : Std.I64),
      number_of_pairs nums1 b k = ok rb →
        number_of_pairs nums1 nums2 k = ok r → rb.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 b : Slice Std.I64) (k : Std.I64)
    (p : Equiv.Perm (Fin (vals nums2).length))
    (hlb : (vals b).length = (vals nums2).length)
    (hb : ∀ j : Fin (vals b).length,
      (vals b).get j = (vals nums2).get (p (Fin.cast hlb j)))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ (r rb : Std.I64),
      number_of_pairs nums1 b k = ok rb →
        number_of_pairs nums1 nums2 k = ok r → rb.val = r.val) := by
  sorry

/-- Whenever number_of_pairs(a, nums2, k) and number_of_pairs(nums1, nums2, k) return results r_a and r, r_a >= r.
  Preconditions: Let n = len(nums1) and m = len(nums2). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 1000000, for every j with 0 <= j < m, 1 <= nums2[j] <= 1000000, and 1 <= k <= 1000. Let a be a slice of length len(nums1) such that 1 <= a[i] <= 1000000 and nums1[i] divides a[i] for every i. -/
theorem spec_11 (nums1 nums2 a : Slice Std.I64) (k : Std.I64)
    (hla : (vals a).length = (vals nums1).length)
    (ha_bounds : ∀ v ∈ a.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (ha : ∀ i : Fin (vals nums1).length,
      DivisibleBy ((vals a).get (Fin.cast hla.symm i)) ((vals nums1).get i))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
    ∀ (r ra : Std.I64),
      number_of_pairs a nums2 k = ok ra →
        number_of_pairs nums1 nums2 k = ok r → r.val ≤ ra.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 a : Slice Std.I64) (k : Std.I64)
    (hla : (vals a).length = (vals nums1).length)
    (ha_bounds : ∀ v ∈ a.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (ha : ∀ i : Fin (vals nums1).length,
      DivisibleBy ((vals a).get (Fin.cast hla.symm i)) ((vals nums1).get i))
    (hn_pos : 1 ≤ nums1.val.length) (hn_le : nums1.val.length ≤ 100000)
    (hm_pos : 1 ≤ nums2.val.length) (hm_le : nums2.val.length ≤ 100000)
    (h1 : ∀ v ∈ nums1.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (h2 : ∀ v ∈ nums2.val, (1 : Int) ≤ v.val ∧ v.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ (r ra : Std.I64),
      number_of_pairs a nums2 k = ok ra →
        number_of_pairs nums1 nums2 k = ok r → r.val ≤ ra.val) := by
  sorry

end AegisSpec.NumberOfPairs
