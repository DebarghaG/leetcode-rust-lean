import Aegis.FindLength.Code.Funs

/-!
# Specifications of `Aegis.FindLength.find_length`

LeetCode problem `maximum-length-of-repeated-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindLength

namespace AegisSpec.FindLength

def MatchAt (xs ys : List Std.I64) (i j L : ℕ) : Prop :=
  ∀ k : ℕ, k < L → xs[i + k]? = ys[j + k]?

def Common (nums1 nums2 : Slice Std.I64) (L : ℤ) : Prop :=
  0 ≤ L ∧ L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) ∧
    ∃ i j : ℕ,
      (i : ℤ) ≤ (nums1.val.length : ℤ) - L ∧
        (j : ℤ) ≤ (nums2.val.length : ℤ) - L ∧
          MatchAt nums1.val nums2.val i j L.toNat

def revSlice (s : Slice Std.I64) : Slice Std.I64 where
  leng := s.val.reverse.length
  list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
  bound := by
    rw [List.length_reverse]
    have h : s.val.length = s.leng := Aeneas.Data.ListN.ListN_length s.list
    rw [h]
    exact s.bound

theorem revSlice_val (s : Slice Std.I64) : (revSlice s).val = s.val.reverse := by
  simp [revSlice, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

theorem revSlice_length (s : Slice Std.I64) : (revSlice s).val.length = s.val.length := by
  rw [revSlice_val, List.length_reverse]

/-- Define Common(L) to mean: 0 <= L <= min(len(nums1), len(nums2)) and there exist indices i, j with 0 <= i <= len(nums1)-L, 0 <= j <= len(nums2)-L, and for every k with 0 <= k < L, nums1[i+k] = nums2[j+k]. Whenever find_length(nums1, nums2) returns a result r, r is the maximum L such that Common(L); equivalently, Common(r) holds and for every L with r < L <= min(len(nums1), len(nums2)), Common(L) is false.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      Common nums1 nums2 r.val ∧
        ∀ L : ℤ, r.val < L →
          L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
            ¬ Common nums1 nums2 L := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      Common nums1 nums2 r.val ∧
        ∀ L : ℤ, r.val < L →
          L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
            ¬ Common nums1 nums2 L) := by
  sorry

/-- For every nums1 and nums2 satisfying the preconditions, find_length(nums1, nums2) returns a result r; it does not fail, overflow, access out of bounds, or panic.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∃ r : Std.I64, find_length nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∃ r : Std.I64, find_length nums1 nums2 = ok r) := by
  sorry

/-- Whenever find_length(nums1, nums2) returns a result r, 0 <= r <= min(len(nums1), len(nums2)).
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      0 ≤ r.val ∧ r.val ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      0 ≤ r.val ∧ r.val ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ)) := by
  sorry

/-- Define Common(L) to mean: 0 <= L <= min(len(nums1), len(nums2)) and there exist indices i, j with 0 <= i <= len(nums1)-L, 0 <= j <= len(nums2)-L, and for every k with 0 <= k < L, nums1[i+k] = nums2[j+k]. Whenever find_length(nums1, nums2) returns a result r, Common(r) holds; that is, there is an actual common contiguous subarray of length r.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r → Common nums1 nums2 r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r → Common nums1 nums2 r.val) := by
  sorry

/-- Define Common(L) to mean: 0 <= L <= min(len(nums1), len(nums2)) and there exist indices i, j with 0 <= i <= len(nums1)-L, 0 <= j <= len(nums2)-L, and for every k with 0 <= k < L, nums1[i+k] = nums2[j+k]. Whenever find_length(nums1, nums2) returns a result r, for every L with r < L <= min(len(nums1), len(nums2)), Common(L) is false; no longer common contiguous subarray exists.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      ∀ L : ℤ, r.val < L →
        L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
          ¬ Common nums1 nums2 L := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      ∀ L : ℤ, r.val < L →
        L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
          ¬ Common nums1 nums2 L) := by
  sorry

/-- Whenever find_length(nums1, nums2) returns a result r, r = 0 if and only if for every i with 0 <= i < len(nums1) and every j with 0 <= j < len(nums2), nums1[i] != nums2[j].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      (r.val = 0 ↔
        ∀ (i : ℕ) (hi : i < nums1.val.length) (j : ℕ) (hj : j < nums2.val.length),
          nums1.val[i] ≠ nums2.val[j]) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      (r.val = 0 ↔
        ∀ (i : ℕ) (hi : i < nums1.val.length) (j : ℕ) (hj : j < nums2.val.length),
          nums1.val[i] ≠ nums2.val[j])) := by
  sorry

/-- Whenever find_length(nums1, nums2) returns a result r: if len(nums1) <= len(nums2), then r = len(nums1) if and only if there exists j with 0 <= j <= len(nums2)-len(nums1) and for every i with 0 <= i < len(nums1), nums1[i] = nums2[j+i]; and if len(nums2) <= len(nums1), then r = len(nums2) if and only if there exists i with 0 <= i <= len(nums1)-len(nums2) and for every j with 0 <= j < len(nums2), nums2[j] = nums1[i+j].
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      (nums1.val.length ≤ nums2.val.length →
          (r.val = (nums1.val.length : ℤ) ↔
            ∃ j : ℕ, j ≤ nums2.val.length - nums1.val.length ∧
              MatchAt nums1.val nums2.val 0 j nums1.val.length)) ∧
        (nums2.val.length ≤ nums1.val.length →
          (r.val = (nums2.val.length : ℤ) ↔
            ∃ i : ℕ, i ≤ nums1.val.length - nums2.val.length ∧
              MatchAt nums2.val nums1.val 0 i nums2.val.length)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      (nums1.val.length ≤ nums2.val.length →
          (r.val = (nums1.val.length : ℤ) ↔
            ∃ j : ℕ, j ≤ nums2.val.length - nums1.val.length ∧
              MatchAt nums1.val nums2.val 0 j nums1.val.length)) ∧
        (nums2.val.length ≤ nums1.val.length →
          (r.val = (nums2.val.length : ℤ) ↔
            ∃ i : ℕ, i ≤ nums1.val.length - nums2.val.length ∧
              MatchAt nums2.val nums1.val 0 i nums2.val.length))) := by
  sorry

/-- Whenever find_length(nums1, nums2) returns a result r1 and find_length(nums2, nums1) returns a result r2, r1 = r2.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r1 r2 : Std.I64, find_length nums1 nums2 = ok r1 →
      find_length nums2 nums1 = ok r2 → r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r1 r2 : Std.I64, find_length nums1 nums2 = ok r1 →
      find_length nums2 nums1 = ok r2 → r1 = r2) := by
  sorry

/-- Let rev(x) denote the array with len(rev(x)) = len(x) and rev(x)[i] = x[len(x)-1-i] for every 0 <= i < len(x). Whenever find_length(nums1, nums2) returns a result r and find_length(rev(nums1), rev(nums2)) returns a result r', r = r'.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length (revSlice nums1) (revSlice nums2) = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length (revSlice nums1) (revSlice nums2) = ok r' → r = r') := by
  sorry

/-- For every array a satisfying the same length/value constraints as nums1 (1 <= len(a) <= 1000 and 0 <= a[i] <= 100 for every i) and such that nums1 is a prefix of a (len(nums1) <= len(a) and nums1[i] = a[i] for every 0 <= i < len(nums1)), whenever find_length(nums1, nums2) returns a result r and find_length(a, nums2) returns a result r', we have r' >= r.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_10 (nums1 nums2 a : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100)
    (halen : 1 ≤ a.val.length) (hacap : a.val.length ≤ 1000)
    (haval : ∀ (i : ℕ) (hi : i < a.val.length), 0 ≤ a.val[i].val ∧ a.val[i].val ≤ 100)
    (haprefix_len : nums1.val.length ≤ a.val.length)
    (haprefix : MatchAt nums1.val a.val 0 0 nums1.val.length) :
    ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length a nums2 = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 a : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100)
    (halen : 1 ≤ a.val.length) (hacap : a.val.length ≤ 1000)
    (haval : ∀ (i : ℕ) (hi : i < a.val.length), 0 ≤ a.val[i].val ∧ a.val[i].val ≤ 100)
    (haprefix_len : nums1.val.length ≤ a.val.length)
    (haprefix : MatchAt nums1.val a.val 0 0 nums1.val.length), ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length a nums2 = ok r' → r.val ≤ r'.val) := by
  sorry

/-- For every integer c such that the arrays a and b defined by a[i] = nums1[i] + c for 0 <= i < len(nums1) and b[j] = nums2[j] + c for 0 <= j < len(nums2) still satisfy the same length/value constraints (0 <= a[i] <= 100 and 0 <= b[j] <= 100), whenever find_length(nums1, nums2) returns a result r and find_length(a, b) returns a result r', we have r = r'.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_11 (nums1 nums2 a b : Slice Std.I64) (c : ℤ)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100)
    (halen : a.val.length = nums1.val.length)
    (hb_len : b.val.length = nums2.val.length)
    (haval : a.val.map (fun x => x.val) = (nums1.val.map (fun x => x.val)).map (fun v => v + c))
    (hbval : b.val.map (fun y => y.val) = (nums2.val.map (fun y => y.val)).map (fun v => v + c))
    (hab : ∀ (x : ℕ) (hx : x < a.val.length), 0 ≤ a.val[x].val ∧ a.val[x].val ≤ 100)
    (hbb : ∀ (y : ℕ) (hy : y < b.val.length), 0 ≤ b.val[y].val ∧ b.val[y].val ≤ 100) :
    ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length a b = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 a b : Slice Std.I64) (c : ℤ)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100)
    (halen : a.val.length = nums1.val.length)
    (hb_len : b.val.length = nums2.val.length)
    (haval : a.val.map (fun x => x.val) = (nums1.val.map (fun x => x.val)).map (fun v => v + c))
    (hbval : b.val.map (fun y => y.val) = (nums2.val.map (fun y => y.val)).map (fun v => v + c))
    (hab : ∀ (x : ℕ) (hx : x < a.val.length), 0 ≤ a.val[x].val ∧ a.val[x].val ≤ 100)
    (hbb : ∀ (y : ℕ) (hy : y < b.val.length), 0 ≤ b.val[y].val ∧ b.val[y].val ≤ 100), ∀ r r' : Std.I64, find_length nums1 nums2 = ok r →
      find_length a b = ok r' → r = r') := by
  sorry

/-- Define Common(L) to mean: 0 <= L <= min(len(nums1), len(nums2)) and there exist indices i, j with 0 <= i <= len(nums1)-L, 0 <= j <= len(nums2)-L, and for every k with 0 <= k < L, nums1[i+k] = nums2[j+k]. Whenever find_length(nums1, nums2) returns a result r, for every L with 0 <= L <= min(len(nums1), len(nums2)), Common(L) holds if and only if L <= r.
  Preconditions: len(nums1) >= 1, len(nums2) >= 1, len(nums1) <= 1000, len(nums2) <= 1000, for every i with 0 <= i < len(nums1), 0 <= nums1[i] <= 100, and for every j with 0 <= j < len(nums2), 0 <= nums2[j] <= 100. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100) :
    ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      ∀ L : ℤ, 0 ≤ L → L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
        (Common nums1 nums2 L ↔ L ≤ r.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (h1len : 1 ≤ nums1.val.length) (h2len : 1 ≤ nums2.val.length)
    (h1cap : nums1.val.length ≤ 1000) (h2cap : nums2.val.length ≤ 1000)
    (h1val : ∀ (i : ℕ) (hi : i < nums1.val.length), 0 ≤ nums1.val[i].val ∧ nums1.val[i].val ≤ 100)
    (h2val : ∀ (j : ℕ) (hj : j < nums2.val.length), 0 ≤ nums2.val[j].val ∧ nums2.val[j].val ≤ 100), ∀ r : Std.I64, find_length nums1 nums2 = ok r →
      ∀ L : ℤ, 0 ≤ L → L ≤ ((min nums1.val.length nums2.val.length : ℕ) : ℤ) →
        (Common nums1 nums2 L ↔ L ≤ r.val)) := by
  sorry

end AegisSpec.FindLength
