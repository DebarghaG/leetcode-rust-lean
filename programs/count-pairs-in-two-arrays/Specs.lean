import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-pairs-in-two-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPairs

open Aegis.CountPairs

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def elem (s : Slice Std.I64) (k : ℕ) : ℤ := (vals s).getD k 0

def totalPairs (n : ℕ) : ℕ := n * (n - 1) / 2

def pairCount (l1 l2 : List ℤ) : ℕ :=
  (((Finset.range l1.length).product (Finset.range l1.length)).filter
    (fun p : ℕ × ℕ =>
      p.1 < p.2 ∧
        l1.getD p.1 0 + l1.getD p.2 0 > l2.getD p.1 0 + l2.getD p.2 0)).card

def tieCount (l1 l2 : List ℤ) : ℕ :=
  (((Finset.range l1.length).product (Finset.range l1.length)).filter
    (fun p : ℕ × ℕ =>
      p.1 < p.2 ∧
        l1.getD p.1 0 + l1.getD p.2 0 = l2.getD p.1 0 + l2.getD p.2 0)).card

/-- The function returns a result r, and r is the number of pairs (i,j) of indices such that 0 <= i < j < n and nums1[i] + nums1[j] > nums2[i] + nums2[j].
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧
      r.val = (pairCount (vals nums1) (vals nums2) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧
      r.val = (pairCount (vals nums1) (vals nums2) : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums1 nums2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∃ r : Std.I64, count_pairs nums1 nums2 = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n*(n-1)/2, where n = len(nums1) and n*(n-1)/2 is the exact number of index pairs with 0 <= i < j < n.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs n : ℤ)) := by
  sorry

/-- The function returns the result r = 0.
  Preconditions: len(nums1) = len(nums2) = n, n = 1, and 1 <= nums1[0] <= 100000 and 1 <= nums2[0] <= 100000. -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn : n = 1)
    (h1 : 1 ≤ elem nums1 0 ∧ elem nums1 0 ≤ 100000)
    (h2 : 1 ≤ elem nums2 0 ∧ elem nums2 0 ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn : n = 1)
    (h1 : 1 ≤ elem nums1 0 ∧ elem nums1 0 ≤ 100000)
    (h2 : 1 ≤ elem nums2 0 ∧ elem nums2 0 ≤ 100000), ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = 1 if nums1[0] + nums1[1] > nums2[0] + nums2[1], and returns r = 0 otherwise.
  Preconditions: len(nums1) = len(nums2) = n, n = 2, and for 0 <= k < 2, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn : n = 2)
    (hb1 : ∀ k, k < 2 → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < 2 → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧
      r.val = if elem nums1 0 + elem nums1 1 > elem nums2 0 + elem nums2 1
        then (1 : ℤ) else 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn : n = 2)
    (hb1 : ∀ k, k < 2 → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < 2 → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∃ r : Std.I64, count_pairs nums1 nums2 = ok r ∧
      r.val = if elem nums1 0 + elem nums1 1 > elem nums2 0 + elem nums2 1
        then (1 : ℤ) else 0) := by
  sorry

/-- Whenever the function returns a result r, r = n*(n-1)/2 if and only if for every pair (i,j) with 0 <= i < j < n, nums1[i] + nums1[j] > nums2[i] + nums2[j].
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (r.val = (totalPairs n : ℤ) ↔
        ∀ i j : ℕ, i < j → j < n →
          elem nums1 i + elem nums1 j > elem nums2 i + elem nums2 j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (r.val = (totalPairs n : ℤ) ↔
        ∀ i j : ℕ, i < j → j < n →
          elem nums1 i + elem nums1 j > elem nums2 i + elem nums2 j)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every pair (i,j) with 0 <= i < j < n, nums1[i] + nums1[j] <= nums2[i] + nums2[j].
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_7 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (r.val = 0 ↔
        ∀ i j : ℕ, i < j → j < n →
          elem nums1 i + elem nums1 j ≤ elem nums2 i + elem nums2 j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (r.val = 0 ↔
        ∀ i j : ℕ, i < j → j < n →
          elem nums1 i + elem nums1 j ≤ elem nums2 i + elem nums2 j)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j with 0 <= i < j < n such that nums1[i] + nums1[j] > nums2[i] + nums2[j].
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_8 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (0 < r.val ↔
        ∃ i j : ℕ, i < j ∧ j < n ∧
          elem nums1 i + elem nums1 j > elem nums2 i + elem nums2 j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000), ∀ r : Std.I64, count_pairs nums1 nums2 = ok r →
      (0 < r.val ↔
        ∃ i j : ℕ, i < j ∧ j < n ∧
          elem nums1 i + elem nums1 j > elem nums2 i + elem nums2 j)) := by
  sorry

/-- For every permutation p of {0,...,n-1}, let nums1p[k] = nums1[p(k)] and nums2p[k] = nums2[p(k)] for 0 <= k < n. Whenever count_pairs(nums1,nums2) returns r and count_pairs(nums1p,nums2p) returns rp, we have rp = r.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (p : Equiv.Perm (Fin n)) (nums1p nums2p : Slice Std.I64)
    (h1p : vals nums1p = List.ofFn (fun i : Fin n => elem nums1 (p i).val))
    (h2p : vals nums2p = List.ofFn (fun i : Fin n => elem nums2 (p i).val))
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1p nums2p = ok rp) :
    rp = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (p : Equiv.Perm (Fin n)) (nums1p nums2p : Slice Std.I64)
    (h1p : vals nums1p = List.ofFn (fun i : Fin n => elem nums1 (p i).val))
    (h2p : vals nums2p = List.ofFn (fun i : Fin n => elem nums2 (p i).val))
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1p nums2p = ok rp), rp = r) := by
  sorry

/-- For every slice nums1p of length n with nums1[k] <= nums1p[k] <= 100000 for all 0 <= k < n, whenever count_pairs(nums1,nums2) returns r and count_pairs(nums1p,nums2) returns rp, we have rp >= r.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_10 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (nums1p : Slice Std.I64) (hlenp : nums1p.val.length = n)
    (hge : ∀ k, k < n → elem nums1 k ≤ elem nums1p k ∧ elem nums1p k ≤ 100000)
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1p nums2 = ok rp) :
    r.val ≤ rp.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (nums1p : Slice Std.I64) (hlenp : nums1p.val.length = n)
    (hge : ∀ k, k < n → elem nums1 k ≤ elem nums1p k ∧ elem nums1p k ≤ 100000)
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1p nums2 = ok rp), r.val ≤ rp.val) := by
  sorry

/-- For every slice nums2p of length n with 1 <= nums2p[k] <= nums2[k] for all 0 <= k < n, whenever count_pairs(nums1,nums2) returns r and count_pairs(nums1,nums2p) returns rp, we have rp >= r.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (nums2p : Slice Std.I64) (hlenp : nums2p.val.length = n)
    (hle : ∀ k, k < n → 1 ≤ elem nums2p k ∧ elem nums2p k ≤ elem nums2 k)
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1 nums2p = ok rp) :
    r.val ≤ rp.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (nums2p : Slice Std.I64) (hlenp : nums2p.val.length = n)
    (hle : ∀ k, k < n → 1 ≤ elem nums2p k ∧ elem nums2p k ≤ elem nums2 k)
    (r rp : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrp : count_pairs nums1 nums2p = ok rp), r.val ≤ rp.val) := by
  sorry

/-- For every integer c such that 1 <= nums1[k] + c <= 100000 and 1 <= nums2[k] + c <= 100000 for all 0 <= k < n, let nums1c and nums2c be the slices with nums1c[k] = nums1[k] + c and nums2c[k] = nums2[k] + c. Whenever count_pairs(nums1,nums2) returns r and count_pairs(nums1c,nums2c) returns rc, we have rc = r.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (c : ℤ) (nums1c nums2c : Slice Std.I64)
    (h1c : vals nums1c = (vals nums1).map (fun x => x + c))
    (h2c : vals nums2c = (vals nums2).map (fun x => x + c))
    (hc1 : ∀ k, k < n → 1 ≤ elem nums1 k + c ∧ elem nums1 k + c ≤ 100000)
    (hc2 : ∀ k, k < n → 1 ≤ elem nums2 k + c ∧ elem nums2 k + c ≤ 100000)
    (r rc : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrc : count_pairs nums1c nums2c = ok rc) :
    rc = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (c : ℤ) (nums1c nums2c : Slice Std.I64)
    (h1c : vals nums1c = (vals nums1).map (fun x => x + c))
    (h2c : vals nums2c = (vals nums2).map (fun x => x + c))
    (hc1 : ∀ k, k < n → 1 ≤ elem nums1 k + c ∧ elem nums1 k + c ≤ 100000)
    (hc2 : ∀ k, k < n → 1 ≤ elem nums2 k + c ∧ elem nums2 k + c ≤ 100000)
    (r rc : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrc : count_pairs nums1c nums2c = ok rc), rc = r) := by
  sorry

/-- For every integer k >= 1 such that 1 <= k*nums1[t] <= 100000 and 1 <= k*nums2[t] <= 100000 for all 0 <= t < n, let nums1k and nums2k be the slices with nums1k[t] = k*nums1[t] and nums2k[t] = k*nums2[t]. Whenever count_pairs(nums1,nums2) returns r and count_pairs(nums1k,nums2k) returns rk, we have rk = r.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_13 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (m : ℕ) (hm : 1 ≤ m) (nums1m nums2m : Slice Std.I64)
    (h1m : vals nums1m = (vals nums1).map (fun x => (m : ℤ) * x))
    (h2m : vals nums2m = (vals nums2).map (fun x => (m : ℤ) * x))
    (hm1 : ∀ t, t < n → 1 ≤ (m : ℤ) * elem nums1 t ∧ (m : ℤ) * elem nums1 t ≤ 100000)
    (hm2 : ∀ t, t < n → 1 ≤ (m : ℤ) * elem nums2 t ∧ (m : ℤ) * elem nums2 t ≤ 100000)
    (r rm : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrm : count_pairs nums1m nums2m = ok rm) :
    rm = r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (m : ℕ) (hm : 1 ≤ m) (nums1m nums2m : Slice Std.I64)
    (h1m : vals nums1m = (vals nums1).map (fun x => (m : ℤ) * x))
    (h2m : vals nums2m = (vals nums2).map (fun x => (m : ℤ) * x))
    (hm1 : ∀ t, t < n → 1 ≤ (m : ℤ) * elem nums1 t ∧ (m : ℤ) * elem nums1 t ≤ 100000)
    (hm2 : ∀ t, t < n → 1 ≤ (m : ℤ) * elem nums2 t ∧ (m : ℤ) * elem nums2 t ≤ 100000)
    (r rm : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrm : count_pairs nums1m nums2m = ok rm), rm = r) := by
  sorry

/-- Let e be the number of pairs (i,j) with 0 <= i < j < n and nums1[i] + nums1[j] = nums2[i] + nums2[j]. Whenever count_pairs(nums1,nums2) returns r and count_pairs(nums2,nums1) returns rswapped, we have r + rswapped + e = n*(n-1)/2.
  Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100000, and for every k with 0 <= k < n, 1 <= nums1[k] <= 100000 and 1 <= nums2[k] <= 100000. -/
theorem spec_14 (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (r rswapped : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrs : count_pairs nums2 nums1 = ok rswapped) :
    r.val + rswapped.val + (tieCount (vals nums1) (vals nums2) : ℤ) = (totalPairs n : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
    (hlen1 : (Slice.len nums1).val = n) (hlen2 : (Slice.len nums2).val = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hb1 : ∀ k, k < n → 1 ≤ elem nums1 k ∧ elem nums1 k ≤ 100000)
    (hb2 : ∀ k, k < n → 1 ≤ elem nums2 k ∧ elem nums2 k ≤ 100000)
    (r rswapped : Std.I64)
    (hr : count_pairs nums1 nums2 = ok r)
    (hrs : count_pairs nums2 nums1 = ok rswapped), r.val + rswapped.val + (tieCount (vals nums1) (vals nums2) : ℤ) = (totalPairs n : ℤ)) := by
  sorry

end AegisSpec.CountPairs
