import Aegis.TupleSameProduct.Code.Funs

/-!
# Specifications of `Aegis.TupleSameProduct.tuple_same_product`

LeetCode problem `tuple-with-same-product`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TupleSameProduct

open Aegis.TupleSameProduct

def sliceInts (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def elemAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def ValidSlice (nums : Slice Std.I64) : Prop :=
  let l := sliceInts nums
  1 ≤ l.length ∧ l.length ≤ 1000 ∧
    (∀ i, i < l.length → 1 ≤ elemAt l i ∧ elemAt l i ≤ 10 ^ 4) ∧
    (∀ i j, i < j → j < l.length → elemAt l i ≠ elemAt l j)

def Splittable (l : List ℤ) (a b c d : ℕ) : Prop :=
  elemAt l a * elemAt l b = elemAt l c * elemAt l d ∨
    elemAt l a * elemAt l c = elemAt l b * elemAt l d ∨
      elemAt l a * elemAt l d = elemAt l b * elemAt l c

def GoodQuad (l : List ℤ) (i j k m : ℕ) : Prop :=
  i < j ∧ j < k ∧ k < m ∧ m < l.length ∧ Splittable l i j k m

instance decidableSplittable (l : List ℤ) (a b c d : ℕ) : Decidable (Splittable l a b c d) := by
  unfold Splittable
  infer_instance

instance decidableGoodQuad (l : List ℤ) (i j k m : ℕ) : Decidable (GoodQuad l i j k m) := by
  unfold GoodQuad
  infer_instance

def pairProdCount (l : List ℤ) (p : ℤ) : ℕ :=
  ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.range l.length,
    if i < j ∧ elemAt l i * elemAt l j = p then 1 else 0

def pairProdValues (l : List ℤ) : Finset ℤ :=
  (((Finset.range l.length).product (Finset.range l.length)).filter
      (fun q => q.1 < q.2)).image
    (fun q => elemAt l q.1 * elemAt l q.2)

def pairWeightSum (l : List ℤ) : ℕ :=
  ∑ p ∈ pairProdValues l, pairProdCount l p * (pairProdCount l p - 1) / 2

def goodQuadCount (l : List ℤ) : ℕ :=
  ∑ i ∈ Finset.range l.length, ∑ j ∈ Finset.range l.length,
    ∑ k ∈ Finset.range l.length, ∑ m ∈ Finset.range l.length,
      (if GoodQuad l i j k m then 1 else 0)

def choose4 (n : ℕ) : ℕ := if n < 4 then 0 else n * (n - 1) * (n - 2) * (n - 3) / 24

def NoDisjointEqualPairs (l : List ℤ) : Prop :=
  ∀ i j k m : ℕ, i < j → j < l.length → k < m → m < l.length →
    i ≠ k → i ≠ m → j ≠ k → j ≠ m →
      elemAt l i * elemAt l j ≠ elemAt l k * elemAt l m

/-- Let P be the set of unordered index pairs {i, j} with 0 <= i < j < len(nums). For each integer p, let k_p = |{ {i,j} in P : nums[i] * nums[j] = p }|. The function returns a result r such that r = 8 * Σ_p (k_p * (k_p - 1) / 2), where the sum is over all distinct values p that occur as nums[i]*nums[j] for some {i,j} in P.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct (i.e., for 0 <= i < j < len(nums), nums[i] != nums[j]). -/
theorem spec_1 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val = 8 * ((pairWeightSum (sliceInts nums) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val = 8 * ((pairWeightSum (sliceInts nums) : ℕ) : ℤ)) := by
  sorry

/-- Let a 4-element index set S = {i,j,k,l} with 0 <= i < j < k < l < len(nums) be called good if there exists a partition of S into two unordered pairs {a,b} and {c,d} (so {a,b,c,d} = {i,j,k,l}) such that nums[a]*nums[b] = nums[c]*nums[d]. The function returns a result r such that r = 8 * (number of good 4-element index sets).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_2 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val = 8 * ((goodQuadCount (sliceInts nums) : ℕ) : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val = 8 * ((goodQuadCount (sliceInts nums) : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_3 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r is a multiple of 8 (i.e., there exists an integer q with r = 8*q).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_4 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧ ∃ q : ℤ, r.val = 8 * q := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧ ∃ q : ℤ, r.val = 8 * q) := by
  sorry

/-- The function returns a result r and r <= 8 * C(len(nums), 4), where C(n,4) = n*(n-1)*(n-2)*(n-3)/24 for n >= 4, and C(n,4) = 0 for n < 4.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_5 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val ≤ 8 * ((choose4 (sliceInts nums).length : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      r.val ≤ 8 * ((choose4 (sliceInts nums).length : ℕ) : ℤ)) := by
  sorry

/-- If len(nums) < 4, then the function returns r = 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_6 (nums : Slice Std.I64) (h : ValidSlice nums) :
    (sliceInts nums).length < 4 →
      ∃ r : Std.I64, tuple_same_product nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), (sliceInts nums).length < 4 →
      ∃ r : Std.I64, tuple_same_product nums = ok r ∧ r.val = 0) := by
  sorry

/-- If len(nums) = 4, then the function returns r = 8 if there exists a partition of the four elements into two unordered pairs {a,b} and {c,d} such that a*b = c*d, and returns r = 0 otherwise.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_7 (nums : Slice Std.I64) (h : ValidSlice nums) :
    (sliceInts nums).length = 4 →
      ∃ r : Std.I64, tuple_same_product nums = ok r ∧
        (Splittable (sliceInts nums) 0 1 2 3 → r.val = 8) ∧
        (¬ Splittable (sliceInts nums) 0 1 2 3 → r.val = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), (sliceInts nums).length = 4 →
      ∃ r : Std.I64, tuple_same_product nums = ok r ∧
        (Splittable (sliceInts nums) 0 1 2 3 → r.val = 8) ∧
        (¬ Splittable (sliceInts nums) 0 1 2 3 → r.val = 0)) := by
  sorry

/-- If there exist indices i, j, k, l with 0 <= i < j < k < l < len(nums) such that nums[i]*nums[j] = nums[k]*nums[l], then the function returns r >= 8.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_8 (nums : Slice Std.I64) (h : ValidSlice nums)
    (hw : ∃ i j k m : ℕ, i < j ∧ j < k ∧ k < m ∧ m < (sliceInts nums).length ∧
      elemAt (sliceInts nums) i * elemAt (sliceInts nums) j =
        elemAt (sliceInts nums) k * elemAt (sliceInts nums) m) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧ 8 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums)
    (hw : ∃ i j k m : ℕ, i < j ∧ j < k ∧ k < m ∧ m < (sliceInts nums).length ∧
      elemAt (sliceInts nums) i * elemAt (sliceInts nums) j =
        elemAt (sliceInts nums) k * elemAt (sliceInts nums) m), ∃ r : Std.I64, tuple_same_product nums = ok r ∧ 8 ≤ r.val) := by
  sorry

/-- Let r1 be the result of tuple_same_product(nums1) and r2 be the result of tuple_same_product(nums2). Then r1 = r2.
  Preconditions: Both slices nums1 and nums2 satisfy: 1 <= len <= 1000; for every i, 1 <= nums[i] <= 10^4; all elements pairwise distinct. Additionally, len(nums1) = len(nums2) and there exists a bijection π from {0,...,len(nums1)-1} to {0,...,len(nums2)-1} such that nums1[i] = nums2[π(i)] for all i (i.e., nums2 is a permutation of nums1). -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (h1 : ValidSlice nums1)
    (h2 : ValidSlice nums2)
    (hlen : (sliceInts nums1).length = (sliceInts nums2).length)
    (hperm : ∃ π : ℕ → ℕ,
      (∀ i, i < (sliceInts nums1).length → π i < (sliceInts nums2).length) ∧
        (∀ j, j < (sliceInts nums2).length → ∃ i, i < (sliceInts nums1).length ∧ π i = j) ∧
          (∀ i, i < (sliceInts nums1).length →
            elemAt (sliceInts nums1) i = elemAt (sliceInts nums2) (π i))) :
    ∃ r1 r2 : Std.I64,
      tuple_same_product nums1 = ok r1 ∧ tuple_same_product nums2 = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (h1 : ValidSlice nums1)
    (h2 : ValidSlice nums2)
    (hlen : (sliceInts nums1).length = (sliceInts nums2).length)
    (hperm : ∃ π : ℕ → ℕ,
      (∀ i, i < (sliceInts nums1).length → π i < (sliceInts nums2).length) ∧
        (∀ j, j < (sliceInts nums2).length → ∃ i, i < (sliceInts nums1).length ∧ π i = j) ∧
          (∀ i, i < (sliceInts nums1).length →
            elemAt (sliceInts nums1) i = elemAt (sliceInts nums2) (π i))), ∃ r1 r2 : Std.I64,
      tuple_same_product nums1 = ok r1 ∧ tuple_same_product nums2 = ok r2 ∧ r1 = r2) := by
  sorry

/-- Let r = tuple_same_product(nums) and r' = tuple_same_product(nums'). Then r = r'.
  Preconditions: Let nums be a slice satisfying: 1 <= len(nums) <= 1000; for every i, 1 <= nums[i] <= 10^4; all elements pairwise distinct. Let c be a positive integer such that the slice nums' defined by nums'[i] = c * nums[i] for all i also satisfies the same preconditions (in particular, 1 <= nums'[i] <= 10^4 and all elements pairwise distinct). -/
theorem spec_10 (nums nums' : Slice Std.I64) (c : ℤ) (hc : 1 ≤ c)
    (h : ValidSlice nums) (h' : ValidSlice nums')
    (hscale : sliceInts nums' = (sliceInts nums).map (fun x => c * x)) :
    ∃ r r' : Std.I64,
      tuple_same_product nums = ok r ∧ tuple_same_product nums' = ok r' ∧ r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ) (hc : 1 ≤ c)
    (h : ValidSlice nums) (h' : ValidSlice nums')
    (hscale : sliceInts nums' = (sliceInts nums).map (fun x => c * x)), ∃ r r' : Std.I64,
      tuple_same_product nums = ok r ∧ tuple_same_product nums' = ok r' ∧ r = r') := by
  sorry

/-- The function returns a result r (i.e., it does not fail with an overflow, out-of-bounds, or panic).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_11 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r) := by
  sorry

/-- The function returns a result r and r = 0 if and only if for every two disjoint unordered index pairs {i,j} and {k,l} (with 0 <= i < j < len(nums), 0 <= k < l < len(nums), and {i,j} ∩ {k,l} = ∅) we have nums[i]*nums[j] != nums[k]*nums[l].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^4; all elements of nums are pairwise distinct. -/
theorem spec_12 (nums : Slice Std.I64) (h : ValidSlice nums) :
    ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      (r.val = 0 ↔ NoDisjointEqualPairs (sliceInts nums)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : ValidSlice nums), ∃ r : Std.I64, tuple_same_product nums = ok r ∧
      (r.val = 0 ↔ NoDisjointEqualPairs (sliceInts nums))) := by
  sorry

end AegisSpec.TupleSameProduct
