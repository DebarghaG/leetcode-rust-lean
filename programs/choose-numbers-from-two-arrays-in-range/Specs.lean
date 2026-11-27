import Aegis.CountSubranges.Code.Funs

/-!
# Specifications of `Aegis.CountSubranges.count_subranges`

LeetCode problem `choose-numbers-from-two-arrays-in-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountSubranges

  namespace AegisSpec.CountSubranges

  def entry (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  theorem entry_eq_getElem (nums : Slice Std.I64) (i : ℕ) (h : i < nums.val.length) :
      entry nums i = (nums.val[i]'h).val := by
    simp only [entry, List.getElem?_eq_getElem h]

  def C (nums1 nums2 : Slice Std.I64) (l r : ℕ) : ℕ :=
    ((Finset.Icc l r).powerset.filter
      (fun S => ∑ i ∈ S, (entry nums1 i + entry nums2 i)
        = ∑ i ∈ Finset.Icc l r, entry nums2 i)).card

  def Btotal (nums1 nums2 : Slice Std.I64) (n : ℕ) : ℕ :=
    ∑ l ∈ Finset.range n, ∑ r ∈ Finset.Ico l n, C nums1 nums2 l r

  def zerosIn (nums : Slice Std.I64) (l r : ℕ) : ℕ :=
    ((Finset.Icc l r).filter (fun i => entry nums i = 0)).card

  def zerosBelow (nums : Slice Std.I64) (n : ℕ) : ℕ :=
    ((Finset.range n).filter (fun i => entry nums i = 0)).card

  def Bpow (nums : Slice Std.I64) (n : ℕ) : ℕ :=
    ∑ l ∈ Finset.range n, ∑ r ∈ Finset.Ico l n, 2 ^ zerosIn nums l r

  def Cm (c d : ℤ) (m : ℕ) : ℤ :=
    ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℤ) * (if (k : ℤ) * (c + d) = (m : ℤ) * d then 1 else 0)

  def Buniform (c d : ℤ) (n : ℕ) : ℤ :=
    ∑ m ∈ Finset.Ico 1 (n + 1), ((n - m + 1 : ℕ) : ℤ) * Cm c d m

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    ⟨nums.val.reverse.length, Aeneas.Data.ListN.ListN.fromList nums.val.reverse, by simp⟩

  theorem revSlice_val (nums : Slice Std.I64) : (revSlice nums).val = nums.val.reverse := by
    have h : ∀ l : List Std.I64, (Aeneas.Data.ListN.ListN.fromList l).toList = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        rw [show Aeneas.Data.ListN.ListN.fromList (x :: xs)
              = Aeneas.Data.ListN.ListN.cons x (Aeneas.Data.ListN.ListN.fromList xs) from rfl]
        rw [show (Aeneas.Data.ListN.ListN.cons x (Aeneas.Data.ListN.ListN.fromList xs)).toList
              = x :: (Aeneas.Data.ListN.ListN.fromList xs).toList from rfl, ih]
    simpa [revSlice, Slice.val] using h nums.val.reverse

  /-- Let M = 1000000007. For each pair (l,r) with 0 <= l <= r < n, let C(l,r) be the number of subsets S of {l,l+1,...,r} such that sum_{i in S} (nums1[i] + nums2[i]) = sum_{i=l}^{r} nums2[i]. Let B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} C(l,r). The function returns a result r, interpreted as an integer, and r = B mod M, i.e. r is the unique integer with 0 <= r < M and r congruent to B modulo M. Equivalently, S is the set of indices where nums1 is chosen and its complement in [l,r] is where nums2 is chosen; two choices on the same range are counted separately.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access out of bounds.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r on an allowed input, 0 <= r < M, where M = 1000000007. In particular, the returned I64 value is within its representable range.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      ∀ r : Std.I64, count_subranges nums1 nums2 = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), ∀ r : Std.I64, count_subranges nums1 nums2 = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- If n = 1, then the function returns r = (if nums1[0] = 0 then 1 else 0) + (if nums2[0] = 0 then 1 else 0).
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hn : n = 1) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = (if entry nums1 0 = 0 then (1 : ℤ) else 0)
          + (if entry nums2 0 = 0 then (1 : ℤ) else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hn : n = 1), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (if entry nums1 0 = 0 then (1 : ℤ) else 0)
            + (if entry nums2 0 = 0 then (1 : ℤ) else 0)) := by
    sorry

  /-- If nums1[i] = 0 and nums2[i] = 0 for every i with 0 <= i < n, then the function returns r = (2^(n+2) - 2n - 4) mod M, with M = 1000000007.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hz1 : ∀ i, i < n → entry nums1 i = 0)
      (hz2 : ∀ i, i < n → entry nums2 i = 0) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = ((2 : ℤ) ^ (n + 2) - 2 * (n : ℤ) - 4) % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hz1 : ∀ i, i < n → entry nums1 i = 0)
        (hz2 : ∀ i, i < n → entry nums2 i = 0), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = ((2 : ℤ) ^ (n + 2) - 2 * (n : ℤ) - 4) % 1000000007) := by
    sorry

  /-- If nums2[i] = 0 for every i with 0 <= i < n, then let z(l,r) = #{i : l <= i <= r and nums1[i] = 0} for each range [l,r]. Set B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} 2^(z(l,r)). The function returns r = B mod M, where M = 1000000007.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hz : ∀ i, i < n → entry nums2 i = 0) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = (Bpow nums1 n : ℤ) % 1000000007 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hz : ∀ i, i < n → entry nums2 i = 0), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Bpow nums1 n : ℤ) % 1000000007) := by
    sorry

  /-- If nums1[i] = 0 for every i with 0 <= i < n, then let z2(l,r) = #{i : l <= i <= r and nums2[i] = 0}. Set B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} 2^(z2(l,r)). The function returns r = B mod M, where M = 1000000007.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hz : ∀ i, i < n → entry nums1 i = 0) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = (Bpow nums2 n : ℤ) % 1000000007 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hz : ∀ i, i < n → entry nums1 i = 0), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Bpow nums2 n : ℤ) % 1000000007) := by
    sorry

  /-- For every allowed input, let r be the result of count_subranges(nums1, nums2) and let s be the result of count_subranges(nums2, nums1). Both calls return results, and r = s.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      ∃ r s : Std.I64, count_subranges nums1 nums2 = ok r ∧
        count_subranges nums2 nums1 = ok s ∧ r = s := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), ∃ r s : Std.I64, count_subranges nums1 nums2 = ok r ∧
          count_subranges nums2 nums1 = ok s ∧ r = s) := by
    sorry

  /-- If n <= 27, then let B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} C(l,r), where C(l,r) is the number of subsets S of {l,l+1,...,r} satisfying sum_{i in S}(nums1[i]+nums2[i]) = sum_{i=l}^{r} nums2[i]. Then B < M = 1000000007, and the function returns r = B (not merely B mod M).
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hn : n ≤ 27) :
      (Btotal nums1 nums2 n : ℤ) < 1000000007 ∧
        ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Btotal nums1 nums2 n : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hn : n ≤ 27), (Btotal nums1 nums2 n : ℤ) < 1000000007 ∧
          ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
            r.val = (Btotal nums1 nums2 n : ℤ)) := by
    sorry

  /-- If n = 2, write a0=nums1[0], a1=nums1[1], b0=nums2[0], b1=nums2[1], and for a proposition P let [P] be 1 if P is true and 0 otherwise. Then the function returns r = [a0=0] + [b0=0] + [a1=0] + [b1=0] + [b0=0 and b1=0] + [a0=b1] + [a1=b0] + [a0=0 and a1=0].
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (hn : n = 2) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = (if entry nums1 0 = 0 then (1 : ℤ) else 0)
          + (if entry nums2 0 = 0 then (1 : ℤ) else 0)
          + (if entry nums1 1 = 0 then (1 : ℤ) else 0)
          + (if entry nums2 1 = 0 then (1 : ℤ) else 0)
          + (if entry nums2 0 = 0 ∧ entry nums2 1 = 0 then (1 : ℤ) else 0)
          + (if entry nums1 0 = entry nums2 1 then (1 : ℤ) else 0)
          + (if entry nums1 1 = entry nums2 0 then (1 : ℤ) else 0)
          + (if entry nums1 0 = 0 ∧ entry nums1 1 = 0 then (1 : ℤ) else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (hn : n = 2), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (if entry nums1 0 = 0 then (1 : ℤ) else 0)
            + (if entry nums2 0 = 0 then (1 : ℤ) else 0)
            + (if entry nums1 1 = 0 then (1 : ℤ) else 0)
            + (if entry nums2 1 = 0 then (1 : ℤ) else 0)
            + (if entry nums2 0 = 0 ∧ entry nums2 1 = 0 then (1 : ℤ) else 0)
            + (if entry nums1 0 = entry nums2 1 then (1 : ℤ) else 0)
            + (if entry nums1 1 = entry nums2 0 then (1 : ℤ) else 0)
            + (if entry nums1 0 = 0 ∧ entry nums1 1 = 0 then (1 : ℤ) else 0)) := by
    sorry

  /-- If there exist integers c,d with 0 <= c <= 100 and 0 <= d <= 100 such that nums1[i] = c and nums2[i] = d for every i, then for each m = 1,...,n let C_m = sum_{k=0}^{m} binom(m,k) * [k(c+d) = m d], where binom(m,k) is the binomial coefficient and [P] is 1 if P is true and 0 otherwise. Set B = sum_{m=1}^{n} (n-m+1) C_m. The function returns r = B mod M, where M = 1000000007.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_11 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
      (c d : ℤ) (hc : 0 ≤ c ∧ c ≤ 100) (hd : 0 ≤ d ∧ d ≤ 100)
      (hc' : ∀ i, i < n → entry nums1 i = c)
      (hd' : ∀ i, i < n → entry nums2 i = d) :
      ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
        r.val = Buniform c d n % 1000000007 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100)
        (c d : ℤ) (hc : 0 ≤ c ∧ c ≤ 100) (hd : 0 ≤ d ∧ d ≤ 100)
        (hc' : ∀ i, i < n → entry nums1 i = c)
        (hd' : ∀ i, i < n → entry nums2 i = d), ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = Buniform c d n % 1000000007) := by
    sorry

  /-- For every allowed input, let B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} C(l,r), where C(l,r) is the number of subsets S of {l,l+1,...,r} satisfying sum_{i in S}(nums1[i]+nums2[i]) = sum_{i=l}^{r} nums2[i]. Then B <= 2^(n+2) - 2n - 4, the total number of (nonempty range, selection) pairs. Consequently the returned value is the residue modulo M of an integer in this range.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_12 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      (Btotal nums1 nums2 n : ℤ) ≤ (2 : ℤ) ^ (n + 2) - 2 * (n : ℤ) - 4 ∧
        ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), (Btotal nums1 nums2 n : ℤ) ≤ (2 : ℤ) ^ (n + 2) - 2 * (n : ℤ) - 4 ∧
          ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
            r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007) := by
    sorry

  /-- For every allowed input, let B = sum_{l=0}^{n-1} sum_{r=l}^{n-1} C(l,r), where C(l,r) is the number of subsets S of {l,l+1,...,r} satisfying sum_{i in S}(nums1[i]+nums2[i]) = sum_{i=l}^{r} nums2[i]. Let Z = #{i : 0 <= i < n and nums1[i]=0} + #{i : 0 <= i < n and nums2[i]=0}. Then B >= Z. The returned value is B mod M, where M = 1000000007.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_13 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      (zerosBelow nums1 n : ℤ) + (zerosBelow nums2 n : ℤ)
          ≤ (Btotal nums1 nums2 n : ℤ) ∧
        ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
          r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), (zerosBelow nums1 n : ℤ) + (zerosBelow nums2 n : ℤ)
            ≤ (Btotal nums1 nums2 n : ℤ) ∧
          ∃ r : Std.I64, count_subranges nums1 nums2 = ok r ∧
            r.val = (Btotal nums1 nums2 n : ℤ) % 1000000007) := by
    sorry

  /-- For every allowed input, let nums1' and nums2' be the reversals of nums1 and nums2, so nums1'[j] = nums1[n-1-j] and nums2'[j] = nums2[n-1-j] for 0 <= j < n. Then both count_subranges(nums1, nums2) and count_subranges(nums1', nums2') return results, and the two results are equal.
    Preconditions: len(nums1) = len(nums2) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100 and 0 <= nums2[i] <= 100. -/
  theorem spec_14 (nums1 nums2 : Slice Std.I64) (n : ℕ)
      (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
      (hb : ∀ i, i < n →
        0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
        0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100) :
      ∃ r s : Std.I64, count_subranges nums1 nums2 = ok r ∧
        count_subranges (revSlice nums1) (revSlice nums2) = ok s ∧ r = s := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (n : ℕ)
        (h1 : nums1.val.length = n) (h2 : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
        (hb : ∀ i, i < n →
          0 ≤ entry nums1 i ∧ entry nums1 i ≤ 100 ∧
          0 ≤ entry nums2 i ∧ entry nums2 i ≤ 100), ∃ r s : Std.I64, count_subranges nums1 nums2 = ok r ∧
          count_subranges (revSlice nums1) (revSlice nums2) = ok s ∧ r = s) := by
    sorry

  end AegisSpec.CountSubranges
