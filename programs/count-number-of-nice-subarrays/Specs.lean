import Aegis.NumberOfSubarrays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubarrays.number_of_subarrays`

LeetCode problem `count-number-of-nice-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.NumberOfSubarrays

  namespace AegisSpec.NumberOfSubarrays

  def ints (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def IsOdd (x : ℤ) : Prop := x % 2 ≠ 0

  def oddB (x : ℤ) : Bool := x % 2 != 0

  def OddAt (xs : List ℤ) (i : ℕ) : Bool :=
    match xs[i]? with
    | some x => oddB x
    | none => false

  def oddPrefix (xs : List ℤ) (m : ℕ) : ℕ :=
    (List.range m).countP (fun t => OddAt xs t)

  def totalOdd (xs : List ℤ) : ℕ := oddPrefix xs xs.length

  def oddCount (xs : List ℤ) (i j : ℕ) : ℕ :=
    (List.range (j + 1 - i)).countP (fun t => OddAt xs (i + t))

  def HasKOdds (xs : List ℤ) (k : ℤ) (i j : ℕ) : Prop := (oddCount xs i j : ℤ) = k

  def subarrayPairs (xs : List ℤ) : List (ℕ × ℕ) :=
    (List.range xs.length).flatMap (fun i =>
      (List.range (xs.length - i)).map (fun t => (i, i + t)))

  def numSubarrays (xs : List ℤ) (k : ℤ) : ℕ :=
    (subarrayPairs xs).countP (fun p => ((oddCount xs p.1 p.2 : ℤ) == k))

  def prefixCount (xs : List ℤ) (k : ℤ) : ℕ :=
    (List.range xs.length).countP (fun j => ((oddCount xs 0 j : ℤ) == k))

  def prefixCountInclEmpty (xs : List ℤ) (k : ℤ) : ℕ :=
    (List.range (xs.length + 1)).countP (fun m => ((oddPrefix xs m : ℤ) == k))

  def suffixCount (xs : List ℤ) (k : ℤ) : ℕ :=
    (List.range xs.length).countP (fun i => ((oddCount xs i (xs.length - 1) : ℤ) == k))

  def AllOdd (xs : List ℤ) : Prop := ∀ x ∈ xs, IsOdd x

  def allOdd (xs : List ℤ) : Bool := xs.all oddB

  def SameParity (xs ys : List ℤ) : Prop := List.Forall₂ (fun x y => x % 2 = y % 2) xs ys

  def InRange (xs : List ℤ) : Prop := ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 100000

  /-- Whenever the function returns a result r, r equals the number of pairs of indices (i, j) such that 0 <= i <= j < len(nums) and the contiguous nonempty subarray nums[i..j] contains exactly k odd values. Here nums[i..j] includes both endpoints, and a value x is odd iff x mod 2 != 0.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums)) :
      ∀ r, number_of_subarrays nums k = ok r →
        r.val = (numSubarrays (ints nums) k.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums)), ∀ r, number_of_subarrays nums k = ok r →
          r.val = (numSubarrays (ints nums) k.val : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail (for example, it does not panic or overflow) on any input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums)) :
      ∃ r, number_of_subarrays nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums)), ∃ r, number_of_subarrays nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(nums)*(len(nums)+1)/2.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums)) :
      ∀ r, number_of_subarrays nums k = ok r →
        0 ≤ r.val ∧
          r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums)), ∀ r, number_of_subarrays nums k = ok r →
          0 ≤ r.val ∧
            r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5; let m be the number of indices i with 0 <= i < len(nums) such that nums[i] is odd; assume m < k. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (hm : (totalOdd (ints nums) : ℤ) < k.val) :
      ∀ r, number_of_subarrays nums k = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (hm : (totalOdd (ints nums) : ℤ) < k.val), ∀ r, number_of_subarrays nums k = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r >= m - k + 1.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5; let m be the number of indices i with 0 <= i < len(nums) such that nums[i] is odd; assume m >= k. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (hm : k.val ≤ (totalOdd (ints nums) : ℤ)) :
      ∀ r, number_of_subarrays nums k = ok r →
        (totalOdd (ints nums) : ℤ) - k.val + 1 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (hm : k.val ≤ (totalOdd (ints nums) : ℤ)), ∀ r, number_of_subarrays nums k = ok r →
          (totalOdd (ints nums) : ℤ) - k.val + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = (p + 1) * (len(nums) - q).
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5; let m be the number of indices i with 0 <= i < len(nums) such that nums[i] is odd; assume m = k; let p be the smallest index i with 0 <= i < len(nums) and nums[i] odd; let q be the largest such index; p and q exist because m = k >= 1. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (p q : ℕ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (hm : (totalOdd (ints nums) : ℤ) = k.val)
      (hp_lt : p < nums.val.length) (hp_odd : OddAt (ints nums) p = true)
      (hp_min : ∀ i, i < p → OddAt (ints nums) i = false)
      (hq_lt : q < nums.val.length) (hq_odd : OddAt (ints nums) q = true)
      (hq_max : ∀ i, q < i → i < nums.val.length → OddAt (ints nums) i = false) :
      ∀ r, number_of_subarrays nums k = ok r →
        r.val = ((p : ℤ) + 1) * ((nums.val.length : ℤ) - (q : ℤ)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (p q : ℕ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (hm : (totalOdd (ints nums) : ℤ) = k.val)
        (hp_lt : p < nums.val.length) (hp_odd : OddAt (ints nums) p = true)
        (hp_min : ∀ i, i < p → OddAt (ints nums) i = false)
        (hq_lt : q < nums.val.length) (hq_odd : OddAt (ints nums) q = true)
        (hq_max : ∀ i, q < i → i < nums.val.length → OddAt (ints nums) i = false), ∀ r, number_of_subarrays nums k = ok r →
          r.val = ((p : ℤ) + 1) * ((nums.val.length : ℤ) - (q : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = len(nums) - k + 1.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5; every element nums[i] with 0 <= i < len(nums) is odd. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (hall : AllOdd (ints nums)) :
      ∀ r, number_of_subarrays nums k = ok r →
        r.val = (nums.val.length : ℤ) - k.val + 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (hall : AllOdd (ints nums)), ∀ r, number_of_subarrays nums k = ok r →
          r.val = (nums.val.length : ℤ) - k.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if every element of nums is odd, and r = 0 otherwise.
    Preconditions: 1 <= len(nums) <= 50000; k = len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk : k.val = (nums.val.length : ℤ))
      (hrange : InRange (ints nums)) :
      ∀ r, number_of_subarrays nums k = ok r →
        r.val = if allOdd (ints nums) then 1 else 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk : k.val = (nums.val.length : ℤ))
        (hrange : InRange (ints nums)), ∀ r, number_of_subarrays nums k = ok r →
          r.val = if allOdd (ints nums) then 1 else 0) := by
    sorry

  /-- Whenever the function returns r1 on input (nums1, k) and r2 on input (nums2, k), r1 = r2.
    Preconditions: Let nums1 and nums2 be slices. Assume 1 <= len(nums1) = len(nums2) <= 50000; 1 <= k <= len(nums1); for every i with 0 <= i < len(nums1), 1 <= nums1[i] <= 10^5, 1 <= nums2[i] <= 10^5, and nums1[i] mod 2 = nums2[i] mod 2. -/
  theorem spec_9 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums1.val.length)
      (hlen_eq : nums1.val.length = nums2.val.length)
      (hlen_hi : nums1.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums1.val.length : ℤ))
      (hrange1 : InRange (ints nums1)) (hrange2 : InRange (ints nums2))
      (hpar : SameParity (ints nums1) (ints nums2)) :
      ∀ r1 r2, number_of_subarrays nums1 k = ok r1 →
        number_of_subarrays nums2 k = ok r2 → r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums1.val.length)
        (hlen_eq : nums1.val.length = nums2.val.length)
        (hlen_hi : nums1.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums1.val.length : ℤ))
        (hrange1 : InRange (ints nums1)) (hrange2 : InRange (ints nums2))
        (hpar : SameParity (ints nums1) (ints nums2)), ∀ r1 r2, number_of_subarrays nums1 k = ok r1 →
          number_of_subarrays nums2 k = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever the function returns r on input (nums, k) and r' on input (rev, k), r = r'.
    Preconditions: 1 <= len(nums) <= 50000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^5; let rev be the slice of length len(nums) with rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). -/
  theorem spec_10 (nums rev : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (hrev : ints rev = (ints nums).reverse) :
      ∀ r r', number_of_subarrays nums k = ok r →
        number_of_subarrays rev k = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 50000)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (hrev : ints rev = (ints nums).reverse), ∀ r r', number_of_subarrays nums k = ok r →
          number_of_subarrays rev k = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on input (nums, k) and r' on input (nums', k), r' = r + P, where P is the number of indices j with 0 <= j < n such that the prefix nums[0..j] contains exactly k odd values.
    Preconditions: Let nums be a slice with 1 <= len(nums) <= 49999; let n = len(nums); 1 <= k <= n; for every i with 0 <= i < n, 1 <= nums[i] <= 10^5. Let e be an integer with 1 <= e <= 10^5 and e even. Let nums' be the slice of length n+1 with nums'[0] = e and nums'[i+1] = nums[i] for every 0 <= i < n. Thus len(nums') <= 50000. -/
  theorem spec_11 (nums nums' : Slice Std.I64) (k : Std.I64) (e : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (he_lo : 1 ≤ e) (he_hi : e ≤ 100000) (he_even : e % 2 = 0)
      (hnums' : ints nums' = e :: ints nums) :
      ∀ r r', number_of_subarrays nums k = ok r →
        number_of_subarrays nums' k = ok r' →
        r'.val = r.val + (prefixCount (ints nums) k.val : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (e : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (he_lo : 1 ≤ e) (he_hi : e ≤ 100000) (he_even : e % 2 = 0)
        (hnums' : ints nums' = e :: ints nums), ∀ r r', number_of_subarrays nums k = ok r →
          number_of_subarrays nums' k = ok r' →
          r'.val = r.val + (prefixCount (ints nums) k.val : ℤ)) := by
    sorry

  /-- Whenever the function returns r on input (nums, k) and r' on input (nums', k), r' = r + Q, where Q is the number of prefixes of nums, including the empty prefix, whose number of odd values is exactly k-1. More explicitly, Q is the number of j with -1 <= j < n such that the prefix for j (empty when j = -1, and nums[0..j] when j >= 0) contains exactly k-1 odd values.
    Preconditions: Let nums be a slice with 1 <= len(nums) <= 49999; let n = len(nums); 1 <= k <= n; for every i with 0 <= i < n, 1 <= nums[i] <= 10^5. Let o be an integer with 1 <= o <= 10^5 and o odd. Let nums' be the slice of length n+1 with nums'[0] = o and nums'[i+1] = nums[i] for every 0 <= i < n. Thus len(nums') <= 50000. -/
  theorem spec_12 (nums nums' : Slice Std.I64) (k : Std.I64) (o : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (ho_lo : 1 ≤ o) (ho_hi : o ≤ 100000) (ho_odd : o % 2 ≠ 0)
      (hnums' : ints nums' = o :: ints nums) :
      ∀ r r', number_of_subarrays nums k = ok r →
        number_of_subarrays nums' k = ok r' →
        r'.val = r.val + (prefixCountInclEmpty (ints nums) (k.val - 1) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (o : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (ho_lo : 1 ≤ o) (ho_hi : o ≤ 100000) (ho_odd : o % 2 ≠ 0)
        (hnums' : ints nums' = o :: ints nums), ∀ r r', number_of_subarrays nums k = ok r →
          number_of_subarrays nums' k = ok r' →
          r'.val = r.val + (prefixCountInclEmpty (ints nums) (k.val - 1) : ℤ)) := by
    sorry

  /-- Whenever the function returns r on input (nums, k) and r' on input (nums', k), r' = r + S, where S is the number of indices i with 0 <= i < n such that the suffix nums[i..n-1] contains exactly k odd values.
    Preconditions: Let nums be a slice with 1 <= len(nums) <= 49999; let n = len(nums); 1 <= k <= n; for every i with 0 <= i < n, 1 <= nums[i] <= 10^5. Let e be an integer with 1 <= e <= 10^5 and e even. Let nums' be the slice of length n+1 with nums'[i] = nums[i] for every 0 <= i < n and nums'[n] = e. Thus len(nums') <= 50000. -/
  theorem spec_13 (nums nums' : Slice Std.I64) (k : Std.I64) (e : ℤ)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
      (hrange : InRange (ints nums))
      (he_lo : 1 ≤ e) (he_hi : e ≤ 100000) (he_even : e % 2 = 0)
      (hnums' : ints nums' = ints nums ++ [e]) :
      ∀ r r', number_of_subarrays nums k = ok r →
        number_of_subarrays nums' k = ok r' →
        r'.val = r.val + (suffixCount (ints nums) k.val : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (e : ℤ)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 49999)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ (nums.val.length : ℤ))
        (hrange : InRange (ints nums))
        (he_lo : 1 ≤ e) (he_hi : e ≤ 100000) (he_even : e % 2 = 0)
        (hnums' : ints nums' = ints nums ++ [e]), ∀ r r', number_of_subarrays nums k = ok r →
          number_of_subarrays nums' k = ok r' →
          r'.val = r.val + (suffixCount (ints nums) k.val : ℤ)) := by
    sorry

  end AegisSpec.NumberOfSubarrays
