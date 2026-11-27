import Aegis.SubarrayGcd.Code.Funs

/-!
# Specifications of `Aegis.SubarrayGcd.subarray_gcd`

LeetCode problem `number-of-subarrays-with-gcd-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SubarrayGcd

  def i64Max : Int := 9223372036854775807

  def Seg (xs : List Int) (l u : Nat) : List Int := (xs.drop l).take (u + 1 - l)

  def gcdList (xs : List Int) : Nat := (xs.map Int.natAbs).foldl Nat.gcd 0

  def IsGCD (xs : List Int) (d : Int) : Prop :=
    0 < d ∧ (∀ x ∈ xs, d ∣ x) ∧ ∀ e : Int, 0 < e → (∀ x ∈ xs, e ∣ x) → e ∣ d

  def gcdSeg (xs : List Int) (l u : Nat) : Int := ((gcdList (Seg xs l u) : Nat) : Int)

  def GcdIs (xs : List Int) (k : Int) (l u : Nat) : Prop := gcdSeg xs l u = k

  def countPairs : Nat → (Nat → Nat → Bool) → Nat
    | 0, _ => 0
    | n + 1, p => countPairs n p + ((List.range (n + 1)).filter (fun l => p l n)).length

  def countGcdSubarrays (xs : List Int) (k : Int) : Nat :=
    countPairs xs.length (fun l u => decide (gcdSeg xs l u = k))

  def countGcdInBlock (xs : List Int) (k : Int) (a b : Nat) : Nat :=
    countPairs (b + 1 - a) (fun i j => decide (gcdSeg xs (a + i) (a + j) = k))

  def countEq (xs : List Int) (c : Int) : Nat := (xs.filter (fun x => decide (x = c))).length

  def countGcdQuotientSubarrays (xs : List Int) (k : Int) : Nat :=
    countPairs xs.length
      (fun l u => decide (gcdSeg (xs.map (fun x => x / k)) l u = 1))

  def allDvd (k : Int) (xs : List Int) : Bool := xs.all (fun x => decide (k ∣ x))

  def AllDvd (k : Int) (xs : List Int) : Prop := allDvd k xs = true

  def dvdAt (xs : List Int) (k : Int) (j : Nat) : Bool :=
    match xs[j]? with
    | none => false
    | some x => decide (k ∣ x)

  def DvdAt (xs : List Int) (k : Int) (j : Nat) : Prop := dvdAt xs k j = true

  def IsMaxDvdBlock (xs : List Int) (k : Int) (a b : Nat) : Prop :=
    a ≤ b ∧ b < xs.length ∧ AllDvd k (Seg xs a b) ∧
      (a = 0 ∨ ¬ DvdAt xs k (a - 1)) ∧ ¬ DvdAt xs k (b + 1)

  instance decidableIsMaxDvdBlock (xs : List Int) (k : Int) (a b : Nat) :
      Decidable (IsMaxDvdBlock xs k a b) := by
    unfold IsMaxDvdBlock AllDvd DvdAt
    infer_instance

  def maxDvdBlocks (xs : List Int) (k : Int) : List (Nat × Nat) :=
    List.filter (fun p => decide (IsMaxDvdBlock xs k p.1 p.2))
      (List.product (List.range xs.length) (List.range xs.length))

  def sumOverMaxDvdBlocks (xs : List Int) (k : Int) : Nat :=
    (maxDvdBlocks xs k).foldl (fun acc p => acc + countGcdInBlock xs k p.1 p.2) 0

  def ValidInput (nums : Slice Std.I64) (k : Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 1000 ∧
      (∀ (i : Nat) (h : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ i64Max) ∧
      1 ≤ k.val ∧ k.val ≤ i64Max

  /-- The function returns a result r and r equals the number of pairs (l,u) of integers such that 0 <= l <= u < len(nums) and gcd(nums[l], nums[l+1], ..., nums[u]) = k, where gcd of a non-empty finite collection of positive integers is the largest positive integer that divides every element of the collection. The subarray corresponding to (l,u) is non-empty, contiguous, inclusive, and 0-indexed.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∃ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r ∧
        r.val = ((countGcdSubarrays nums.val k.val : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∃ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r ∧
          r.val = ((countGcdSubarrays nums.val k.val : Nat) : Int)) := by
    sorry

  /-- subarray_gcd(nums, k) returns a result r; it does not fail, overflow, panic, or go out of bounds.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∃ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∃ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, 0 <= r.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, r <= len(nums)*(len(nums)+1)/2, the total number of non-empty contiguous subarrays of nums.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          r.val ≤ ((nums.val.length * (nums.val.length + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, r > 0 if and only if there exists a pair (l,u) with 0 <= l <= u < len(nums) such that gcd(nums[l], nums[l+1], ..., nums[u]) = k, where gcd is the greatest positive common divisor.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        (0 < r.val ↔ ∃ l u : Nat, l ≤ u ∧ u < nums.val.length ∧ GcdIs nums.val k.val l u) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          (0 < r.val ↔ ∃ l u : Nat, l ≤ u ∧ u < nums.val.length ∧ GcdIs nums.val k.val l u)) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, r >= the number of indices i with 0 <= i < len(nums) and nums[i] = k.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        ((countEq nums.val k.val : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          ((countEq nums.val k.val : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, r equals the sum, over all maximal contiguous intervals [a,b] of indices with 0 <= a <= b < len(nums) such that k divides nums[j] for every j with a <= j <= b, of the number of pairs (l,u) with a <= l <= u <= b and gcd(nums[l], nums[l+1], ..., nums[u]) = k. A maximal interval is one that cannot be enlarged to the left or right while keeping all its elements divisible by k; the sum is 0 if there is no such interval. Here gcd is the greatest positive common divisor.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; and 1 <= k <= 9223372036854775807. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        r.val = ((sumOverMaxDvdBlocks nums.val k.val : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          r.val = ((sumOverMaxDvdBlocks nums.val k.val : Nat) : Int)) := by
    sorry

  /-- Let nums' be the slice of length len(nums)+1 with nums'[i] = nums[i] for every 0 <= i < len(nums) and nums'[len(nums)] = x. Whenever subarray_gcd(nums, k) returns r and subarray_gcd(nums', k) returns r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; 1 <= k <= 9223372036854775807; x is an integer with 1 <= x <= 9223372036854775807; len(nums) <= 999; and k does not divide x. -/
  theorem spec_8 (nums : Slice Std.I64) (k x : Std.I64) (hpre : ValidInput nums k)
      (hx_lb : 1 ≤ x.val) (hx_ub : x.val ≤ i64Max) (hlen : nums.val.length ≤ 999)
      (hkx : ¬ k.val ∣ x.val) (nums' : Slice Std.I64)
      (h_len : nums'.val.length = nums.val.length + 1)
      (h_agree : ∀ (i : Nat) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
      (h_last : nums'.val[nums.val.length] = x) :
      ∀ r r' : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        Aegis.SubarrayGcd.subarray_gcd nums' k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k x : Std.I64) (hpre : ValidInput nums k)
        (hx_lb : 1 ≤ x.val) (hx_ub : x.val ≤ i64Max) (hlen : nums.val.length ≤ 999)
        (hkx : ¬ k.val ∣ x.val) (nums' : Slice Std.I64)
        (h_len : nums'.val.length = nums.val.length + 1)
        (h_agree : ∀ (i : Nat) (h : i < nums.val.length), nums'.val[i] = nums.val[i])
        (h_last : nums'.val[nums.val.length] = x), ∀ r r' : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          Aegis.SubarrayGcd.subarray_gcd nums' k = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns r and subarray_gcd(nums2, k2) returns r2, we have r = r2.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; 1 <= k <= 9223372036854775807; c is an integer with c >= 1; nums2 is a slice with len(nums2) = len(nums) and nums2[i] = c*nums[i] for every 0 <= i < len(nums); k2 = c*k; and for every i, 1 <= nums2[i] <= 9223372036854775807 and 1 <= k2 <= 9223372036854775807. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
      (c : Int) (hc : 1 ≤ c) (nums2 : Slice Std.I64) (k2 : Std.I64)
      (h_len : nums2.val.length = nums.val.length)
      (h_val : ∀ (i : Nat) (h : i < nums.val.length),
        (nums2.val[i]).val = c * (nums.val[i]).val)
      (h_k2 : k2.val = c * k.val)
      (h_bound : ∀ (i : Nat) (h : i < nums2.val.length),
        1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ i64Max)
      (h_k2_bound : 1 ≤ k2.val ∧ k2.val ≤ i64Max) :
      ∀ r r2 : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        Aegis.SubarrayGcd.subarray_gcd nums2 k2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
        (c : Int) (hc : 1 ≤ c) (nums2 : Slice Std.I64) (k2 : Std.I64)
        (h_len : nums2.val.length = nums.val.length)
        (h_val : ∀ (i : Nat) (h : i < nums.val.length),
          (nums2.val[i]).val = c * (nums.val[i]).val)
        (h_k2 : k2.val = c * k.val)
        (h_bound : ∀ (i : Nat) (h : i < nums2.val.length),
          1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ i64Max)
        (h_k2_bound : 1 ≤ k2.val ∧ k2.val ≤ i64Max), ∀ r r2 : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          Aegis.SubarrayGcd.subarray_gcd nums2 k2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns a result r, r equals the number of pairs (l,u) with 0 <= l <= u < len(nums) such that gcd(nums[l]/k, nums[l+1]/k, ..., nums[u]/k) = 1, where each quotient is an integer and gcd is the greatest positive common divisor.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; 1 <= k <= 9223372036854775807; and k divides nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
      (hdvd : ∀ (i : Nat) (h : i < nums.val.length), k.val ∣ (nums.val[i]).val) :
      ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        r.val = ((countGcdQuotientSubarrays nums.val k.val : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
        (hdvd : ∀ (i : Nat) (h : i < nums.val.length), k.val ∣ (nums.val[i]).val), ∀ r : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          r.val = ((countGcdQuotientSubarrays nums.val k.val : Nat) : Int)) := by
    sorry

  /-- Whenever subarray_gcd(nums, k) returns r and subarray_gcd(revnums, k) returns r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 9223372036854775807; 1 <= k <= 9223372036854775807; and revnums is the slice with len(revnums) = len(nums) and revnums[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
      (revnums : Slice Std.I64) (h_len : revnums.val.length = nums.val.length)
      (h_val : ∀ (i : Nat) (h : i < revnums.val.length),
        (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val) :
      ∀ r r' : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
        Aegis.SubarrayGcd.subarray_gcd revnums k = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (hpre : ValidInput nums k)
        (revnums : Slice Std.I64) (h_len : revnums.val.length = nums.val.length)
        (h_val : ∀ (i : Nat) (h : i < revnums.val.length),
          (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val), ∀ r r' : Std.I64, Aegis.SubarrayGcd.subarray_gcd nums k = ok r →
          Aegis.SubarrayGcd.subarray_gcd revnums k = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.SubarrayGcd
