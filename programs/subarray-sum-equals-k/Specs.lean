import Aegis.SubarraySum.Code.Funs

/-!
# Specifications of `Aegis.SubarraySum.subarray_sum`

LeetCode problem `subarray-sum-equals-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SubarraySum

  namespace AegisSpec.SubarraySum

  def i64Min : ℤ := -9223372036854775808

  def i64Max : ℤ := 9223372036854775807

  def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def segSum (l : List ℤ) (i j : ℕ) : ℤ := ((l.drop i).take (j + 1 - i)).sum

  def countSubarrays (l : List ℤ) (k : ℤ) : ℕ :=
    (((Finset.range l.length).product (Finset.range l.length)).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ segSum l p.1 p.2 = k)).card

  def prefixSum (l : List ℤ) : ℕ → ℤ
    | 0 => 0
    | n + 1 => prefixSum l n + l.getD n 0

  def countPrefixPairs (l : List ℤ) (k : ℤ) : ℕ :=
    (((Finset.range (l.length + 1)).product (Finset.range (l.length + 1))).filter
      (fun p : ℕ × ℕ => p.1 < p.2 ∧ prefixSum l p.2 - prefixSum l p.1 = k)).card

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    Slice.from nums.val.reverse (by simp)

  def negSlice (nums : Slice Std.I64)
      (h : ∀ i : Fin nums.val.length,
        i64Min ≤ -(nums.val.get i).val ∧ -(nums.val.get i).val ≤ i64Max) :
      Slice Std.I64 :=
    Slice.from
      (List.ofFn fun i : Fin nums.val.length =>
        Std.I64.ofInt (-(nums.val.get i).val) (h i))
      (by simp)

  def scaleSlice (c : ℤ) (nums : Slice Std.I64)
      (h : ∀ i : Fin nums.val.length,
        i64Min ≤ c * (nums.val.get i).val ∧ c * (nums.val.get i).val ≤ i64Max) :
      Slice Std.I64 :=
    Slice.from
      (List.ofFn fun i : Fin nums.val.length =>
        Std.I64.ofInt (c * (nums.val.get i).val) (h i))
      (by simp)

  def scaleScalar (c : ℤ) (k : Std.I64) (h : i64Min ≤ c * k.val ∧ c * k.val ≤ i64Max) :
      Std.I64 :=
    Std.I64.ofInt (c * k.val) h

  def negScalar (k : Std.I64) (h : i64Min ≤ -k.val ∧ -k.val ≤ i64Max) : Std.I64 :=
    Std.I64.ofInt (-k.val) h

  lemma i64_neg_of_bounds_1000 (x : Std.I64) (h : -1000 ≤ x.val ∧ x.val ≤ 1000) :
      i64Min ≤ -x.val ∧ -x.val ≤ i64Max := by
    simp only [i64Min, i64Max]
    omega

  lemma i64_neg_of_bounds_1e7 (x : Std.I64) (h : -10 ^ 7 ≤ x.val ∧ x.val ≤ 10 ^ 7) :
      i64Min ≤ -x.val ∧ -x.val ≤ i64Max := by
    simp only [i64Min, i64Max]
    omega

  /-- The function returns a result r (i.e., it does not fail) and r equals the number of pairs (i, j) of integers such that 0 <= i <= j < len(nums) and the sum of nums[t] for t from i to j inclusive equals k.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ r.val = (countSubarrays (contents nums) k.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ r.val = (countSubarrays (contents nums) k.val : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(nums) * (len(nums) + 1) / 2.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ 0 ≤ r.val
        ∧ r.val ≤ (nums.val.length * (nums.val.length + 1) / 2 : ℕ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ 0 ≤ r.val
          ∧ r.val ≤ (nums.val.length * (nums.val.length + 1) / 2 : ℕ)) := by
    sorry

  /-- The function returns a result r and r = 1 if nums[0] = k, and r = 0 otherwise.
    Preconditions: len(nums) = 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : nums.val.length = 1) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ r.val = if (nums.val[0]!).val = k.val then 1 else 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : nums.val.length = 1) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ r.val = if (nums.val[0]!).val = k.val then 1 else 0) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), nums[i] > 0 and nums[i] <= 1000, and k <= 0 with -10^7 <= k. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        0 < (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 0) :
      ∃ r, subarray_sum nums k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          0 < (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 0), ∃ r, subarray_sum nums k = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r and r = len(nums) * (len(nums) + 1) / 2.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), nums[i] = 0, and k = 0. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = 0)
      (hk : k.val = 0) :
      ∃ r, subarray_sum nums k = ok r
        ∧ r.val = (nums.val.length * (nums.val.length + 1) / 2 : ℕ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]).val = 0)
        (hk : k.val = 0), ∃ r, subarray_sum nums k = ok r
          ∧ r.val = (nums.val.length * (nums.val.length + 1) / 2 : ℕ)) := by
    sorry

  /-- The function returns a result r and r > 0 if and only if there exists a pair (i, j) with 0 <= i <= j < len(nums) such that the sum of nums[t] for t from i to j inclusive equals k.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ (0 < r.val
          ↔ ∃ (i j : ℕ), i ≤ j ∧ j < nums.val.length
              ∧ segSum (contents nums) i j = k.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ (0 < r.val
            ↔ ∃ (i j : ℕ), i ≤ j ∧ j < nums.val.length
                ∧ segSum (contents nums) i j = k.val)) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if for every pair (i, j) with 0 <= i <= j < len(nums), the sum of nums[t] for t from i to j inclusive is not equal to k.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ (r.val = 0
          ↔ ∀ (i j : ℕ), i ≤ j → j < nums.val.length
              → segSum (contents nums) i j ≠ k.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ (r.val = 0
            ↔ ∀ (i j : ℕ), i ≤ j → j < nums.val.length
                → segSum (contents nums) i j ≠ k.val)) := by
    sorry

  /-- Let r be the result of subarray_sum(nums, k) and let r_rev be the result of subarray_sum on the slice whose i-th element is nums[len(nums) - 1 - i] for 0 <= i < len(nums), with the same k. Then r = r_rev.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r r_rev, subarray_sum nums k = ok r
        ∧ subarray_sum (revSlice nums) k = ok r_rev
        ∧ r = r_rev := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r r_rev, subarray_sum nums k = ok r
          ∧ subarray_sum (revSlice nums) k = ok r_rev
          ∧ r = r_rev) := by
    sorry

  /-- Let r be the result of subarray_sum(nums, k) and let r_neg be the result of subarray_sum on the slice whose i-th element is -nums[i] for 0 <= i < len(nums), with parameter -k. Then r = r_neg.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r r_neg,
        subarray_sum nums k = ok r
        ∧ subarray_sum
            (negSlice nums fun i => i64_neg_of_bounds_1000 _ (hbounds i.val i.isLt))
            (negScalar k (i64_neg_of_bounds_1e7 k hk))
          = ok r_neg
        ∧ r = r_neg := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r r_neg,
          subarray_sum nums k = ok r
          ∧ subarray_sum
              (negSlice nums fun i => i64_neg_of_bounds_1000 _ (hbounds i.val i.isLt))
              (negScalar k (i64_neg_of_bounds_1e7 k hk))
            = ok r_neg
          ∧ r = r_neg) := by
    sorry

  /-- Let P be the sequence of length len(nums) + 1 defined by P[0] = 0 and P[i+1] = P[i] + nums[i] for 0 <= i < len(nums). The function returns a result r and r equals the number of pairs (i, j) of integers such that 0 <= i < j <= len(nums) and P[j] - P[i] = k.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7) :
      ∃ r, subarray_sum nums k = ok r
        ∧ r.val = (countPrefixPairs (contents nums) k.val : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7), ∃ r, subarray_sum nums k = ok r
          ∧ r.val = (countPrefixPairs (contents nums) k.val : ℤ)) := by
    sorry

  /-- If k < -1000 * len(nums) or k > 1000 * len(nums), then the function returns a result r and r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7)
      (hout : k.val < -(1000 * (nums.val.length : ℤ))
        ∨ 1000 * (nums.val.length : ℤ) < k.val) :
      ∃ r, subarray_sum nums k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7)
        (hout : k.val < -(1000 * (nums.val.length : ℤ))
          ∨ 1000 * (nums.val.length : ℤ) < k.val), ∃ r, subarray_sum nums k = ok r ∧ r.val = 0) := by
    sorry

  /-- Let r be the result of subarray_sum(nums, k) and let r_scaled be the result of subarray_sum on the slice whose i-th element is c * nums[i] for 0 <= i < len(nums), with parameter c * k. Then both calls return results and r = r_scaled.
    Preconditions: len(nums) >= 1, len(nums) <= 2 * 10^4, for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000, and -10^7 <= k <= 10^7. Additionally, c is a positive integer, and the following values all lie within the 64-bit signed integer range: c * nums[i] for every i, c * k, and for every prefix sum P[i] = nums[0] + ... + nums[i-1] (with P[0] = 0 and 0 <= i <= len(nums)), both c * P[i] and c * P[i] - c * k. -/
  theorem spec_13 (nums : Slice Std.I64) (k : Std.I64) (c : ℤ)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
      (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
        -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7)
      (hc : 0 < c)
      (hscale : ∀ (i : ℕ) (hi : i < nums.val.length),
        i64Min ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ i64Max)
      (hk_scaled : i64Min ≤ c * k.val ∧ c * k.val ≤ i64Max)
      (hP : ∀ (i : ℕ), i ≤ nums.val.length →
        i64Min ≤ c * prefixSum (contents nums) i
          ∧ c * prefixSum (contents nums) i ≤ i64Max)
      (hPk : ∀ (i : ℕ), i ≤ nums.val.length →
        i64Min ≤ c * prefixSum (contents nums) i - c * k.val
          ∧ c * prefixSum (contents nums) i - c * k.val ≤ i64Max) :
      ∃ r r_scaled,
        subarray_sum nums k = ok r
        ∧ subarray_sum
            (scaleSlice c nums fun i => hscale i.val i.isLt)
            (scaleScalar c k hk_scaled)
          = ok r_scaled
        ∧ r = r_scaled := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (c : ℤ)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 2 * 10 ^ 4)
        (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
          -1000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (hk : -10 ^ 7 ≤ k.val ∧ k.val ≤ 10 ^ 7)
        (hc : 0 < c)
        (hscale : ∀ (i : ℕ) (hi : i < nums.val.length),
          i64Min ≤ c * (nums.val[i]).val ∧ c * (nums.val[i]).val ≤ i64Max)
        (hk_scaled : i64Min ≤ c * k.val ∧ c * k.val ≤ i64Max)
        (hP : ∀ (i : ℕ), i ≤ nums.val.length →
          i64Min ≤ c * prefixSum (contents nums) i
            ∧ c * prefixSum (contents nums) i ≤ i64Max)
        (hPk : ∀ (i : ℕ), i ≤ nums.val.length →
          i64Min ≤ c * prefixSum (contents nums) i - c * k.val
            ∧ c * prefixSum (contents nums) i - c * k.val ≤ i64Max), ∃ r r_scaled,
          subarray_sum nums k = ok r
          ∧ subarray_sum
              (scaleSlice c nums fun i => hscale i.val i.isLt)
              (scaleScalar c k hk_scaled)
            = ok r_scaled
          ∧ r = r_scaled) := by
    sorry

  end AegisSpec.SubarraySum
