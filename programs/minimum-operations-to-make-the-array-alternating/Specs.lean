import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-operations-to-make-the-array-alternating`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperations

  def IsPos64 (x : ℤ) : Prop := 1 ≤ x ∧ x ≤ 2 ^ 63 - 1

  def valAt (nums : Slice Std.I64) (i : ℕ) : ℤ := (nums.val.getD i default).val

  def evenFreq (nums : Slice Std.I64) (x : ℤ) : ℕ :=
    (List.range nums.val.length).countP (fun i => i % 2 == 0 && (valAt nums i == x))

  def oddFreq (nums : Slice Std.I64) (y : ℤ) : ℕ :=
    (List.range nums.val.length).countP (fun i => i % 2 == 1 && (valAt nums i == y))

  def evenIdxCount (n : ℕ) : ℕ := (List.range n).countP (fun i => i % 2 == 0)

  def oddIdxCount (n : ℕ) : ℕ := (List.range n).countP (fun i => i % 2 == 1)

  def IsAlternating (nums : Slice Std.I64) : Prop :=
    (∀ i, i + 2 < nums.val.length → valAt nums i = valAt nums (i + 2)) ∧
    (∀ i, i + 1 < nums.val.length → valAt nums i ≠ valAt nums (i + 1))

  def IsAlternatingArray (n : ℕ) (A : ℕ → ℤ) : Prop :=
    (∀ i, i < n → IsPos64 (A i)) ∧
    (∀ i, i + 2 < n → A i = A (i + 2)) ∧
    (∀ i, i + 1 < n → A i ≠ A (i + 1))

  def mismatchCount (nums : Slice Std.I64) (A : ℕ → ℤ) : ℕ :=
    (List.range nums.val.length).countP (fun i => decide (A i ≠ valAt nums i))

  def maxEvenFreq (nums : Slice Std.I64) : ℕ :=
    ((List.range nums.val.length).map (fun i => evenFreq nums (valAt nums i))).foldr max 0

  def maxOddFreq (nums : Slice Std.I64) : ℕ :=
    ((List.range nums.val.length).map (fun i => oddFreq nums (valAt nums i))).foldr max 0

  def maxEvenFreqNe (nums : Slice Std.I64) (v : ℤ) : ℕ :=
    (((List.range nums.val.length).filter (fun i => decide (valAt nums i ≠ v))).map
        (fun i => evenFreq nums (valAt nums i))).foldr max 0

  def maxOddFreqNe (nums : Slice Std.I64) (v : ℤ) : ℕ :=
    (((List.range nums.val.length).filter (fun i => decide (valAt nums i ≠ v))).map
        (fun i => oddFreq nums (valAt nums i))).foldr max 0

  def reverse (nums : Slice Std.I64) : Slice Std.I64 where
    leng := nums.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList nums.val.reverse
    bound := by simp

  theorem reverse_val (nums : Slice Std.I64) :
      (reverse nums).val = nums.val.reverse := by
    simp [reverse, Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  def LengthBounds (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100000

  def ValueBounds (nums : Slice Std.I64) : Prop :=
    ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100000

  /-- Whenever the function returns a result r, r equals the minimum of the set of all values C(A) = #{i | 0 <= i < n and nums[i] != A[i]}, where A ranges over all length-n arrays of positive 64-bit integers (1 <= A[i] <= 2^63-1) that are alternating: for every i with 2 <= i < n, A[i-2] = A[i], and for every i with 1 <= i < n, A[i-1] != A[i]. The set is nonempty because such arrays A exist.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_1 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∃ r, Aegis.MinimumOperations.minimum_operations nums = ok r ∧
        IsLeast {c : ℤ | ∃ A : ℕ → ℤ,
          IsAlternatingArray nums.val.length A ∧ (mismatchCount nums A : ℤ) = c} r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∃ r, Aegis.MinimumOperations.minimum_operations nums = ok r ∧
          IsLeast {c : ℤ | ∃ A : ℕ → ℤ,
            IsAlternatingArray nums.val.length A ∧ (mismatchCount nums A : ℤ) = c} r.val) := by
    sorry

  /-- The function returns a result r (it does not fail by overflow, out-of-bounds access, or panic) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∃ r, Aegis.MinimumOperations.minimum_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∃ r, Aegis.MinimumOperations.minimum_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n - 1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let n = len(nums). n = 1 and 1 <= nums[0] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (hlen : nums.val.length = 1)
      (h0 : 1 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 100000) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 1)
        (h0 : 1 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 100000), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if nums[0] != nums[1], and r = 1 if nums[0] = nums[1].
    Preconditions: Let n = len(nums). n = 2 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (hlen : nums.val.length = 2) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (valAt nums 0 ≠ valAt nums 1 → r.val = 0) ∧
        (valAt nums 0 = valAt nums 1 → r.val = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 2) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (valAt nums 0 ≠ valAt nums 1 → r.val = 0) ∧
          (valAt nums 0 = valAt nums 1 → r.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if nums itself is alternating, meaning (for every i with 2 <= i < n, nums[i-2] = nums[i]) and (for every i with 1 <= i < n, nums[i-1] != nums[i]).
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (r.val = 0 ↔ IsAlternating nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (r.val = 0 ↔ IsAlternating nums)) := by
    sorry

  /-- Whenever the function returns a result r, r = min(e, o), where e = #{i | 0 <= i < n and i mod 2 = 0} and o = #{i | 0 <= i < n and i mod 2 = 1}. Equivalently e = ceil(n/2) and o = floor(n/2).
    Preconditions: Let n = len(nums). 2 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and for all i with 0 <= i < n, nums[i] = nums[0]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums)
      (hconst : ∀ i, i < nums.val.length → valAt nums i = valAt nums 0) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        r.val = ((min (evenIdxCount nums.val.length) (oddIdxCount nums.val.length) : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums)
        (hconst : ∀ i, i < nums.val.length → valAt nums i = valAt nums 0), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          r.val = ((min (evenIdxCount nums.val.length) (oddIdxCount nums.val.length) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exist positive 64-bit integers x and y with x != y such that r = n - (E(x) + O(y)), where E(x) = #{i | 0 <= i < n and i mod 2 = 0 and nums[i] = x} and O(y) = #{i | 0 <= i < n and i mod 2 = 1 and nums[i] = y}.
    Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        ∃ x y : ℤ, IsPos64 x ∧ IsPos64 y ∧ x ≠ y ∧
          r.val = (nums.val.length : ℤ) - ((evenFreq nums x : ℤ) + (oddFreq nums y : ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          ∃ x y : ℤ, IsPos64 x ∧ IsPos64 y ∧ x ≠ y ∧
            r.val = (nums.val.length : ℤ) - ((evenFreq nums x : ℤ) + (oddFreq nums y : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of positive 64-bit integers x and y with x != y, r <= n - (E(x) + O(y)), where E(x) = #{i | 0 <= i < n and i mod 2 = 0 and nums[i] = x} and O(y) = #{i | 0 <= i < n and i mod 2 = 1 and nums[i] = y}.
    Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        ∀ x y : ℤ, IsPos64 x → IsPos64 y → x ≠ y →
          r.val ≤ (nums.val.length : ℤ) - ((evenFreq nums x : ℤ) + (oddFreq nums y : ℤ)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          ∀ x y : ℤ, IsPos64 x → IsPos64 y → x ≠ y →
            r.val ≤ (nums.val.length : ℤ) - ((evenFreq nums x : ℤ) + (oddFreq nums y : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r >= n - (mE + mO), where mE = max { E(x) | x is a positive 64-bit integer } and mO = max { O(y) | y is a positive 64-bit integer }, with E(x) = #{i | 0 <= i < n and i mod 2 = 0 and nums[i] = x} and O(y) = #{i | 0 <= i < n and i mod 2 = 1 and nums[i] = y}. If there are no odd indices, mO = 0.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (nums.val.length : ℤ) - ((maxEvenFreq nums : ℤ) + (maxOddFreq nums : ℤ)) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (nums.val.length : ℤ) - ((maxEvenFreq nums : ℤ) + (maxOddFreq nums : ℤ)) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= n - max(mE, mO), where mE and mO are the maximum even-index and odd-index frequencies as defined in spec_10.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        r.val ≤ (nums.val.length : ℤ) -
          ((max (maxEvenFreq nums) (maxOddFreq nums) : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          r.val ≤ (nums.val.length : ℤ) -
            ((max (maxEvenFreq nums) (maxOddFreq nums) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r on nums and r2 on nums2, r = r2.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let nums2 be any length-n array satisfying the same value bounds and having, for every positive 64-bit integer x, the same count of x on even indices as nums and the same count of x on odd indices as nums. -/
  theorem spec_12 (nums nums2 : Slice Std.I64)
      (hlen : LengthBounds nums) (hval : ValueBounds nums)
      (hlen2 : nums2.val.length = nums.val.length) (hval2 : ValueBounds nums2)
      (heven : ∀ x : ℤ, IsPos64 x → evenFreq nums2 x = evenFreq nums x)
      (hodd : ∀ x : ℤ, IsPos64 x → oddFreq nums2 x = oddFreq nums x) :
      ∀ r r2, Aegis.MinimumOperations.minimum_operations nums = ok r →
        Aegis.MinimumOperations.minimum_operations nums2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (hlen : LengthBounds nums) (hval : ValueBounds nums)
        (hlen2 : nums2.val.length = nums.val.length) (hval2 : ValueBounds nums2)
        (heven : ∀ x : ℤ, IsPos64 x → evenFreq nums2 x = evenFreq nums x)
        (hodd : ∀ x : ℤ, IsPos64 x → oddFreq nums2 x = oddFreq nums x), ∀ r r2, Aegis.MinimumOperations.minimum_operations nums = ok r →
          Aegis.MinimumOperations.minimum_operations nums2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever the function returns r on nums and rrev on rev, r = rrev.
    Preconditions: Let n = len(nums). 1 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let rev be the length-n array with rev[i] = nums[n-1-i] for 0 <= i < n. -/
  theorem spec_13 (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums) :
      ∀ r rrev, Aegis.MinimumOperations.minimum_operations nums = ok r →
        Aegis.MinimumOperations.minimum_operations (reverse nums) = ok rrev → r.val = rrev.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : LengthBounds nums) (hval : ValueBounds nums), ∀ r rrev, Aegis.MinimumOperations.minimum_operations nums = ok r →
          Aegis.MinimumOperations.minimum_operations (reverse nums) = ok rrev → r.val = rrev.val) := by
    sorry

  /-- Let E(x) = #{i | 0 <= i < n and i mod 2 = 0 and nums[i] = x} and O(y) = #{i | 0 <= i < n and i mod 2 = 1 and nums[i] = y}, for positive 64-bit integers x and y. Let mE = max { E(x) | x is a positive 64-bit integer } and mO = max { O(y) | y is a positive 64-bit integer }. Whenever the function returns a result r, if there exist positive 64-bit integers x and y with x != y such that E(x) = mE and O(y) = mO, then r = n - (mE + mO).
    Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_14 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (∃ x y : ℤ, IsPos64 x ∧ IsPos64 y ∧ x ≠ y ∧
          evenFreq nums x = maxEvenFreq nums ∧ oddFreq nums y = maxOddFreq nums) →
        r.val = (nums.val.length : ℤ) - ((maxEvenFreq nums : ℤ) + (maxOddFreq nums : ℤ)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (∃ x y : ℤ, IsPos64 x ∧ IsPos64 y ∧ x ≠ y ∧
            evenFreq nums x = maxEvenFreq nums ∧ oddFreq nums y = maxOddFreq nums) →
          r.val = (nums.val.length : ℤ) - ((maxEvenFreq nums : ℤ) + (maxOddFreq nums : ℤ))) := by
    sorry

  /-- Let E(x) = #{i | 0 <= i < n and i mod 2 = 0 and nums[i] = x} and O(y) = #{i | 0 <= i < n and i mod 2 = 1 and nums[i] = y}, for positive 64-bit integers x and y. Let mE = max { E(x) | x is a positive 64-bit integer } and mO = max { O(y) | y is a positive 64-bit integer }. Suppose there is a positive 64-bit integer v such that E(v) = mE, O(v) = mO, and for every positive 64-bit integer x with x != v, E(x) < mE and O(x) < mO. Let E2 = max { E(x) | x is a positive 64-bit integer and x != v } and O2 = max { O(x) | x is a positive 64-bit integer and x != v }, with the maximum of an empty set taken as 0. Whenever the function returns a result r, r = n - max(mE + O2, mO + E2).
    Preconditions: Let n = len(nums). 2 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
  theorem spec_15 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums) :
      ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
        ∀ v : ℤ, IsPos64 v →
          evenFreq nums v = maxEvenFreq nums →
          oddFreq nums v = maxOddFreq nums →
          (∀ x : ℤ, IsPos64 x → x ≠ v →
            evenFreq nums x < maxEvenFreq nums ∧ oddFreq nums x < maxOddFreq nums) →
          r.val = (nums.val.length : ℤ) -
            max ((maxEvenFreq nums : ℤ) + (maxOddFreqNe nums v : ℤ))
                ((maxOddFreq nums : ℤ) + (maxEvenFreqNe nums v : ℤ)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.val.length ∧ nums.val.length ≤ 100000) (hval : ValueBounds nums), ∀ r, Aegis.MinimumOperations.minimum_operations nums = ok r →
          ∀ v : ℤ, IsPos64 v →
            evenFreq nums v = maxEvenFreq nums →
            oddFreq nums v = maxOddFreq nums →
            (∀ x : ℤ, IsPos64 x → x ≠ v →
              evenFreq nums x < maxEvenFreq nums ∧ oddFreq nums x < maxOddFreq nums) →
            r.val = (nums.val.length : ℤ) -
              max ((maxEvenFreq nums : ℤ) + (maxOddFreqNe nums v : ℤ))
                  ((maxOddFreq nums : ℤ) + (maxEvenFreqNe nums v : ℤ))) := by
    sorry

  end AegisSpec.MinimumOperations
