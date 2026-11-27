import Aegis.MaximumPrimeDifference.Code.Funs

/-!
# Specifications of `Aegis.MaximumPrimeDifference.maximum_prime_difference`

LeetCode problem `maximum-prime-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumPrimeDifference

def IsPrime (n : ℤ) : Prop := 2 ≤ n ∧ ∀ d : ℤ, 1 < d → d < n → ¬ d ∣ n

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def PrimeAt (nums : Slice Std.I64) (i : ℕ) : Prop :=
  i < nums.val.length ∧ IsPrime (elem nums i)

def primeIndices (nums : Slice Std.I64) : Set ℕ := {i | PrimeAt nums i}

def primeDistances (nums : Slice Std.I64) : Set ℤ :=
  {d | ∃ i j : ℕ, PrimeAt nums i ∧ PrimeAt nums j ∧ d = |(i : ℤ) - (j : ℤ)|}

/-- The function returns a result r and r = max { |i - j| : 0 <= i < len(nums), 0 <= j < len(nums), IsPrime(nums[i]), IsPrime(nums[j]) }, where the maximum is taken over the nonempty finite set of pairs of indices whose values are prime.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∃ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv ∧
        IsGreatest (primeDistances nums) rv.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∃ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv ∧
        IsGreatest (primeDistances nums) rv.val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums) - 1.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        0 ≤ rv.val ∧ rv.val ≤ (nums.val.length : ℤ) - 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        0 ≤ rv.val ∧ rv.val ≤ (nums.val.length : ℤ) - 1) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: there is no integer overflow, panic, out-of-bounds access, or other failure.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∃ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∃ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv) := by
  sorry

/-- Whenever the function returns a result r, let L be the least index i with 0 <= i < len(nums) and IsPrime(nums[i]), and let R be the greatest such index; then r = R - L.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ (rv : Std.I64) (L R : ℕ),
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        IsLeast (primeIndices nums) L → IsGreatest (primeIndices nums) R →
          rv.val = (R : ℤ) - (L : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ (rv : Std.I64) (L R : ℕ),
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        IsLeast (primeIndices nums) L → IsGreatest (primeIndices nums) R →
          rv.val = (R : ℤ) - (L : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < len(nums), 0 <= j < len(nums), IsPrime(nums[i]), and IsPrime(nums[j]), the inequality |i - j| <= r holds.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
          IsPrime (nums.val[i]).val → IsPrime (nums.val[j]).val →
            |(i : ℤ) - (j : ℤ)| ≤ rv.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
          IsPrime (nums.val[i]).val → IsPrime (nums.val[j]).val →
            |(i : ℤ) - (j : ℤ)| ≤ rv.val) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), IsPrime(nums[i]), IsPrime(nums[j]), and |i - j| = r.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
          IsPrime (nums.val[i]).val ∧ IsPrime (nums.val[j]).val ∧
            |(i : ℤ) - (j : ℤ)| = rv.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
          IsPrime (nums.val[i]).val ∧ IsPrime (nums.val[j]).val ∧
            |(i : ℤ) - (j : ℤ)| = rv.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is exactly one index i with 0 <= i < len(nums) and IsPrime(nums[i]).
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        (rv.val = 0 ↔ ∃! i, PrimeAt nums i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        (rv.val = 0 ↔ ∃! i, PrimeAt nums i)) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) - 1 if and only if both IsPrime(nums[0]) and IsPrime(nums[len(nums) - 1]) hold.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        (rv.val = (nums.val.length : ℤ) - 1 ↔
          IsPrime (nums.val[0]).val ∧ IsPrime (nums.val[nums.val.length - 1]).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        (rv.val = (nums.val.length : ℤ) - 1 ↔
          IsPrime (nums.val[0]).val ∧ IsPrime (nums.val[nums.val.length - 1]).val)) := by
  sorry

/-- Whenever the function returns a result r on nums, for every second array nums2 satisfying len(nums2) = len(nums), 1 <= nums2[i] <= 100 for every 0 <= i < len(nums2), having at least one prime element, and satisfying IsPrime(nums[i]) if and only if IsPrime(nums2[i]) for every 0 <= i < len(nums), if the function returns r2 on nums2 then r2 = r.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (nums2 : Slice Std.I64) (hlen : nums2.val.length = nums.val.length)
          (hval2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
            1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100)
          (hprime2 : ∃ i, PrimeAt nums2 i)
          (hiff : ∀ (i : ℕ) (hi : i < nums.val.length),
            (IsPrime (nums.val[i]).val ↔ IsPrime (nums2.val[i]).val)),
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference nums2 = ok rv2 →
              rv2.val = rv.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (nums2 : Slice Std.I64) (hlen : nums2.val.length = nums.val.length)
          (hval2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
            1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100)
          (hprime2 : ∃ i, PrimeAt nums2 i)
          (hiff : ∀ (i : ℕ) (hi : i < nums.val.length),
            (IsPrime (nums.val[i]).val ↔ IsPrime (nums2.val[i]).val)),
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference nums2 = ok rv2 →
              rv2.val = rv.val) := by
  sorry

/-- Whenever the function returns a result r on nums, for every second array nums2 satisfying len(nums2) = len(nums), 1 <= nums2[i] <= 100 for every 0 <= i < len(nums2), having at least one prime element, and satisfying for every 0 <= i < len(nums) that IsPrime(nums[i]) implies IsPrime(nums2[i]), if the function returns r2 on nums2 then r2 >= r.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (nums2 : Slice Std.I64) (hlen : nums2.val.length = nums.val.length)
          (hval2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
            1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100)
          (hprime2 : ∃ i, PrimeAt nums2 i)
          (hmono : ∀ (i : ℕ) (hi : i < nums.val.length),
            (IsPrime (nums.val[i]).val → IsPrime (nums2.val[i]).val)),
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference nums2 = ok rv2 →
              rv.val ≤ rv2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ rv : Std.I64,
      Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
        ∀ (nums2 : Slice Std.I64) (hlen : nums2.val.length = nums.val.length)
          (hval2 : ∀ (i : ℕ) (hi : i < nums2.val.length),
            1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100)
          (hprime2 : ∃ i, PrimeAt nums2 i)
          (hmono : ∀ (i : ℕ) (hi : i < nums.val.length),
            (IsPrime (nums.val[i]).val → IsPrime (nums2.val[i]).val)),
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference nums2 = ok rv2 →
              rv.val ≤ rv2.val) := by
  sorry

/-- Let revnums be the array with len(revnums) = len(nums) and revnums[i] = nums[len(nums) - 1 - i] for every 0 <= i < len(nums). Whenever the function returns a result r on nums and returns r2 on revnums, r2 = r.
  Preconditions: Let len(nums) denote the number of elements of nums and nums[i] the 0-based element at index i. The input satisfies 1 <= len(nums) <= 300000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; and there exists at least one i with 0 <= i < len(nums) such that IsPrime(nums[i]). Here IsPrime(n) means n >= 2 and for every integer d with 1 < d < n, d does not divide n. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i) :
    ∀ (revnums : Slice Std.I64) (hlen : revnums.val.length = nums.val.length)
      (hrev : ∀ (i : ℕ) (hi : i < nums.val.length),
        (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val),
      ∀ (rv : Std.I64),
        Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference revnums = ok rv2 →
              rv2.val = rv.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 300000)
    (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hprime : ∃ i, PrimeAt nums i), ∀ (revnums : Slice Std.I64) (hlen : revnums.val.length = nums.val.length)
      (hrev : ∀ (i : ℕ) (hi : i < nums.val.length),
        (revnums.val[i]).val = (nums.val[nums.val.length - 1 - i]).val),
      ∀ (rv : Std.I64),
        Aegis.MaximumPrimeDifference.maximum_prime_difference nums = ok rv →
          ∀ rv2 : Std.I64,
            Aegis.MaximumPrimeDifference.maximum_prime_difference revnums = ok rv2 →
              rv2.val = rv.val) := by
  sorry

end AegisSpec.MaximumPrimeDifference
