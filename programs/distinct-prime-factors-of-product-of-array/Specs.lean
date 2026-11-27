import Aegis.DistinctPrimeFactors.Code.Funs

/-!
# Specifications of `Aegis.DistinctPrimeFactors.distinct_prime_factors`

LeetCode problem `distinct-prime-factors-of-product-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistinctPrimeFactors

def IsPrime (p : ℤ) : Prop :=
  1 < p ∧ ∀ d : ℤ, 0 < d → d ∣ p → d = 1 ∨ d = p

def EntriesInRange (nums : Slice I64) : Prop :=
  ∀ x ∈ nums.val, 2 ≤ x.val ∧ x.val ≤ 1000

def ValidInput (nums : Slice I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 10000 ∧ EntriesInRange nums

def maxEntryOf (l : List I64) : ℕ := List.foldr (fun x m => max x.val.toNat m) 0 l

def maxEntry (nums : Slice I64) : ℕ := maxEntryOf nums.val

noncomputable def dividingPrimes (nums : Slice I64) : Finset ℕ := by
  classical
  exact (Finset.range (maxEntry nums + 1)).filter
    (fun p => IsPrime (p : ℤ) ∧ ∃ x ∈ nums.val, (p : ℤ) ∣ x.val)

noncomputable def primeCountUpTo (bound : ℕ) : ℕ := by
  classical
  exact ((Finset.range (bound + 1)).filter (fun p : ℕ => IsPrime (p : ℤ))).card

noncomputable def distinctPrimeFactorCount (x : ℤ) : ℕ := by
  classical
  exact ((Finset.range (x.toNat + 1)).filter (fun p : ℕ => IsPrime (p : ℤ) ∧ (p : ℤ) ∣ x)).card

noncomputable def freshDividingPrimes (l : List I64) (x : I64) : Finset ℕ := by
  classical
  exact (Finset.range (max (maxEntryOf l) x.val.toNat + 1)).filter
    (fun p => IsPrime (p : ℤ) ∧ (p : ℤ) ∣ x.val ∧ ∀ y ∈ l, ¬ (p : ℤ) ∣ y.val)

def IsReorderingOf (nums2 nums1 : Slice I64) : Prop := nums2.val.Perm nums1.val

def eraseIdxSlice (nums : Slice I64) (j : ℕ) (h : nums.val.length ≤ 10000) : Slice I64 :=
  Slice.from (nums.val.eraseIdx j) (by
    have hmax : (10000 : ℕ) ≤ Usize.max := by
      have := Usize.cMax_bound_concrete
      omega
    have := List.length_eraseIdx_le nums.val j
    omega)

@[simp]
theorem eraseIdxSlice_val (nums : Slice I64) (j : ℕ) (h : nums.val.length ≤ 10000) :
    (eraseIdxSlice nums j h).val = nums.val.eraseIdx j :=
  Slice.from_val _ _

def appendEntrySlice (nums : Slice I64) (x : I64) (h : nums.val.length < 10000) : Slice I64 :=
  Slice.from (nums.val ++ [x]) (by
    have hmax : (10000 : ℕ) ≤ Usize.max := by
      have := Usize.cMax_bound_concrete
      omega
    simp only [List.length_append, List.length_singleton]
    omega)

@[simp]
theorem appendEntrySlice_val (nums : Slice I64) (x : I64) (h : nums.val.length < 10000) :
    (appendEntrySlice nums x h).val = nums.val ++ [x] :=
  Slice.from_val _ _

/-- The function returns a result r, and r equals the number of distinct primes p such that p divides nums[i] for at least one index i with 0 ≤ i < len(nums). Here a prime is an integer p > 1 whose only positive divisors are 1 and p, and 'p divides nums[i]' means there exists an integer k with nums[i] = p·k. In set notation, r = |{ p : p is prime and ∃ i, 0 ≤ i < len(nums) and p divides nums[i] }|.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000 (nums[i] read as a mathematical integer). -/
theorem spec_1 (nums : Slice I64) (hnums : ValidInput nums) :
    ∃ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r ∧
      r.val = ((dividingPrimes nums).card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∃ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r ∧
      r.val = ((dividingPrimes nums).card : ℤ)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail (no panic, no out-of-bounds access, and no arithmetic overflow).
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_2 (nums : Slice I64) (hnums : ValidInput nums) :
    ∃ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∃ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 ≤ r.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_3 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r ≤ 168.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_4 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r → r.val ≤ 168 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r → r.val ≤ 168) := by
  sorry

/-- Whenever the function returns a result r, r ≤ 4 * len(nums).
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_5 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      r.val ≤ 4 * (nums.val.length : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      r.val ≤ 4 * (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns r1 on nums1 and r2 on nums2, r1 = r2.
  Preconditions: Both nums1 and nums2 satisfy 1 ≤ len ≤ 10^4 and all entries lie in [2,1000]. Also nums2 is a permutation (reordering) of nums1: there is a bijection φ from the indices of nums1 to the indices of nums2 with nums2[φ(i)] = nums1[i] for every i. -/
theorem spec_6 (nums1 nums2 : Slice I64) (h1 : ValidInput nums1) (h2 : ValidInput nums2)
    (hperm : IsReorderingOf nums2 nums1) :
    ∀ r1 r2, Aegis.DistinctPrimeFactors.distinct_prime_factors nums1 = ok r1 →
      Aegis.DistinctPrimeFactors.distinct_prime_factors nums2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h1 : ValidInput nums1) (h2 : ValidInput nums2)
    (hperm : IsReorderingOf nums2 nums1), ∀ r1 r2, Aegis.DistinctPrimeFactors.distinct_prime_factors nums1 = ok r1 →
      Aegis.DistinctPrimeFactors.distinct_prime_factors nums2 = ok r2 → r1.val = r2.val) := by
  sorry

/-- Whenever the function returns r1 on nums1 and r2 on nums2, r2 ≤ r1.
  Preconditions: Both nums1 and nums2 satisfy 1 ≤ len ≤ 10^4 and all entries lie in [2,1000]. For every prime p, if p divides nums2[i] for some i, then p divides nums1[j] for some j. Equivalently, the set of primes dividing at least one element of nums2 is contained in the corresponding set for nums1. -/
theorem spec_7 (nums1 nums2 : Slice I64) (h1 : ValidInput nums1) (h2 : ValidInput nums2)
    (hsub : ∀ p : ℤ, IsPrime p → (∃ x ∈ nums2.val, p ∣ x.val) →
      ∃ y ∈ nums1.val, p ∣ y.val) :
    ∀ r1 r2, Aegis.DistinctPrimeFactors.distinct_prime_factors nums1 = ok r1 →
      Aegis.DistinctPrimeFactors.distinct_prime_factors nums2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (h1 : ValidInput nums1) (h2 : ValidInput nums2)
    (hsub : ∀ p : ℤ, IsPrime p → (∃ x ∈ nums2.val, p ∣ x.val) →
      ∃ y ∈ nums1.val, p ∣ y.val), ∀ r1 r2, Aegis.DistinctPrimeFactors.distinct_prime_factors nums1 = ok r1 →
      Aegis.DistinctPrimeFactors.distinct_prime_factors nums2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if there exists a prime p such that every element nums[i] is a power of p, i.e., for each i with 0 ≤ i < len(nums) there is an integer k_i ≥ 1 with nums[i] = p^{k_i}.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_8 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      (r.val = 1 ↔ ∃ p : ℤ, IsPrime p ∧ ∀ x ∈ nums.val, ∃ k : ℕ, 1 ≤ k ∧ x.val = p ^ k) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      (r.val = 1 ↔ ∃ p : ℤ, IsPrime p ∧ ∀ x ∈ nums.val, ∃ k : ℕ, 1 ≤ k ∧ x.val = p ^ k)) := by
  sorry

/-- Whenever the function returns a result r, r ≤ π(M), where π(M) is the number of primes p with p ≤ M.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. Let M = max { nums[i] : 0 ≤ i < len(nums) }, which is well-defined because len(nums) ≥ 1. -/
theorem spec_9 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      r.val ≤ (primeCountUpTo (maxEntry nums) : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      r.val ≤ (primeCountUpTo (maxEntry nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 ≤ i < len(nums), r ≥ d(nums[i]).
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. For an integer x ≥ 2, let d(x) be the number of distinct primes dividing x. -/
theorem spec_10 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      ∀ x ∈ nums.val, (distinctPrimeFactorCount x.val : ℤ) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      ∀ x ∈ nums.val, (distinctPrimeFactorCount x.val : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', r = r'.
  Preconditions: nums satisfies 1 ≤ len(nums) ≤ 10^4 and all entries lie in [2,1000], and len(nums) ≥ 2. Let j and k be indices with 0 ≤ j < len(nums), 0 ≤ k < len(nums), j ≠ k, and nums[j] divides nums[k]. Let nums' be the slice obtained from nums by deleting the element at index j; it has length len(nums)-1 and still satisfies the basic constraints. -/
theorem spec_11 (nums : Slice I64) (hnums : ValidInput nums) (hlen : 2 ≤ nums.val.length)
    (j : ℕ) (hj : j < nums.val.length)
    (hdiv : ∃ (k : ℕ) (hk : k < nums.val.length), k ≠ j ∧
      (nums.val.get ⟨j, hj⟩).val ∣ (nums.val.get ⟨k, hk⟩).val) :
    ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (eraseIdxSlice nums j hnums.2.1) = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums) (hlen : 2 ≤ nums.val.length)
    (j : ℕ) (hj : j < nums.val.length)
    (hdiv : ∃ (k : ℕ) (hk : k < nums.val.length), k ≠ j ∧
      (nums.val.get ⟨j, hj⟩).val ∣ (nums.val.get ⟨k, hk⟩).val), ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (eraseIdxSlice nums j hnums.2.1) = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, there exist r distinct primes p_1 < p_2 < ... < p_r such that: (i) for every t with 1 ≤ t ≤ r, p_t divides nums[i] for some i with 0 ≤ i < len(nums); and (ii) for every prime q, if q divides nums[i] for some i, then q = p_t for some t with 1 ≤ t ≤ r.
  Preconditions: 1 ≤ len(nums) ≤ 10^4, and for every i with 0 ≤ i < len(nums), 2 ≤ nums[i] ≤ 1000. -/
theorem spec_12 (nums : Slice I64) (hnums : ValidInput nums) :
    ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      ∃ ps : List ℤ, r.val = (ps.length : ℤ) ∧ ps.Pairwise (· < ·) ∧
        (∀ p ∈ ps, IsPrime p ∧ ∃ x ∈ nums.val, p ∣ x.val) ∧
        (∀ q : ℤ, IsPrime q → (∃ x ∈ nums.val, q ∣ x.val) → q ∈ ps) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums), ∀ r, Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      ∃ ps : List ℤ, r.val = (ps.length : ℤ) ∧ ps.Pairwise (· < ·) ∧
        (∀ p ∈ ps, IsPrime p ∧ ∃ x ∈ nums.val, p ∣ x.val) ∧
        (∀ q : ℤ, IsPrime q → (∃ x ∈ nums.val, q ∣ x.val) → q ∈ ps)) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums ++ [x], r' = r + |{ p : p is prime, p divides x, and for every i with 0 ≤ i < len(nums), p does not divide nums[i] }|.
  Preconditions: nums satisfies 1 ≤ len(nums) ≤ 10^4 and every nums[i] lies in [2,1000]; x is an integer with 2 ≤ x ≤ 1000; and len(nums) < 10^4 so that nums ++ [x] also satisfies the length constraint. -/
theorem spec_13 (nums : Slice I64) (x : I64) (hnums : ValidInput nums)
    (hlen : nums.val.length < 10000) (hx : 2 ≤ x.val ∧ x.val ≤ 1000) :
    ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (appendEntrySlice nums x hlen) = ok r' →
      r'.val = r.val + ((freshDividingPrimes nums.val x).card : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (x : I64) (hnums : ValidInput nums)
    (hlen : nums.val.length < 10000) (hx : 2 ≤ x.val ∧ x.val ≤ 1000), ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (appendEntrySlice nums x hlen) = ok r' →
      r'.val = r.val + ((freshDividingPrimes nums.val x).card : ℤ)) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', r' = r - |{ p : p is prime, p divides nums[j], and for every i with 0 ≤ i < len(nums) and i ≠ j, p does not divide nums[i] }|.
  Preconditions: nums satisfies 1 ≤ len(nums) ≤ 10^4 and every entry lies in [2,1000]; len(nums) ≥ 2; j is an index with 0 ≤ j < len(nums); and nums' is the slice obtained from nums by deleting nums[j]. -/
theorem spec_14 (nums : Slice I64) (hnums : ValidInput nums) (hlen : 2 ≤ nums.val.length)
    (j : ℕ) (hj : j < nums.val.length) :
    ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (eraseIdxSlice nums j hnums.2.1) = ok r' →
      r'.val = r.val -
        ((freshDividingPrimes (nums.val.eraseIdx j) (nums.val.get ⟨j, hj⟩)).card : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (hnums : ValidInput nums) (hlen : 2 ≤ nums.val.length)
    (j : ℕ) (hj : j < nums.val.length), ∀ r r', Aegis.DistinctPrimeFactors.distinct_prime_factors nums = ok r →
      Aegis.DistinctPrimeFactors.distinct_prime_factors (eraseIdxSlice nums j hnums.2.1) = ok r' →
      r'.val = r.val -
        ((freshDividingPrimes (nums.val.eraseIdx j) (nums.val.get ⟨j, hj⟩)).card : ℤ)) := by
  sorry

end AegisSpec.DistinctPrimeFactors
