import Aegis.MaximumSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumSum.maximum_sum`

LeetCode problem `maximum-element-sum-of-a-complete-subset-of-indices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.MaximumSum

def sliceList (nums : Slice Std.I64) : List Int := nums.list.toList.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : Nat) : Int := (sliceList nums).getD i 0

def IsPerfectSquare (m : Nat) : Prop := ∃ k : Nat, m = k * k

def Compatible (n : Nat) (S : Finset Nat) : Prop :=
  S.Nonempty ∧ (∀ i ∈ S, 1 ≤ i ∧ i ≤ n) ∧ ∀ i ∈ S, ∀ j ∈ S, IsPerfectSquare (i * j)

def subsetSum (nums : Slice Std.I64) (S : Finset Nat) : Int :=
  S.sum (fun i => elem nums (i - 1))

def AdmissibleSums (nums : Slice Std.I64) (n : Nat) : Set Int :=
  {v : Int | ∃ S : Finset Nat, Compatible n S ∧ v = subsetSum nums S}

def largestSquareRoot (k : Nat) : Nat := (k.divisors.filter (fun m => m * m ∣ k)).sup id

def squarefreePart (k : Nat) : Nat := k / (largestSquareRoot k * largestSquareRoot k)

def classSum (nums : Slice Std.I64) (n d : Nat) : Int :=
  ((Finset.Icc 1 n).filter (fun i => squarefreePart i = d)).sum (fun i => elem nums (i - 1))

def NonemptyClassSums (nums : Slice Std.I64) (n : Nat) : Set Int :=
  {v : Int | ∃ d : Nat,
    0 < d ∧ ((Finset.Icc 1 n).filter (fun i => squarefreePart i = d)).Nonempty ∧
      v = classSum nums n d}

def classSize (n d : Nat) : Nat :=
  ((Finset.Icc 1 n).filter (fun i => squarefreePart i = d)).card

def maxClassSize (n : Nat) : Nat :=
  ((Finset.Icc 1 n).image squarefreePart).sup (fun d => classSize n d)

def totalSum (nums : Slice Std.I64) (n : Nat) : Int :=
  (Finset.range n).sum (fun i => elem nums i)

noncomputable def sumOverSquareIndices (nums : Slice Std.I64) (n : Nat) : Int :=
  letI : DecidablePred (fun i : Nat => IsPerfectSquare i) := Classical.decPred _
  ((Finset.Icc 1 n).filter (fun i => IsPerfectSquare i)).sum (fun i => elem nums (i - 1))

/-- The function returns a result r (i.e., it does not fail) and r equals the maximum value of sum_{i in S} nums[i-1] over all non-empty subsets S of {1,2,...,n} such that for every i,j in S, the product i*j is a perfect square (i.e., there exists an integer k >= 0 with i*j = k^2).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r ∧
        IsGreatest (AdmissibleSums nums n) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r ∧
        IsGreatest (AdmissibleSums nums n) r.val) := by
  sorry

/-- For every input nums satisfying the preconditions, the function returns a result (i.e., it does not return an error or panic).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaximumSum.maximum_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∃ r : Std.I64, Aegis.MaximumSum.maximum_sum nums = ok r) := by
  sorry

/-- The result r satisfies r >= max_{0 <= i < n} nums[i].
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → ∀ i : Nat, i < n → elem nums i ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → ∀ i : Nat, i < n → elem nums i ≤ r.val) := by
  sorry

/-- The result r satisfies r <= sum_{0 <= i < n} nums[i].
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val ≤ totalSum nums n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val ≤ totalSum nums n) := by
  sorry

/-- There exists a non-empty subset S of {1,2,...,n} such that (a) for every i,j in S, i*j is a perfect square, and (b) r = sum_{i in S} nums[i-1].
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∃ S : Finset Nat, Compatible n S ∧ r.val = subsetSum nums S := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∃ S : Finset Nat, Compatible n S ∧ r.val = subsetSum nums S) := by
  sorry

/-- For every non-empty subset S of {1,2,...,n} such that for every i,j in S, i*j is a perfect square, it holds that sum_{i in S} nums[i-1] <= r.
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∀ S : Finset Nat, Compatible n S → subsetSum nums S ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∀ S : Finset Nat, Compatible n S → subsetSum nums S ≤ r.val) := by
  sorry

/-- Let sf(k) denote the squarefree part of a positive integer k (the product of primes with odd exponent in the prime factorization of k, or equivalently the unique squarefree d such that k/d is a perfect square). Then r = max_{d} ( sum over all i with 1 <= i <= n and sf(i)=d of nums[i-1] ), where the maximum is over all positive integers d for which the set {i | 1 <= i <= n and sf(i)=d} is non-empty.
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        IsGreatest (NonemptyClassSums nums n) r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        IsGreatest (NonemptyClassSums nums n) r.val) := by
  sorry

/-- If nums[i] <= nums'[i] for all 0 <= i < n, then maximum_sum(nums) <= maximum_sum(nums').
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let nums' be another array of length n such that for every i with 0 <= i < n, 1 <= nums'[i] <= 1000000000. -/
theorem spec_8 (nums nums' : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn' : n = (sliceList nums').length)
    (hbounds' : ∀ i : Nat, i < n → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hmono : ∀ i : Nat, i < n → elem nums i ≤ elem nums' i) :
    ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn' : n = (sliceList nums').length)
    (hbounds' : ∀ i : Nat, i < n → 1 ≤ elem nums' i ∧ elem nums' i ≤ 1000000000)
    (hmono : ∀ i : Nat, i < n → elem nums i ≤ elem nums' i), ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- For any positive integer c such that 1 <= c * nums[i] <= 1000000000 for all 0 <= i < n, let nums' be the array defined by nums'[i] = c * nums[i] for 0 <= i < n. Then maximum_sum(nums') = c * maximum_sum(nums).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hc : 1 ≤ c)
    (hcbounds : ∀ i : Nat, i < n → 1 ≤ c * elem nums i ∧ c * elem nums i ≤ 1000000000)
    (hn' : n = (sliceList nums').length)
    (hscale : ∀ i : Nat, i < n → elem nums' i = c * elem nums i) :
    ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' → r'.val = c * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat) (c : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hc : 1 ≤ c)
    (hcbounds : ∀ i : Nat, i < n → 1 ≤ c * elem nums i ∧ c * elem nums i ≤ 1000000000)
    (hn' : n = (sliceList nums').length)
    (hscale : ∀ i : Nat, i < n → elem nums' i = c * elem nums i), ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' → r'.val = c * r.val) := by
  sorry

/-- r = nums[0].
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Additionally, n = 1. -/
theorem spec_10 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn1 : n = 1) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val = elem nums 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn1 : n = 1), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val = elem nums 0) := by
  sorry

/-- r = max(nums[0], nums[1]).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Additionally, n = 2. -/
theorem spec_11 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn2 : n = 2) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0) (elem nums 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn2 : n = 2), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0) (elem nums 1)) := by
  sorry

/-- r = max(nums[0], nums[1], nums[2]).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Additionally, n = 3. -/
theorem spec_12 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn3 : n = 3) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0) (max (elem nums 1) (elem nums 2)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn3 : n = 3), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0) (max (elem nums 1) (elem nums 2))) := by
  sorry

/-- r = max(nums[0] + nums[3], nums[1], nums[2]).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Additionally, n = 4. -/
theorem spec_13 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn4 : n = 4) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0 + elem nums 3) (max (elem nums 1) (elem nums 2)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hn4 : n = 4), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        r.val = max (elem nums 0 + elem nums 3) (max (elem nums 1) (elem nums 2))) := by
  sorry

/-- r >= sum over all i with 1 <= i <= n and i is a perfect square of nums[i-1].
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → sumOverSquareIndices nums n ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → sumOverSquareIndices nums n ≤ r.val) := by
  sorry

/-- For any integer v with 1 <= v <= 1000000000, let nums' be the array of length n+1 obtained by appending v to nums, so nums'[i] = nums[i] for 0 <= i < n and nums'[n] = v. Let S_new = {i | 1 <= i <= n and sf(i) = sf(n+1)}, where sf(k) is the squarefree part of k as defined in spec_7. Then maximum_sum(nums') = max( maximum_sum(nums), v + sum over all i in S_new of nums[i-1] ).
  Preconditions: Let n = len(nums). We assume 1 <= n <= 9999 (equivalently n+1 <= 10000) and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_15 (nums nums' : Slice Std.I64) (n : Nat) (v : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 9999)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hv₁ : 1 ≤ v) (hv₂ : v ≤ 1000000000)
    (hn' : (sliceList nums').length = n + 1)
    (hprefix : ∀ i : Nat, i < n → elem nums' i = elem nums i)
    (hlast : elem nums' n = v) :
    ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' →
          r'.val = max r.val (v + classSum nums n (squarefreePart (n + 1))) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : Nat) (v : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 9999)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hv₁ : 1 ≤ v) (hv₂ : v ≤ 1000000000)
    (hn' : (sliceList nums').length = n + 1)
    (hprefix : ∀ i : Nat, i < n → elem nums' i = elem nums i)
    (hlast : elem nums' n = v), ∀ r r' : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        Aegis.MaximumSum.maximum_sum nums' = ok r' →
          r'.val = max r.val (v + classSum nums n (squarefreePart (n + 1)))) := by
  sorry

/-- r = v * max_{d} ( |{i | 1 <= i <= n and sf(i)=d}| ), where sf(k) is the squarefree part of k as defined in spec_7.
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Additionally, there exists an integer v such that nums[i] = v for all 0 <= i < n. -/
theorem spec_16 (nums : Slice Std.I64) (n : Nat) (v : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hconst : ∀ i : Nat, i < n → elem nums i = v) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val = v * (maxClassSize n : Int) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat) (v : Int)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000)
    (hconst : ∀ i : Nat, i < n → elem nums i = v), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r → r.val = v * (maxClassSize n : Int)) := by
  sorry

/-- For every positive squarefree integer d, r >= sum over all i with 1 <= i <= n and sf(i) = d of nums[i-1], where sf(k) is the squarefree part of k as defined in spec_7.
  Preconditions: Let n = len(nums). We assume 1 <= n <= 10000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_17 (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000) :
    ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∀ d : Nat, Squarefree d → 0 < d → classSum nums n d ≤ r.val := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat)
    (hn : n = (sliceList nums).length)
    (hpos : 1 ≤ n) (hle : n ≤ 10000)
    (hbounds : ∀ i : Nat, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000), ∀ r : Std.I64,
      Aegis.MaximumSum.maximum_sum nums = ok r →
        ∀ d : Nat, Squarefree d → 0 < d → classSum nums n d ≤ r.val) := by
  sorry

end AegisSpec.MaximumSum
