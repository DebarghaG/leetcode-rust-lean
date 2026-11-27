import Aegis.MaxFrequency.Code.Funs

/-!
# Specifications of `Aegis.MaxFrequency.max_frequency`

LeetCode problem `frequency-of-the-most-frequent-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxFrequency

def numsList (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elemAt (nums : Slice Std.I64) (i : ℕ) : Int := (numsList nums).getD i 0

def Occurs (nums : Slice Std.I64) (v : Int) : Prop := v ∈ numsList nums

def countOcc (nums : Slice Std.I64) (v : Int) : ℕ :=
  ((numsList nums).filter (fun x => x = v)).length

def maxCount (nums : Slice Std.I64) : ℕ :=
  (numsList nums).foldr (fun x acc => max (countOcc nums x) acc) 0

def maxElem (nums : Slice Std.I64) : Int :=
  match numsList nums with
  | [] => 0
  | x :: xs => xs.foldr max x

def Cost (nums : Slice Std.I64) (j : ℕ) (S : Finset ℕ) : Int :=
  ∑ i ∈ S, (elemAt nums j - elemAt nums i)

def IsWitness (nums : Slice Std.I64) (k : Int) (c : Int) (j : ℕ) (S : Finset ℕ) : Prop :=
  j < nums.val.length ∧
  (∀ i ∈ S, i < nums.val.length) ∧
  (S.card : Int) = c ∧
  (∀ i ∈ S, elemAt nums i ≤ elemAt nums j) ∧
  Cost nums j S ≤ k

def Achievable (nums : Slice Std.I64) (k : Int) (c : Int) : Prop :=
  ∃ j : ℕ, ∃ S : Finset ℕ, IsWitness nums k c j S

def WindowAchievable (sorted : Slice Std.I64) (k : Int) (c : Int) : Prop :=
  ∃ l u : ℕ,
    l ≤ u ∧ u < sorted.val.length ∧ ((u - l + 1 : ℕ) : Int) = c ∧
      (∑ i ∈ Finset.Icc l u, (elemAt sorted u - elemAt sorted i)) ≤ k

/-- Whenever the function returns a result r, r is the maximum integer c for which there exists an index j with 0 <= j < n and a set S of exactly c indices from {0, ..., n-1} such that (a) for every i in S, nums[i] <= nums[j], and (b) sum_{i in S} (nums[j] - nums[i]) <= k. (If S is empty, the sum is 0.)
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Achievable nums k.val r.val ∧ ∀ c : Int, Achievable nums k.val c → c ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Achievable nums k.val r.val ∧ ∀ c : Int, Achievable nums k.val c → c ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(nums).
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      (1 : Int) ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      (1 : Int) ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= m.
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. Let m = max { count(v) : v is an integer }, where count(v) = |{i : 0 <= i < n and nums[i] = v}|. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      (maxCount nums : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      (maxCount nums : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. Let M = max_{0 <= i < n} nums[i]. Assume k >= sum_{i=0}^{n-1} (M - nums[i]). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hn' : nums.val.length ≤ 100000)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hbig : k.val ≥ ∑ i ∈ Finset.range nums.val.length, (maxElem nums - elemAt nums i)) :
    ∃ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r ∧ r.val = (nums.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hn' : nums.val.length ≤ 100000)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hbig : k.val ≥ ∑ i ∈ Finset.range nums.val.length, (maxElem nums - elemAt nums i)), ∃ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r ∧ r.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index j with 0 <= j < n and a set S of exactly r indices from {0, ..., n-1} such that for every i in S, nums[i] <= nums[j], and sum_{i in S} (nums[j] - nums[i]) <= k.
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∃ j : ℕ, ∃ S : Finset ℕ, IsWitness nums k.val r.val j S := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∃ j : ℕ, ∃ S : Finset ℕ, IsWitness nums k.val r.val j S) := by
  sorry

/-- Whenever the function returns a result r, for every index j with 0 <= j < n and every set S of indices from {0, ..., n-1}, if for every i in S, nums[i] <= nums[j], and sum_{i in S} (nums[j] - nums[i]) <= k, then |S| <= r.
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∀ j : ℕ, j < nums.val.length →
        ∀ S : Finset ℕ, (∀ i ∈ S, i < nums.val.length) →
          (∀ i ∈ S, elemAt nums i ≤ elemAt nums j) → Cost nums j S ≤ k.val →
            (S.card : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∀ j : ℕ, j < nums.val.length →
        ∀ S : Finset ℕ, (∀ i ∈ S, i < nums.val.length) →
          (∀ i ∈ S, elemAt nums i ≤ elemAt nums j) → Cost nums j S ≤ k.val →
            (S.card : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hn' : nums.val.length ≤ 100000)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∃ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hn' : nums.val.length ≤ 100000)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∃ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r) := by
  sorry

/-- Whenever max_frequency(nums, k) returns a result r and max_frequency(nums', k) returns a result r', we have r = r'.
  Preconditions: Let nums and nums' be two arrays of length n >= 1, with elements in [1, 100000], and k >= 1. Suppose there exists a bijection p: {0, ..., n-1} -> {0, ..., n-1} such that nums'[i] = nums[p(i)] for all i in {0, ..., n-1} (i.e., nums' is a permutation of nums). -/
theorem spec_8 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hval' : ∀ i : ℕ, i < nums'.val.length →
      (1 : Int) ≤ elemAt nums' i ∧ elemAt nums' i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ p : Equiv.Perm (Fin nums.val.length),
      ∀ i : Fin nums.val.length, elemAt nums' (i : ℕ) = elemAt nums (p i : ℕ)) :
    ∀ r r', Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Aegis.MaxFrequency.max_frequency nums' k = Result.ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hval' : ∀ i : ℕ, i < nums'.val.length →
      (1 : Int) ≤ elemAt nums' i ∧ elemAt nums' i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ p : Equiv.Perm (Fin nums.val.length),
      ∀ i : Fin nums.val.length, elemAt nums' (i : ℕ) = elemAt nums (p i : ℕ)), ∀ r r', Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Aegis.MaxFrequency.max_frequency nums' k = Result.ok r' → r.val = r'.val) := by
  sorry

/-- Whenever max_frequency(nums, k1) returns a result r1 and max_frequency(nums, k2) returns a result r2, we have r1 <= r2.
  Preconditions: Let n = len(nums) >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let k1 and k2 be 64-bit integers with 1 <= k1 <= k2. -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk1 : (1 : Int) ≤ k1.val)
    (hk12 : k1.val ≤ k2.val) :
    ∀ r1 r2, Aegis.MaxFrequency.max_frequency nums k1 = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k2 = Result.ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk1 : (1 : Int) ≤ k1.val)
    (hk12 : k1.val ≤ k2.val), ∀ r1 r2, Aegis.MaxFrequency.max_frequency nums k1 = Result.ok r1 →
      Aegis.MaxFrequency.max_frequency nums k2 = Result.ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever max_frequency(nums, k) returns a result r and max_frequency(nums', k) returns a result r', we have r <= r'.
  Preconditions: Let nums be an array of length n >= 1 with elements in [1, 100000], and let x be an integer in [1, 100000]. Let nums' = nums ++ [x] (length n+1). Let k >= 1. -/
theorem spec_10 (nums nums' : Slice Std.I64) (x k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hx : (1 : Int) ≤ x.val ∧ x.val ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hcat : nums'.val = nums.val ++ [x]) :
    ∀ r r', Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Aegis.MaxFrequency.max_frequency nums' k = Result.ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hx : (1 : Int) ≤ x.val ∧ x.val ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hcat : nums'.val = nums.val ++ [x]), ∀ r r', Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      Aegis.MaxFrequency.max_frequency nums' k = Result.ok r' → r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 2 if and only if there exist indices i and j with 0 <= i < j < n such that |nums[i] - nums[j]| <= k.
  Preconditions: Let n = len(nums) >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ((2 : Int) ≤ r.val ↔
        ∃ i j : ℕ, i < j ∧ j < nums.val.length ∧ |elemAt nums i - elemAt nums j| ≤ k.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ((2 : Int) ≤ r.val ↔
        ∃ i j : ℕ, i < j ∧ j < nums.val.length ∧ |elemAt nums i - elemAt nums j| ≤ k.val)) := by
  sorry

/-- Whenever the function returns a result r, for every integer c with 1 <= c <= r, there exists an index j with 0 <= j < n and a set S of exactly c indices from {0, ..., n-1} such that for every i in S, nums[i] <= nums[j], and sum_{i in S} (nums[j] - nums[i]) <= k.
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∀ c : ℕ, 1 ≤ c → (c : Int) ≤ r.val → Achievable nums k.val (c : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      ∀ c : ℕ, 1 ≤ c → (c : Int) ≤ r.val → Achievable nums k.val (c : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is the maximum integer c for which there exist indices l and u with 0 <= l <= u < n and u - l + 1 = c such that sum_{i=l}^{u} (sorted[u] - sorted[i]) <= k.
  Preconditions: Let n = len(nums). Assume n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 100000, and k >= 1. Let sorted be a nondecreasing permutation of nums (so sorted[0] <= ... <= sorted[n-1] and the multiset of sorted equals that of nums). -/
theorem spec_13 (nums sorted : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hlen : sorted.val.length = nums.val.length)
    (hnondecr : List.Pairwise (· ≤ ·) (numsList sorted))
    (hperm : List.Perm (numsList sorted) (numsList nums)) :
    ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      WindowAchievable sorted k.val r.val ∧
        ∀ c : Int, WindowAchievable sorted k.val c → c ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums sorted : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length)
    (hval : ∀ i : ℕ, i < nums.val.length → (1 : Int) ≤ elemAt nums i ∧ elemAt nums i ≤ 100000)
    (hk : (1 : Int) ≤ k.val)
    (hlen : sorted.val.length = nums.val.length)
    (hnondecr : List.Pairwise (· ≤ ·) (numsList sorted))
    (hperm : List.Perm (numsList sorted) (numsList nums)), ∀ r, Aegis.MaxFrequency.max_frequency nums k = Result.ok r →
      WindowAchievable sorted k.val r.val ∧
        ∀ c : Int, WindowAchievable sorted k.val c → c ≤ r.val) := by
  sorry

end AegisSpec.MaxFrequency
