import Aegis.MinimizeSum.Code.Funs

/-!
# Specifications of `Aegis.MinimizeSum.minimize_sum`

LeetCode problem `minimum-score-by-changing-two-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimizeSum

  set_option autoImplicit false

  namespace AegisSpec.MinimizeSum

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def Pre (nums : Slice I64) : Prop :=
    3 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
      ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000000

  def IsRearrangement (a l : List ℤ) : Prop :=
    a.length = l.length ∧ List.Pairwise (· ≤ ·) a ∧ a.Perm l

  def entry (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

  def lmax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def lmin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def occCount (v : ℤ) (l : List ℤ) : ℕ := (l.filter (fun x => x = v)).length

  def gapList (b : List ℤ) : List ℤ :=
    (List.range b.length).flatMap fun i =>
      (List.range b.length).filterMap fun j =>
        if i < j then some |entry b i - entry b j| else none

  def diam (b : List ℤ) : ℤ :=
    lmax (b.flatMap fun x => b.map fun y => |x - y|)

  def minGap (b : List ℤ) : ℤ := lmin (gapList b)

  def score (b : List ℤ) : ℤ := diam b + minGap b

  def AgreesOutside (b l : List ℤ) (I : Finset ℕ) : Prop :=
    ∀ i, i < b.length → i ∉ I → entry b i = entry l i

  /-- Let a be a nondecreasing rearrangement of nums, so a has length n, a[0] <= a[1] <= ... <= a[n-1], and a is a permutation of nums. The function returns a result r and r = min(a[n-1] - a[2], a[n-2] - a[1], a[n-3] - a[0]).
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice I64) (a : List ℤ) (hpre : Pre nums)
      (hlen : a.length = (vals nums).length)
      (hsorted : List.Pairwise (· ≤ ·) a)
      (hperm : a.Perm (vals nums)) :
      ∃ r, minimize_sum nums = ok r ∧
        r.val = min (min (entry a (a.length - 1) - entry a 2)
                         (entry a (a.length - 2) - entry a 1))
                    (entry a (a.length - 3) - entry a 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (a : List ℤ) (hpre : Pre nums)
        (hlen : a.length = (vals nums).length)
        (hsorted : List.Pairwise (· ≤ ·) a)
        (hperm : a.Perm (vals nums)), ∃ r, minimize_sum nums = ok r ∧
          r.val = min (min (entry a (a.length - 1) - entry a 2)
                           (entry a (a.length - 2) - entry a 1))
                      (entry a (a.length - 3) - entry a 0)) := by
    sorry

  /-- The function returns a result r; in particular, under these preconditions it does not fail, panic, encounter integer overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice I64) (hpre : Pre nums) :
      ∃ r, minimize_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∃ r, minimize_sum nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice I64) (hpre : Pre nums) (r : I64)
      (hres : minimize_sum nums = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (r : I64)
        (hres : minimize_sum nums = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= (max over 0 <= i < n of nums[i]) - (min over 0 <= i < n of nums[i]).
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice I64) (hpre : Pre nums) (r : I64)
      (hres : minimize_sum nums = ok r) :
      r.val ≤ lmax (vals nums) - lmin (vals nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (r : I64)
        (hres : minimize_sum nums = ok r), r.val ≤ lmax (vals nums) - lmin (vals nums)) := by
    sorry

  /-- Let a be a nondecreasing rearrangement of nums. Whenever the function returns a result r, r <= a[n-1] - a[2], r <= a[n-2] - a[1], and r <= a[n-3] - a[0].
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice I64) (a : List ℤ) (hpre : Pre nums)
      (hlen : a.length = (vals nums).length)
      (hsorted : List.Pairwise (· ≤ ·) a)
      (hperm : a.Perm (vals nums))
      (r : I64) (hres : minimize_sum nums = ok r) :
      r.val ≤ entry a (a.length - 1) - entry a 2 ∧
      r.val ≤ entry a (a.length - 2) - entry a 1 ∧
      r.val ≤ entry a (a.length - 3) - entry a 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (a : List ℤ) (hpre : Pre nums)
        (hlen : a.length = (vals nums).length)
        (hsorted : List.Pairwise (· ≤ ·) a)
        (hperm : a.Perm (vals nums))
        (r : I64) (hres : minimize_sum nums = ok r), r.val ≤ entry a (a.length - 1) - entry a 2 ∧
        r.val ≤ entry a (a.length - 2) - entry a 1 ∧
        r.val ≤ entry a (a.length - 3) - entry a 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists an integer v such that the number of indices i with 0 <= i < n and nums[i] = v is at least n - 2.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice I64) (hpre : Pre nums) (r : I64)
      (hres : minimize_sum nums = ok r) :
      (r.val = 0 ↔ ∃ v : ℤ, (vals nums).length - 2 ≤ occCount v (vals nums)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (r : I64)
        (hres : minimize_sum nums = ok r), (r.val = 0 ↔ ∃ v : ℤ, (vals nums).length - 2 ≤ occCount v (vals nums))) := by
    sorry

  /-- The function returns results r on nums and r2 on nums2, and r2 = r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let nums2 be any list of length n that is a permutation of nums. -/
  theorem spec_7 (nums nums2 : Slice I64) (hpre : Pre nums)
      (hlen : nums2.val.length = nums.val.length)
      (hperm : (vals nums2).Perm (vals nums)) :
      ∃ r r2, minimize_sum nums = ok r ∧ minimize_sum nums2 = ok r2 ∧
        r2.val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums nums2 : Slice I64) (hpre : Pre nums)
        (hlen : nums2.val.length = nums.val.length)
        (hperm : (vals nums2).Perm (vals nums)), ∃ r r2, minimize_sum nums = ok r ∧ minimize_sum nums2 = ok r2 ∧
          r2.val = r.val) := by
    sorry

  /-- The function returns results r on nums and r_shifted on shifted, and r_shifted = r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let c be an integer such that 1 <= nums[i] + c <= 1000000000 for every i with 0 <= i < n. Let shifted be the list of length n with shifted[i] = nums[i] + c. -/
  theorem spec_8 (nums shifted : Slice I64) (c : ℤ) (hpre : Pre nums)
      (hc : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 1000000000)
      (hshift : vals shifted = (vals nums).map (fun x => x + c)) :
      ∃ r rs, minimize_sum nums = ok r ∧ minimize_sum shifted = ok rs ∧
        rs.val = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums shifted : Slice I64) (c : ℤ) (hpre : Pre nums)
        (hc : ∀ x ∈ vals nums, 1 ≤ x + c ∧ x + c ≤ 1000000000)
        (hshift : vals shifted = (vals nums).map (fun x => x + c)), ∃ r rs, minimize_sum nums = ok r ∧ minimize_sum shifted = ok rs ∧
          rs.val = r.val) := by
    sorry

  /-- The function returns results r on nums and r_scaled on scaled, and r_scaled = c * r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let c be a positive integer such that 1 <= c * nums[i] <= 1000000000 for every i with 0 <= i < n. Let scaled be the list of length n with scaled[i] = c * nums[i]. -/
  theorem spec_9 (nums scaled : Slice I64) (c : ℤ) (hpre : Pre nums)
      (hcpos : 0 < c)
      (hc : ∀ x ∈ vals nums, 1 ≤ c * x ∧ c * x ≤ 1000000000)
      (hscale : vals scaled = (vals nums).map (fun x => c * x)) :
      ∃ r rsc, minimize_sum nums = ok r ∧ minimize_sum scaled = ok rsc ∧
        rsc.val = c * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums scaled : Slice I64) (c : ℤ) (hpre : Pre nums)
        (hcpos : 0 < c)
        (hc : ∀ x ∈ vals nums, 1 ≤ c * x ∧ c * x ≤ 1000000000)
        (hscale : vals scaled = (vals nums).map (fun x => c * x)), ∃ r rsc, minimize_sum nums = ok r ∧ minimize_sum scaled = ok rsc ∧
          rsc.val = c * r.val) := by
    sorry

  /-- The function returns results r on nums and r_reflected on reflected, and r_reflected = r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let C be an integer such that 1 <= C - nums[i] <= 1000000000 for every i with 0 <= i < n. Let reflected be the list of length n with reflected[i] = C - nums[i]. -/
  theorem spec_10 (nums reflected : Slice I64) (C : ℤ) (hpre : Pre nums)
      (hC : ∀ x ∈ vals nums, 1 ≤ C - x ∧ C - x ≤ 1000000000)
      (href : vals reflected = (vals nums).map (fun x => C - x)) :
      ∃ r rr, minimize_sum nums = ok r ∧ minimize_sum reflected = ok rr ∧
        rr.val = r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums reflected : Slice I64) (C : ℤ) (hpre : Pre nums)
        (hC : ∀ x ∈ vals nums, 1 ≤ C - x ∧ C - x ≤ 1000000000)
        (href : vals reflected = (vals nums).map (fun x => C - x)), ∃ r rr, minimize_sum nums = ok r ∧ minimize_sum reflected = ok rr ∧
          rr.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist an array b of length n and a set I of at most two indices such that: (i) b[i] = nums[i] for every i with 0 <= i < n and i not in I; (ii) the score of b, defined as (max over 0 <= i < n and 0 <= j < n of |b[i] - b[j]|) + (min over 0 <= i < j < n of |b[i] - b[j]|), is equal to r; and (iii) min over 0 <= i < j < n of |b[i] - b[j]| = 0.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_11 (nums : Slice I64) (hpre : Pre nums) (r : I64)
      (hres : minimize_sum nums = ok r) :
      ∃ b : List ℤ, b.length = (vals nums).length ∧
        ∃ I : Finset ℕ, I.card ≤ 2 ∧ (∀ i ∈ I, i < b.length) ∧
          AgreesOutside b (vals nums) I ∧ score b = r.val ∧ minGap b = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (r : I64)
        (hres : minimize_sum nums = ok r), ∃ b : List ℤ, b.length = (vals nums).length ∧
          ∃ I : Finset ℕ, I.card ≤ 2 ∧ (∀ i ∈ I, i < b.length) ∧
            AgreesOutside b (vals nums) I ∧ score b = r.val ∧ minGap b = 0) := by
    sorry

  /-- Whenever the function returns a result r, for every array b of length n and every set I of at most two indices such that b[i] = nums[i] for all i with 0 <= i < n and i not in I, the score of b, defined as (max over 0 <= i < n and 0 <= j < n of |b[i] - b[j]|) + (min over 0 <= i < j < n of |b[i] - b[j]|), is at least r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
  theorem spec_12 (nums : Slice I64) (hpre : Pre nums) (r : I64)
      (hres : minimize_sum nums = ok r) :
      ∀ b : List ℤ, b.length = (vals nums).length →
        ∀ I : Finset ℕ, I.card ≤ 2 → (∀ i ∈ I, i < b.length) →
          AgreesOutside b (vals nums) I → r.val ≤ score b := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (r : I64)
        (hres : minimize_sum nums = ok r), ∀ b : List ℤ, b.length = (vals nums).length →
          ∀ I : Finset ℕ, I.card ≤ 2 → (∀ i ∈ I, i < b.length) →
            AgreesOutside b (vals nums) I → r.val ≤ score b) := by
    sorry

  /-- If a[i] = a2[i] for every i in the set containing 0, 1, 2, n-3, n-2, and n-1, then the function returns results r on nums and r2 on nums2, and r2 = r.
    Preconditions: Let n = len(nums). 3 <= n <= 100000 and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. Let nums2 be another list of length n satisfying the same bounds. Let a and a2 be nondecreasing rearrangements of nums and nums2 respectively. -/
  theorem spec_13 (nums nums2 : Slice I64) (a a2 : List ℤ)
      (hpre : Pre nums) (hpre2 : Pre nums2)
      (hlen2 : nums2.val.length = nums.val.length)
      (hr1 : IsRearrangement a (vals nums))
      (hr2 : IsRearrangement a2 (vals nums2))
      (hagree : ∀ i ∈ ({0, 1, 2, (vals nums).length - 3, (vals nums).length - 2,
                        (vals nums).length - 1} : Finset ℕ), entry a i = entry a2 i) :
      ∃ r r2, minimize_sum nums = ok r ∧ minimize_sum nums2 = ok r2 ∧
        r2.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums2 : Slice I64) (a a2 : List ℤ)
        (hpre : Pre nums) (hpre2 : Pre nums2)
        (hlen2 : nums2.val.length = nums.val.length)
        (hr1 : IsRearrangement a (vals nums))
        (hr2 : IsRearrangement a2 (vals nums2))
        (hagree : ∀ i ∈ ({0, 1, 2, (vals nums).length - 3, (vals nums).length - 2,
                          (vals nums).length - 1} : Finset ℕ), entry a i = entry a2 i), ∃ r r2, minimize_sum nums = ok r ∧ minimize_sum nums2 = ok r2 ∧
          r2.val = r.val) := by
    sorry

  end AegisSpec.MinimizeSum
