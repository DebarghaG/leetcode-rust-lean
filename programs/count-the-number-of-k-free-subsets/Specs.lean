import Aegis.CountTheNumOfKFreeSubsets.Code.Funs

/-!
# Specifications of `Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets`

LeetCode problem `count-the-number-of-k-free-subsets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountTheNumOfKFreeSubsets

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := (nums.val.getD i 0#i64).val

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def IsKFree (nums : Slice Std.I64) (k : Int) (I : Finset Nat) : Prop :=
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → |valAt nums i - valAt nums j| ≠ k

  noncomputable def kFreeCount (nums : Slice Std.I64) (k : Int) : Nat := by
    classical
    exact (((Finset.range nums.val.length).powerset).filter (fun I => IsKFree nums k I)).card

  def fib : Nat → Nat
    | 0 => 0
    | 1 => 1
    | (m + 2) => fib (m + 1) + fib m

  noncomputable def conflictPairs (nums : Slice Std.I64) (k : Int) : Finset (Nat × Nat) := by
    classical
    exact ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
      (fun p => p.1 < p.2 ∧ |valAt nums p.1 - valAt nums p.2| = k)

  def PairwiseDisjointPairs (P : Finset (Nat × Nat)) : Prop :=
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

  /-- Let n = len(nums). For an index set I subset of {0,1,...,n-1}, call I k-free if for every i in I and j in I with i != j, |nums[i] - nums[j]| != k, where absolute value is over the integers. Whenever the function returns a result r, r is exactly the number of k-free index sets I, with the empty set included. Equivalently, r is the number of selections of elements of nums in which no two selected elements have absolute difference k.
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; and 1 <= k <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val = (kFreeCount nums k.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val = (kFreeCount nums k.val : Int)) := by
    sorry

  /-- For every nums and k satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or leave the result undefined.
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; and 1 <= k <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∃ r, Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∃ r, Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= len(nums) + 1.
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; and 1 <= k <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      (nums.val.length : Int) + 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), (nums.val.length : Int) + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2^(len(nums)).
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; and 1 <= k <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val ≤ (2 : Int) ^ nums.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val ≤ (2 : Int) ^ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, r = 2^(len(nums)).
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; 1 <= k <= 1000; and for every i,j with 0 <= i < j < n, |nums[i] - nums[j]| != k. -/
  theorem spec_5 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hfree : ∀ i j, i < j → j < nums.val.length → |valAt nums i - valAt nums j| ≠ k.val)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val = (2 : Int) ^ nums.val.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hfree : ∀ i j, i < j → j < nums.val.length → |valAt nums i - valAt nums j| ≠ k.val)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val = (2 : Int) ^ nums.val.length) := by
    sorry

  /-- Let n = len(nums). For every integer m with 1 <= m and every collection of m pairwise disjoint unordered index pairs {i_t,j_t}, t = 1,...,m, such that 0 <= i_t < j_t < n and |nums[i_t] - nums[j_t]| = k for every t, whenever the function returns a result r, r <= 3^m * 2^(n - 2m).
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; and 1 <= k <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (k r : Std.I64) (m : Nat)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hm : 1 ≤ m)
      (pr : Fin m → Nat × Nat)
      (hpr_lt : ∀ t, (pr t).1 < (pr t).2 ∧ (pr t).2 < nums.val.length)
      (hpr_conf : ∀ t, |valAt nums (pr t).1 - valAt nums (pr t).2| = k.val)
      (hpr_disj : ∀ t s, t ≠ s →
        (pr t).1 ≠ (pr s).1 ∧ (pr t).1 ≠ (pr s).2 ∧ (pr t).2 ≠ (pr s).1 ∧
          (pr t).2 ≠ (pr s).2)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val ≤ (3 : Int) ^ m * (2 : Int) ^ (nums.val.length - 2 * m) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64) (m : Nat)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hm : 1 ≤ m)
        (pr : Fin m → Nat × Nat)
        (hpr_lt : ∀ t, (pr t).1 < (pr t).2 ∧ (pr t).2 < nums.val.length)
        (hpr_conf : ∀ t, |valAt nums (pr t).1 - valAt nums (pr t).2| = k.val)
        (hpr_disj : ∀ t s, t ≠ s →
          (pr t).1 ≠ (pr s).1 ∧ (pr t).1 ≠ (pr s).2 ∧ (pr t).2 ≠ (pr s).1 ∧
            (pr t).2 ≠ (pr s).2)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val ≤ (3 : Int) ^ m * (2 : Int) ^ (nums.val.length - 2 * m)) := by
    sorry

  /-- Let Fib be defined by Fib(1)=1, Fib(2)=1, and Fib(m)=Fib(m-1)+Fib(m-2) for m >= 3. Whenever the function returns a result r, r = Fib(n+2).
    Preconditions: len(nums) is an integer n with 3 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; 1 <= k <= 1000; and there exists an integer a such that the set of values {nums[i] | 0 <= i < n} equals {a + t*k | 0 <= t < n}. -/
  theorem spec_7 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_ge : 3 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hshape : ∃ a : Int, Finset.image (valAt nums) (Finset.range nums.val.length) =
        Finset.image (fun t : Nat => a + (t : Int) * k.val) (Finset.range nums.val.length))
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val = (fib (nums.val.length + 2) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_ge : 3 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hshape : ∃ a : Int, Finset.image (valAt nums) (Finset.range nums.val.length) =
          Finset.image (fun t : Nat => a + (t : Int) * k.val) (Finset.range nums.val.length))
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val = (fib (nums.val.length + 2) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 3^m * 2^(n - 2m).
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; 1 <= k <= 1000; the set P = {{i,j} | 0 <= i < j < n and |nums[i] - nums[j]| = k} is nonempty and pairwise disjoint in the sense that no index occurs in two different pairs; and m = |P|. -/
  theorem spec_8 (nums : Slice Std.I64) (k r : Std.I64) (m : Nat)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hm : m = (conflictPairs nums k.val).card)
      (hne : (conflictPairs nums k.val).Nonempty)
      (hdisj : PairwiseDisjointPairs (conflictPairs nums k.val))
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      r.val = (3 : Int) ^ m * (2 : Int) ^ (nums.val.length - 2 * m) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64) (m : Nat)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hm : m = (conflictPairs nums k.val).card)
        (hne : (conflictPairs nums k.val).Nonempty)
        (hdisj : PairwiseDisjointPairs (conflictPairs nums k.val))
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), r.val = (3 : Int) ^ m * (2 : Int) ^ (nums.val.length - 2 * m)) := by
    sorry

  /-- If a call on nums with this k returns r and a call on nums2 with the same k returns r2, then r = r2.
    Preconditions: len(nums) = len(nums2) = n with 1 <= n <= 50; both nums and nums2 have pairwise distinct elements all in the range 1..1000; nums2 is a permutation of nums, meaning the multiset of values of nums2 equals the multiset of values of nums; and 1 <= k <= 1000. -/
  theorem spec_9 (nums nums2 : Slice Std.I64) (k r r2 : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hn_len : nums2.val.length = nums.val.length)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hval2 : ∀ i, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hdistinct2 : ∀ i j, i < j → j < nums2.val.length → valAt nums2 i ≠ valAt nums2 j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hperm : (vals nums2).Perm (vals nums))
      (h1 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r)
      (h2 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums2 k = ok r2) :
      r.val = r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k r r2 : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hn_len : nums2.val.length = nums.val.length)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hval2 : ∀ i, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hdistinct2 : ∀ i j, i < j → j < nums2.val.length → valAt nums2 i ≠ valAt nums2 j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hperm : (vals nums2).Perm (vals nums))
        (h1 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r)
        (h2 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums2 k = ok r2), r.val = r2.val) := by
    sorry

  /-- If a call on nums with this k returns r and a call on nums2 with the same k returns r2, then r2 = 2*r.
    Preconditions: nums and nums2 are slices; len(nums) = n and len(nums2) = n+1, with 1 <= n and n+1 <= 50; both have pairwise distinct elements all in the range 1..1000; there exists an integer x such that the multiset of values of nums2 is the multiset of values of nums together with x, and for every i with 0 <= i < n, |x - nums[i]| != k; and 1 <= k <= 1000. -/
  theorem spec_10 (nums nums2 : Slice Std.I64) (k r r2 : Std.I64) (n : Nat) (x : Int)
      (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn2 : nums2.val.length = n + 1)
      (hn_le : n + 1 ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hval2 : ∀ i, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hdistinct2 : ∀ i j, i < j → j < nums2.val.length → valAt nums2 i ≠ valAt nums2 j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hperm : (vals nums2).Perm (vals nums ++ [x]))
      (hx : ∀ i, i < nums.val.length → |x - valAt nums i| ≠ k.val)
      (h1 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r)
      (h2 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums2 k = ok r2) :
      r2.val = 2 * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (k r r2 : Std.I64) (n : Nat) (x : Int)
        (hn : nums.val.length = n) (hn_pos : 1 ≤ n) (hn2 : nums2.val.length = n + 1)
        (hn_le : n + 1 ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hval2 : ∀ i, i < nums2.val.length → 1 ≤ valAt nums2 i ∧ valAt nums2 i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hdistinct2 : ∀ i j, i < j → j < nums2.val.length → valAt nums2 i ≠ valAt nums2 j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hperm : (vals nums2).Perm (vals nums ++ [x]))
        (hx : ∀ i, i < nums.val.length → |x - valAt nums i| ≠ k.val)
        (h1 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r)
        (h2 : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums2 k = ok r2), r2.val = 2 * r.val) := by
    sorry

  /-- Whenever the function returns a result r, r is even.
    Preconditions: len(nums) is an integer n with 1 <= n <= 50; for every i with 0 <= i < n, 1 <= nums[i] <= 1000; for every i,j with 0 <= i < j < n, nums[i] != nums[j]; 1 <= k <= 1000; and there exists an index i0 with 0 <= i0 < n such that for every j with 0 <= j < n and j != i0, |nums[i0] - nums[j]| != k. -/
  theorem spec_11 (nums : Slice Std.I64) (k r : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
      (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
      (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (h0 : ∃ i0, i0 < nums.val.length ∧
        ∀ j, j < nums.val.length → j ≠ i0 → |valAt nums i0 - valAt nums j| ≠ k.val)
      (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r) :
      ∃ c : Int, r.val = 2 * c := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k r : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 50)
        (hval : ∀ i, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 1000)
        (hdistinct : ∀ i j, i < j → j < nums.val.length → valAt nums i ≠ valAt nums j)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (h0 : ∃ i0, i0 < nums.val.length ∧
          ∀ j, j < nums.val.length → j ≠ i0 → |valAt nums i0 - valAt nums j| ≠ k.val)
        (h : Aegis.CountTheNumOfKFreeSubsets.count_the_num_of_k_free_subsets nums k = ok r), ∃ c : Int, r.val = 2 * c) := by
    sorry

  end AegisSpec.CountTheNumOfKFreeSubsets
