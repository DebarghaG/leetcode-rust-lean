import Aegis.WaysToPartition.Code.Funs

/-!
# Specifications of `Aegis.WaysToPartition.ways_to_partition`

LeetCode problem `maximum-number-of-ways-to-partition-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WaysToPartition

  namespace AegisSpec.WaysToPartition

  def entry (nums : Slice Std.I64) (i : ℕ) (hi : i < nums.val.length) : ℤ :=
    (nums.val.get ⟨i, hi⟩).val

  def setAt (a : List ℤ) (j : ℕ) (v : ℤ) : List ℤ := a.set j v

  def W (a : List ℤ) : ℤ :=
    (((List.range a.length).filter
        (fun p => decide (1 ≤ p ∧ (a.take p).sum = (a.drop p).sum))).length : ℤ)

  def bestScore (a : List ℤ) (k : ℤ) : ℤ :=
    (W a :: (List.range a.length).map (fun j => W (setAt a j k))).foldr max 0

  def isAllowed (a : List ℤ) (t : Option ℕ) : Prop := ∀ j, t = some j → j < a.length

  def chosen (a : List ℤ) (k : ℤ) (t : Option ℕ) : List ℤ :=
    match t with
    | none => a
    | some j => setAt a j k

  /-- For any integer array a of length n, let W(a) be the number of indices p with 1 <= p < n such that sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. For 0 <= j < n, let nums_j be the length-n array with nums_j[j] = k and nums_j[i] = nums[i] for i != j. The function returns a result r and r = max( W(nums), max_{0 <= j < n} W(nums_j) ).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. All sums mentioned are ordinary mathematical integers. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧ r.val = bestScore nums.val k.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧ r.val = bestScore nums.val k.val) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n - 1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, overflow, access out of bounds, or panic on any input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r) := by
    sorry

  /-- The function returns a result r and there exists an allowed choice t, where either t = none meaning leave nums unchanged, or t = j for some index 0 <= j < n meaning replace nums[j] by k, such that r = W(a_t), where a_none = nums and a_j is nums with index j set to k.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        ∃ t : Option ℕ, isAllowed nums.val t ∧ r.val = W (chosen nums.val k.val t) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          ∃ t : Option ℕ, isAllowed nums.val t ∧ r.val = W (chosen nums.val k.val t)) := by
    sorry

  /-- The function returns a result r and for every index j with 0 <= j < n, W(nums_j) <= r.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. For 0 <= j < n, let nums_j be nums with index j set to k. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        ∀ j : ℕ, j < nums.val.length → W (setAt nums.val j k.val) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          ∀ j : ℕ, j < nums.val.length → W (setAt nums.val j k.val) ≤ r.val) := by
    sorry

  /-- The function returns a result r and W(nums) <= r.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧ W nums.val ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧ W nums.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if W(nums) = 0 and W(nums_j) = 0 for every j with 0 <= j < n.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. For 0 <= j < n, let nums_j be nums with index j set to k. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        (r.val = 0 ↔ W nums.val = 0 ∧
          ∀ j : ℕ, j < nums.val.length → W (setAt nums.val j k.val) = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          (r.val = 0 ↔ W nums.val = 0 ∧
            ∀ j : ℕ, j < nums.val.length → W (setAt nums.val j k.val) = 0)) := by
    sorry

  /-- The function returns a result r and r = 1 if nums[0] = nums[1] or k = nums[1] or nums[0] = k, and r = 0 otherwise.
    Preconditions: Let n = len(nums). Assume n = 2, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : nums.val.length = 2)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        ((entry nums 0 (by omega) = entry nums 1 (by omega) ∨
            k.val = entry nums 1 (by omega) ∨
            entry nums 0 (by omega) = k.val) → r.val = 1) ∧
        (¬ (entry nums 0 (by omega) = entry nums 1 (by omega) ∨
            k.val = entry nums 1 (by omega) ∨
            entry nums 0 (by omega) = k.val) → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : nums.val.length = 2)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          ((entry nums 0 (by omega) = entry nums 1 (by omega) ∨
              k.val = entry nums 1 (by omega) ∨
              entry nums 0 (by omega) = k.val) → r.val = 1) ∧
          (¬ (entry nums 0 (by omega) = entry nums 1 (by omega) ∨
              k.val = entry nums 1 (by omega) ∨
              entry nums 0 (by omega) = k.val) → r.val = 0)) := by
    sorry

  /-- The function returns a result r and r = n - 1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, nums[i] = 0, and -100000 <= k <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length), entry nums i hi = 0)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        r.val = (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length), entry nums i hi = 0)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          r.val = (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Let rev be the length-n array with rev[i] = nums[n-1-i] for 0 <= i < n, and for 0 <= j < n let rev_j be rev with index j set to k. The function returns a result r and r = max( W(rev), max_{0 <= j < n} W(rev_j) ).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        r.val = bestScore nums.val.reverse k.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          r.val = bestScore nums.val.reverse k.val) := by
    sorry

  /-- Let neg be the length-n array with neg[i] = -nums[i] for 0 <= i < n, and for 0 <= j < n let neg_j be neg with index j set to -k. The function returns a result r and r = max( W(neg), max_{0 <= j < n} W(neg_j) ).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        r.val = bestScore (nums.val.map (fun x => -x)) (-k.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          r.val = bestScore (nums.val.map (fun x => -x)) (-k.val)) := by
    sorry

  /-- The function returns a result r and either r = W(nums), or there exists an index j with 0 <= j < n and nums[j] != k such that r = W(nums_j).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and -100000 <= k <= 100000. Define W(a) as the number of pivots p with 1 <= p < n and sum_{i=0}^{p-1} a[i] = sum_{i=p}^{n-1} a[i]. For 0 <= j < n, let nums_j be nums with index j set to k. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
        -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
      (hk : -100000 ≤ k.val ∧ k.val ≤ 100000) :
      ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
        (r.val = W nums.val ∨
          ∃ (j : ℕ) (hj : j < nums.val.length), entry nums j hj ≠ k.val ∧
            r.val = W (setAt nums.val j k.val)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hnums : ∀ (i : ℕ) (hi : i < nums.val.length),
          -100000 ≤ entry nums i hi ∧ entry nums i hi ≤ 100000)
        (hk : -100000 ≤ k.val ∧ k.val ≤ 100000), ∃ r : Std.I64, ways_to_partition nums k = ok r ∧
          (r.val = W nums.val ∨
            ∃ (j : ℕ) (hj : j < nums.val.length), entry nums j hj ≠ k.val ∧
              r.val = W (setAt nums.val j k.val))) := by
    sorry

  end AegisSpec.WaysToPartition
