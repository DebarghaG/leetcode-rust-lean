import Aegis.MaxAlternatingSum.Code.Funs

/-!
# Specifications of `Aegis.MaxAlternatingSum.max_alternating_sum`

LeetCode problem `maximum-alternating-subsequence-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxAlternatingSum

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def IsSubseqIdx (n : ℕ) (js : List ℕ) : Prop :=
    js.Pairwise (· < ·) ∧ ∀ j ∈ js, j < n

  def altSum : List ℤ → List ℕ → ℤ
    | _, [] => 0
    | v, j :: js => v.getD j 0 - altSum v js

  def idxLists : ℕ → List (List ℕ)
    | 0 => [[]]
    | n + 1 => idxLists n ++ (idxLists n).map (fun js => js ++ [n])

  def altMax (v : List ℤ) : ℤ :=
    ((idxLists v.length).map (fun js => altSum v js)).foldr max 0

  def climbSum (v : List ℤ) : ℤ :=
    ((List.range (v.length - 1)).map
      (fun i => max (0 : ℤ) (v.getD (i + 1) 0 - v.getD i 0))).sum

  def totalSum (v : List ℤ) : ℤ := v.sum

  theorem val_length_le (nums : Slice Std.I64) : nums.val.length ≤ Usize.max := by
    have h : nums.val.length = nums.leng := by
      simp [Slice.val, Aeneas.Data.ListN.ListN_length]
    rw [h]
    exact nums.bound

  def revSlice (nums : Slice Std.I64) : Slice Std.I64 :=
    ⟨nums.val.reverse.length, Aeneas.Data.ListN.ListN.fromList nums.val.reverse,
      Nat.le_trans (by rw [List.length_reverse]) (val_length_le nums)⟩

  def takeSlice (nums : Slice Std.I64) (k : ℕ) : Slice Std.I64 :=
    ⟨(nums.val.take k).length, Aeneas.Data.ListN.ListN.fromList _,
      Nat.le_trans (by rw [List.length_take]; exact Nat.min_le_right _ _)
        (val_length_le nums)⟩

  def scaleI64 (c : ℤ) (x : Std.I64) : Std.I64 :=
    IScalar.mk (BitVec.ofInt 64 (c * x.val))

  def scaleSlice (c : ℤ) (nums : Slice Std.I64) : Slice Std.I64 :=
    ⟨(nums.val.map (scaleI64 c)).length, Aeneas.Data.ListN.ListN.fromList _,
      Nat.le_trans (by rw [List.length_map]) (val_length_le nums)⟩

  /-- Whenever the function returns a result r, the following holds. For a subsequence of nums given by indices 0 <= j_0 < j_1 < ... < j_{k-1} < n (with k >= 0; k = 0 is the empty subsequence), define its alternating sum by alt(j_0,...,j_{k-1}) = sum_{t=0}^{k-1} (-1)^t * nums[j_t], and alt(empty) = 0. Then r = max { alt(J) | J is a subsequence of nums }.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val = altMax (vals nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val = altMax (vals nums)) := by
    sorry

  /-- The function returns a result r and does not fail (no panic, indexing error, or arithmetic overflow) for every nums satisfying the preconditions.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
      ∃ r : Std.I64, Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : Std.I64, Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every integer i with 0 <= i < n we have r >= nums[i].
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      ∀ (i : ℕ) (hi : i < n), r.val ≥ (nums.val[i]).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), ∀ (i : ℕ) (hi : i < n), r.val ≥ (nums.val[i]).val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} nums[i].
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val ≤ totalSum (vals nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val ≤ totalSum (vals nums)) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 100000 * n (and therefore r <= 10^10).
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      1 ≤ r.val ∧ r.val ≤ 100000 * (n : ℤ) ∧ r.val ≤ (10 : ℤ) ^ 10 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), 1 ≤ r.val ∧ r.val ≤ 100000 * (n : ℤ) ∧ r.val ≤ (10 : ℤ) ^ 10) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subsequence J of nums (possibly empty) such that alt(J) = r, where for indices j_0 < ... < j_{k-1} we define alt(J) = sum_{t=0}^{k-1} (-1)^t * nums[j_t], and alt(empty) = 0.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_6 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      ∃ js : List ℕ, IsSubseqIdx n js ∧ altSum (vals nums) js = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), ∃ js : List ℕ, IsSubseqIdx n js ∧ altSum (vals nums) js = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every subsequence J of nums we have alt(J) <= r, where for indices j_0 < ... < j_{k-1} we define alt(J) = sum_{t=0}^{k-1} (-1)^t * nums[j_t], and alt(empty) = 0.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_7 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      ∀ js : List ℕ, IsSubseqIdx n js → altSum (vals nums) js ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), ∀ js : List ℕ, IsSubseqIdx n js → altSum (vals nums) js ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[0].
    Preconditions: len(nums) = n with 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n, and n = 1. -/
  theorem spec_8 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (hn3 : n = 1)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val = (nums.val[0]).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (hn3 : n = 1)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val = (nums.val[0]).val) := by
    sorry

  /-- Whenever the function returns a result r, r = max(nums[0], nums[1]).
    Preconditions: len(nums) = n with 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n, and n = 2. -/
  theorem spec_9 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (hn3 : n = 2)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val = max (nums.val[0]).val (nums.val[1]).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (hn3 : n = 2)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val = max (nums.val[0]).val (nums.val[1]).val) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[n-1].
    Preconditions: len(nums) = n with 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n, and nums[i] <= nums[i+1] for every integer i with 0 <= i < n-1. -/
  theorem spec_10 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (hsorted : ∀ (i : ℕ) (hi : i < n - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val = (nums.val[n - 1]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (hsorted : ∀ (i : ℕ) (hi : i < n - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val = (nums.val[n - 1]).val) := by
    sorry

  /-- Whenever the function returns a result r, r = nums[0] + sum_{i=1}^{n-1} max(0, nums[i] - nums[i-1]), where max is the integer maximum and the sum is empty when n = 1.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_11 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r) :
      r.val = (nums.val[0]).val + climbSum (vals nums) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r), r.val = (nums.val[0]).val + climbSum (vals nums)) := by
    sorry

  /-- Let rev(nums) be the array of length n defined by rev(nums)[i] = nums[n-1-i] for 0 <= i < n. Whenever the function returns r on nums and returns r_rev on rev(nums), we have r = r_rev.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_12 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
      (r_rev : Std.I64)
      (hr_rev : Aegis.MaxAlternatingSum.max_alternating_sum (revSlice nums) = ok r_rev) :
      r.val = r_rev.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
        (r_rev : Std.I64)
        (hr_rev : Aegis.MaxAlternatingSum.max_alternating_sum (revSlice nums) = ok r_rev), r.val = r_rev.val) := by
    sorry

  /-- For every integer k with 1 <= k <= n, let prefix_k be the array consisting of the first k elements nums[0],...,nums[k-1]. Whenever the function returns r on nums and returns r_k on prefix_k, we have r_k <= r.
    Preconditions: len(nums) = n with 1 <= n <= 100000, and 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_13 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
      (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
      (r_k : Std.I64)
      (hr_k : Aegis.MaxAlternatingSum.max_alternating_sum (takeSlice nums k) = ok r_k) :
      r_k.val ≤ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
        (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n)
        (r_k : Std.I64)
        (hr_k : Aegis.MaxAlternatingSum.max_alternating_sum (takeSlice nums k) = ok r_k), r_k.val ≤ r.val) := by
    sorry

  /-- Let scaled be the array of length n defined by scaled[i] = c * nums[i]. Whenever the function returns r on nums and returns r_scaled on scaled, we have r_scaled = c * r.
    Preconditions: len(nums) = n with 1 <= n <= 100000, 1 <= nums[i] <= 100000 for every integer i with 0 <= i < n, and c is an integer with c >= 1 and c * nums[i] <= 100000 for every integer i with 0 <= i < n. -/
  theorem spec_14 (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
      (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
      (c : ℤ) (hc : 1 ≤ c)
      (hcval : ∀ (i : ℕ) (hi : i < n), c * (nums.val[i]).val ≤ 100000)
      (r_scaled : Std.I64)
      (hr_scaled : Aegis.MaxAlternatingSum.max_alternating_sum (scaleSlice c nums) = ok r_scaled) :
      r_scaled.val = c * r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : nums.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
        (hval : ∀ (i : ℕ) (hi : i < n), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (r : Std.I64) (hr : Aegis.MaxAlternatingSum.max_alternating_sum nums = ok r)
        (c : ℤ) (hc : 1 ≤ c)
        (hcval : ∀ (i : ℕ) (hi : i < n), c * (nums.val[i]).val ≤ 100000)
        (r_scaled : Std.I64)
        (hr_scaled : Aegis.MaxAlternatingSum.max_alternating_sum (scaleSlice c nums) = ok r_scaled), r_scaled.val = c * r.val) := by
    sorry

  end AegisSpec.MaxAlternatingSum
