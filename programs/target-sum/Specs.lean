import Aegis.FindTargetSumWays.Code.Funs

/-!
# Specifications of `Aegis.FindTargetSumWays.find_target_sum_ways`

LeetCode problem `target-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTargetSumWays

  def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def numsLen (nums : Slice I64) : ℕ := nums.val.length

  def numsTotal (nums : Slice I64) : ℤ := (vals nums).sum

  def zeroCount (l : List ℤ) : ℕ := (l.filter (fun x => x = 0)).length

  def signSum (l : List ℤ) (s : Fin l.length → Bool) : ℤ :=
    ∑ i : Fin l.length, if s i then l.get i else -l.get i

  def signCount (l : List ℤ) (t : ℤ) : ℕ :=
    ((Finset.univ : Finset (Fin l.length → Bool)).filter (fun s => signSum l s = t)).card

  def subsetCount (l : List ℤ) (t : ℤ) : ℕ :=
    ((Finset.univ : Finset (Finset (Fin l.length))).filter
      (fun S => S.sum (fun i => l.get i) = t)).card

  def targetRange : Finset ℤ :=
    (Finset.range 2001).map
      ⟨fun k : ℕ => (k : ℤ) - 1000, by
        intro a b h
        simp only at h
        omega⟩

  def i64neg (x : I64) : I64 := ⟨-x.bv⟩

  /-- The function returns a result r, and r is the number of sign functions s: {0,...,n-1} -> {1,-1} such that sum_{i=0}^{n-1} s(i) * nums[i] = target.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_1 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∃ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r ∧
        r.val = (signCount (vals nums) target.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∃ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r ∧
          r.val = (signCount (vals nums) target.val : ℤ)) := by
    sorry

  /-- The function does not fail: find_target_sum_ways nums target returns some result r.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_2 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∃ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∃ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, we have 0 <= r <= 2^n, where n = len(nums).
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_3 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        0 ≤ r.val ∧ r.val ≤ (2 : ℤ) ^ numsLen nums := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          0 ≤ r.val ∧ r.val ≤ (2 : ℤ) ^ numsLen nums) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if |target| > total, then r = 0.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_4 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        |target.val| > numsTotal nums → r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          |target.val| > numsTotal nums → r.val = 0) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if target - total is odd, then r = 0.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_5 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        Odd (target.val - numsTotal nums) → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          Odd (target.val - numsTotal nums) → r.val = 0) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if target = total or target = -total, then r = 2^z.
    Preconditions: Let n = len(nums), total = sum_{i=0}^{n-1} nums[i], and z = the number of indices i with 0 <= i < n and nums[i] = 0. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_6 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        (target.val = numsTotal nums ∨ target.val = -numsTotal nums) →
          r.val = (2 : ℤ) ^ zeroCount (vals nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          (target.val = numsTotal nums ∨ target.val = -numsTotal nums) →
            r.val = (2 : ℤ) ^ zeroCount (vals nums)) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if nums[i] = 0 for every i with 0 <= i < n, then r = 2^n when target = 0, and r = 0 when target != 0.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_7 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        (∀ x ∈ vals nums, x = 0) →
          ((target.val = 0 → r.val = (2 : ℤ) ^ numsLen nums) ∧
            (target.val ≠ 0 → r.val = 0)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          (∀ x ∈ vals nums, x = 0) →
            ((target.val = 0 → r.val = (2 : ℤ) ^ numsLen nums) ∧
              (target.val ≠ 0 → r.val = 0))) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if n = 1 and x = nums[0], then r = (1 if target = x else 0) + (1 if target = -x else 0).
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. Additionally n = 1. -/
  theorem spec_8 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
      (hn1 : numsLen nums = 1)
      (x : ℤ) (hx : vals nums = [x]) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        r.val = (if target.val = x then (1 : ℤ) else 0) +
          (if target.val = -x then (1 : ℤ) else 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
        (hn1 : numsLen nums = 1)
        (x : ℤ) (hx : vals nums = [x]), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          r.val = (if target.val = x then (1 : ℤ) else 0) +
            (if target.val = -x then (1 : ℤ) else 0)) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r and find_target_sum_ways nums (-target) returns a result r', we have r = r'.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_9 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        Aegis.FindTargetSumWays.find_target_sum_ways nums (i64neg target) = ok r' →
          r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          Aegis.FindTargetSumWays.find_target_sum_ways nums (i64neg target) = ok r' →
            r = r') := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns r and find_target_sum_ways nums' target returns r', we have r' = 2 * r.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. Additionally n <= 19. Let nums' be the slice of length n+1 with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = 0; then nums' and target also satisfy the standing preconditions. -/
  theorem spec_10 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
      (hn19 : numsLen nums ≤ 19)
      (nums' : Slice I64) (hpush : vals nums' = vals nums ++ [0])
      (hlen' : 1 ≤ numsLen nums') (hnlen' : numsLen nums' ≤ 20)
      (hentries' : ∀ x ∈ vals nums', 0 ≤ x ∧ x ≤ 1000)
      (htotal' : 0 ≤ numsTotal nums' ∧ numsTotal nums' ≤ 1000) :
      ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        Aegis.FindTargetSumWays.find_target_sum_ways nums' target = ok r' →
          r'.val = 2 * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
        (hn19 : numsLen nums ≤ 19)
        (nums' : Slice I64) (hpush : vals nums' = vals nums ++ [0])
        (hlen' : 1 ≤ numsLen nums') (hnlen' : numsLen nums' ≤ 20)
        (hentries' : ∀ x ∈ vals nums', 0 ≤ x ∧ x ≤ 1000)
        (htotal' : 0 ≤ numsTotal nums' ∧ numsTotal nums' ≤ 1000), ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          Aegis.FindTargetSumWays.find_target_sum_ways nums' target = ok r' →
            r'.val = 2 * r.val) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, r > 0 if and only if there exists a sign function s: {0,...,n-1} -> {1,-1} such that sum_{i=0}^{n-1} s(i) * nums[i] = target.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_11 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        (0 < r.val ↔ ∃ s : Fin (vals nums).length → Bool,
          signSum (vals nums) s = target.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          (0 < r.val ↔ ∃ s : Fin (vals nums).length → Bool,
            signSum (vals nums) s = target.val)) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if target = 0, then r is even.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_12 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        target.val = 0 → Even r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          target.val = 0 → Even r.val) := by
    sorry

  /-- Under the assumption that each call returns a result, sum_{t=-1000}^{1000} r_t = 2^n.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The array nums satisfies 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; and 0 <= total <= 1000. For each integer t with -1000 <= t <= 1000, let r_t be the result of find_target_sum_ways nums t, assuming that each such call returns a result. -/
  theorem spec_13 (nums : Slice I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (T : ℤ → I64) (hT : ∀ t : ℤ, -1000 ≤ t → t ≤ 1000 → (T t).val = t)
      (r : ℤ → I64)
      (hr : ∀ t : ℤ, -1000 ≤ t → t ≤ 1000 →
        Aegis.FindTargetSumWays.find_target_sum_ways nums (T t) = ok (r t)) :
      (∑ t ∈ targetRange, (r t).val) = (2 : ℤ) ^ numsLen nums := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (T : ℤ → I64) (hT : ∀ t : ℤ, -1000 ≤ t → t ≤ 1000 → (T t).val = t)
        (r : ℤ → I64)
        (hr : ∀ t : ℤ, -1000 ≤ t → t ≤ 1000 →
          Aegis.FindTargetSumWays.find_target_sum_ways nums (T t) = ok (r t)), (∑ t ∈ targetRange, (r t).val) = (2 : ℤ) ^ numsLen nums) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns a result r, if target and total have the same parity and |target| <= total, then r equals the number of subsets S of {0,...,n-1} such that sum_{i in S} nums[i] = (target + total) / 2.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. -/
  theorem spec_14 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000) :
      ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        Even (target.val - numsTotal nums) → |target.val| ≤ numsTotal nums →
          r.val = (subsetCount (vals nums) ((target.val + numsTotal nums) / 2) : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000), ∀ r : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          Even (target.val - numsTotal nums) → |target.val| ≤ numsTotal nums →
            r.val = (subsetCount (vals nums) ((target.val + numsTotal nums) / 2) : ℤ)) := by
    sorry

  /-- Whenever find_target_sum_ways nums target returns r and find_target_sum_ways nums' target' returns r', we have r = r'.
    Preconditions: Let n = len(nums) and total = sum_{i=0}^{n-1} nums[i]. The original inputs satisfy 1 <= n <= 20; for every i with 0 <= i < n, 0 <= nums[i] <= 1000; 0 <= total <= 1000; and -1000 <= target <= 1000. Let k be a positive integer. Let nums' be a slice with len(nums') = n and nums'[i] = k * nums[i] for every i; suppose nums' also satisfies 0 <= nums'[i] <= 1000 for every i and sum(nums') <= 1000, and let target' = k * target with -1000 <= target' <= 1000. -/
  theorem spec_15 (nums : Slice I64) (target : I64)
      (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
      (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
      (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
      (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
      (k : ℤ) (hk : 0 < k)
      (nums' : Slice I64) (hscale : vals nums' = (vals nums).map (fun x => k * x))
      (hentries' : ∀ x ∈ vals nums', 0 ≤ x ∧ x ≤ 1000)
      (htotal' : 0 ≤ numsTotal nums' ∧ numsTotal nums' ≤ 1000)
      (target' : I64) (htarget' : target'.val = k * target.val)
      (htarget'_range : -1000 ≤ target'.val ∧ target'.val ≤ 1000) :
      ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
        Aegis.FindTargetSumWays.find_target_sum_ways nums' target' = ok r' → r = r' := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64) (target : I64)
        (hlen : 1 ≤ numsLen nums) (hnlen : numsLen nums ≤ 20)
        (hentries : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 1000)
        (htotal : 0 ≤ numsTotal nums ∧ numsTotal nums ≤ 1000)
        (htarget : -1000 ≤ target.val ∧ target.val ≤ 1000)
        (k : ℤ) (hk : 0 < k)
        (nums' : Slice I64) (hscale : vals nums' = (vals nums).map (fun x => k * x))
        (hentries' : ∀ x ∈ vals nums', 0 ≤ x ∧ x ≤ 1000)
        (htotal' : 0 ≤ numsTotal nums' ∧ numsTotal nums' ≤ 1000)
        (target' : I64) (htarget' : target'.val = k * target.val)
        (htarget'_range : -1000 ≤ target'.val ∧ target'.val ≤ 1000), ∀ r r' : I64, Aegis.FindTargetSumWays.find_target_sum_ways nums target = ok r →
          Aegis.FindTargetSumWays.find_target_sum_ways nums' target' = ok r' → r = r') := by
    sorry

  end AegisSpec.FindTargetSumWays
