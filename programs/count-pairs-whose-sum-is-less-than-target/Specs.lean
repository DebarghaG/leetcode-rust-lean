import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-pairs-whose-sum-is-less-than-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountPairs

  namespace AegisSpec.CountPairs

  def entry (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    ((nums.val[i]?).map (fun x => x.val)).getD 0

  def pairCount (nums : Slice Std.I64) (p : ℤ → ℤ → Prop) [DecidableRel p] : ℕ :=
    (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
      (fun q : ℕ × ℕ => q.1 < q.2 ∧ p (entry nums q.1) (entry nums q.2))).card

  def ltCount (nums : Slice Std.I64) (target : Std.I64) : ℕ :=
    pairCount nums (fun a b => a + b < target.val)

  def geCount (nums : Slice Std.I64) (target : Std.I64) : ℕ :=
    pairCount nums (fun a b => target.val ≤ a + b)

  def neCount (nums : Slice Std.I64) (target : Std.I64) : ℕ :=
    (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
      (fun q : ℕ × ℕ => q.1 ≠ q.2 ∧
        entry nums q.1 + entry nums q.2 < target.val)).card

  def ci (nums : Slice Std.I64) (target : Std.I64) (i : ℕ) : ℕ :=
    ((Finset.range nums.val.length).filter
      (fun j => i < j ∧ entry nums i + entry nums j < target.val)).card

  def sumCi (nums : Slice Std.I64) (target : Std.I64) : ℕ :=
    ∑ i ∈ Finset.range nums.val.length, ci nums target i

  def IsPermutation (nums nums' : Slice Std.I64) : Prop :=
    nums'.val.length = nums.val.length ∧
      ∃ π : ℕ → ℕ,
        (∀ k, k < nums.val.length → π k < nums.val.length) ∧
        (∀ m, m < nums.val.length → ∃ k, k < nums.val.length ∧ π k = m) ∧
        (∀ k, k < nums.val.length → entry nums' k = entry nums (π k))

  /-- The function returns a result r, and r equals the number of pairs (i, j) of indices satisfying 0 <= i < j < n and nums[i] + nums[j] < target, where nums[i] + nums[j] is the mathematical sum of the two integers (which lies in [-100, 100] and hence does not overflow i64).
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∃ r, count_pairs nums target = ok r ∧ r.val = (ltCount nums target : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∃ r, count_pairs nums target = ok r ∧ r.val = (ltCount nums target : ℤ)) := by
    sorry

  /-- The function returns a result r (that is, it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∃ r, count_pairs nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∃ r, count_pairs nums target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n * (n - 1) / 2.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r →
        0 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r →
          0 ≤ r.val ∧ r.val ≤ ((n * (n - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: len(nums) = n = 1; -50 <= nums[0] <= 50; and -50 <= target <= 50. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : n = 1)
      (hentry : -50 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∃ r, count_pairs nums target = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : n = 1)
        (hentry : -50 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∃ r, count_pairs nums target = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns r = 1 if nums[0] + nums[1] < target, and r = 0 otherwise.
    Preconditions: len(nums) = n = 2; -50 <= nums[0] <= 50; -50 <= nums[1] <= 50; and -50 <= target <= 50. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn2 : n = 2)
      (hentry0 : -50 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
      (hentry1 : -50 ≤ entry nums 1 ∧ entry nums 1 ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∃ r, count_pairs nums target = ok r ∧
        r.val = (if entry nums 0 + entry nums 1 < target.val then 1 else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn2 : n = 2)
        (hentry0 : -50 ≤ entry nums 0 ∧ entry nums 0 ≤ 50)
        (hentry1 : -50 ≤ entry nums 1 ∧ entry nums 1 ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∃ r, count_pairs nums target = ok r ∧
          r.val = (if entry nums 0 + entry nums 1 < target.val then 1 else 0)) := by
    sorry

  /-- Whenever the function returns r on (nums, target) and r' on (nums', target), we have r = r'.
    Preconditions: len(nums) = n and len(nums') = n with 1 <= n <= 50; every entry of nums and nums' lies in [-50, 50]; -50 <= target <= 50; and nums' is a permutation of nums, i.e., there exists a bijection π from {0, ..., n-1} to itself such that nums'[k] = nums[π(k)] for every k with 0 <= k < n. -/
  theorem spec_6 (nums nums' : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn' : nums'.val.length = n)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (hentries' : ∀ i, i < n → -50 ≤ entry nums' i ∧ entry nums' i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50)
      (hperm : IsPermutation nums nums') :
      ∀ r r', count_pairs nums target = ok r → count_pairs nums' target = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn' : nums'.val.length = n)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (hentries' : ∀ i, i < n → -50 ≤ entry nums' i ∧ entry nums' i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50)
        (hperm : IsPermutation nums nums'), ∀ r r', count_pairs nums target = ok r → count_pairs nums' target = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r1 on (nums, target1) and r2 on (nums, target2), we have r1 <= r2.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target1 <= target2 <= 50. -/
  theorem spec_7 (nums : Slice Std.I64) (target1 target2 : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htargets : -50 ≤ target1.val ∧ target1.val ≤ target2.val ∧ target2.val ≤ 50) :
      ∀ r1 r2, count_pairs nums target1 = ok r1 → count_pairs nums target2 = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target1 target2 : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htargets : -50 ≤ target1.val ∧ target1.val ≤ target2.val ∧ target2.val ≤ 50), ∀ r1 r2, count_pairs nums target1 = ok r1 → count_pairs nums target2 = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r, let q = |{(i, j) : 0 <= i < j < n and nums[i] + nums[j] >= target}|. Then r + q = n * (n - 1) / 2.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r →
        r.val + (geCount nums target : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r →
          r.val + (geCount nums target : ℤ) = ((n * (n - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r, r > 0 if and only if there exist indices i, j with 0 <= i < j < n and nums[i] + nums[j] < target.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_9 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r →
        (0 < r.val ↔ ∃ i j : ℕ, i < j ∧ j < n ∧ entry nums i + entry nums j < target.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r →
          (0 < r.val ↔ ∃ i j : ℕ, i < j ∧ j < n ∧ entry nums i + entry nums j < target.val)) := by
    sorry

  /-- Whenever the function returns r, r = n * (n - 1) / 2 if 2*v < target, and r = 0 otherwise (that is, if 2*v >= target).
    Preconditions: len(nums) = n with 1 <= n <= 50; there exists an integer v with -50 <= v <= 50 such that nums[i] = v for every i with 0 <= i < n; and -50 <= target <= 50. -/
  theorem spec_10 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ) (v : ℤ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hv : -50 ≤ v ∧ v ≤ 50)
      (hconst : ∀ i, i < n → entry nums i = v)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r →
        r.val = (if 2 * v < target.val then ((n * (n - 1) / 2 : ℕ) : ℤ) else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ) (v : ℤ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hv : -50 ≤ v ∧ v ≤ 50)
        (hconst : ∀ i, i < n → entry nums i = v)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r →
          r.val = (if 2 * v < target.val then ((n * (n - 1) / 2 : ℕ) : ℤ) else 0)) := by
    sorry

  /-- The function returns r = n * (n - 1) / 2.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 0; and 0 < target <= 50. -/
  theorem spec_11 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 0)
      (htarget : 0 < target.val ∧ target.val ≤ 50) :
      ∃ r, count_pairs nums target = ok r ∧ r.val = ((n * (n - 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 0)
        (htarget : 0 < target.val ∧ target.val ≤ 50), ∃ r, count_pairs nums target = ok r ∧ r.val = ((n * (n - 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r, let s = |{(i, j) : 0 <= i < n, 0 <= j < n, i != j, and nums[i] + nums[j] < target}|. Then s = 2*r.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r → (neCount nums target : ℤ) = 2 * r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r → (neCount nums target : ℤ) = 2 * r.val) := by
    sorry

  /-- Whenever the function returns r, for each i with 0 <= i < n define c_i = |{j : i < j < n and nums[i] + nums[j] < target}|. Then r = sum_{i=0}^{n-1} c_i.
    Preconditions: len(nums) = n with 1 <= n <= 50; for every i with 0 <= i < n, -50 <= nums[i] <= 50; and -50 <= target <= 50. -/
  theorem spec_13 (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
      (htarget : -50 ≤ target.val ∧ target.val ≤ 50) :
      ∀ r, count_pairs nums target = ok r → r.val = (sumCi nums target : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : ℕ)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hentries : ∀ i, i < n → -50 ≤ entry nums i ∧ entry nums i ≤ 50)
        (htarget : -50 ≤ target.val ∧ target.val ≤ 50), ∀ r, count_pairs nums target = ok r → r.val = (sumCi nums target : ℤ)) := by
    sorry

  end AegisSpec.CountPairs
