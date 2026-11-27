import Aegis.MissingElement.Code.Funs

/-!
# Specifications of `Aegis.MissingElement.missing_element`

LeetCode problem `missing-element-in-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MissingElement

  def valsOf (nums : Slice Std.I64) : List ℤ := nums.val.map (fun a => a.val)

  def occursIn (nums : Slice Std.I64) (x : ℤ) : Prop := x ∈ valsOf nums

  def atIdx (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    match nums.val[i]? with
    | some v => v.val
    | none => 0

  def lastOf (nums : Slice Std.I64) : ℤ := atIdx nums (nums.val.length - 1)

  def countNotOcc (nums : Slice Std.I64) (a b : ℤ) : ℕ :=
    ((List.range (b + 1 - a).toNat).filter (fun t => decide (a + (t : ℤ) ∉ valsOf nums))).length

  def countLessThan (nums : Slice Std.I64) (r : ℤ) : ℕ :=
    ((valsOf nums).filter (fun v => decide (v < r))).length

  /-- The function returns a result r, and r is the k-th smallest integer x such that x > nums[0] and x is not equal to nums[i] for every i with 0 <= i < len(nums). Equivalently: r > nums[0]; r is not equal to any nums[i]; and the number of integers x with nums[0] < x < r and x not equal to nums[i] for all i with 0 <= i < len(nums) is exactly k - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∃ r, Aegis.MissingElement.missing_element nums k = ok r ∧
        atIdx nums 0 < r ∧ ¬ occursIn nums r ∧
        (countNotOcc nums (atIdx nums 0 + 1) (r - 1) : ℤ) = k.val - 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∃ r, Aegis.MissingElement.missing_element nums k = ok r ∧
          atIdx nums 0 < r ∧ ¬ occursIn nums r ∧
          (countNotOcc nums (atIdx nums 0 + 1) (r - 1) : ℤ) = k.val - 1) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail because of integer overflow, out-of-bounds indexing, or a panic.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∃ r, Aegis.MissingElement.missing_element nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∃ r, Aegis.MissingElement.missing_element nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= nums[0] + k.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        atIdx nums 0 + k.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          atIdx nums 0 + k.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= nums[0] + k + len(nums) - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        r.val ≤ atIdx nums 0 + k.val + (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          r.val ≤ atIdx nums 0 + k.val + (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r is not equal to nums[i].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        ∀ (i : ℕ), i < nums.val.length → atIdx nums i ≠ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          ∀ (i : ℕ), i < nums.val.length → atIdx nums i ≠ r.val) := by
    sorry

  /-- Whenever the function returns a result r, the number of integers x such that nums[0] < x <= r and x is not equal to nums[i] for all i with 0 <= i < len(nums) is exactly k.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        (countNotOcc nums (atIdx nums 0 + 1) r.val : ℤ) = k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          (countNotOcc nums (atIdx nums 0 + 1) r.val : ℤ) = k.val) := by
    sorry

  /-- Whenever the function returns a result r, let j be the number of indices i with 0 <= i < len(nums) and nums[i] < r. Then r = nums[0] + k + j - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        r.val = atIdx nums 0 + k.val + (countLessThan nums r.val : ℤ) - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          r.val = atIdx nums 0 + k.val + (countLessThan nums r.val : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r and len(nums) = 1, r = nums[0] + k.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        nums.val.length = 1 → r.val = atIdx nums 0 + k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          nums.val.length = 1 → r.val = atIdx nums 0 + k.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) >= 2 and k <= nums[1] - nums[0] - 1, then r = nums[0] + k.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        2 ≤ nums.val.length →
        k.val ≤ atIdx nums 1 - atIdx nums 0 - 1 → r.val = atIdx nums 0 + k.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          2 ≤ nums.val.length →
          k.val ≤ atIdx nums 1 - atIdx nums 0 - 1 → r.val = atIdx nums 0 + k.val) := by
    sorry

  /-- Whenever the function returns a result r, if k > nums[len(nums)-1] - nums[0] - len(nums) + 1, then r = nums[len(nums)-1] + k - (nums[len(nums)-1] - nums[0] - len(nums) + 1). Equivalently, under this condition, r = nums[0] + k + len(nums) - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        k.val > lastOf nums - atIdx nums 0 - (nums.val.length : ℤ) + 1 →
        r.val = lastOf nums + k.val - (lastOf nums - atIdx nums 0 - (nums.val.length : ℤ) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          k.val > lastOf nums - atIdx nums 0 - (nums.val.length : ℤ) + 1 →
          r.val = lastOf nums + k.val - (lastOf nums - atIdx nums 0 - (nums.val.length : ℤ) + 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer y with nums[0] < y < r, the number of integers x such that nums[0] < x <= y and x is not equal to nums[i] for all i with 0 <= i < len(nums) is at most k - 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        ∀ y : ℤ, atIdx nums 0 < y → y < r.val →
          (countNotOcc nums (atIdx nums 0 + 1) y : ℤ) ≤ k.val - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          ∀ y : ℤ, atIdx nums 0 < y → y < r.val →
            (countNotOcc nums (atIdx nums 0 + 1) y : ℤ) ≤ k.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index j with 0 <= j < len(nums) such that either j < len(nums)-1 and nums[j] < r < nums[j+1], or j = len(nums)-1 and r > nums[j].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 50000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000; for every i and j with 0 <= i < j < len(nums), nums[i] < nums[j]; and 1 <= k <= 100000000. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
      (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
      (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
      (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000) :
      ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
        ∃ (j : ℕ), j < nums.val.length ∧
          ((j + 1 < nums.val.length ∧ atIdx nums j < r.val ∧ r.val < atIdx nums (j + 1)) ∨
            (j = nums.val.length - 1 ∧ atIdx nums j < r.val)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ nums.val.length) (hlen' : nums.val.length ≤ 50000)
        (hbnd : ∀ (i : ℕ), i < nums.val.length → 1 ≤ atIdx nums i ∧ atIdx nums i ≤ 10000000)
        (hsorted : ∀ (i j : ℕ), i < j → j < nums.val.length → atIdx nums i < atIdx nums j)
        (hk : 1 ≤ k.val) (hk' : k.val ≤ 100000000), ∀ (r : Std.I64), Aegis.MissingElement.missing_element nums k = ok r →
          ∃ (j : ℕ), j < nums.val.length ∧
            ((j + 1 < nums.val.length ∧ atIdx nums j < r.val ∧ r.val < atIdx nums (j + 1)) ∨
              (j = nums.val.length - 1 ∧ atIdx nums j < r.val))) := by
    sorry

  end AegisSpec.MissingElement
