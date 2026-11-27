import Aegis.ThreeSumClosest.Code.Funs

/-!
# Specifications of `Aegis.ThreeSumClosest.three_sum_closest`

LeetCode problem `3sum-closest`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ThreeSumClosest

  def nth (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def IsThreeSum (nums : Slice Std.I64) (s : Int) : Prop :=
    ∃ i j k : Nat,
      i < j ∧ j < k ∧ k < nums.val.length ∧
        nth nums i + nth nums j + nth nums k = s

  def IsClosest (nums : Slice Std.I64) (target : Int) (s : Int) : Prop :=
    IsThreeSum nums s ∧
      ∀ t : Int, IsThreeSum nums t → |s - target| ≤ |t - target|

  def UniqueClosest (nums : Slice Std.I64) (target : Int) : Prop :=
    ∃! s : Int, IsClosest nums target s

  def countOf (nums : Slice Std.I64) (v : Int) : Nat :=
    nums.val.countP (fun x => decide (x.val = v))

  /-- The function returns a result r (it does not fail), and r = nums[i]+nums[j]+nums[k] for some 0 <= i < j < k < len(nums), and for every 0 <= i < j < k < len(nums), |r - target| <= |(nums[i]+nums[j]+nums[k]) - target|.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; -10000 <= target <= 10000; and there is exactly one integer s of the form nums[i]+nums[j]+nums[k] with 0 <= i < j < k < len(nums) that minimizes |s - target| among all such three-element sums. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hunique : UniqueClosest nums target.val) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        (∃ i j k : Nat,
          i < j ∧ j < k ∧ k < nums.val.length ∧
            r.val = nth nums i + nth nums j + nth nums k) ∧
        (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          |r.val - target.val| ≤
            |nth nums i + nth nums j + nth nums k - target.val|) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hunique : UniqueClosest nums target.val), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          (∃ i j k : Nat,
            i < j ∧ j < k ∧ k < nums.val.length ∧
              r.val = nth nums i + nth nums j + nth nums k) ∧
          (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
            |r.val - target.val| ≤
              |nth nums i + nth nums j + nth nums k - target.val|)) := by
    sorry

  /-- The function returns a result r; it does not fail because of arithmetic overflow, out-of-bounds access, or a panic.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; and -10000 <= target <= 10000. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.ThreeSumClosest.three_sum_closest nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64, Aegis.ThreeSumClosest.three_sum_closest nums target = ok r) := by
    sorry

  /-- The function returns a result r, and there exist indices i, j, k with 0 <= i < j < k < len(nums) such that r = nums[i]+nums[j]+nums[k].
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; and -10000 <= target <= 10000. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        ∃ i j k : Nat,
          i < j ∧ j < k ∧ k < nums.val.length ∧
            r.val = nth nums i + nth nums j + nth nums k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          ∃ i j k : Nat,
            i < j ∧ j < k ∧ k < nums.val.length ∧
              r.val = nth nums i + nth nums j + nth nums k) := by
    sorry

  /-- The function returns a result r, and for every i, j, k with 0 <= i < j < k < len(nums), |r - target| <= |(nums[i]+nums[j]+nums[k]) - target|.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; and -10000 <= target <= 10000. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          |r.val - target.val| ≤
            |nth nums i + nth nums j + nth nums k - target.val| := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
            |r.val - target.val| ≤
              |nth nums i + nth nums j + nth nums k - target.val|) := by
    sorry

  /-- The function returns a result r, and -3000 <= r <= 3000.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; and -10000 <= target <= 10000. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        -3000 ≤ r.val ∧ r.val ≤ 3000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          -3000 ≤ r.val ∧ r.val ≤ 3000) := by
    sorry

  /-- The function returns a result r, and r = target.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; -10000 <= target <= 10000; and there exist indices a, b, c with 0 <= a < b < c < len(nums) such that nums[a]+nums[b]+nums[c] = target. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hexact : ∃ a b c : Nat,
        a < b ∧ b < c ∧ c < nums.val.length ∧
          nth nums a + nth nums b + nth nums c = target.val) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        r.val = target.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hexact : ∃ a b c : Nat,
          a < b ∧ b < c ∧ c < nums.val.length ∧
            nth nums a + nth nums b + nth nums c = target.val), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          r.val = target.val) := by
    sorry

  /-- The function returns a result r, and r = nums[0]+nums[1]+nums[2].
    Preconditions: len(nums) = 3; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; and -10000 <= target <= 10000. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
      (hlen : nums.val.length = 3)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        r.val = nth nums 0 + nth nums 1 + nth nums 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen : nums.val.length = 3)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          r.val = nth nums 0 + nth nums 1 + nth nums 2) := by
    sorry

  /-- The function returns a result r, and r = 3*c.
    Preconditions: len(nums) is between 3 and 500; there exists an integer c with -1000 <= c <= 1000 such that for every i with 0 <= i < len(nums), nums[i] = c; and -10000 <= target <= 10000. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64) (c : Int)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hc_lo : -1000 ≤ c) (hc_hi : c ≤ 1000)
      (hconst : ∀ (i : Nat), i < nums.val.length → nth nums i = c)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        r.val = 3 * c := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (c : Int)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hc_lo : -1000 ≤ c) (hc_hi : c ≤ 1000)
        (hconst : ∀ (i : Nat), i < nums.val.length → nth nums i = c)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          r.val = 3 * c) := by
    sorry

  /-- Let r be the result of the function on (nums, target) and r' the result on (xs, target). The function returns both r and r', and r = r'.
    Preconditions: nums and target satisfy the base constraints: len(nums) is between 3 and 500, every nums[i] is in [-1000,1000], and -10000 <= target <= 10000; nums has a unique closest three-element sum; xs is a slice with len(xs) = len(nums) and, for every integer v, the number of indices i with nums[i] = v equals the number of indices i with xs[i] = v, so xs is a permutation of nums. -/
  theorem spec_9 (nums xs : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hunique : UniqueClosest nums target.val)
      (hlen_xs : xs.val.length = nums.val.length)
      (hperm : ∀ (v : Int), countOf nums v = countOf xs v) :
      ∃ r r' : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        Aegis.ThreeSumClosest.three_sum_closest xs target = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums xs : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hunique : UniqueClosest nums target.val)
        (hlen_xs : xs.val.length = nums.val.length)
        (hperm : ∀ (v : Int), countOf nums v = countOf xs v), ∃ r r' : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          Aegis.ThreeSumClosest.three_sum_closest xs target = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- Let r be the result of the function on (nums, target) and r' the result on (xs, target+3*c). The function returns both r and r', and r' = r + 3*c.
    Preconditions: nums and target satisfy the base constraints: len(nums) is between 3 and 500, every nums[i] is in [-1000,1000], and -10000 <= target <= 10000; nums has a unique closest three-element sum; c is an integer; xs is a slice with len(xs) = len(nums) and xs[i] = nums[i]+c for every i; every xs[i] is in [-1000,1000]; and -10000 <= target+3*c <= 10000. -/
  theorem spec_10 (nums xs : Slice Std.I64) (target target' : Std.I64) (c : Int)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hunique : UniqueClosest nums target.val)
      (hlen_xs : xs.val.length = nums.val.length)
      (hshift : ∀ (i : Nat), i < xs.val.length → nth xs i = nth nums i + c)
      (hxs_val : ∀ (i : Nat), i < xs.val.length →
        -1000 ≤ nth xs i ∧ nth xs i ≤ 1000)
      (htarget'_eq : target'.val = target.val + 3 * c)
      (htarget'_lo : -10000 ≤ target.val + 3 * c)
      (htarget'_hi : target.val + 3 * c ≤ 10000) :
      ∃ r r' : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        Aegis.ThreeSumClosest.three_sum_closest xs target' = ok r' ∧
        r'.val = r.val + 3 * c := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums xs : Slice Std.I64) (target target' : Std.I64) (c : Int)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hunique : UniqueClosest nums target.val)
        (hlen_xs : xs.val.length = nums.val.length)
        (hshift : ∀ (i : Nat), i < xs.val.length → nth xs i = nth nums i + c)
        (hxs_val : ∀ (i : Nat), i < xs.val.length →
          -1000 ≤ nth xs i ∧ nth xs i ≤ 1000)
        (htarget'_eq : target'.val = target.val + 3 * c)
        (htarget'_lo : -10000 ≤ target.val + 3 * c)
        (htarget'_hi : target.val + 3 * c ≤ 10000), ∃ r r' : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          Aegis.ThreeSumClosest.three_sum_closest xs target' = ok r' ∧
          r'.val = r.val + 3 * c) := by
    sorry

  /-- Let r be the result of the function on (nums, target) and r' the result on (xs, -target). The function returns both r and r', and r' = -r.
    Preconditions: nums and target satisfy the base constraints: len(nums) is between 3 and 500, every nums[i] is in [-1000,1000], and -10000 <= target <= 10000; nums has a unique closest three-element sum; xs is a slice with len(xs) = len(nums) and xs[i] = -nums[i] for every i. -/
  theorem spec_11 (nums xs : Slice Std.I64) (target target' : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hunique : UniqueClosest nums target.val)
      (hlen_xs : xs.val.length = nums.val.length)
      (hneg : ∀ (i : Nat), i < xs.val.length → nth xs i = -nth nums i)
      (htarget'_eq : target'.val = -target.val) :
      ∃ r r' : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        Aegis.ThreeSumClosest.three_sum_closest xs target' = ok r' ∧
        r'.val = -r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums xs : Slice Std.I64) (target target' : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hunique : UniqueClosest nums target.val)
        (hlen_xs : xs.val.length = nums.val.length)
        (hneg : ∀ (i : Nat), i < xs.val.length → nth xs i = -nth nums i)
        (htarget'_eq : target'.val = -target.val), ∃ r r' : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          Aegis.ThreeSumClosest.three_sum_closest xs target' = ok r' ∧
          r'.val = -r.val) := by
    sorry

  /-- The function returns a result r, and there exist indices a, b, c with 0 <= a < b < c < len(nums) such that r = nums[a]+nums[b]+nums[c], and for every i, j, k with 0 <= i < j < k < len(nums), nums[i]+nums[j]+nums[k] <= r.
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; -10000 <= target <= 10000; and for every i, j, k with 0 <= i < j < k < len(nums), nums[i]+nums[j]+nums[k] <= target. -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hle : ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
        nth nums i + nth nums j + nth nums k ≤ target.val) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        (∃ a b c : Nat,
          a < b ∧ b < c ∧ c < nums.val.length ∧
            r.val = nth nums a + nth nums b + nth nums c) ∧
        (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          nth nums i + nth nums j + nth nums k ≤ r.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hle : ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          nth nums i + nth nums j + nth nums k ≤ target.val), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          (∃ a b c : Nat,
            a < b ∧ b < c ∧ c < nums.val.length ∧
              r.val = nth nums a + nth nums b + nth nums c) ∧
          (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
            nth nums i + nth nums j + nth nums k ≤ r.val)) := by
    sorry

  /-- The function returns a result r, and there exist indices a, b, c with 0 <= a < b < c < len(nums) such that r = nums[a]+nums[b]+nums[c], and for every i, j, k with 0 <= i < j < k < len(nums), r <= nums[i]+nums[j]+nums[k].
    Preconditions: len(nums) is between 3 and 500; for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000; -10000 <= target <= 10000; and for every i, j, k with 0 <= i < j < k < len(nums), target <= nums[i]+nums[j]+nums[k]. -/
  theorem spec_13 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
      (hge : ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
        target.val ≤ nth nums i + nth nums j + nth nums k) :
      ∃ r : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
        (∃ a b c : Nat,
          a < b ∧ b < c ∧ c < nums.val.length ∧
            r.val = nth nums a + nth nums b + nth nums c) ∧
        (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          r.val ≤ nth nums i + nth nums j + nth nums k) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget_lo : -10000 ≤ target.val) (htarget_hi : target.val ≤ 10000)
        (hge : ∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
          target.val ≤ nth nums i + nth nums j + nth nums k), ∃ r : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target = ok r ∧
          (∃ a b c : Nat,
            a < b ∧ b < c ∧ c < nums.val.length ∧
              r.val = nth nums a + nth nums b + nth nums c) ∧
          (∀ (i j k : Nat), i < j → j < k → k < nums.val.length →
            r.val ≤ nth nums i + nth nums j + nth nums k)) := by
    sorry

  /-- Let r1 be the result of the function on (nums, target1) and r2 the result on (nums, target2). The function returns both r1 and r2, and r1 <= r2.
    Preconditions: nums satisfies len(nums) between 3 and 500 and every nums[i] in [-1000,1000]; target1 and target2 satisfy -10000 <= target1 <= target2 <= 10000; and for each of target1 and target2, the set of three-element sums has a unique element minimizing its distance to that target. -/
  theorem spec_14 (nums : Slice Std.I64) (target1 target2 : Std.I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
      (hval : ∀ (i : Nat), i < nums.val.length →
        -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
      (htarget1_lo : -10000 ≤ target1.val) (hmono : target1.val ≤ target2.val)
      (htarget2_hi : target2.val ≤ 10000)
      (hunique1 : UniqueClosest nums target1.val)
      (hunique2 : UniqueClosest nums target2.val) :
      ∃ r1 r2 : Std.I64,
        Aegis.ThreeSumClosest.three_sum_closest nums target1 = ok r1 ∧
        Aegis.ThreeSumClosest.three_sum_closest nums target2 = ok r2 ∧
        r1.val ≤ r2.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (target1 target2 : Std.I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 500)
        (hval : ∀ (i : Nat), i < nums.val.length →
          -1000 ≤ nth nums i ∧ nth nums i ≤ 1000)
        (htarget1_lo : -10000 ≤ target1.val) (hmono : target1.val ≤ target2.val)
        (htarget2_hi : target2.val ≤ 10000)
        (hunique1 : UniqueClosest nums target1.val)
        (hunique2 : UniqueClosest nums target2.val), ∃ r1 r2 : Std.I64,
          Aegis.ThreeSumClosest.three_sum_closest nums target1 = ok r1 ∧
          Aegis.ThreeSumClosest.three_sum_closest nums target2 = ok r2 ∧
          r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.ThreeSumClosest
