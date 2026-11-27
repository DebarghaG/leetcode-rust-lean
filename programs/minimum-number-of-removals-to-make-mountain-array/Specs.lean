import Aegis.MinimumMountainRemovals.Code.Funs

/-!
# Specifications of `Aegis.MinimumMountainRemovals.minimum_mountain_removals`

LeetCode problem `minimum-number-of-removals-to-make-mountain-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumMountainRemovals

  namespace AegisSpec.MinimumMountainRemovals

  def Contents (nums : Slice Std.I64) : List Int := nums.val.map (fun v => v.val)

  def StrictlyIncreasing (l : List Int) : Prop := l.Pairwise (· < ·)

  def StrictlyDecreasing (l : List Int) : Prop := l.Pairwise (· > ·)

  def IsMountain (l : List Int) : Prop :=
    ∃ p : Nat, 0 < p ∧ p + 1 < l.length ∧ StrictlyIncreasing (l.take (p + 1)) ∧
      StrictlyDecreasing (l.drop p)

  def IsIndexSeq (nums : List Int) (js : List Nat) : Prop :=
    js.Pairwise (· < ·) ∧ ∀ j ∈ js, j < nums.length

  def MountainSubseq (nums : List Int) (js : List Nat) : Prop :=
    IsIndexSeq nums js ∧ 3 ≤ js.length ∧ IsMountain (js.filterMap (fun j => nums[j]?))

  def HasMountainSubseq (nums : List Int) (k : Nat) : Prop :=
    ∃ js : List Nat, js.length = k ∧ MountainSubseq nums js

  def IsMaxMountainLen (nums : List Int) (L : Nat) : Prop :=
    HasMountainSubseq nums L ∧ ∀ k : Nat, HasMountainSubseq nums k → k ≤ L

  def IncEnd (nums : List Int) (p k : Nat) : Prop :=
    ∃ js : List Nat, IsIndexSeq nums js ∧ js.getLast? = some p ∧ js.length = k ∧
      StrictlyIncreasing (js.filterMap (fun j => nums[j]?))

  def MaxIncEnd (nums : List Int) (p k : Nat) : Prop :=
    IncEnd nums p k ∧ ∀ k' : Nat, IncEnd nums p k' → k' ≤ k

  def DecStart (nums : List Int) (p k : Nat) : Prop :=
    ∃ js : List Nat, IsIndexSeq nums js ∧ js.head? = some p ∧ js.length = k ∧
      StrictlyDecreasing (js.filterMap (fun j => nums[j]?))

  def MaxDecStart (nums : List Int) (p k : Nat) : Prop :=
    DecStart nums p k ∧ ∀ k' : Nat, DecStart nums p k' → k' ≤ k

  def IsMaxPeakLen (nums : List Int) (M : Nat) : Prop :=
    (∃ i a b : Nat, 0 < i ∧ i + 1 < nums.length ∧ MaxIncEnd nums i a ∧
      MaxDecStart nums i b ∧ 2 ≤ a ∧ 2 ≤ b ∧ M = a + b - 1) ∧
    (∀ i a b : Nat, 0 < i → i + 1 < nums.length → MaxIncEnd nums i a →
      MaxDecStart nums i b → 2 ≤ a → 2 ≤ b → a + b - 1 ≤ M)

  def Precondition (nums : Slice Std.I64) : Prop :=
    3 ≤ nums.val.length ∧ nums.val.length ≤ 1000 ∧
    (∀ v ∈ nums.val, 1 ≤ v.val ∧ v.val ≤ 10 ^ 9) ∧
    (∃ js : List Nat, MountainSubseq (Contents nums) js)

  /-- The function returns a result r, and r = len(nums) - L, where L is the maximum k for which there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. Such a sequence nums[j_0],...,nums[j_{k-1}] is called a mountain subsequence of nums.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_1 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        ∃ L : Nat, IsMaxMountainLen (Contents nums) L ∧
          r.val = (nums.val.length : Int) - (L : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          ∃ L : Nat, IsMaxMountainLen (Contents nums) L ∧
            r.val = (nums.val.length : Int) - (L : Int)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access any index outside nums.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_2 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= len(nums) - 3.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_3 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) - 3 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) - 3) := by
    sorry

  /-- The function returns a result r, and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k = len(nums) - r, k >= 3, and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. In other words, nums has a mountain subsequence of length len(nums)-r.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_4 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        ∃ js : List Nat, MountainSubseq (Contents nums) js ∧ 3 ≤ js.length ∧
          (js.length : Int) = (nums.val.length : Int) - r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          ∃ js : List Nat, MountainSubseq (Contents nums) js ∧ 3 ≤ js.length ∧
            (js.length : Int) = (nums.val.length : Int) - r.val) := by
    sorry

  /-- The function returns a result r, and for every choice of indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, satisfying nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}], we have k <= len(nums) - r. In other words, no mountain subsequence of nums is longer than len(nums)-r.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_5 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        ∀ js : List Nat, MountainSubseq (Contents nums) js →
          (js.length : Int) ≤ (nums.val.length : Int) - r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          ∀ js : List Nat, MountainSubseq (Contents nums) js →
            (js.length : Int) ≤ (nums.val.length : Int) - r.val) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if nums itself is a mountain array, i.e., len(nums) >= 3 and there exists p with 0 < p < len(nums)-1 such that nums[0] < nums[1] < ... < nums[p] > nums[p+1] > ... > nums[len(nums)-1].
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_6 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        (r.val = 0 ↔ IsMountain (Contents nums)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          (r.val = 0 ↔ IsMountain (Contents nums))) := by
    sorry

  /-- The function returns a result r, and there exists an index p with 0 < p < len(nums)-1 for which the following holds. Let incEnd(p) be the maximum length of a strictly increasing subsequence of nums[0..p] that ends at index p (i.e., whose last element is nums[p]), and let decStart(p) be the maximum length of a strictly decreasing subsequence of nums[p..len(nums)-1] that starts at index p (i.e., whose first element is nums[p]). Then incEnd(p) >= 2, decStart(p) >= 2, and incEnd(p) + decStart(p) - 1 = len(nums) - r.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_7 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        ∃ p a b : Nat, 0 < p ∧ p + 1 < nums.val.length ∧
          MaxIncEnd (Contents nums) p a ∧ MaxDecStart (Contents nums) p b ∧
          2 ≤ a ∧ 2 ≤ b ∧
          (a : Int) + (b : Int) - 1 = (nums.val.length : Int) - r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          ∃ p a b : Nat, 0 < p ∧ p + 1 < nums.val.length ∧
            MaxIncEnd (Contents nums) p a ∧ MaxDecStart (Contents nums) p b ∧
            2 ≤ a ∧ 2 ≤ b ∧
            (a : Int) + (b : Int) - 1 = (nums.val.length : Int) - r.val) := by
    sorry

  /-- The function returns a result r, and r = len(nums) - M, where M is the maximum, over all indices i with 0 < i < len(nums)-1 and with incEnd(i) >= 2 and decStart(i) >= 2, of incEnd(i) + decStart(i) - 1. Here incEnd(i) is the maximum length of a strictly increasing subsequence of nums[0..i] whose last index is i, and decStart(i) is the maximum length of a strictly decreasing subsequence of nums[i..len(nums)-1] whose first index is i. The maximum is taken over a nonempty set by the preconditions.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_8 (nums : Slice Std.I64) (h : Precondition nums) :
      ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
        ∃ M : Nat, IsMaxPeakLen (Contents nums) M ∧
          r.val = (nums.val.length : Int) - (M : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∃ r : Std.I64, minimum_mountain_removals nums = ok r ∧
          ∃ M : Nat, IsMaxPeakLen (Contents nums) M ∧
            r.val = (nums.val.length : Int) - (M : Int)) := by
    sorry

  /-- If the function returns r on nums and r' on nums', then r = r'.
    Preconditions: Take any two slices nums and nums' of the same length such that both satisfy the common preconditions: 3 <= len <= 1000; every value is between 1 and 10^9; and each has a mountain subsequence of length at least 3. Also assume there exists a strictly increasing function f from integers to integers such that nums'[i] = f(nums[i]) for every 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64) (h : Precondition nums)
      (h' : Precondition nums') (hlen : nums.val.length = nums'.val.length)
      (hf : ∃ f : Int → Int, (∀ a b : Int, a < b → f a < f b) ∧
        ∀ i : Nat, i < nums.val.length →
          ∃ a b : Std.I64, nums.val[i]? = some a ∧ nums'.val[i]? = some b ∧ b.val = f a.val) :
      ∀ r r' : Std.I64, minimum_mountain_removals nums = ok r →
        minimum_mountain_removals nums' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (h : Precondition nums)
        (h' : Precondition nums') (hlen : nums.val.length = nums'.val.length)
        (hf : ∃ f : Int → Int, (∀ a b : Int, a < b → f a < f b) ∧
          ∀ i : Nat, i < nums.val.length →
            ∃ a b : Std.I64, nums.val[i]? = some a ∧ nums'.val[i]? = some b ∧ b.val = f a.val), ∀ r r' : Std.I64, minimum_mountain_removals nums = ok r →
          minimum_mountain_removals nums' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on nums, the following holds. For every index d with 0 <= d < len(nums) such that there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k = len(nums)-r, k >= 3, none of the j_t equals d, and some p, 0 < p < k-1, satisfying nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}], let nums' be the slice obtained from nums by deleting the element at index d. Then nums' satisfies the length and value constraints and still has a mountain subsequence of length at least 3, and the function returns r-1 on nums'.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_10 (nums : Slice Std.I64) (h : Precondition nums) :
      ∀ r : Std.I64, minimum_mountain_removals nums = ok r →
        ∀ d : Nat, d < nums.val.length →
          (∃ js : List Nat, MountainSubseq (Contents nums) js ∧
            (js.length : Int) = (nums.val.length : Int) - r.val ∧ 3 ≤ js.length ∧
            d ∉ js) →
          ∀ nums' : Slice Std.I64, nums'.val = nums.val.eraseIdx d →
            Precondition nums' ∧
              ∃ r' : Std.I64, minimum_mountain_removals nums' = ok r' ∧ r'.val = r.val - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∀ r : Std.I64, minimum_mountain_removals nums = ok r →
          ∀ d : Nat, d < nums.val.length →
            (∃ js : List Nat, MountainSubseq (Contents nums) js ∧
              (js.length : Int) = (nums.val.length : Int) - r.val ∧ 3 ≤ js.length ∧
              d ∉ js) →
            ∀ nums' : Slice Std.I64, nums'.val = nums.val.eraseIdx d →
              Precondition nums' ∧
                ∃ r' : Std.I64, minimum_mountain_removals nums' = ok r' ∧ r'.val = r.val - 1) := by
    sorry

  /-- Whenever the function returns r on nums and r > 0, there exists an index d with 0 <= d < len(nums) such that, letting nums' be the slice obtained from nums by deleting the element at index d, nums' satisfies the length and value constraints and still has a mountain subsequence of length at least 3, and the function returns r-1 on nums'.
    Preconditions: 3 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist indices 0 <= j_0 < ... < j_{k-1} < len(nums) with k >= 3 and some p, 0 < p < k-1, such that nums[j_0] < ... < nums[j_p] > ... > nums[j_{k-1}]. -/
  theorem spec_11 (nums : Slice Std.I64) (h : Precondition nums) :
      ∀ r : Std.I64, minimum_mountain_removals nums = ok r → 0 < r.val →
        ∃ d : Nat, d < nums.val.length ∧
          ∃ nums' : Slice Std.I64, nums'.val = nums.val.eraseIdx d ∧ Precondition nums' ∧
            ∃ r' : Std.I64, minimum_mountain_removals nums' = ok r' ∧ r'.val = r.val - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : Precondition nums), ∀ r : Std.I64, minimum_mountain_removals nums = ok r → 0 < r.val →
          ∃ d : Nat, d < nums.val.length ∧
            ∃ nums' : Slice Std.I64, nums'.val = nums.val.eraseIdx d ∧ Precondition nums' ∧
              ∃ r' : Std.I64, minimum_mountain_removals nums' = ok r' ∧ r'.val = r.val - 1) := by
    sorry

  end AegisSpec.MinimumMountainRemovals
