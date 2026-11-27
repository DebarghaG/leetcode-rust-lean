import Aegis.LengthOfLongestSubsequence.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLongestSubsequence.length_of_longest_subsequence`

LeetCode problem `length-of-the-longest-subsequence-that-sums-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LengthOfLongestSubsequence

  open Aeneas Aeneas.Std Result
  open Aegis.LengthOfLongestSubsequence (length_of_longest_subsequence)

  def StrictlyIncreasing : List Nat → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => x < y ∧ StrictlyIncreasing (y :: rest)

  def valueAt (l : List Std.I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def selectedSum (l : List Std.I64) (is : List Nat) : Int :=
    (is.map (valueAt l)).sum

  def totalSum (l : List Std.I64) : Int :=
    (l.map (fun x => x.val)).sum

  def IndicesSumTo (l : List Std.I64) (is : List Nat) (target : Int) : Prop :=
    StrictlyIncreasing is ∧
      (∀ i, i ∈ is → i < l.length) ∧
      selectedSum l is = target

  def Occurs (l : List Std.I64) (v : Int) : Prop :=
    ∃ i : Nat, ∃ h : i < l.length, (l[i]'h).val = v

  def AllInRange (l : List Std.I64) (lo hi : Int) : Prop :=
    ∀ i : Nat, ∀ h : i < l.length, lo ≤ (l[i]'h).val ∧ (l[i]'h).val ≤ hi

  def IsPermOf (ys xs : List Std.I64) : Prop :=
    ∃ pi : Fin xs.length → Fin ys.length,
      Function.Bijective pi ∧ ∀ i : Fin xs.length, ys.get (pi i) = xs.get i

  /-- The function returns a result r (so it does not fail), and the following holds. Call a target-subsequence any choice of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) for all j and nums[i_0] + ... + nums[i_{k-1}] = target; its length is k (the empty choice, k = 0, is allowed). Then either r = -1 and no target-subsequence exists, or 1 <= r <= len(nums), some target-subsequence has length r, and every target-subsequence has length at most r.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∃ r : Std.I64,
        length_of_longest_subsequence nums target = ok r ∧
          ((r.val = -1 ∧ ¬ ∃ is : List Nat, IndicesSumTo nums.val is target.val) ∨
            (1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) ∧
              (∃ is : List Nat,
                IndicesSumTo nums.val is target.val ∧ (is.length : Int) = r.val) ∧
              (∀ is : List Nat,
                IndicesSumTo nums.val is target.val → (is.length : Int) ≤ r.val))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∃ r : Std.I64,
          length_of_longest_subsequence nums target = ok r ∧
            ((r.val = -1 ∧ ¬ ∃ is : List Nat, IndicesSumTo nums.val is target.val) ∨
              (1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) ∧
                (∃ is : List Nat,
                  IndicesSumTo nums.val is target.val ∧ (is.length : Int) = r.val) ∧
                (∀ is : List Nat,
                  IndicesSumTo nums.val is target.val → (is.length : Int) ≤ r.val)))) := by
    sorry

  /-- The function returns a result r on every input satisfying the preconditions; in particular it does not panic, overflow, or access an out-of-bounds index.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ r : Std.I64,
        length_of_longest_subsequence nums target = ok r →
          (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int))) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ r : Std.I64,
          length_of_longest_subsequence nums target = ok r →
            (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)))) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, r <= target.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ r : Std.I64,
        length_of_longest_subsequence nums target = ok r → 0 ≤ r.val → r.val ≤ target.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ r : Std.I64,
          length_of_longest_subsequence nums target = ok r → 0 ≤ r.val → r.val ≤ target.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exist indices i_0 < i_1 < ... < i_{r-1} such that 0 <= i_j < len(nums) for all j and nums[i_0] + ... + nums[i_{r-1}] = target.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ r : Std.I64,
        length_of_longest_subsequence nums target = ok r → 0 ≤ r.val →
          ∃ is : List Nat,
            IndicesSumTo nums.val is target.val ∧ (is.length : Int) = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ r : Std.I64,
          length_of_longest_subsequence nums target = ok r → 0 ≤ r.val →
            ∃ is : List Nat,
              IndicesSumTo nums.val is target.val ∧ (is.length : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every choice of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) for all j and nums[i_0] + ... + nums[i_{k-1}] = target, we have k <= r.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ r : Std.I64,
        length_of_longest_subsequence nums target = ok r → 0 ≤ r.val →
          ∀ is : List Nat,
            IndicesSumTo nums.val is target.val → (is.length : Int) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ r : Std.I64,
          length_of_longest_subsequence nums target = ok r → 0 ≤ r.val →
            ∀ is : List Nat,
              IndicesSumTo nums.val is target.val → (is.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there is no choice of indices i_0 < ... < i_{k-1} (possibly k = 0) with 0 <= i_j < len(nums) for all j and nums[i_0] + ... + nums[i_{k-1}] = target.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ r : Std.I64,
        length_of_longest_subsequence nums target = ok r →
          (r.val = -1 ↔ ¬ ∃ is : List Nat, IndicesSumTo nums.val is target.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ r : Std.I64,
          length_of_longest_subsequence nums target = ok r →
            (r.val = -1 ↔ ¬ ∃ is : List Nat, IndicesSumTo nums.val is target.val)) := by
    sorry

  /-- If the sum of all entries of nums is strictly less than target, then the function returns -1.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      totalSum nums.val < target.val →
        ∃ r : Std.I64,
          length_of_longest_subsequence nums target = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), totalSum nums.val < target.val →
          ∃ r : Std.I64,
            length_of_longest_subsequence nums target = ok r ∧ r.val = -1) := by
    sorry

  /-- If the sum of all entries of nums is exactly target, then the function returns len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_9 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      totalSum nums.val = target.val →
        ∃ r : Std.I64,
          length_of_longest_subsequence nums target = ok r ∧
            r.val = (nums.val.length : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), totalSum nums.val = target.val →
          ∃ r : Std.I64,
            length_of_longest_subsequence nums target = ok r ∧
              r.val = (nums.val.length : Int)) := by
    sorry

  /-- If len(nums) = 1, then the function returns 1 when nums[0] = target and returns -1 otherwise.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_10 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
      (hlen : nums.val.length = 1) :
      (valueAt nums.val 0 = target.val →
          ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = 1) ∧
        (valueAt nums.val 0 ≠ target.val →
          ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = -1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
        (hlen : nums.val.length = 1), (valueAt nums.val 0 = target.val →
            ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = 1) ∧
          (valueAt nums.val 0 ≠ target.val →
            ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = -1)) := by
    sorry

  /-- If target = 1, then the function returns 1 if there exists an index i with 0 <= i < len(nums) and nums[i] = 1, and returns -1 otherwise.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_11 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
      (htarget : target.val = 1) :
      (Occurs nums.val 1 →
          ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = 1) ∧
        (¬ Occurs nums.val 1 →
          ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = -1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
        (htarget : target.val = 1), (Occurs nums.val 1 →
            ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = 1) ∧
          (¬ Occurs nums.val 1 →
            ∃ r : Std.I64, length_of_longest_subsequence nums target = ok r ∧ r.val = -1)) := by
    sorry

  /-- If nums[i] = 1 for every i with 0 <= i < len(nums), then the function returns target when target <= len(nums), and returns -1 when target > len(nums).
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
      (hall_one : ∀ i : Nat, ∀ h : i < nums.val.length, (nums.val[i]'h).val = 1) :
      ((target.val ≤ (nums.val.length : Int)) →
          ∃ r : Std.I64,
            length_of_longest_subsequence nums target = ok r ∧ r.val = target.val) ∧
        ((nums.val.length : Int) < target.val →
          ∃ r : Std.I64,
            length_of_longest_subsequence nums target = ok r ∧ r.val = -1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000)
        (hall_one : ∀ i : Nat, ∀ h : i < nums.val.length, (nums.val[i]'h).val = 1), ((target.val ≤ (nums.val.length : Int)) →
            ∃ r : Std.I64,
              length_of_longest_subsequence nums target = ok r ∧ r.val = target.val) ∧
          ((nums.val.length : Int) < target.val →
            ∃ r : Std.I64,
              length_of_longest_subsequence nums target = ok r ∧ r.val = -1)) := by
    sorry

  /-- For every slice ys with len(ys) = len(nums) and 1 <= ys[i] <= 1000 for all i, if ys is a permutation of nums (meaning there is a bijection pi on {0,...,len(nums)-1} such that ys[pi(i)] = nums[i] for all i), then whenever the function returns r on nums and r' on ys with the same target, r = r'.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_13 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ ys : Slice Std.I64,
        ys.val.length = nums.val.length →
          AllInRange ys.val 1 1000 →
            IsPermOf ys.val nums.val →
              ∀ r r' : Std.I64,
                length_of_longest_subsequence nums target = ok r →
                  length_of_longest_subsequence ys target = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ ys : Slice Std.I64,
          ys.val.length = nums.val.length →
            AllInRange ys.val 1 1000 →
              IsPermOf ys.val nums.val →
                ∀ r r' : Std.I64,
                  length_of_longest_subsequence nums target = ok r →
                    length_of_longest_subsequence ys target = ok r' → r.val = r'.val) := by
    sorry

  /-- Let ys be any slice with len(ys) <= 1000 and 1 <= ys[j] <= 1000 for every j, such that nums occurs as a subsequence of ys (equivalently, ys can be obtained from nums by inserting zero or more elements). If the function returns r on nums and r' on ys with the same target, then r' >= r, where -1 is smaller than every nonnegative result.
    Preconditions: len(nums) >= 1 and len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] and nums[i] <= 1000; and 1 <= target and target <= 1000. -/
  theorem spec_14 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
      (hentries : AllInRange nums.val 1 1000)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000) :
      ∀ ys : Slice Std.I64,
        ys.val.length ≤ 1000 →
          AllInRange ys.val 1 1000 →
            List.Sublist nums.val ys.val →
              ∀ r r' : Std.I64,
                length_of_longest_subsequence nums target = ok r →
                  length_of_longest_subsequence ys target = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
        (hentries : AllInRange nums.val 1 1000)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 1000), ∀ ys : Slice Std.I64,
          ys.val.length ≤ 1000 →
            AllInRange ys.val 1 1000 →
              List.Sublist nums.val ys.val →
                ∀ r r' : Std.I64,
                  length_of_longest_subsequence nums target = ok r →
                    length_of_longest_subsequence ys target = ok r' → r.val ≤ r'.val) := by
    sorry

  end AegisSpec.LengthOfLongestSubsequence
