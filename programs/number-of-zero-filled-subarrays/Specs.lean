import Aegis.ZeroFilledSubarray.Code.Funs

/-!
# Specifications of `Aegis.ZeroFilledSubarray.zero_filled_subarray`

LeetCode problem `number-of-zero-filled-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ZeroFilledSubarray

  namespace AegisSpec.ZeroFilledSubarray

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def entry (l : List Int) (i : Nat) : Int := l.getD i 0

  def tri (n : Nat) : Nat := n * (n + 1) / 2

  def zerosFrom (l : List Int) (a : Nat) : Nat :=
    ((l.drop a).takeWhile (fun x => x == 0)).length

  def zerosEndingAux (l : List Int) : Nat → Nat
    | 0 => 0
    | (j + 1) => if entry l j = 0 then zerosEndingAux l j + 1 else 0

  def zerosBefore (l : List Int) (i : Nat) : Nat := zerosEndingAux l i

  def zerosAfter (l : List Int) (i : Nat) : Nat := zerosFrom l (i + 1)

  def zeroRuns (l : List Int) : List Nat :=
    (List.range l.length).filterMap (fun a =>
      if entry l a = 0 ∧ (a = 0 ∨ entry l (a - 1) ≠ 0) then
        some (zerosFrom l a)
      else none)

  def longestZeroRun (l : List Int) : Nat :=
    (zeroRuns l).foldr (fun L acc => max L acc) 0

  def zeroCount (l : List Int) : Nat :=
    (List.range l.length).countP (fun i => entry l i == 0)

  def isZeroFilled (l : List Int) (i j : Nat) : Bool :=
    (i ≤ j) && (j < l.length) && (j + 1 - i ≤ zerosFrom l i)

  def zeroFilledSubarrayCount (l : List Int) : Nat :=
    ((List.range l.length).product (List.range l.length)).countP
      (fun p : Nat × Nat => isZeroFilled l p.1 p.2)

  def zerosEndingAt (l : List Int) : Nat → Nat
    | 0 => if entry l 0 = 0 then 1 else 0
    | (i + 1) => if entry l (i + 1) = 0 then zerosEndingAt l i + 1 else 0

  def zeroFilledSubarrayCountByEnd (l : List Int) : Nat :=
    ((List.range l.length).map (fun i => zerosEndingAt l i)).sum

  /-- Whenever the function returns a result r, r equals the number of pairs (i, j) of indices such that 0 <= i <= j < len(nums) and nums[k] = 0 for every k with i <= k <= j.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      r.val = (zeroFilledSubarrayCount (contents nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), r.val = (zeroFilledSubarrayCount (contents nums) : Int)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions (it does not fail).
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000) :
      ∃ r : Std.I64, zero_filled_subarray nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000), ∃ r : Std.I64, zero_filled_subarray nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= z.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let z be the number of indices i with 0 <= i < len(nums) and nums[i] = 0. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      (zeroCount (contents nums) : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), (zeroCount (contents nums) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= z*(z+1)/2.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let z be the number of indices i with 0 <= i < len(nums) and nums[i] = 0. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      r.val ≤ (tri (zeroCount (contents nums)) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), r.val ≤ (tri (zeroCount (contents nums)) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r >= m*(m+1)/2.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let m be the length of the longest contiguous run of zeros in nums (m = 0 if nums has no zero). Formally, m = max { L >= 0 | there exists a with 0 <= a <= a+L-1 < len(nums) and nums[k] = 0 for all a <= k < a+L }. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      (tri (longestZeroRun (contents nums)) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), (tri (longestZeroRun (contents nums)) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9, and nums[i] != 0 for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hnonzero : ∀ x ∈ contents nums, x ≠ 0)
      (hr : zero_filled_subarray nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hnonzero : ∀ x ∈ contents nums, x ≠ 0)
        (hr : zero_filled_subarray nums = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns r on nums, r_left on the slice nums[0..k-1] (the subarray of indices 0 through k-1, empty if k=0), and r_right on the slice nums[k+1..len(nums)-1] (the subarray of indices k+1 through len(nums)-1, empty if k=len(nums)-1), we have r = r_left + r_right. If k=0, r_left = 0; if k=len(nums)-1, r_right = 0.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let k be an index with 0 <= k < len(nums) and nums[k] != 0. -/
  theorem spec_7 (nums left right : Slice Std.I64) (k : Nat)
      (r r_left r_right : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hk : k < nums.length)
      (hk_ne : entry (contents nums) k ≠ 0)
      (hleft : left.val = nums.val.take k)
      (hright : right.val = nums.val.drop (k + 1))
      (hr : zero_filled_subarray nums = ok r)
      (hr_left : zero_filled_subarray left = ok r_left)
      (hr_right : zero_filled_subarray right = ok r_right) :
      r.val = r_left.val + r_right.val ∧
        (k = 0 → r_left.val = 0) ∧
        (nums.length = k + 1 → r_right.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums left right : Slice Std.I64) (k : Nat)
        (r r_left r_right : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hk : k < nums.length)
        (hk_ne : entry (contents nums) k ≠ 0)
        (hleft : left.val = nums.val.take k)
        (hright : right.val = nums.val.drop (k + 1))
        (hr : zero_filled_subarray nums = ok r)
        (hr_left : zero_filled_subarray left = ok r_left)
        (hr_right : zero_filled_subarray right = ok r_right), r.val = r_left.val + r_right.val ∧
          (k = 0 → r_left.val = 0) ∧
          (nums.length = k + 1 → r_right.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r on nums, we have r = L + r_tail, where r_tail = 0 if len(nums) = 1, and otherwise r_tail is the result returned by the function on the slice nums[1..len(nums)-1].
    Preconditions: 1 <= len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; nums[0] = 0; let L be the unique integer such that 1 <= L <= len(nums), nums[i] = 0 for all 0 <= i < L, and (L = len(nums) or nums[L] != 0). -/
  theorem spec_8 (nums tail : Slice Std.I64) (L : Nat) (r r_tail : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hfirst : entry (contents nums) 0 = 0)
      (hL_lo : 1 ≤ L) (hL_hi : L ≤ nums.length)
      (hL_zeros : ∀ i, i < L → entry (contents nums) i = 0)
      (hL_stop : L = nums.length ∨ entry (contents nums) L ≠ 0)
      (htail : tail.val = nums.val.drop 1)
      (hr : zero_filled_subarray nums = ok r)
      (hr_tail : zero_filled_subarray tail = ok r_tail) :
      r.val = (L : Int) + r_tail.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums tail : Slice Std.I64) (L : Nat) (r r_tail : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hfirst : entry (contents nums) 0 = 0)
        (hL_lo : 1 ≤ L) (hL_hi : L ≤ nums.length)
        (hL_zeros : ∀ i, i < L → entry (contents nums) i = 0)
        (hL_stop : L = nums.length ∨ entry (contents nums) L ≠ 0)
        (htail : tail.val = nums.val.drop 1)
        (hr : zero_filled_subarray nums = ok r)
        (hr_tail : zero_filled_subarray tail = ok r_tail), r.val = (L : Int) + r_tail.val) := by
    sorry

  /-- Whenever the function returns a result r on nums, we have r = R + r_prefix, where r_prefix = 0 if len(nums) = 1, and otherwise r_prefix is the result returned by the function on the slice nums[0..len(nums)-2].
    Preconditions: 1 <= len(nums) <= 10^5; for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9; nums[len(nums)-1] = 0; let R be the unique integer such that 1 <= R <= len(nums), nums[i] = 0 for all len(nums)-R <= i < len(nums), and (R = len(nums) or nums[len(nums)-R-1] != 0). -/
  theorem spec_9 (nums pref : Slice Std.I64) (R : Nat) (r r_pref : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hlast : entry (contents nums) (nums.length - 1) = 0)
      (hR_lo : 1 ≤ R) (hR_hi : R ≤ nums.length)
      (hR_zeros : ∀ i, nums.length - R ≤ i → i < nums.length →
        entry (contents nums) i = 0)
      (hR_stop : R = nums.length ∨ entry (contents nums) (nums.length - R - 1) ≠ 0)
      (hpref : pref.val = nums.val.take (nums.length - 1))
      (hr : zero_filled_subarray nums = ok r)
      (hr_pref : zero_filled_subarray pref = ok r_pref) :
      r.val = (R : Int) + r_pref.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums pref : Slice Std.I64) (R : Nat) (r r_pref : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hlast : entry (contents nums) (nums.length - 1) = 0)
        (hR_lo : 1 ≤ R) (hR_hi : R ≤ nums.length)
        (hR_zeros : ∀ i, nums.length - R ≤ i → i < nums.length →
          entry (contents nums) i = 0)
        (hR_stop : R = nums.length ∨ entry (contents nums) (nums.length - R - 1) ≠ 0)
        (hpref : pref.val = nums.val.take (nums.length - 1))
        (hr : zero_filled_subarray nums = ok r)
        (hr_pref : zero_filled_subarray pref = ok r_pref), r.val = (R : Int) + r_pref.val) := by
    sorry

  /-- Whenever the function returns a result r, r = L*(L+1)/2.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. There exists L >= 1 such that the set of indices i with nums[i] = 0 is exactly the interval [a, a+L-1] for some a with 0 <= a <= len(nums)-L, and all other elements are nonzero. -/
  theorem spec_10 (nums : Slice Std.I64) (a L : Nat) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hL : 1 ≤ L)
      (ha : a + L ≤ nums.length)
      (hzeros : ∀ i, i < nums.length →
        (entry (contents nums) i = 0 ↔ a ≤ i ∧ i ≤ a + L - 1))
      (hr : zero_filled_subarray nums = ok r) :
      r.val = (tri L : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (a L : Nat) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hL : 1 ≤ L)
        (ha : a + L ≤ nums.length)
        (hzeros : ∀ i, i < nums.length →
          (entry (contents nums) i = 0 ↔ a ≤ i ∧ i ≤ a + L - 1))
        (hr : zero_filled_subarray nums = ok r), r.val = (tri L : Int)) := by
    sorry

  /-- Whenever the function returns r on nums and r' on nums', r - r' = (a+1)*(b+1).
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let i be an index with 0 <= i < len(nums) and nums[i] = 0. Let a be the number of consecutive zeros immediately before i: a = max { a >= 0 | i-a >= 0 and nums[j] = 0 for all i-a <= j < i }, and a = 0 if i=0 or nums[i-1] != 0. Let b be the number of consecutive zeros immediately after i: b = max { b >= 0 | i+b < len(nums) and nums[j] = 0 for all i < j <= i+b }, and b = 0 if i=len(nums)-1 or nums[i+1] != 0. Let nums' be any array satisfying the constraints, with len(nums') = len(nums), nums'[j] = nums[j] for all j != i, and nums'[i] != 0. -/
  theorem spec_11 (nums nums' : Slice Std.I64) (i : Nat) (r r' : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hlen_lo' : 1 ≤ nums'.length) (hlen_hi' : nums'.length ≤ 100000)
      (hval' : ∀ x ∈ contents nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hi : i < nums.length)
      (hzero : entry (contents nums) i = 0)
      (hlen' : nums'.length = nums.length)
      (hagree : ∀ j, j ≠ i → entry (contents nums') j = entry (contents nums) j)
      (hzero' : entry (contents nums') i ≠ 0)
      (hr : zero_filled_subarray nums = ok r)
      (hr' : zero_filled_subarray nums' = ok r') :
      r.val - r'.val =
        ((zerosBefore (contents nums) i : Int) + 1) *
          ((zerosAfter (contents nums) i : Int) + 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (i : Nat) (r r' : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hlen_lo' : 1 ≤ nums'.length) (hlen_hi' : nums'.length ≤ 100000)
        (hval' : ∀ x ∈ contents nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hi : i < nums.length)
        (hzero : entry (contents nums) i = 0)
        (hlen' : nums'.length = nums.length)
        (hagree : ∀ j, j ≠ i → entry (contents nums') j = entry (contents nums) j)
        (hzero' : entry (contents nums') i ≠ 0)
        (hr : zero_filled_subarray nums = ok r)
        (hr' : zero_filled_subarray nums' = ok r'), r.val - r'.val =
          ((zerosBefore (contents nums) i : Int) + 1) *
            ((zerosAfter (contents nums) i : Int) + 1)) := by
    sorry

  /-- Whenever the function returns r on nums and r' on nums', r = r'.
    Preconditions: 1 <= len(nums) <= 10^5 and 1 <= len(nums') <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9, and for every i with 0 <= i < len(nums'), -10^9 <= nums'[i] <= 10^9. Let the maximal zero runs of nums be its maximal contiguous intervals of indices where nums[k]=0; let their lengths be a multiset (or list) of integers. Similarly for nums'. Assume the multisets of lengths of maximal zero runs of nums and nums' are equal. -/
  theorem spec_12 (nums nums' : Slice Std.I64) (r r' : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hlen_lo' : 1 ≤ nums'.length) (hlen_hi' : nums'.length ≤ 100000)
      (hval' : ∀ x ∈ contents nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hruns : (zeroRuns (contents nums)).Perm (zeroRuns (contents nums')))
      (hr : zero_filled_subarray nums = ok r)
      (hr' : zero_filled_subarray nums' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hlen_lo' : 1 ≤ nums'.length) (hlen_hi' : nums'.length ≤ 100000)
        (hval' : ∀ x ∈ contents nums', -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hruns : (zeroRuns (contents nums)).Perm (zeroRuns (contents nums')))
        (hr : zero_filled_subarray nums = ok r)
        (hr' : zero_filled_subarray nums' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{q=1}^t L_q*(L_q+1)/2.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. Let L_1,...,L_t be the lengths of the maximal contiguous zero runs of nums, with t=0 and empty sum 0 if nums has no zeros. -/
  theorem spec_13 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      r.val = (((zeroRuns (contents nums)).map tri).sum : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), r.val = (((zeroRuns (contents nums)).map tri).sum : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{i=0}^{len(nums)-1} c_i. Equivalently, c_i is the number of zero-filled subarrays ending at i, so each zero-filled subarray is counted once by its right endpoint.
    Preconditions: 1 <= len(nums) <= 10^5 and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. For each i with 0 <= i < len(nums), define c_i = 0 if nums[i] != 0, and otherwise c_i = 1 + (if i > 0 and nums[i-1] = 0 then c_{i-1} else 0). -/
  theorem spec_14 (nums : Slice Std.I64) (r : Std.I64)
      (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
      (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
      (hr : zero_filled_subarray nums = ok r) :
      r.val = (zeroFilledSubarrayCountByEnd (contents nums) : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen_lo : 1 ≤ nums.length) (hlen_hi : nums.length ≤ 100000)
        (hval : ∀ x ∈ contents nums, -1000000000 ≤ x ∧ x ≤ 1000000000)
        (hr : zero_filled_subarray nums = ok r), r.val = (zeroFilledSubarrayCountByEnd (contents nums) : Int)) := by
    sorry

  end AegisSpec.ZeroFilledSubarray
