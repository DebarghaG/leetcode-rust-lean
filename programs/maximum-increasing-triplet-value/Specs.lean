import Aegis.MaximumTripletValue.Code.Funs

/-!
# Specifications of `Aegis.MaximumTripletValue.maximum_triplet_value`

LeetCode problem `maximum-increasing-triplet-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumTripletValue

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def slen (nums : Slice Std.I64) : Nat := nums.val.length

  def valAt (nums : Slice Std.I64) (i : Nat) : Int := (contents nums)[i]?.getD 0

  def IsIncreasingTriplet (nums : Slice Std.I64) (i j k : Nat) : Prop :=
    i < j ∧ j < k ∧ k < slen nums ∧ valAt nums i < valAt nums j ∧
      valAt nums j < valAt nums k

  def tripletValue (nums : Slice Std.I64) (i j k : Nat) : Int :=
    valAt nums i - valAt nums j + valAt nums k

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr min x

  def maxVal (nums : Slice Std.I64) : Int := listMax (contents nums)

  def minGap (nums : Slice Std.I64) : Int :=
    listMin ((List.range (slen nums - 2)).map (fun t => valAt nums (t + 1) - valAt nums t))

  /-- The function returns a result r and r is exactly the maximum of nums[i] - nums[j] + nums[k] over all integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. Equivalently, every such triplet has value <= r, and at least one such triplet has value r.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k) :
      ∃ r : Std.I64,
        Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
        (∀ i j k,
          IsIncreasingTriplet nums i j k → tripletValue nums i j k ≤ r.val) ∧
        (∃ i j k,
          IsIncreasingTriplet nums i j k ∧ tripletValue nums i j k = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k), ∃ r : Std.I64,
          Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
          (∀ i j k,
            IsIncreasingTriplet nums i j k → tripletValue nums i j k ≤ r.val) ∧
          (∃ i j k,
            IsIncreasingTriplet nums i j k ∧ tripletValue nums i j k = r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or go out of bounds.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k) :
      ∃ r : Std.I64, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k), ∃ r : Std.I64, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k], we have r >= nums[i] - nums[j] + nums[k].
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      ∀ i j k, IsIncreasingTriplet nums i j k → tripletValue nums i j k ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), ∀ i j k, IsIncreasingTriplet nums i j k → tripletValue nums i j k ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k] such that r = nums[i] - nums[j] + nums[k].
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      ∃ i j k, IsIncreasingTriplet nums i j k ∧ r.val = tripletValue nums i j k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), ∃ i j k, IsIncreasingTriplet nums i j k ∧ r.val = tripletValue nums i j k) := by
    sorry

  /-- Whenever the function returns a result r, 2 <= r.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      2 ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), 2 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= M - 1, where M is the maximum of all values nums[0], nums[1], ..., nums[len(nums)-1].
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      r.val ≤ maxVal nums - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), r.val ≤ maxVal nums - 1) := by
    sorry

  /-- The function returns a result r and r = nums[0] - nums[1] + nums[2].
    Preconditions: len(nums) = 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : slen nums = 3)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k) :
      ∃ r : Std.I64,
        Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
        r.val = valAt nums 0 - valAt nums 1 + valAt nums 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : slen nums = 3)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k), ∃ r : Std.I64,
          Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
          r.val = valAt nums 0 - valAt nums 1 + valAt nums 2) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums) such that there exist j, k with i < j < k < len(nums) and nums[i] < nums[j] < nums[k], we have r > nums[i].
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      ∀ i, i < slen nums → (∃ j k, IsIncreasingTriplet nums i j k) → r.val > valAt nums i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), ∀ i, i < slen nums → (∃ j k, IsIncreasingTriplet nums i j k) → r.val > valAt nums i) := by
    sorry

  /-- Let a, b, c be the unique indices guaranteed by the preconditions. The function returns a result r and r = nums[a] - nums[b] + nums[c].
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; there exist integers a, b, c with 0 <= a < b < c < len(nums) and nums[a] < nums[b] < nums[c]; and for every i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k], we have i=a, j=b, and k=c. -/
  theorem spec_9 (nums : Slice Std.I64) (a b c : Nat)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : IsIncreasingTriplet nums a b c)
      (huniq : ∀ i j k, IsIncreasingTriplet nums i j k → i = a ∧ j = b ∧ k = c) :
      ∃ r : Std.I64,
        Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
        r.val = valAt nums a - valAt nums b + valAt nums c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (a b c : Nat)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : IsIncreasingTriplet nums a b c)
        (huniq : ∀ i j k, IsIncreasingTriplet nums i j k → i = a ∧ j = b ∧ k = c), ∃ r : Std.I64,
          Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
          r.val = valAt nums a - valAt nums b + valAt nums c) := by
    sorry

  /-- The function returns a result r, and r = nums[len(nums)-1] - D, where D is the minimum of nums[j] - nums[j-1] over all integers j with 1 <= j <= len(nums)-2.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]; and for every i with 0 <= i and i+1 < len(nums), nums[i] < nums[i+1]. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hmono : ∀ i, i + 1 < slen nums → valAt nums i < valAt nums (i + 1)) :
      ∃ r : Std.I64,
        Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
        r.val = valAt nums (slen nums - 1) - minGap nums := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hmono : ∀ i, i + 1 < slen nums → valAt nums i < valAt nums (i + 1)), ∃ r : Std.I64,
          Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
          r.val = valAt nums (slen nums - 1) - minGap nums) := by
    sorry

  /-- Whenever the function returns a result r, for every i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k], we have r >= nums[k] - nums[j] + 1.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; and there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]. -/
  theorem spec_11 (nums : Slice Std.I64) (r : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      ∀ i j k, IsIncreasingTriplet nums i j k → r.val ≥ valAt nums k - valAt nums j + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), ∀ i j k, IsIncreasingTriplet nums i j k → r.val ≥ valAt nums k - valAt nums j + 1) := by
    sorry

  /-- If the function returns r on nums and returns r' on nums', then r' = r + c.
    Preconditions: len(nums) >= 3; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; there exist integers i, j, k with 0 <= i < j < k < len(nums) and nums[i] < nums[j] < nums[k]; let c be an integer such that for every i with 0 <= i < len(nums), 1 <= nums[i] + c <= 10^9; let nums' be the slice of length len(nums) with nums'[i] = nums[i] + c for every i. -/
  theorem spec_12 (nums nums' : Slice Std.I64) (c : Int) (r r' : Std.I64)
      (hlen : 3 ≤ slen nums)
      (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
      (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
      (hc : ∀ i, i < slen nums → 1 ≤ valAt nums i + c ∧ valAt nums i + c ≤ 10 ^ 9)
      (hlen' : slen nums' = slen nums)
      (hshift : ∀ i, i < slen nums → valAt nums' i = valAt nums i + c)
      (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r)
      (hr' : Aegis.MaximumTripletValue.maximum_triplet_value nums' = ok r') :
      r'.val = r.val + c := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : Int) (r r' : Std.I64)
        (hlen : 3 ≤ slen nums)
        (hbounds : ∀ i, i < slen nums → 1 ≤ valAt nums i ∧ valAt nums i ≤ 10 ^ 9)
        (hex : ∃ i j k, IsIncreasingTriplet nums i j k)
        (hc : ∀ i, i < slen nums → 1 ≤ valAt nums i + c ∧ valAt nums i + c ≤ 10 ^ 9)
        (hlen' : slen nums' = slen nums)
        (hshift : ∀ i, i < slen nums → valAt nums' i = valAt nums i + c)
        (hr : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r)
        (hr' : Aegis.MaximumTripletValue.maximum_triplet_value nums' = ok r'), r'.val = r.val + c) := by
    sorry

  end AegisSpec.MaximumTripletValue
