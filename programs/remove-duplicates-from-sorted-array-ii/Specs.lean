import Aegis.RemoveDuplicates.Code.Funs

/-!
# Specifications of `Aegis.RemoveDuplicates.remove_duplicates`

LeetCode problem `remove-duplicates-from-sorted-array-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RemoveDuplicates

  def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

  def cnt (l : List Int) (v : Int) : Nat := (l.filter (fun x => x = v)).length

  def D (l : List Int) : Nat := l.toFinset.card

  def E (l : List Int) : Nat := (l.toFinset.filter (fun v => 2 ≤ cnt l v)).card

  def keptCount (l : List Int) : Nat := l.toFinset.sum (fun v => min (cnt l v) 2)

  abbrev IsKeptIndex (l : List Int) (i : Nat) : Prop := i < 2 ∨ l[i]? ≠ l[i - 2]?

  def keptIndices (l : List Int) : List Nat :=
    (List.range l.length).filter (fun i => decide (IsKeptIndex l i))

  def compress (l : List Int) : List Int := (keptIndices l).filterMap (fun i => l[i]?)

  def Nondecreasing (l : List Int) : Prop :=
    ∀ i, i + 1 < l.length → l.getD i 0 ≤ l.getD (i + 1) 0

  def StrictlyIncreasing (l : List Int) : Prop :=
    ∀ i, i + 1 < l.length → l.getD i 0 < l.getD (i + 1) 0

  def InBounds (l : List Int) : Prop :=
    ∀ i, i < l.length → -10000 ≤ l.getD i 0 ∧ l.getD i 0 ≤ 10000

  def AllEqual (l : List Int) : Prop := ∀ i, i < l.length → l.getD i 0 = l.getD 0 0

  def NoTriple (l : List Int) : Prop :=
    ∀ i, 2 ≤ i → i < l.length → l.getD i 0 ≠ l.getD (i - 2) 0

  def AllOccurAtLeastTwice (l : List Int) : Prop := ∀ v, 1 ≤ cnt l v → 2 ≤ cnt l v

  /-- The function returns an integer r; let k = r (read as a natural number). Then k = sum over all distinct values v occurring in nums of min(c_v, 2), where c_v = the number of indices i with 0 <= i < len(nums) and nums[i] = v. In words: k is the length of the list obtained from nums by keeping, for every distinct value, only its first two occurrences (fewer if the value occurs fewer than two times), i.e. the number of elements remaining after removing duplicates so that each unique element appears at most twice, with relative order preserved.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_1 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = (keptCount (vals nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = (keptCount (vals nums) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions the function returns a result r (it does not panic, does not go out of bounds, and no intermediate 64-bit arithmetic overflows).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_2 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r) := by
    sorry

  /-- The function returns an integer r; let k = r. Then 1 <= k <= len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_3 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r and let D = the number of distinct values occurring in nums, i.e. D = |{v : there exists i with 0 <= i < len(nums) and nums[i] = v}|. Then k >= D.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_4 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        (D (vals nums) : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          (D (vals nums) : Int) ≤ r.val) := by
    sorry

  /-- The function returns an integer r; let k = r and let D = the number of distinct values occurring in nums. Then k <= 2 * D.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_5 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val ≤ 2 * (D (vals nums) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val ≤ 2 * (D (vals nums) : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r. Let D = the number of distinct values occurring in nums and E = the number of distinct values v that occur at least twice in nums (i.e. for which there are at least two indices i, j with 0 <= i < j < len(nums) and nums[i] = nums[j] = v). Then k = D + E.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_6 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = (D (vals nums) : Int) + (E (vals nums) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = (D (vals nums) : Int) + (E (vals nums) : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r. Then k = len(nums) if and only if no value occurs three or more times in nums, which (nums being sorted) is equivalent to: for every i with 2 <= i < len(nums), nums[i] != nums[i-2].
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_7 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        (r.val = (nums.val.length : Int) ↔ NoTriple (vals nums)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          (r.val = (nums.val.length : Int) ↔ NoTriple (vals nums))) := by
    sorry

  /-- If len(nums) <= 2, then the function returns r with r = len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover len(nums) <= 2. -/
  theorem spec_8 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (hlen3 : nums.val.length ≤ 2) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = (nums.val.length : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (hlen3 : nums.val.length ≤ 2), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = (nums.val.length : Int)) := by
    sorry

  /-- If all elements of nums are equal, then the function returns r with r = min(len(nums), 2).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover nums[0] = nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (hall : AllEqual (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = ((min nums.val.length 2 : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (hall : AllEqual (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = ((min nums.val.length 2 : Nat) : Int)) := by
    sorry

  /-- If nums is strictly increasing, then the function returns r with r = len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover nums[i] < nums[i+1] for every i with 0 <= i < len(nums) - 1 (nums is strictly increasing). -/
  theorem spec_10 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (hstrict : StrictlyIncreasing (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = (nums.val.length : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (hstrict : StrictlyIncreasing (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = (nums.val.length : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r and let D = the number of distinct values occurring in nums. If every value occurring in nums occurs at least twice, then k = 2 * D.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover every value occurring in nums occurs at least twice. -/
  theorem spec_11 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (htwice : AllOccurAtLeastTwice (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = 2 * (D (vals nums) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (htwice : AllOccurAtLeastTwice (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = 2 * (D (vals nums) : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r (read as a natural number). Then k equals the number of indices i with 0 <= i < len(nums) such that either i < 2, or (i >= 2 and nums[i] != nums[i-2]). These indices are exactly the kept positions: the first occurrence of each value and, if present, its second occurrence. Reading them in increasing index order gives the sequence obtained by keeping at most the first two occurrences of every value.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_12 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        r.val = ((keptIndices (vals nums)).length : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          r.val = ((keptIndices (vals nums)).length : Int)) := by
    sorry

  /-- Whenever the function returns k on input nums and k' on input ys, we have k = k'.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover c is an integer such that nums[i] + c is representable as a 64-bit signed integer for every i with 0 <= i < len(nums), and ys is a slice with len(ys) = len(nums) and ys[i] = nums[i] + c for every i with 0 <= i < len(nums). -/
  theorem spec_13 (nums ys : Slice I64) (c : Int)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (hrepr : ∀ i, i < nums.val.length →
        -(2 ^ 63 : Int) ≤ (vals nums).getD i 0 + c ∧
          (vals nums).getD i 0 + c ≤ 2 ^ 63 - 1)
      (hylen : ys.val.length = nums.val.length)
      (hys : vals ys = (vals nums).map (fun x => x + c)) :
      ∀ k k', Aegis.RemoveDuplicates.remove_duplicates nums = ok k →
        Aegis.RemoveDuplicates.remove_duplicates ys = ok k' → k.val = k'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums ys : Slice I64) (c : Int)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (hrepr : ∀ i, i < nums.val.length →
          -(2 ^ 63 : Int) ≤ (vals nums).getD i 0 + c ∧
            (vals nums).getD i 0 + c ≤ 2 ^ 63 - 1)
        (hylen : ys.val.length = nums.val.length)
        (hys : vals ys = (vals nums).map (fun x => x + c)), ∀ k k', Aegis.RemoveDuplicates.remove_duplicates nums = ok k →
          Aegis.RemoveDuplicates.remove_duplicates ys = ok k' → k.val = k'.val) := by
    sorry

  /-- Whenever the function returns k on input nums and k' on input ys, we have k' >= k. Moreover k' <= k + (len(ys) - len(nums)).
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4; moreover ys is a slice with len(ys) >= len(nums), ys[i] = nums[i] for every i with 0 <= i < len(nums) (nums is a prefix of ys), and ys is non-decreasing. -/
  theorem spec_14 (nums ys : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
      (hylen : nums.val.length ≤ ys.val.length)
      (hprefix : List.IsPrefix (vals nums) (vals ys))
      (hysorted : Nondecreasing (vals ys)) :
      ∀ k k', Aegis.RemoveDuplicates.remove_duplicates nums = ok k →
        Aegis.RemoveDuplicates.remove_duplicates ys = ok k' →
          k.val ≤ k'.val ∧
            k'.val ≤ k.val + ((ys.val.length - nums.val.length : Nat) : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums ys : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums))
        (hylen : nums.val.length ≤ ys.val.length)
        (hprefix : List.IsPrefix (vals nums) (vals ys))
        (hysorted : Nondecreasing (vals ys)), ∀ k k', Aegis.RemoveDuplicates.remove_duplicates nums = ok k →
          Aegis.RemoveDuplicates.remove_duplicates ys = ok k' →
            k.val ≤ k'.val ∧
              k'.val ≤ k.val + ((ys.val.length - nums.val.length : Nat) : Int)) := by
    sorry

  /-- The function returns an integer r; let k = r. Then there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_0 and i_{k-1} < len(nums) such that the sequence nums[i_0], nums[i_1], ..., nums[i_{k-1}] is exactly the sequence obtained from nums by replacing each maximal block of equal consecutive values, of length c, by the first min(c, 2) elements of that block.
    Preconditions: len(nums) >= 1; len(nums) <= 30000; nums is sorted in non-decreasing order, i.e. for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), -10^4 <= nums[i] <= 10^4. -/
  theorem spec_15 (nums : Slice I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
      (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)) :
      ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
        ∃ idx : List Nat,
          idx.length = r.val.toNat ∧ idx.Pairwise (· < ·) ∧
            (∀ i, i ∈ idx → i < nums.val.length) ∧
              idx.map (fun i => (vals nums)[i]?) = (compress (vals nums)).map some := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 30000)
        (hsorted : Nondecreasing (vals nums)) (hbounds : InBounds (vals nums)), ∃ r, Aegis.RemoveDuplicates.remove_duplicates nums = ok r ∧
          ∃ idx : List Nat,
            idx.length = r.val.toNat ∧ idx.Pairwise (· < ·) ∧
              (∀ i, i ∈ idx → i < nums.val.length) ∧
                idx.map (fun i => (vals nums)[i]?) = (compress (vals nums)).map some) := by
    sorry

  end AegisSpec.RemoveDuplicates
