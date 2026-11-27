import Aegis.LongestSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestSubarray.longest_subarray`

LeetCode problem `longest-subarray-of-1s-after-deleting-one-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestSubarray

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def binary (l : List Int) : Prop := ∀ x ∈ l, x = 0 ∨ x = 1

  def allZero (l : List Int) : Prop := ∀ x ∈ l, x = 0

  def allOne (l : List Int) : Prop := ∀ x ∈ l, x = 1

  def zeroCount (l : List Int) : Nat := (l.filter (fun x => x == 0)).length

  def zeroCountSeg (l : List Int) (lo hi : Nat) : Nat := zeroCount ((l.drop lo).take (hi - lo))

  def onesRun (l : List Int) (start t : Nat) : Bool :=
    (List.range t).all (fun j => l[start + j]? == some 1)

  def maxOnesRun (l : List Int) : Nat :=
    ((List.range (l.length + 1)).filter
        (fun t => t == 0 || (List.range (l.length + 1)).any (fun s => onesRun l s t))).foldr max 0

  def delAt (l : List Int) (d : Nat) : List Int := l.eraseIdx d

  def B (l : List Int) (d : Nat) : Nat := maxOnesRun (delAt l d)

  def maxDeletionB (l : List Int) : Nat := ((List.range l.length).map (fun d => B l d)).foldr max 0

  def leftOnes (l : List Int) (i : Nat) : Nat :=
    ((List.range (i + 1)).filter (fun t => onesRun l (i - t) t)).foldr max 0

  def rightOnes (l : List Int) (i : Nat) : Nat :=
    ((List.range (l.length - i)).filter (fun t => onesRun l (i + 1) t)).foldr max 0

  def zeroScore (l : List Int) (i : Nat) : Nat := leftOnes l i + rightOnes l i

  def maxZeroScore (l : List Int) : Nat :=
    (((List.range l.length).filter (fun i => l[i]? == some 0)).map
        (fun i => zeroScore l i)).foldr max 0

  /-- Whenever longest_subarray nums returns a result r, r equals the maximum over all deletion indices d with 0 <= d < len(nums) of B(d), where B(d) is defined as follows. Let m = len(nums) - 1 and let A_d be the length-m sequence obtained by deleting position d from nums: A_d[j] = nums[j] for 0 <= j < d, and A_d[j] = nums[j+1] for d <= j < m. Then B(d) is the largest integer t with 0 <= t <= m such that either t = 0 or there exists an index l with 0 <= l and l + t <= m and A_d[l+j] = 1 for every j with 0 <= j < t. If no positive t exists, B(d) = 0.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      r.val = (maxDeletionB (vals nums) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), r.val = (maxDeletionB (vals nums) : Int)) := by
    sorry

  /-- For every nums satisfying the preconditions, the function longest_subarray nums returns a result r (it does not fail or panic).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hle : (vals nums).length ≤ 100000)
      (hbin : binary (vals nums)) :
      ∃ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hle : (vals nums).length ≤ 100000)
        (hbin : binary (vals nums)), ∃ r : Std.I64, Aegis.LongestSubarray.longest_subarray nums = ok r) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, 0 <= r.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, r <= len(nums) - 1.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      r.val ≤ ((vals nums).length : Int) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), r.val ≤ ((vals nums).length : Int) - 1) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, r = 0.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] = 0. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hzero : allZero (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hzero : allZero (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), r.val = 0) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, r = len(nums) - 1.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hone : allOne (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      r.val = ((vals nums).length : Int) - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hone : allOne (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), r.val = ((vals nums).length : Int) - 1) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, r > 0 if and only if len(nums) >= 2 and there exists an index i with 0 <= i < len(nums) and nums[i] = 1.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      0 < r.val ↔ 2 ≤ (vals nums).length ∧ ∃ i : Nat, (vals nums)[i]? = some (1 : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), 0 < r.val ↔ 2 ≤ (vals nums).length ∧ ∃ i : Nat, (vals nums)[i]? = some (1 : Int)) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, there exist indices l and m with 0 <= l < m <= len(nums), m - l = r + 1, and the contiguous subarray nums[l..m) contains at most one index j with nums[j] = 0.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      ∃ lo hi : Nat, lo < hi ∧ hi ≤ (vals nums).length ∧
        ((hi - lo : Nat) : Int) = r.val + 1 ∧ zeroCountSeg (vals nums) lo hi ≤ 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), ∃ lo hi : Nat, lo < hi ∧ hi ≤ (vals nums).length ∧
          ((hi - lo : Nat) : Int) = r.val + 1 ∧ zeroCountSeg (vals nums) lo hi ≤ 1) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, for every pair of indices l and m with 0 <= l < m <= len(nums), if nums[l..m) contains at most one index j with nums[j] = 0, then m - l <= r + 1.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_9 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      ∀ lo hi : Nat, lo < hi → hi ≤ (vals nums).length →
        zeroCountSeg (vals nums) lo hi ≤ 1 → ((hi - lo : Nat) : Int) ≤ r.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), ∀ lo hi : Nat, lo < hi → hi ≤ (vals nums).length →
          zeroCountSeg (vals nums) lo hi ≤ 1 → ((hi - lo : Nat) : Int) ≤ r.val + 1) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, for every index i with 0 <= i < len(nums) and nums[i] = 0, r >= L_i + R_i, where L_i is the largest L with 0 <= L <= i and nums[i-L+j] = 1 for all j with 0 <= j < L, and R_i is the largest R with 0 <= R <= len(nums)-1-i and nums[i+1+j] = 1 for all j with 0 <= j < R.
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_10 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      ∀ i : Nat, i < (vals nums).length → (vals nums)[i]? = some (0 : Int) →
        ((leftOnes (vals nums) i + rightOnes (vals nums) i : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), ∀ i : Nat, i < (vals nums).length → (vals nums)[i]? = some (0 : Int) →
          ((leftOnes (vals nums) i + rightOnes (vals nums) i : Nat) : Int) ≤ r.val) := by
    sorry

  /-- For every nums satisfying the preconditions, if longest_subarray nums returns r and longest_subarray (reverse(nums)) returns r', then r = r', where reverse(nums) is the sequence of length len(nums) with reverse(nums)[i] = nums[len(nums)-1-i] for 0 <= i < len(nums).
    Preconditions: len(nums) >= 1 and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_11 (nums nums_rev : Slice Std.I64) (r r' : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (hrev : vals nums_rev = (vals nums).reverse)
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r)
      (hres' : Aegis.LongestSubarray.longest_subarray nums_rev = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums_rev : Slice Std.I64) (r r' : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (hrev : vals nums_rev = (vals nums).reverse)
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r)
        (hres' : Aegis.LongestSubarray.longest_subarray nums_rev = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, r <= len(nums) - 2.
    Preconditions: len(nums) >= 1, for every i with 0 <= i < len(nums), nums[i] is either 0 or 1, and there are at least two indices i with 0 <= i < len(nums) and nums[i] = 0. -/
  theorem spec_12 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hbin : binary (vals nums))
      (htwo : 2 ≤ zeroCount (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      r.val ≤ ((vals nums).length : Int) - 2 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hbin : binary (vals nums))
        (htwo : 2 ≤ zeroCount (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), r.val ≤ ((vals nums).length : Int) - 2) := by
    sorry

  /-- Whenever longest_subarray nums returns a result r, if there exists an index i with nums[i] = 0, then r = max{ L_i + R_i | 0 <= i < len(nums) and nums[i] = 0 }, where L_i is the largest L with 0 <= L <= i and nums[i-L+j] = 1 for all j with 0 <= j < L, and R_i is the largest R with 0 <= R <= len(nums)-1-i and nums[i+1+j] = 1 for all j with 0 <= j < R; if no such index i exists, then r = len(nums) - 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), nums[i] is either 0 or 1. -/
  theorem spec_13 (nums : Slice Std.I64) (r : Std.I64)
      (hne : 1 ≤ (vals nums).length)
      (hle : (vals nums).length ≤ 100000)
      (hbin : binary (vals nums))
      (hres : Aegis.LongestSubarray.longest_subarray nums = ok r) :
      ((∃ i : Nat, (vals nums)[i]? = some (0 : Int)) →
          r.val = (maxZeroScore (vals nums) : Int)) ∧
        (¬ (∃ i : Nat, (vals nums)[i]? = some (0 : Int)) →
          r.val = ((vals nums).length : Int) - 1) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
        (hne : 1 ≤ (vals nums).length)
        (hle : (vals nums).length ≤ 100000)
        (hbin : binary (vals nums))
        (hres : Aegis.LongestSubarray.longest_subarray nums = ok r), ((∃ i : Nat, (vals nums)[i]? = some (0 : Int)) →
            r.val = (maxZeroScore (vals nums) : Int)) ∧
          (¬ (∃ i : Nat, (vals nums)[i]? = some (0 : Int)) →
            r.val = ((vals nums).length : Int) - 1)) := by
    sorry

  end AegisSpec.LongestSubarray
