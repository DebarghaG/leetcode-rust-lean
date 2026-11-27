import Aegis.KLengthApart.Code.Funs

/-!
# Specifications of `Aegis.KLengthApart.k_length_apart`

LeetCode problem `check-if-all-1s-are-at-least-length-k-places-away`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.KLengthApart

  namespace AegisSpec.KLengthApart

  def len (nums : Slice Std.I64) : ℕ := nums.val.length

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def entry (nums : Slice Std.I64) (i : ℕ) : ℤ := (vals nums).getD i 0

  def isOne (nums : Slice Std.I64) (i : ℕ) : Prop := entry nums i = 1

  def binary (nums : Slice Std.I64) : Prop :=
    ∀ i : ℕ, i < len nums → entry nums i = 0 ∨ entry nums i = 1

  def KAPart (nums : Slice Std.I64) (k : ℤ) : Prop :=
    ∀ (i j : ℕ), i < j → j < len nums → isOne nums i → isOne nums j →
      (j : ℤ) - (i : ℤ) > k

  def KClose (nums : Slice Std.I64) (k : ℤ) : Prop :=
    ∃ (i j : ℕ), i < j ∧ j < len nums ∧ isOne nums i ∧ isOne nums j ∧
      (j : ℤ) - (i : ℤ) ≤ k

  def AtMostOne (nums : Slice Std.I64) : Prop :=
    ∀ (i j : ℕ), i < len nums → j < len nums → isOne nums i → isOne nums j → i = j

  def ZeroTail (nums : Slice Std.I64) (k : ℤ) : Prop :=
    ∀ i : ℕ, i < len nums → isOne nums i →
      ∀ d : ℕ, 1 ≤ d → (d : ℤ) ≤ k → i + d < len nums → entry nums (i + d) = 0

  def Consecutive (nums : Slice Std.I64) (i j : ℕ) : Prop :=
    i < j ∧ j < len nums ∧ isOne nums i ∧ isOne nums j ∧
      ∀ h : ℕ, i < h → h < j → ¬ isOne nums h

  def Padded (nums nums' : Slice Std.I64) (a b : ℕ) : Prop :=
    len nums' = a + len nums + b ∧
      (∀ i : ℕ, i < len nums → entry nums' (a + i) = entry nums i) ∧
      (∀ j : ℕ, j < a → entry nums' j = 0) ∧
      (∀ j : ℕ, a + len nums ≤ j → j < a + len nums + b → entry nums' j = 0)

  def IsRev (nums numsR : Slice Std.I64) : Prop :=
    len numsR = len nums ∧
      ∀ i : ℕ, i < len nums → entry numsR i = entry nums (len nums - 1 - i)

  def IsSub (nums sub : Slice Std.I64) (l r : ℕ) : Prop :=
    len sub = r - l + 1 ∧
      ∀ i : ℕ, i < r - l + 1 → entry sub i = entry nums (l + i)

  def OnesSubset (nums nums' : Slice Std.I64) : Prop :=
    len nums' = len nums ∧
      (∀ i : ℕ, i < len nums → entry nums' i = 0 ∨ entry nums' i = 1) ∧
      (∀ i : ℕ, i < len nums → isOne nums' i → isOne nums i)

  /-- The function returns a result r (not an error), and r = true if and only if for every pair of indices i, j with 0 <= i < j < n such that nums[i] = 1 and nums[j] = 1, we have j - i > k. Equivalently, r = false if and only if there exist two 1s whose index difference is at most k.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums) :
      ∃ r : Bool, k_length_apart nums k = ok r ∧
        (r = true ↔ KAPart nums k.val) ∧
        (r = false ↔ KClose nums k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums), ∃ r : Bool, k_length_apart nums k = ok r ∧
          (r = true ↔ KAPart nums k.val) ∧
          (r = false ↔ KClose nums k.val)) := by
    sorry

  /-- For every nums and k satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or return an error.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums) :
      ∃ r : Bool, k_length_apart nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums), ∃ r : Bool, k_length_apart nums k = ok r) := by
    sorry

  /-- If k >= n - 1, then the function returns a result r and r = true if and only if nums contains at most one index i with nums[i] = 1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hk : (len nums : ℤ) - 1 ≤ k.val) :
      ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ AtMostOne nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hk : (len nums : ℤ) - 1 ≤ k.val), ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ AtMostOne nums)) := by
    sorry

  /-- Whenever the function returns a result r with r = false, there exist indices i < j such that nums[i] = 1, nums[j] = 1, j - i <= k, and no index h with i < h < j has nums[h] = 1 (that is, i and j are consecutive positions of 1 in nums).
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums) :
      ∀ r : Bool, k_length_apart nums k = ok r → r = false →
        ∃ (i j : ℕ), Consecutive nums i j ∧ (j : ℤ) - (i : ℤ) ≤ k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums), ∀ r : Bool, k_length_apart nums k = ok r → r = false →
          ∃ (i j : ℕ), Consecutive nums i j ∧ (j : ℤ) - (i : ℤ) ≤ k.val) := by
    sorry

  /-- If k_length_apart nums k2 returns a result r2 with r2 = true, then k_length_apart nums k1 returns a result r1 with r1 = true.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let k1 and k2 be integers with 0 <= k1 <= k2 <= n. -/
  theorem spec_5 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hbin : binary nums)
      (hk1_lb : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2_ub : k2.val ≤ (len nums : ℤ)) :
      ∀ r2 : Bool, k_length_apart nums k2 = ok r2 → r2 = true →
        ∃ r1 : Bool, k_length_apart nums k1 = ok r1 ∧ r1 = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hbin : binary nums)
        (hk1_lb : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2_ub : k2.val ≤ (len nums : ℤ)), ∀ r2 : Bool, k_length_apart nums k2 = ok r2 → r2 = true →
          ∃ r1 : Bool, k_length_apart nums k1 = ok r1 ∧ r1 = true) := by
    sorry

  /-- Then k_length_apart nums k and k_length_apart nums' k return the same boolean result: both true or both false.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let a >= 0 and b >= 0, and let nums' be an array of length a + n + b with 1 <= len(nums') <= 100000 such that nums'[a + i] = nums[i] for 0 <= i < n, and nums'[j] = 0 for 0 <= j < a or a + n <= j < a + n + b. -/
  theorem spec_6 (nums nums' : Slice Std.I64) (k : Std.I64) (a b : ℕ)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hlen'_lb : 1 ≤ len nums') (hlen'_ub : len nums' ≤ 100000)
      (hpad : Padded nums nums' a b) :
      (∀ r : Bool, k_length_apart nums k = ok r →
          ∃ r' : Bool, k_length_apart nums' k = ok r' ∧ r' = r) ∧
        (∀ r' : Bool, k_length_apart nums' k = ok r' →
          ∃ r : Bool, k_length_apart nums k = ok r ∧ r = r') := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (a b : ℕ)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hlen'_lb : 1 ≤ len nums') (hlen'_ub : len nums' ≤ 100000)
        (hpad : Padded nums nums' a b), (∀ r : Bool, k_length_apart nums k = ok r →
            ∃ r' : Bool, k_length_apart nums' k = ok r' ∧ r' = r) ∧
          (∀ r' : Bool, k_length_apart nums' k = ok r' →
            ∃ r : Bool, k_length_apart nums k = ok r ∧ r = r')) := by
    sorry

  /-- The function returns a result r and r = true if and only if for every index i with 0 <= i < n and nums[i] = 1, and for every d with 1 <= d <= k and i + d < n, we have nums[i + d] = 0.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums) :
      ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ ZeroTail nums k.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums), ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ ZeroTail nums k.val)) := by
    sorry

  /-- If k_length_apart nums k returns a result r0 with r0 = true, then k_length_apart (nums[l..r]) k returns a result r1 with r1 = true, where nums[l..r] is the contiguous subarray nums[l], nums[l+1], ..., nums[r].
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let l and r be indices with 0 <= l <= r < n and r - l + 1 >= k. -/
  theorem spec_8 (nums sub : Slice Std.I64) (k : Std.I64) (l r : ℕ)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hlr : l ≤ r) (hrn : r < len nums)
      (hkr : k.val ≤ ((r - l + 1 : ℕ) : ℤ))
      (hsub : IsSub nums sub l r) :
      ∀ r0 : Bool, k_length_apart nums k = ok r0 → r0 = true →
        ∃ r1 : Bool, k_length_apart sub k = ok r1 ∧ r1 = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums sub : Slice Std.I64) (k : Std.I64) (l r : ℕ)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hlr : l ≤ r) (hrn : r < len nums)
        (hkr : k.val ≤ ((r - l + 1 : ℕ) : ℤ))
        (hsub : IsSub nums sub l r), ∀ r0 : Bool, k_length_apart nums k = ok r0 → r0 = true →
          ∃ r1 : Bool, k_length_apart sub k = ok r1 ∧ r1 = true) := by
    sorry

  /-- Then k_length_apart nums k and k_length_apart rev(nums) k return the same boolean result.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let rev(nums) be the array of length n with rev(nums)[i] = nums[n - 1 - i] for 0 <= i < n. -/
  theorem spec_9 (nums numsR : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hrev : IsRev nums numsR) :
      (∀ r : Bool, k_length_apart nums k = ok r →
          ∃ r' : Bool, k_length_apart numsR k = ok r' ∧ r' = r) ∧
        (∀ r' : Bool, k_length_apart numsR k = ok r' →
          ∃ r : Bool, k_length_apart nums k = ok r ∧ r = r') := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums numsR : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hrev : IsRev nums numsR), (∀ r : Bool, k_length_apart nums k = ok r →
            ∃ r' : Bool, k_length_apart numsR k = ok r' ∧ r' = r) ∧
          (∀ r' : Bool, k_length_apart numsR k = ok r' →
            ∃ r : Bool, k_length_apart nums k = ok r ∧ r = r')) := by
    sorry

  /-- If k_length_apart nums k returns a result r with r = true, then k_length_apart nums' k returns a result r' with r' = true.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. Let nums' be an array of length n such that for every i with 0 <= i < n, nums'[i] = 0 or 1, and if nums'[i] = 1 then nums[i] = 1 (so the 1s of nums' are a subset of the 1s of nums). -/
  theorem spec_10 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hsub : OnesSubset nums nums') :
      ∀ r : Bool, k_length_apart nums k = ok r → r = true →
        ∃ r' : Bool, k_length_apart nums' k = ok r' ∧ r' = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hsub : OnesSubset nums nums'), ∀ r : Bool, k_length_apart nums k = ok r → r = true →
          ∃ r' : Bool, k_length_apart nums' k = ok r' ∧ r' = true) := by
    sorry

  /-- If there exists an index i with 0 <= i < n - 1 such that nums[i] = 1 and nums[i + 1] = 1, then the function returns a result r and r = true if and only if k = 0.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; 0 <= k <= n; for every i with 0 <= i < n, nums[i] = 0 or nums[i] = 1. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
      (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
      (hbin : binary nums)
      (hadj : ∃ i : ℕ, i + 1 < len nums ∧ isOne nums i ∧ isOne nums (i + 1)) :
      ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ k.val = 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_lb : 1 ≤ len nums) (hlen_ub : len nums ≤ 100000)
        (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (len nums : ℤ))
        (hbin : binary nums)
        (hadj : ∃ i : ℕ, i + 1 < len nums ∧ isOne nums i ∧ isOne nums (i + 1)), ∃ r : Bool, k_length_apart nums k = ok r ∧ (r = true ↔ k.val = 0)) := by
    sorry

  end AegisSpec.KLengthApart
