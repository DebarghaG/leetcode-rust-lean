import Aegis.NumberGame.Code.Funs

/-!
# Specifications of `Aegis.NumberGame.number_game`

LeetCode problem `minimum-number-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberGame

  def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

  def countVal (l : List Std.I64) (v : Int) : Nat := (vals l).countP (fun w => w == v)

  def countValPrefix (l : List Std.I64) (k : Nat) (v : Int) : Nat := countVal (l.take k) v

  def Nondecreasing (l : List Std.I64) : Prop :=
    ∀ i j, i ≤ j → j < l.length → (l[i]!).val ≤ (l[j]!).val

  def NondecreasingRearrangement (l s : List Std.I64) : Prop :=
    s.length = l.length ∧ Nondecreasing s ∧ ∀ v : Int, countVal s v = countVal l v

  def IsMinOf (f : Int → Nat) (x : Int) : Prop := 0 < f x ∧ ∀ v, 0 < f v → x ≤ v

  def IsMaxOf (f : Int → Nat) (x : Int) : Prop := 0 < f x ∧ ∀ v, 0 < f v → v ≤ x

  def countValDeleteOne (l : List Std.I64) (a : Int) : Int → Nat :=
    fun v => countVal l v - (if v = a then 1 else 0)

  theorem nondecreasingRearrangement_iff (l s : List Std.I64) :
      NondecreasingRearrangement l s ↔
        s.length = l.length ∧ Nondecreasing s ∧ ∀ v : Int, countVal s v = countVal l v :=
    Iff.rfl

  /-- Let n = len(nums), and let s be the nondecreasing rearrangement of nums: len(s) = n, s[0] <= s[1] <= ... <= s[n-1], and every value occurs in s exactly as many times as in nums. The function returns a result r (it does not fail) such that len(r) = n and, for every k with 0 <= k < n/2, r[2*k] = s[2*k+1] and r[2*k+1] = s[2*k].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (s : List Std.I64) (h_s_len : s.length = nums.val.length) (h_s_sorted : Nondecreasing s)
      (h_s_mult : ∀ v : Int, countVal s v = countVal nums.val v) :
      ∃ r, Aegis.NumberGame.number_game nums = ok r ∧
        r.val.length = nums.val.length ∧
        ∀ k, k < nums.val.length / 2 →
          (r.val[2 * k]!).val = (s[2 * k + 1]!).val ∧
          (r.val[2 * k + 1]!).val = (s[2 * k]!).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (s : List Std.I64) (h_s_len : s.length = nums.val.length) (h_s_sorted : Nondecreasing s)
        (h_s_mult : ∀ v : Int, countVal s v = countVal nums.val v), ∃ r, Aegis.NumberGame.number_game nums = ok r ∧
          r.val.length = nums.val.length ∧
          ∀ k, k < nums.val.length / 2 →
            (r.val[2 * k]!).val = (s[2 * k + 1]!).val ∧
            (r.val[2 * k + 1]!).val = (s[2 * k]!).val) := by
    sorry

  /-- The function returns a result r; that is, it does not fail on any input satisfying the preconditions.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100) :
      ∃ r, Aegis.NumberGame.number_game nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100), ∃ r, Aegis.NumberGame.number_game nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r) :
      r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r), r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, r is a permutation of nums: for every integer value v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r) :
      ∀ v : Int, countVal r.val v = countVal nums.val v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r), ∀ v : Int, countVal r.val v = countVal nums.val v) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(nums), for every k with 0 <= k < len(nums)/2, r[2*k] >= r[2*k+1].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      ∀ k, k < nums.val.length / 2 → (r.val[2 * k + 1]!).val ≤ (r.val[2 * k]!).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), ∀ k, k < nums.val.length / 2 → (r.val[2 * k + 1]!).val ≤ (r.val[2 * k]!).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(nums), for every k with 0 <= k < len(nums)/2 - 1, r[2*k+1] <= r[2*k+3].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      ∀ k, k < nums.val.length / 2 - 1 → (r.val[2 * k + 1]!).val ≤ (r.val[2 * k + 3]!).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), ∀ k, k < nums.val.length / 2 - 1 → (r.val[2 * k + 1]!).val ≤ (r.val[2 * k + 3]!).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = len(nums), for every k with 0 <= k < len(nums)/2 - 1, r[2*k] <= r[2*k+2].
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      ∀ k, k < nums.val.length / 2 - 1 → (r.val[2 * k]!).val ≤ (r.val[2 * k + 2]!).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), ∀ k, k < nums.val.length / 2 - 1 → (r.val[2 * k]!).val ≤ (r.val[2 * k + 2]!).val) := by
    sorry

  /-- Let m be the minimum value among nums. Whenever the function returns a result r with len(r) = len(nums), r[1] = m, and r[0] is the minimum of the multiset obtained from nums by deleting one occurrence of m.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (m : Int) (h_m : IsMinOf (countVal nums.val) m)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      (r.val[1]!).val = m ∧ IsMinOf (countValDeleteOne nums.val m) (r.val[0]!).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (m : Int) (h_m : IsMinOf (countVal nums.val) m)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), (r.val[1]!).val = m ∧ IsMinOf (countValDeleteOne nums.val m) (r.val[0]!).val) := by
    sorry

  /-- Let n = len(nums) and let M be the maximum value among nums. Whenever the function returns a result r with len(r) = n, r[n-2] = M, and r[n-1] is the maximum of the multiset obtained from nums by deleting one occurrence of M.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (M : Int) (h_M : IsMaxOf (countVal nums.val) M)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      (r.val[nums.val.length - 2]!).val = M ∧
        IsMaxOf (countValDeleteOne nums.val M) (r.val[nums.val.length - 1]!).val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (M : Int) (h_M : IsMaxOf (countVal nums.val) M)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), (r.val[nums.val.length - 2]!).val = M ∧
          IsMaxOf (countValDeleteOne nums.val M) (r.val[nums.val.length - 1]!).val) := by
    sorry

  /-- Let n = len(nums), and let s be the nondecreasing rearrangement of nums. Whenever the function returns a result r with len(r) = n, for every k with 0 <= k < n/2 and every integer value v, the number of indices i with 0 <= i <= 2*k+1 and r[i] = v equals the number of indices i with 0 <= i <= 2*k+1 and s[i] = v.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_10 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (s : List Std.I64) (h_s_len : s.length = nums.val.length) (h_s_sorted : Nondecreasing s)
      (h_s_mult : ∀ v : Int, countVal s v = countVal nums.val v)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h_len : r.val.length = nums.val.length) :
      ∀ k, k < nums.val.length / 2 → ∀ v : Int,
        countValPrefix r.val (2 * k + 2) v = countValPrefix s (2 * k + 2) v := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (s : List Std.I64) (h_s_len : s.length = nums.val.length) (h_s_sorted : Nondecreasing s)
        (h_s_mult : ∀ v : Int, countVal s v = countVal nums.val v)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h_len : r.val.length = nums.val.length), ∀ k, k < nums.val.length / 2 → ∀ v : Int,
          countValPrefix r.val (2 * k + 2) v = countValPrefix s (2 * k + 2) v) := by
    sorry

  /-- If the function returns r on input nums and returns r2 on input nums2, then r = r2.
    Preconditions: nums and nums2 are two arrays satisfying len(nums) is even, 2 <= len(nums) <= 100, 1 <= nums[i] <= 100 for all i, and similarly for nums2; and nums and nums2 have the same multiset: for every integer value v, the number of indices i with 0 <= i < len(nums) and nums[i] = v equals the number of indices i with 0 <= i < len(nums2) and nums2[i] = v. -/
  theorem spec_11 (nums nums2 : Slice Std.I64)
      (h_even : nums.val.length % 2 = 0) (h_ge : 2 ≤ nums.val.length)
      (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (h_even2 : nums2.val.length % 2 = 0) (h_ge2 : 2 ≤ nums2.val.length)
      (h_le2 : nums2.val.length ≤ 100)
      (h_bnd2 : ∀ i, i < nums2.val.length →
        1 ≤ (nums2.val[i]!).val ∧ (nums2.val[i]!).val ≤ 100)
      (h_same : ∀ v : Int, countVal nums.val v = countVal nums2.val v)
      (r r2 : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
      (h2 : Aegis.NumberGame.number_game nums2 = ok r2) :
      r = r2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64)
        (h_even : nums.val.length % 2 = 0) (h_ge : 2 ≤ nums.val.length)
        (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (h_even2 : nums2.val.length % 2 = 0) (h_ge2 : 2 ≤ nums2.val.length)
        (h_le2 : nums2.val.length ≤ 100)
        (h_bnd2 : ∀ i, i < nums2.val.length →
          1 ≤ (nums2.val[i]!).val ∧ (nums2.val[i]!).val ≤ 100)
        (h_same : ∀ v : Int, countVal nums.val v = countVal nums2.val v)
        (r r2 : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r)
        (h2 : Aegis.NumberGame.number_game nums2 = ok r2), r = r2) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 1 <= r[i] <= 100.
    Preconditions: len(nums) is even, 2 <= len(nums) <= 100, and 1 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_12 (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
      (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
      (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
      (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r) :
      ∀ i, i < r.val.length → 1 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 100 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (h_even : nums.val.length % 2 = 0)
        (h_ge : 2 ≤ nums.val.length) (h_le : nums.val.length ≤ 100)
        (h_bnd : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
        (r : alloc.vec.Vec Std.I64) (h : Aegis.NumberGame.number_game nums = ok r), ∀ i, i < r.val.length → 1 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 100) := by
    sorry

  end AegisSpec.NumberGame
