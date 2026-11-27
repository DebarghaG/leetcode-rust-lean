import Aegis.LargestInteger.Code.Funs

/-!
# Specifications of `Aegis.LargestInteger.largest_integer`

LeetCode problem `find-the-largest-almost-missing-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestInteger

  namespace AegisSpec.LargestInteger

  def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def at? (nums : Slice Std.I64) (j : Nat) : Option Int := (vals nums)[j]?

  def window (nums : Slice Std.I64) (k s : Nat) (x : Int) : Prop :=
    ∃ j, s ≤ j ∧ j < s + k ∧ at? nums j = some x

  def windowBool (nums : Slice Std.I64) (k s : Nat) (x : Int) : Bool :=
    (List.range k).any (fun t => decide (at? nums (s + t) = some x))

  theorem windowBool_eq_true_iff (nums : Slice Std.I64) (k s : Nat) (x : Int) :
      windowBool nums k s x = true ↔ window nums k s x := by
    simp only [windowBool, window, List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨t, ht, h⟩
      exact ⟨s + t, by omega, by omega, of_decide_eq_true h⟩
    · rintro ⟨j, hj1, hj2, hj3⟩
      refine ⟨j - s, by omega, ?_⟩
      have h : s + (j - s) = j := by omega
      simp [h, hj3]

  def count (nums : Slice Std.I64) (k : Nat) (x : Int) : Nat :=
    ((List.range (nums.val.length + 1)).filter
        (fun s => decide (s + k ≤ nums.val.length) && windowBool nums k s x)).length

  def occCount (nums : Slice Std.I64) (x : Int) : Nat :=
    ((List.range nums.val.length).filter (fun i => decide (at? nums i = some x))).length

  def IsGreatest (p : Int → Prop) (v : Int) : Prop := p v ∧ ∀ y, p y → y ≤ v

  def edgeCandidates (nums : Slice Std.I64) (v : Int) : Prop :=
    ((vals nums)[0]? = some v ∧
        ∀ j, 1 ≤ j → j < (vals nums).length → (vals nums)[j]? ≠ some v) ∨
      ((vals nums)[(vals nums).length - 1]? = some v ∧
        ∀ j, j < (vals nums).length - 1 → (vals nums)[j]? ≠ some v)

  /-- For any integer x, let count(x) be the number of start indices s with 0 <= s <= len(nums) - k such that the length-k contiguous subarray nums[s..s+k-1] contains x, i.e. there exists j with s <= j < s + k and nums[j] = x. The function returns a result r, and: if there exists an integer x with count(x) = 1, then count(r) = 1 and every integer y with count(y) = 1 satisfies y <= r; otherwise r = -1.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. All indices are 0-based. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∃ r : Std.I64,
        largest_integer nums k = ok r ∧
          ((∃ x : Int, count nums k.val.toNat x = 1) →
            count nums k.val.toNat r.val = 1 ∧
              ∀ y : Int, count nums k.val.toNat y = 1 → y ≤ r.val) ∧
          (¬ (∃ x : Int, count nums k.val.toNat x = 1) → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∃ r : Std.I64,
          largest_integer nums k = ok r ∧
            ((∃ x : Int, count nums k.val.toNat x = 1) →
              count nums k.val.toNat r.val = 1 ∧
                ∀ y : Int, count nums k.val.toNat y = 1 → y ≤ r.val) ∧
            (¬ (∃ x : Int, count nums k.val.toNat x = 1) → r.val = -1)) := by
    sorry

  /-- The function returns a result for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∃ r : Std.I64, largest_integer nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∃ r : Std.I64, largest_integer nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or there exists an index i with 0 <= i < len(nums) and nums[i] = r.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∀ r : Std.I64,
        largest_integer nums k = ok r →
          r.val = -1 ∨ ∃ i : Nat, i < nums.val.length ∧ at? nums i = some r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∀ r : Std.I64,
          largest_integer nums k = ok r →
            r.val = -1 ∨ ∃ i : Nat, i < nums.val.length ∧ at? nums i = some r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exists exactly one start index s with 0 <= s <= len(nums) - k such that the length-k subarray nums[s..s+k-1] contains r.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∀ r : Std.I64,
        largest_integer nums k = ok r →
          r.val ≠ -1 →
            ∃! s : Nat, s + k.val.toNat ≤ nums.val.length ∧ window nums k.val.toNat s r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∀ r : Std.I64,
          largest_integer nums k = ok r →
            r.val ≠ -1 →
              ∃! s : Nat, s + k.val.toNat ≤ nums.val.length ∧ window nums k.val.toNat s r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every integer y with y > r, the number of length-k subarrays of nums that contain y is not equal to 1.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∀ r : Std.I64,
        largest_integer nums k = ok r →
          r.val ≠ -1 → ∀ y : Int, r.val < y → count nums k.val.toNat y ≠ 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∀ r : Std.I64,
          largest_integer nums k = ok r →
            r.val ≠ -1 → ∀ y : Int, r.val < y → count nums k.val.toNat y ≠ 1) := by
    sorry

  /-- Whenever the function returns r = -1, every distinct integer v that occurs in nums is contained in at least two length-k subarrays of nums.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50) :
      ∀ r : Std.I64,
        largest_integer nums k = ok r →
          r.val = -1 → ∀ v : Int, v ∈ vals nums → 2 ≤ count nums k.val.toNat v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50), ∀ r : Std.I64,
          largest_integer nums k = ok r →
            r.val = -1 → ∀ v : Int, v ∈ vals nums → 2 ≤ count nums k.val.toNat v) := by
    sorry

  /-- For every input satisfying the preconditions with k = len(nums), the function returns r = max{nums[i] | 0 <= i < len(nums)}.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
      (h_k_eq_len : k.val = (nums.val.length : Int)) :
      ∃ r : Std.I64, largest_integer nums k = ok r ∧ IsGreatest (fun v => v ∈ vals nums) r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
        (h_k_eq_len : k.val = (nums.val.length : Int)), ∃ r : Std.I64, largest_integer nums k = ok r ∧ IsGreatest (fun v => v ∈ vals nums) r.val) := by
    sorry

  /-- For every input satisfying the preconditions with k = 1, the function returns r, where r is the largest integer v such that exactly one index i with 0 <= i < len(nums) has nums[i] = v, and r = -1 if no such v exists.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
      (h_k_eq_one : k.val = 1) :
      ∃ r : Std.I64,
        largest_integer nums k = ok r ∧
          ((∃ v : Int, occCount nums v = 1) → IsGreatest (fun v => occCount nums v = 1) r.val) ∧
          (¬ (∃ v : Int, occCount nums v = 1) → r.val = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
        (h_k_eq_one : k.val = 1), ∃ r : Std.I64,
          largest_integer nums k = ok r ∧
            ((∃ v : Int, occCount nums v = 1) → IsGreatest (fun v => occCount nums v = 1) r.val) ∧
            (¬ (∃ v : Int, occCount nums v = 1) → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions in which all elements of nums are equal to one integer c, the function returns c if k = len(nums), and returns -1 if k < len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
      (c : Int) (h_all_eq : ∀ x ∈ vals nums, x = c) :
      (k.val = (nums.val.length : Int) →
          ∃ r : Std.I64, largest_integer nums k = ok r ∧ r.val = c) ∧
        (k.val < (nums.val.length : Int) →
          ∃ r : Std.I64, largest_integer nums k = ok r ∧ r.val = -1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
        (c : Int) (h_all_eq : ∀ x ∈ vals nums, x = c), (k.val = (nums.val.length : Int) →
            ∃ r : Std.I64, largest_integer nums k = ok r ∧ r.val = c) ∧
          (k.val < (nums.val.length : Int) →
            ∃ r : Std.I64, largest_integer nums k = ok r ∧ r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions with len(nums) >= 2 and k = len(nums) - 1, the function returns r, where r is the maximum of the set of integers v such that either (v = nums[0] and no index i with 1 <= i < len(nums) has nums[i] = v) or (v = nums[len(nums)-1] and no index i with 0 <= i < len(nums)-1 has nums[i] = v); if this set is empty, r = -1.
    Preconditions: len(nums) >= 1, len(nums) <= 50, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 50. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
      (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
      (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
      (h_len_ge_two : 2 ≤ nums.val.length) (h_k_eq : k.val = (nums.val.length : Int) - 1) :
      ∃ r : Std.I64,
        largest_integer nums k = ok r ∧
          ((∃ v : Int, edgeCandidates nums v) → IsGreatest (edgeCandidates nums) r.val) ∧
          (¬ (∃ v : Int, edgeCandidates nums v) → r.val = -1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (h_len_ge_one : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 50)
        (h_k_ge_one : 1 ≤ k.val) (h_k_le_len : k.val ≤ (nums.val.length : Int))
        (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 50)
        (h_len_ge_two : 2 ≤ nums.val.length) (h_k_eq : k.val = (nums.val.length : Int) - 1), ∃ r : Std.I64,
          largest_integer nums k = ok r ∧
            ((∃ v : Int, edgeCandidates nums v) → IsGreatest (edgeCandidates nums) r.val) ∧
            (¬ (∃ v : Int, edgeCandidates nums v) → r.val = -1)) := by
    sorry

  end AegisSpec.LargestInteger
