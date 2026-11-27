import Aegis.KBigIndices.Code.Funs

/-!
# Specifications of `Aegis.KBigIndices.k_big_indices`

LeetCode problem `count-the-number-of-k-big-indices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KBigIndices

  def valAt (xs : List Std.I64) (i : Nat) : Int := (xs.getD i 0#i64).val

  def countLtLeft (xs : List Std.I64) (i : Nat) (v : Int) : Nat :=
    List.countP (fun x => decide (x.val < v)) (xs.take i)

  def countLtRight (xs : List Std.I64) (i : Nat) (v : Int) : Nat :=
    List.countP (fun x => decide (x.val < v)) (xs.drop (i + 1))

  def countLtNe (xs : List Std.I64) (n i : Nat) (v : Int) : Nat :=
    List.countP (fun j => decide (j ≠ i ∧ valAt xs j < v)) (List.range n)

  @[reducible] def IsKBig (xs : List Std.I64) (k : Int) (i : Nat) : Prop :=
    k ≤ (countLtLeft xs i (valAt xs i) : Int) ∧
      k ≤ (countLtRight xs i (valAt xs i) : Int)

  def kBigIndices (xs : List Std.I64) (k : Int) : List Nat :=
    List.filter (fun i => decide (IsKBig xs k i)) (List.range xs.length)

  def numKBig (xs : List Std.I64) (k : Int) : Nat := (kBigIndices xs k).length

  def ValuesInRange (xs : List Std.I64) : Prop :=
    ∀ i (hi : i < xs.length), 1 ≤ xs[i].val ∧ xs[i].val ≤ (xs.length : Int)

  def Nondecreasing (xs : List Std.I64) : Prop :=
    ∀ i j (hij : i < j) (hj : j < xs.length), xs[i].val ≤ xs[j].val

  def SameOrder (xs ys : List Std.I64) : Prop :=
    ∀ i j, i < xs.length → j < xs.length →
      (valAt xs i < valAt xs j ↔ valAt ys i < valAt ys j)

  def revSlice (s : Slice Std.I64) : Slice Std.I64 :=
    ⟨s.val.reverse.length, Aeneas.Data.ListN.ListN.fromList s.val.reverse, by
      have hb := s.bound
      have h : s.val.length = s.leng := by
        simp only [Slice.val]
        exact Aeneas.Data.ListN.ListN_length s.list
      have h2 : s.val.reverse.length = s.val.length := List.length_reverse ..
      omega⟩

  theorem revSlice_val (s : Slice Std.I64) : (revSlice s).val = s.val.reverse := by
    simp [revSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  open Aegis.KBigIndices

  /-- The function returns a result r, and r equals the number of integers i with 0 <= i < len(nums) such that both (1) the number of integers j with 0 <= j < i and nums[j] < nums[i] is at least k, and (2) the number of integers j with i < j < len(nums) and nums[j] < nums[i] is at least k.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). Here len(nums) is the number of elements of the slice nums, and nums[i] is the i-th element (0-indexed). -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∃ r, k_big_indices nums k = ok r ∧ r.val = (numKBig nums.val k.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∃ r, k_big_indices nums k = ok r ∧ r.val = (numKBig nums.val k.val : Int)) := by
    sorry

  /-- The function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∃ r, k_big_indices nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∃ r, k_big_indices nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r, k_big_indices nums k = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r, k_big_indices nums k = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(nums).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r, k_big_indices nums k = ok r → r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r, k_big_indices nums k = ok r → r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r <= max(0, len(nums) - 2*k), where max(0, len(nums) - 2*k) is the larger of 0 and the integer len(nums) - 2*k.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r, k_big_indices nums k = ok r →
        r.val ≤ max 0 ((nums.val.length : Int) - 2 * k.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r, k_big_indices nums k = ok r →
          r.val ≤ max 0 ((nums.val.length : Int) - 2 * k.val)) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums), and for every i,j with 0 <= i < j < len(nums), nums[i] <= nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val)
      (hsorted : Nondecreasing nums.val) :
      ∃ r, k_big_indices nums k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val)
        (hsorted : Nondecreasing nums.val), ∃ r, k_big_indices nums k = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever k_big_indices(nums, k1) returns a result r1 and k_big_indices(nums, k2) returns a result r2, we have r2 <= r1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums), and 1 <= k1 <= k2 <= len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hvals : ValuesInRange nums.val)
      (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
      (hk2 : k2.val ≤ (nums.val.length : Int)) :
      ∀ r1 r2, k_big_indices nums k1 = ok r1 → k_big_indices nums k2 = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hvals : ValuesInRange nums.val)
        (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
        (hk2 : k2.val ≤ (nums.val.length : Int)), ∀ r1 r2, k_big_indices nums k1 = ok r1 → k_big_indices nums k2 = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  /-- Let rev(nums) be the slice of length len(nums) with rev(nums)[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). Whenever k_big_indices(nums, k) returns a result r and k_big_indices(rev(nums), k) returns a result r', we have r = r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r r', k_big_indices nums k = ok r → k_big_indices (revSlice nums) k = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r r', k_big_indices nums k = ok r → k_big_indices (revSlice nums) k = ok r' →
          r.val = r'.val) := by
    sorry

  /-- If for every i,j with 0 <= i < len(nums) and 0 <= j < len(nums) we have nums[i] < nums[j] if and only if nums'[i] < nums'[j], then whenever k_big_indices(nums, k) returns a result r and k_big_indices(nums', k) returns a result r', we have r = r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums), and nums' is a slice of i64 with len(nums') = len(nums) and for every i with 0 <= i < len(nums), 1 <= nums'[i] <= len(nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val)
      (hlen' : nums'.val.length = nums.val.length)
      (hvals' : ValuesInRange nums'.val)
      (horder : SameOrder nums.val nums'.val) :
      ∀ r r', k_big_indices nums k = ok r → k_big_indices nums' k = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val)
        (hlen' : nums'.val.length = nums.val.length)
        (hvals' : ValuesInRange nums'.val)
        (horder : SameOrder nums.val nums'.val), ∀ r r', k_big_indices nums k = ok r → k_big_indices nums' k = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an integer i with 0 <= i < len(nums) such that i is k-big (the number of j with 0 <= j < i and nums[j] < nums[i] is at least k, and the number of j with i < j < len(nums) and nums[j] < nums[i] is at least k).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r, k_big_indices nums k = ok r →
        (0 < r.val ↔ ∃ i, i < nums.val.length ∧ IsKBig nums.val k.val i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r, k_big_indices nums k = ok r →
          (0 < r.val ↔ ∃ i, i < nums.val.length ∧ IsKBig nums.val k.val i)) := by
    sorry

  /-- Whenever the function returns a result r, if len(nums) >= 2*k and r = len(nums) - 2*k, then for every integer i with k <= i <= len(nums) - 1 - k, i is k-big (the number of j with 0 <= j < i and nums[j] < nums[i] is at least k, and the number of j with i < j < len(nums) and nums[j] < nums[i] is at least k).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, 1 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
      (hvals : ValuesInRange nums.val) :
      ∀ r, k_big_indices nums k = ok r →
        2 * k.val ≤ (nums.val.length : Int) →
        r.val = (nums.val.length : Int) - 2 * k.val →
        ∀ i : Nat, k.val ≤ (i : Int) → (i : Int) ≤ (nums.val.length : Int) - 1 - k.val →
          IsKBig nums.val k.val i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_max : nums.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
        (hvals : ValuesInRange nums.val), ∀ r, k_big_indices nums k = ok r →
          2 * k.val ≤ (nums.val.length : Int) →
          r.val = (nums.val.length : Int) - 2 * k.val →
          ∀ i : Nat, k.val ≤ (i : Int) → (i : Int) ≤ (nums.val.length : Int) - 1 - k.val →
            IsKBig nums.val k.val i) := by
    sorry

  end AegisSpec.KBigIndices
