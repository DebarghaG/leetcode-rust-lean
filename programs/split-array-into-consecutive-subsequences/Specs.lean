import Aegis.IsPossible.Code.Funs

/-!
# Specifications of `Aegis.IsPossible.is_possible`

LeetCode problem `split-array-into-consecutive-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.IsPossible (is_possible)

  namespace AegisSpec.IsPossible

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def countVals (nums : Slice Std.I64) (x : ℤ) : ℕ := (vals nums).countP (fun y => y == x)

  def StepsByOne (l : List ℤ) : Prop := ∀ p ∈ l.zip l.tail, p.2 = p.1 + 1

  def blockVals (nums : Slice Std.I64) (b : List (Fin nums.val.length)) : List ℤ :=
    b.map (fun i => (nums.val.get i).val)

  def IsRunBlock (nums : Slice Std.I64) (b : List (Fin nums.val.length)) : Prop :=
    3 ≤ b.length ∧ b.Pairwise (· < ·) ∧ StepsByOne (blockVals nums b)

  def IsRunPartition (nums : Slice Std.I64) (m : ℕ)
      (blocks : Fin m → List (Fin nums.val.length)) : Prop :=
    (∀ j, IsRunBlock nums (blocks j)) ∧ (∀ i, ∃! j : Fin m, i ∈ blocks j)

  def HasRunPartition (nums : Slice Std.I64) : Prop :=
    ∃ (m : ℕ) (blocks : Fin m → List (Fin nums.val.length)),
      1 ≤ m ∧ IsRunPartition nums m blocks

  /-- Whenever the function returns a result r, r = true if and only if there exist an integer m >= 1 and a partition of the index set {0, ..., len(nums)-1} into m nonempty sets S_1, ..., S_m such that, for each j from 1 to m, writing the indices of S_j in increasing order as i_1 < ... < i_k, we have k >= 3 and nums[i_{t+1}] = nums[i_t] + 1 for every t with 1 <= t < k. If no such partition exists, r = false.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → (r = true ↔ HasRunPartition nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → (r = true ↔ HasRunPartition nums)) := by
    sorry

  /-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∃ r, is_possible nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∃ r, is_possible nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then 3 <= len(nums).
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true → 3 ≤ nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true → 3 ≤ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if nums[1] = nums[0] + 1 and nums[2] = nums[1] + 1.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums); and len(nums) = 3. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
      (h_len3 : nums.val.length = 3) :
      ∀ r, is_possible nums = ok r →
        (r = true ↔ (nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
          (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
        (h_len3 : nums.val.length = 3), ∀ r, is_possible nums = ok r →
          (r = true ↔ (nums.val[1]'(by omega)).val = (nums.val[0]'(by omega)).val + 1 ∧
            (nums.val[2]'(by omega)).val = (nums.val[1]'(by omega)).val + 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums); and nums[0] = nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
      (h_const : ∀ (i : ℕ) (h : i < nums.val.length),
        (nums.val[i]'h).val = (nums.val[0]'(by omega)).val) :
      ∀ r, is_possible nums = ok r → r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
        (h_const : ∀ (i : ℕ) (h : i < nums.val.length),
          (nums.val[i]'h).val = (nums.val[0]'(by omega)).val), ∀ r, is_possible nums = ok r → r = false) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every integer v, letting c(x) be the number of indices i with 0 <= i < len(nums) and nums[i] = x, if c(v+1) = 0 then c(v) <= c(v-1) and c(v) <= c(v-2).
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true →
        ∀ v : ℤ, countVals nums (v + 1) = 0 →
          countVals nums v ≤ countVals nums (v - 1) ∧
            countVals nums v ≤ countVals nums (v - 2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true →
          ∀ v : ℤ, countVals nums (v + 1) = 0 →
            countVals nums v ≤ countVals nums (v - 1) ∧
              countVals nums v ≤ countVals nums (v - 2)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every integer v, letting c(x) be the number of indices i with 0 <= i < len(nums) and nums[i] = x, if c(v-1) = 0 then c(v) <= c(v+1) and c(v) <= c(v+2).
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true →
        ∀ v : ℤ, countVals nums (v - 1) = 0 →
          countVals nums v ≤ countVals nums (v + 1) ∧
            countVals nums v ≤ countVals nums (v + 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true →
          ∀ v : ℤ, countVals nums (v - 1) = 0 →
            countVals nums v ≤ countVals nums (v + 1) ∧
              countVals nums v ≤ countVals nums (v + 2)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every integer v, c(v) <= c(v-1) + c(v+1), where c(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true →
        ∀ v : ℤ, countVals nums v ≤ countVals nums (v - 1) + countVals nums (v + 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true →
          ∀ v : ℤ, countVals nums v ≤ countVals nums (v - 1) + countVals nums (v + 1)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every integer v, c(v) <= floor(len(nums) / 3), where c(x) is the number of indices i with 0 <= i < len(nums) and nums[i] = x.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true →
        ∀ v : ℤ, countVals nums v ≤ nums.val.length / 3 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true →
          ∀ v : ℤ, countVals nums v ≤ nums.val.length / 3) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then every valid split of nums into consecutive increasing subsequences of length at least three has a number of parts m satisfying 1 <= m <= floor(len(nums) / 3).
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r → r = true →
        ∀ (m : ℕ) (blocks : Fin m → List (Fin nums.val.length)),
          IsRunPartition nums m blocks → 1 ≤ m ∧ m ≤ nums.val.length / 3 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r → r = true →
          ∀ (m : ℕ) (blocks : Fin m → List (Fin nums.val.length)),
            IsRunPartition nums m blocks → 1 ≤ m ∧ m ≤ nums.val.length / 3) := by
    sorry

  /-- Whenever the function returns a result r, if there exist integers a, L, and k with L >= 3 and k >= 1 such that, letting c(x) be the number of indices i with 0 <= i < len(nums) and nums[i] = x, c(x) = k for every integer x with a <= x < a + L and c(x) = 0 for every integer x not in the interval [a, a + L - 1], then r = true.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; and -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000) :
      ∀ r, is_possible nums = ok r →
        (∃ (a : ℤ) (L : ℤ) (k : ℕ),
          3 ≤ L ∧ 1 ≤ k ∧
            (∀ x : ℤ, a ≤ x → x < a + L → countVals nums x = k) ∧
            (∀ x : ℤ, ¬(a ≤ x ∧ x < a + L) → countVals nums x = 0)) →
        r = true := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000), ∀ r, is_possible nums = ok r →
          (∃ (a : ℤ) (L : ℤ) (k : ℕ),
            3 ≤ L ∧ 1 ≤ k ∧
              (∀ x : ℤ, a ≤ x → x < a + L → countVals nums x = k) ∧
              (∀ x : ℤ, ¬(a ≤ x ∧ x < a + L) → countVals nums x = 0)) →
          r = true) := by
    sorry

  /-- Let nums' be the slice of length len(nums) defined by nums'[i] = nums[i] + c for every i with 0 <= i < len(nums). Whenever the function returns a result r on nums and a result r' on nums', we have r = r'.
    Preconditions: nums is sorted in non-decreasing order; 1 <= len(nums) <= 10000; -1000 <= nums[i] <= 1000 for every i with 0 <= i < len(nums); and c is an integer with -1000 <= nums[i] + c <= 1000 for every i with 0 <= i < len(nums). -/
  theorem spec_12 (nums nums' : Slice Std.I64) (c : ℤ)
      (h_sorted : (vals nums).Pairwise (· ≤ ·))
      (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
      (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
      (h_shift_bound : ∀ (i : ℕ) (h : i < nums.val.length),
        -1000 ≤ (nums.val[i]'h).val + c ∧ (nums.val[i]'h).val + c ≤ 1000)
      (h_len' : nums'.val.length = nums.val.length)
      (h_shift : ∀ (i : ℕ) (h : i < nums.val.length),
        (nums'.val[i]'(by omega)).val = (nums.val[i]'h).val + c) :
      ∀ r r', is_possible nums = ok r → is_possible nums' = ok r' → r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
        (h_sorted : (vals nums).Pairwise (· ≤ ·))
        (h_len : 1 ≤ nums.val.length ∧ nums.val.length ≤ 10000)
        (h_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 1000)
        (h_shift_bound : ∀ (i : ℕ) (h : i < nums.val.length),
          -1000 ≤ (nums.val[i]'h).val + c ∧ (nums.val[i]'h).val + c ≤ 1000)
        (h_len' : nums'.val.length = nums.val.length)
        (h_shift : ∀ (i : ℕ) (h : i < nums.val.length),
          (nums'.val[i]'(by omega)).val = (nums.val[i]'h).val + c), ∀ r r', is_possible nums = ok r → is_possible nums' = ok r' → r = r') := by
    sorry

  end AegisSpec.IsPossible
