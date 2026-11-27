import Aegis.FindMatrix.Code.Funs

/-!
# Specifications of `Aegis.FindMatrix.find_matrix`

LeetCode problem `convert-an-array-into-a-2d-array-with-conditions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMatrix

  def rowContents (row : alloc.vec.Vec Std.I64) : List ℤ :=
    row.val.map (fun x => x.val)

  def rowsContents (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    r.val.map rowContents

  def numsContents (nums : Slice Std.I64) : List ℤ :=
    nums.val.map (fun x => x.val)

  def countOcc (l : List ℤ) (v : ℤ) : ℕ :=
    l.countP (fun x => decide (x = v))

  def maxcnt (l : List ℤ) : ℕ :=
    (l.map (fun v => countOcc l v)).foldr max 0

  def numDistinct (l : List ℤ) : ℕ :=
    l.dedup.length

  def rowsContaining (rows : List (List ℤ)) (v : ℤ) : ℕ :=
    rows.countP (fun row => decide (v ∈ row))

  /-- The function returns a result r. Let rows = r, define cnt(v) as the number of indices k with 0 <= k < len(nums) and nums[k] = v, and define maxcnt as the maximum of cnt(v) over all integers v with cnt(v) > 0. Then: (1) for every integer v, the number of pairs (i,j) with 0 <= i < len(rows), 0 <= j < len(rows[i]), and rows[i][j] = v is exactly cnt(v); (2) for every i with 0 <= i < len(rows), the entries of rows[i] are pairwise distinct, meaning rows[i][j] != rows[i][k] whenever 0 <= j < k < len(rows[i]); (3) len(rows) = maxcnt. Thus rows uses exactly the multiset of nums, every row has distinct integers, and the number of rows is minimal.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ)) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMatrix.find_matrix nums = ok r ∧
        (∀ v : ℤ,
          countOcc (rowsContents r).flatten v = countOcc (numsContents nums) v) ∧
        (∀ (i : ℕ) (hi : i < (rowsContents r).length)
           (j k : ℕ) (hjk : j < k) (hk : k < ((rowsContents r)[i]'hi).length),
          ((rowsContents r)[i]'hi)[j]'(by omega) ≠ ((rowsContents r)[i]'hi)[k]'hk) ∧
        (rowsContents r).length = maxcnt (numsContents nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMatrix.find_matrix nums = ok r ∧
          (∀ v : ℤ,
            countOcc (rowsContents r).flatten v = countOcc (numsContents nums) v) ∧
          (∀ (i : ℕ) (hi : i < (rowsContents r).length)
             (j k : ℕ) (hjk : j < k) (hk : k < ((rowsContents r)[i]'hi).length),
            ((rowsContents r)[i]'hi)[j]'(by omega) ≠ ((rowsContents r)[i]'hi)[k]'hk) ∧
          (rowsContents r).length = maxcnt (numsContents nums)) := by
    sorry

  /-- The function returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, panic, or other failure occurs).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ)) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMatrix.find_matrix nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMatrix.find_matrix nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, define cnt(v) as the number of indices k with 0 <= k < len(nums) and nums[k] = v, and define maxcnt as the maximum of cnt(v) over all integers v with cnt(v) > 0. Then len(r) = maxcnt.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      (rowsContents r).length = maxcnt (numsContents nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), (rowsContents r).length = maxcnt (numsContents nums)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the sum over i with 0 <= i < len(r) of the number of indices j with 0 <= j < len(r[i]) and r[i][j] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ v : ℤ,
        ((rowsContents r).map (fun row => countOcc row v)).sum
          = countOcc (numsContents nums) v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ v : ℤ,
          ((rowsContents r).map (fun row => countOcc row v)).sum
            = countOcc (numsContents nums) v) := by
    sorry

  /-- Whenever the function returns a result r, for every row index i with 0 <= i < len(r) and all column indices j,k with 0 <= j < k < len(r[i]), we have r[i][j] != r[i][k].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ (i : ℕ) (hi : i < (rowsContents r).length)
        (j k : ℕ) (hjk : j < k) (hk : k < ((rowsContents r)[i]'hi).length),
        ((rowsContents r)[i]'hi)[j]'(by omega) ≠ ((rowsContents r)[i]'hi)[k]'hk := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ (i : ℕ) (hi : i < (rowsContents r).length)
          (j k : ℕ) (hjk : j < k) (hk : k < ((rowsContents r)[i]'hi).length),
          ((rowsContents r)[i]'hi)[j]'(by omega) ≠ ((rowsContents r)[i]'hi)[k]'hk) := by
    sorry

  /-- Whenever the function returns a result r, the sum of the lengths of all rows equals len(nums): sum_{i=0}^{len(r)-1} len(r[i]) = len(nums).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ((rowsContents r).map List.length).sum = nums.val.length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ((rowsContents r).map List.length).sum = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, every row is nonempty: for every i with 0 <= i < len(r), len(r[i]) >= 1.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ (i : ℕ) (hi : i < (rowsContents r).length), 1 ≤ ((rowsContents r)[i]'hi).length := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ (i : ℕ) (hi : i < (rowsContents r).length), 1 ≤ ((rowsContents r)[i]'hi).length) := by
    sorry

  /-- Whenever the function returns a result r, every entry of every row is an element of nums: for every i,j with 0 <= i < len(r) and 0 <= j < len(r[i]), there exists k with 0 <= k < len(nums) and nums[k] = r[i][j].
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ (i : ℕ) (hi : i < (rowsContents r).length)
        (j : ℕ) (hj : j < ((rowsContents r)[i]'hi).length),
        ∃ (k : ℕ) (hk : k < (numsContents nums).length),
          (numsContents nums)[k]'hk = ((rowsContents r)[i]'hi)[j]'hj := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ (i : ℕ) (hi : i < (rowsContents r).length)
          (j : ℕ) (hj : j < ((rowsContents r)[i]'hi).length),
          ∃ (k : ℕ) (hk : k < (numsContents nums).length),
            (numsContents nums)[k]'hk = ((rowsContents r)[i]'hi)[j]'hj) := by
    sorry

  /-- Whenever the function returns a result r, the number of rows is between 1 and len(nums): 1 <= len(r) <= len(nums).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_9 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      1 ≤ (rowsContents r).length ∧ (rowsContents r).length ≤ nums.val.length := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), 1 ≤ (rowsContents r).length ∧ (rowsContents r).length ≤ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, let D be the number of distinct integers occurring in nums. Then every row has length at most D: for every i with 0 <= i < len(r), len(r[i]) <= D.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_10 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ (i : ℕ) (hi : i < (rowsContents r).length),
        ((rowsContents r)[i]'hi).length ≤ numDistinct (numsContents nums) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ (i : ℕ) (hi : i < (rowsContents r).length),
          ((rowsContents r)[i]'hi).length ≤ numDistinct (numsContents nums)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of occurrences of v in nums is at most len(r): the number of indices k with 0 <= k < len(nums) and nums[k] = v is <= len(r).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_11 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ v : ℤ, countOcc (numsContents nums) v ≤ (rowsContents r).length := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ v : ℤ, countOcc (numsContents nums) v ≤ (rowsContents r).length) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer v such that the number of indices k with 0 <= k < len(nums) and nums[k] = v equals len(r).
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_12 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∃ v : ℤ, countOcc (numsContents nums) v = (rowsContents r).length := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∃ v : ℤ, countOcc (numsContents nums) v = (rowsContents r).length) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of row indices i with 0 <= i < len(r) for which there exists j with 0 <= j < len(r[i]) and r[i][j] = v equals the number of indices k with 0 <= k < len(nums) and nums[k] = v.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 200, and for every index k with 0 <= k < len(nums), 1 <= nums[k] <= len(nums). -/
  theorem spec_13 (nums : Slice Std.I64)
      (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
      (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : Aegis.FindMatrix.find_matrix nums = ok r) :
      ∀ v : ℤ,
        rowsContaining (rowsContents r) v = countOcc (numsContents nums) v := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
        (h_range : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ (nums.val.length : ℤ))
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : Aegis.FindMatrix.find_matrix nums = ok r), ∀ v : ℤ,
          rowsContaining (rowsContents r) v = countOcc (numsContents nums) v) := by
    sorry

  end AegisSpec.FindMatrix
