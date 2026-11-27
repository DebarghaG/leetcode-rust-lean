import Aegis.MaximumDifference.Code.Funs

/-!
# Specifications of `Aegis.MaximumDifference.maximum_difference`

LeetCode problem `maximum-difference-between-increasing-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaximumDifference

  namespace AegisSpec.MaximumDifference

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr max x

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => xs.foldr min x

  def maxElem (nums : Slice Std.I64) : ℤ := listMax (vals nums)

  def minElem (nums : Slice Std.I64) : ℤ := listMin (vals nums)

  def HasAscent (nums : Slice Std.I64) : Prop :=
    ∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
      i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val

  /-- The function returns a result r (a 64-bit integer) and the following hold. If there exist indices i,j with 0 <= i < j < len(nums) and nums[i] < nums[j], then (a) there exist such indices i,j with r = nums[j] - nums[i], and (b) for every such pair i,j, nums[j] - nums[i] <= r. If no such pair i,j exists, then r = -1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∃ (r : Std.I64), maximum_difference nums = ok r ∧
        ((HasAscent nums →
            (∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
              i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
                r.val = (nums.val[j]'hj).val - (nums.val[i]'hi).val) ∧
            (∀ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
              i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
                (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ r.val)) ∧
          (¬ HasAscent nums → r.val = -1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∃ (r : Std.I64), maximum_difference nums = ok r ∧
          ((HasAscent nums →
              (∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
                i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
                  r.val = (nums.val[j]'hj).val - (nums.val[i]'hi).val) ∧
              (∀ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
                i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
                  (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ r.val)) ∧
            (¬ HasAscent nums → r.val = -1))) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∃ (r : Std.I64), maximum_difference nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∃ (r : Std.I64), maximum_difference nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= 999999999.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∀ (r : Std.I64), maximum_difference nums = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 999999999) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∀ (r : Std.I64), maximum_difference nums = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 999999999)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist indices i,j such that 0 <= i < j < len(nums), nums[i] < nums[j], and r = nums[j] - nums[i].
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
        ∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
          i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
            r.val = (nums.val[j]'hj).val - (nums.val[i]'hi).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
          ∃ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
            i < j ∧ (nums.val[i]'hi).val < (nums.val[j]'hj).val ∧
              r.val = (nums.val[j]'hj).val - (nums.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every pair of indices i,j with 0 <= i < j < len(nums) and nums[i] < nums[j], we have nums[j] - nums[i] <= r.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
        ∀ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
          i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
            (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
          ∀ (i : ℕ) (hi : i < nums.val.length) (j : ℕ) (hj : j < nums.val.length),
            i < j → (nums.val[i]'hi).val < (nums.val[j]'hj).val →
              (nums.val[j]'hj).val - (nums.val[i]'hi).val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there do not exist indices i,j with 0 <= i < j < len(nums) and nums[i] < nums[j].
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∀ (r : Std.I64), maximum_difference nums = ok r → (r.val = -1 ↔ ¬ HasAscent nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∀ (r : Std.I64), maximum_difference nums = ok r → (r.val = -1 ↔ ¬ HasAscent nums)) := by
    sorry

  /-- Whenever maximum_difference(nums) returns r and maximum_difference(s) returns r', we have r = r'.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. Let c be an integer and let s be a slice with len(s) = len(nums) and s[k] = nums[k] + c for every k; assume 2 <= len(s) <= 1000 and 1 <= s[k] <= 1000000000 for every k. -/
  theorem spec_7 (nums s : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000)
      (hslen : s.val.length = nums.val.length)
      (hsval : ∀ (k : ℕ) (hkn : k < nums.val.length) (hks : k < s.val.length),
        (s.val[k]'hks).val = (nums.val[k]'hkn).val + c)
      (hs2 : 2 ≤ s.val.length) (hs3 : s.val.length ≤ 1000)
      (hsbnd : ∀ (k : ℕ) (hk : k < s.val.length),
        1 ≤ (s.val[k]'hk).val ∧ (s.val[k]'hk).val ≤ 1000000000) :
      ∀ (r r' : Std.I64), maximum_difference nums = ok r → maximum_difference s = ok r' →
        r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums s : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000)
        (hslen : s.val.length = nums.val.length)
        (hsval : ∀ (k : ℕ) (hkn : k < nums.val.length) (hks : k < s.val.length),
          (s.val[k]'hks).val = (nums.val[k]'hkn).val + c)
        (hs2 : 2 ≤ s.val.length) (hs3 : s.val.length ≤ 1000)
        (hsbnd : ∀ (k : ℕ) (hk : k < s.val.length),
          1 ≤ (s.val[k]'hk).val ∧ (s.val[k]'hk).val ≤ 1000000000), ∀ (r r' : Std.I64), maximum_difference nums = ok r → maximum_difference s = ok r' →
          r = r') := by
    sorry

  /-- Whenever maximum_difference(nums) returns r and maximum_difference(s) returns r', then r = -1 if and only if r' = -1, and if r != -1 then r' = c * r.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. Let c be a positive integer and let s be a slice with len(s) = len(nums) and s[k] = c * nums[k] for every k; assume 2 <= len(s) <= 1000 and 1 <= s[k] <= 1000000000 for every k. -/
  theorem spec_8 (nums s : Slice Std.I64) (n : ℕ) (c : ℤ)
      (hcpos : 0 < c)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000)
      (hslen : s.val.length = nums.val.length)
      (hsval : ∀ (k : ℕ) (hkn : k < nums.val.length) (hks : k < s.val.length),
        (s.val[k]'hks).val = c * (nums.val[k]'hkn).val)
      (hs2 : 2 ≤ s.val.length) (hs3 : s.val.length ≤ 1000)
      (hsbnd : ∀ (k : ℕ) (hk : k < s.val.length),
        1 ≤ (s.val[k]'hk).val ∧ (s.val[k]'hk).val ≤ 1000000000) :
      ∀ (r r' : Std.I64), maximum_difference nums = ok r → maximum_difference s = ok r' →
        (r.val = -1 ↔ r'.val = -1) ∧ (r.val ≠ -1 → r'.val = c * r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums s : Slice Std.I64) (n : ℕ) (c : ℤ)
        (hcpos : 0 < c)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000)
        (hslen : s.val.length = nums.val.length)
        (hsval : ∀ (k : ℕ) (hkn : k < nums.val.length) (hks : k < s.val.length),
          (s.val[k]'hks).val = c * (nums.val[k]'hkn).val)
        (hs2 : 2 ≤ s.val.length) (hs3 : s.val.length ≤ 1000)
        (hsbnd : ∀ (k : ℕ) (hk : k < s.val.length),
          1 ≤ (s.val[k]'hk).val ∧ (s.val[k]'hk).val ≤ 1000000000), ∀ (r r' : Std.I64), maximum_difference nums = ok r → maximum_difference s = ok r' →
          (r.val = -1 ↔ r'.val = -1) ∧ (r.val ≠ -1 → r'.val = c * r.val)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r <= max(nums) - min(nums), where max(nums) is the largest element of nums and min(nums) is the smallest element of nums.
    Preconditions: len(nums) = n, 2 <= n <= 1000, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : ℕ)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
      (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
        1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000) :
      ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
        r.val ≤ maxElem nums - minElem nums := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn3 : n ≤ 1000)
        (hbnd : ∀ (k : ℕ) (hk : k < nums.val.length),
          1 ≤ (nums.val[k]'hk).val ∧ (nums.val[k]'hk).val ≤ 1000000000), ∀ (r : Std.I64), maximum_difference nums = ok r → r.val ≠ -1 →
          r.val ≤ maxElem nums - minElem nums) := by
    sorry

  end AegisSpec.MaximumDifference
