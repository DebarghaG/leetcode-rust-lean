import Aegis.LengthAfterTransformations.Code.Funs

/-!
# Specifications of `Aegis.LengthAfterTransformations.length_after_transformations`

LeetCode problem `total-characters-in-string-after-transformations-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LengthAfterTransformations

namespace AegisSpec.LengthAfterTransformations

def M : ℤ := 1000000007

def sumRange (m : ℕ) (f : ℕ → ℤ) : ℤ := ((List.range m).map (fun j => f (j + 1))).sum

def numsList (nums : Slice Std.I64) : List ℤ := nums.val.map (fun v => v.val)

def F (nums : List ℤ) : ℕ → ℕ → ℤ
  | _, 0 => 1
  | c, k + 1 => sumRange (nums.getD c 0).toNat (fun j => F nums ((c + j) % 26) k)

def countOf (l : List Std.U8) (c : ℕ) : ℕ := (l.filter (fun b => b.val = 97 + c)).length

def total (s : List Std.U8) (nums : List ℤ) (k : ℕ) : ℤ :=
  (s.map (fun b => F nums (b.val - 97) k)).sum

def totalByCounts (s : List Std.U8) (nums : List ℤ) (k : ℕ) : ℤ :=
  ((List.range 26).map (fun c => (countOf s c : ℤ) * F nums c k)).sum

/-- Whenever the function returns a result r, r = (sum_{i=0}^{len(s)-1} F(s[i] - 97, t)) mod (10^9 + 7), where for any integer c with 0 <= c < 26 and integer k >= 0, F(c, k) is defined recursively by F(c, 0) = 1 and F(c, k+1) = sum_{j=1}^{nums[c]} F((c + j) mod 26, k). Here (c + j) mod 26 denotes the remainder of c + j divided by 26, which lies in 0..25.
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25. -/
theorem spec_1
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (r : Std.I64) (hr : length_after_transformations s t nums = ok r) :
    r.val = total s.val (numsList nums) t.val.toNat % M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (r : Std.I64) (hr : length_after_transformations s t nums = ok r), r.val = total s.val (numsList nums) t.val.toNat % M) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 10^9 + 6.
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25. -/
theorem spec_2
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (r : Std.I64) (hr : length_after_transformations s t nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ 1000000006 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (r : Std.I64) (hr : length_after_transformations s t nums = ok r), 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
  sorry

/-- The function returns a result r (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25. -/
theorem spec_3
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25) :
    ∃ r : Std.I64, length_after_transformations s t nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25), ∃ r : Std.I64, length_after_transformations s t nums = ok r) := by
  sorry

/-- The function returns a result r and r = (sum_{i=0}^{len(s)-1} nums[s[i] - 97]) mod (10^9 + 7).
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; t = 1; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25. -/
theorem spec_4
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000) (ht_one : t.val = 1)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25) :
    ∃ r : Std.I64, length_after_transformations s t nums = ok r ∧
      r.val = (s.val.map (fun b => (numsList nums).getD (b.val - 97) 0)).sum % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000) (ht_one : t.val = 1)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25), ∃ r : Std.I64, length_after_transformations s t nums = ok r ∧
      r.val = (s.val.map (fun b => (numsList nums).getD (b.val - 97) 0)).sum % M) := by
  sorry

/-- The function returns a result r and r = len(s) mod (10^9 + 7).
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, nums[j] = 1 (which implies 1 <= nums[j] <= 25). -/
theorem spec_5
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_one : ∀ (j : ℕ) (h : j < nums.val.length), (nums.val[j]'h).val = 1) :
    ∃ r : Std.I64, length_after_transformations s t nums = ok r ∧
      r.val = (s.val.length : ℤ) % M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_one : ∀ (j : ℕ) (h : j < nums.val.length), (nums.val[j]'h).val = 1), ∃ r : Std.I64, length_after_transformations s t nums = ok r ∧
      r.val = (s.val.length : ℤ) % M) := by
  sorry

/-- Let r be the result of the function on s1 ++ s2, let r1 be the result on s1, and let r2 be the result on s2 (all with the same t and nums). Then the function returns r, r1, r2 and r = (r1 + r2) mod (10^9 + 7).
  Preconditions: For every t and nums satisfying 1 <= t <= 10^9, len(nums) == 26, and for every j with 0 <= j < 26, 1 <= nums[j] <= 25, and for every two non-empty strings s1 and s2 with len(s1) + len(s2) <= 10^5, for every i with 0 <= i < len(s1), 97 <= s1[i] <= 122, and for every i with 0 <= i < len(s2), 97 <= s2[i] <= 122: -/
theorem spec_6
    (s s1 s2 : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs1_pos : 1 ≤ s1.val.length) (hs2_pos : 1 ≤ s2.val.length)
    (hs_len : s1.val.length + s2.val.length ≤ 100000)
    (hs1_chars : ∀ (i : ℕ) (h : i < s1.val.length),
      97 ≤ (s1.val[i]'h).val ∧ (s1.val[i]'h).val ≤ 122)
    (hs2_chars : ∀ (i : ℕ) (h : i < s2.val.length),
      97 ≤ (s2.val[i]'h).val ∧ (s2.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hs : s.val = s1.val ++ s2.val) :
    ∃ r r1 r2 : Std.I64,
      length_after_transformations s t nums = ok r ∧
      length_after_transformations s1 t nums = ok r1 ∧
      length_after_transformations s2 t nums = ok r2 ∧
      r.val = (r1.val + r2.val) % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s s1 s2 : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs1_pos : 1 ≤ s1.val.length) (hs2_pos : 1 ≤ s2.val.length)
    (hs_len : s1.val.length + s2.val.length ≤ 100000)
    (hs1_chars : ∀ (i : ℕ) (h : i < s1.val.length),
      97 ≤ (s1.val[i]'h).val ∧ (s1.val[i]'h).val ≤ 122)
    (hs2_chars : ∀ (i : ℕ) (h : i < s2.val.length),
      97 ≤ (s2.val[i]'h).val ∧ (s2.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hs : s.val = s1.val ++ s2.val), ∃ r r1 r2 : Std.I64,
      length_after_transformations s t nums = ok r ∧
      length_after_transformations s1 t nums = ok r1 ∧
      length_after_transformations s2 t nums = ok r2 ∧
      r.val = (r1.val + r2.val) % M) := by
  sorry

/-- Let r1 be the result of the function on s1 and r2 be the result on s2, both with the same t and nums. If for every c in 0..25 the number of occurrences of the byte 97+c in s1 equals the number of occurrences of 97+c in s2, then the function returns r1 and r2 and r1 = r2.
  Preconditions: For every t and nums satisfying 1 <= t <= 10^9, len(nums) == 26, and for every j with 0 <= j < 26, 1 <= nums[j] <= 25, and for every two strings s1 and s2 with 1 <= len(s1) <= 10^5, 1 <= len(s2) <= 10^5, for every i with 0 <= i < len(s1), 97 <= s1[i] <= 122, and for every i with 0 <= i < len(s2), 97 <= s2[i] <= 122: -/
theorem spec_7
    (s1 s2 : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs1_pos : 1 ≤ s1.val.length) (hs1_le : s1.val.length ≤ 100000)
    (hs2_pos : 1 ≤ s2.val.length) (hs2_le : s2.val.length ≤ 100000)
    (hs1_chars : ∀ (i : ℕ) (h : i < s1.val.length),
      97 ≤ (s1.val[i]'h).val ∧ (s1.val[i]'h).val ≤ 122)
    (hs2_chars : ∀ (i : ℕ) (h : i < s2.val.length),
      97 ≤ (s2.val[i]'h).val ∧ (s2.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hcounts : ∀ c : ℕ, c < 26 → countOf s1.val c = countOf s2.val c) :
    ∃ r1 r2 : Std.I64,
      length_after_transformations s1 t nums = ok r1 ∧
      length_after_transformations s2 t nums = ok r2 ∧
      r1.val = r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 s2 : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs1_pos : 1 ≤ s1.val.length) (hs1_le : s1.val.length ≤ 100000)
    (hs2_pos : 1 ≤ s2.val.length) (hs2_le : s2.val.length ≤ 100000)
    (hs1_chars : ∀ (i : ℕ) (h : i < s1.val.length),
      97 ≤ (s1.val[i]'h).val ∧ (s1.val[i]'h).val ≤ 122)
    (hs2_chars : ∀ (i : ℕ) (h : i < s2.val.length),
      97 ≤ (s2.val[i]'h).val ∧ (s2.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hcounts : ∀ c : ℕ, c < 26 → countOf s1.val c = countOf s2.val c), ∃ r1 r2 : Std.I64,
      length_after_transformations s1 t nums = ok r1 ∧
      length_after_transformations s2 t nums = ok r2 ∧
      r1.val = r2.val) := by
  sorry

/-- Let r1 be the result of the function on the string consisting of a single copy of c (with the same t and nums). Then the function returns a result r on s and r = (n * r1) mod (10^9 + 7).
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25; there exists a character c with 97 <= c <= 122 and an integer n >= 1 such that s is the list of length n where every element equals c. -/
theorem spec_8
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (c : Std.U8) (hc_lower : 97 ≤ c.val) (hc_upper : c.val ≤ 122)
    (n : ℕ) (hn : 1 ≤ n) (hs : s.val = List.replicate n c)
    (s1 : Slice Std.U8) (hs1 : s1.val = [c]) (r1 : Std.I64)
    (hr1 : length_after_transformations s1 t nums = ok r1) :
    ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = ((n : ℤ) * r1.val) % M := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (c : Std.U8) (hc_lower : 97 ≤ c.val) (hc_upper : c.val ≤ 122)
    (n : ℕ) (hn : 1 ≤ n) (hs : s.val = List.replicate n c)
    (s1 : Slice Std.U8) (hs1 : s1.val = [c]) (r1 : Std.I64)
    (hr1 : length_after_transformations s1 t nums = ok r1), ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = ((n : ℤ) * r1.val) % M) := by
  sorry

/-- The function returns a result r and r = (sum_{j=1}^{nums[s[0] - 97]} nums[(s[0] - 97 + j) mod 26]) mod (10^9 + 7).
  Preconditions: len(s) >= 1; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25; t = 2; len(s) = 1. -/
theorem spec_9
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000) (ht_two : t.val = 2)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hs_len : s.val.length = 1) (b : Std.U8) (hs : s.val = [b]) :
    ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = sumRange ((numsList nums).getD (b.val - 97) 0).toNat
        (fun j => (numsList nums).getD ((b.val - 97 + j) % 26) 0) % M := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000) (ht_two : t.val = 2)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25)
    (hs_len : s.val.length = 1) (b : Std.U8) (hs : s.val = [b]), ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = sumRange ((numsList nums).getD (b.val - 97) 0).toNat
        (fun j => (numsList nums).getD ((b.val - 97 + j) % 26) 0) % M) := by
  sorry

/-- Let count_s(c) be the number of indices i with 0 <= i < len(s) such that s[i] = 97 + c. The function returns a result r and r = (sum_{c=0}^{25} count_s(c) * F(c, t)) mod (10^9 + 7), where F is defined as in spec_1: F(c, 0) = 1 and F(c, k+1) = sum_{j=1}^{nums[c]} F((c + j) mod 26, k).
  Preconditions: 1 <= len(s) <= 10^5; for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s[i] is the ASCII code of a lowercase English letter); 1 <= t <= 10^9; len(nums) == 26; for every j with 0 <= j < 26, 1 <= nums[j] <= 25. -/
theorem spec_10
    (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25) :
    ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = totalByCounts s.val (numsList nums) t.val.toNat % M := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (t : Std.I64) (nums : Slice Std.I64)
    (hs_pos : 1 ≤ s.val.length) (hs_le : s.val.length ≤ 100000)
    (hs_chars : ∀ (i : ℕ) (h : i < s.val.length),
      97 ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ 122)
    (ht_pos : 1 ≤ t.val) (ht_le : t.val ≤ 1000000000)
    (hnums_len : nums.val.length = 26)
    (hnums_bounds : ∀ (j : ℕ) (h : j < nums.val.length),
      1 ≤ (nums.val[j]'h).val ∧ (nums.val[j]'h).val ≤ 25), ∃ r : Std.I64,
      length_after_transformations s t nums = ok r ∧
      r.val = totalByCounts s.val (numsList nums) t.val.toNat % M) := by
  sorry

end AegisSpec.LengthAfterTransformations
