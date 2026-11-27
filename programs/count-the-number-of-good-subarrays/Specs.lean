import Aegis.CountGood.Code.Funs

/-!
# Specifications of `Aegis.CountGood.count_good`

LeetCode problem `count-the-number-of-good-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountGood

namespace AegisSpec.CountGood

def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def pairCount (l : List Int) (a b : Nat) : Nat :=
  (((Finset.range b).product (Finset.range b)).filter
      (fun p : Nat × Nat =>
        a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < l.length ∧ l[p.1]? = l[p.2]?)).card

def goodSet (l : List Int) (k : Int) : Finset (Nat × Nat) :=
  ((Finset.range (l.length + 1)).product (Finset.range (l.length + 1))).filter
    (fun p : Nat × Nat => p.1 < p.2 ∧ k ≤ (pairCount l p.1 p.2 : Int))

def goodCount (l : List Int) (k : Int) : Nat := (goodSet l k).card

def startSet (l : List Int) (k : Int) : Finset Nat :=
  (Finset.range l.length).filter (fun i => k ≤ (pairCount l i l.length : Int))

def startCount (l : List Int) (k : Int) : Nat := (startSet l k).card

def sizeBound (n : Nat) (k : Int) : Nat :=
  Finset.sum (Finset.Icc 1 n)
    (fun L => if k ≤ ((L * (L - 1) / 2 : Nat) : Int) then (n - L + 1) else 0)

def revSlice (s : Slice Std.I64) : Slice Std.I64 :=
  Slice.from s.val.reverse (by simp)

theorem revSlice_val (s : Slice Std.I64) : (revSlice s).val = s.val.reverse := by
  simp [revSlice]

theorem vals_length (s : Slice Std.I64) : (vals s).length = s.val.length := by
  simp [vals]

/-- The function returns a result ans and, interpreting ans as a mathematical integer, ans = # { (l,u) | 0 <= l < u <= len(nums) and P(nums,l,u) >= k }, where for 0 <= l <= u <= len(nums), P(nums,l,u) = # { (i,j) | l <= i < j < u and nums[i] = nums[j] }. Thus ans is exactly the number of non-empty contiguous subarrays nums[l],...,nums[u-1] whose number of equal-value index pairs is at least k.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∃ r, count_good nums k = ok r ∧ r.val = (goodCount (vals nums) k.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∃ r, count_good nums k = ok r ∧ r.val = (goodCount (vals nums) k.val : Int)) := by
  sorry

/-- Whenever the function returns ans, 0 <= ans <= len(nums)*(len(nums)+1)/2.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r, count_good nums k = ok r →
      0 ≤ r.val ∧
        r.val ≤ (((nums.val.length * (nums.val.length + 1)) / 2 : Nat) : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, count_good nums k = ok r →
      0 ≤ r.val ∧
        r.val ≤ (((nums.val.length * (nums.val.length + 1)) / 2 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns ans, ans <= sum_{L=1}^{len(nums)} I(L), where I(L) = len(nums)-L+1 if L*(L-1)/2 >= k, and I(L) = 0 otherwise.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r, count_good nums k = ok r → r.val ≤ (sizeBound nums.val.length k.val : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, count_good nums k = ok r → r.val ≤ (sizeBound nums.val.length k.val : Int)) := by
  sorry

/-- Whenever the function returns ans, if k > P(nums,0,len(nums)) then ans = 0, where P(nums,0,len(nums)) = # { (i,j) | 0 <= i < j < len(nums) and nums[i] = nums[j] }.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r, count_good nums k = ok r →
      k.val > (pairCount (vals nums) 0 nums.val.length : Int) → r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, count_good nums k = ok r →
      k.val > (pairCount (vals nums) 0 nums.val.length : Int) → r.val = 0) := by
  sorry

/-- For any slice nums2 with len(nums2) = len(nums), each nums2[i] in [1,1000000000], and with nums[i] = nums[j] if and only if nums2[i] = nums2[j] for all 0 <= i,j < len(nums), if count_good(nums,k) returns ans1 and count_good(nums2,k) returns ans2, then ans1 = ans2.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_5 (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len : nums2.val.length = nums.val.length)
    (h2range : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 1000000000)
    (h2eq : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length)
      (hi2 : i < nums2.val.length) (hj2 : j < nums2.val.length),
      ((nums.val[i]'hi).val = (nums.val[j]'hj).val ↔
        (nums2.val[i]'hi2).val = (nums2.val[j]'hj2).val)) :
    ∀ r1 r2, count_good nums k = ok r1 → count_good nums2 k = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len : nums2.val.length = nums.val.length)
    (h2range : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 1000000000)
    (h2eq : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length)
      (hi2 : i < nums2.val.length) (hj2 : j < nums2.val.length),
      ((nums.val[i]'hi).val = (nums.val[j]'hj).val ↔
        (nums2.val[i]'hi2).val = (nums2.val[j]'hj2).val)), ∀ r1 r2, count_good nums k = ok r1 → count_good nums2 k = ok r2 → r1.val = r2.val) := by
  sorry

/-- Let rev(nums) be the slice of length len(nums) with rev(nums)[i] = nums[len(nums)-1-i] for 0 <= i < len(nums). If count_good(nums,k) returns ans1 and count_good(rev(nums),k) returns ans2, then ans1 = ans2.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r1 r2, count_good nums k = ok r1 → count_good (revSlice nums) k = ok r2 →
      r1.val = r2.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r1 r2, count_good nums k = ok r1 → count_good (revSlice nums) k = ok r2 →
      r1.val = r2.val) := by
  sorry

/-- For any k1,k2 with 1 <= k1 <= k2 <= 1000000000, if count_good(nums,k1) returns ans1 and count_good(nums,k2) returns ans2, then ans1 >= ans2.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000) :
    ∀ r1 r2, count_good nums k1 = ok r1 → count_good nums k2 = ok r2 → r1.val ≥ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000), ∀ r1 r2, count_good nums k1 = ok r1 → count_good nums k2 = ok r2 → r1.val ≥ r2.val) := by
  sorry

/-- For any integer x with 1 <= x <= 1000000000 and with len(nums) < 100000, let ext be the slice of length len(nums)+1 with ext[i] = nums[i] for 0 <= i < len(nums) and ext[len(nums)] = x. If count_good(nums,k) returns ans and count_good(ext,k) returns ans_ext, then ans <= ans_ext.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_8 (nums ext : Slice Std.I64) (k x : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums.val.length < 100000)
    (hext : ext.val = nums.val ++ [x]) :
    ∀ r r', count_good nums k = ok r → count_good ext k = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums ext : Slice Std.I64) (k x : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums.val.length < 100000)
    (hext : ext.val = nums.val ++ [x]), ∀ r r', count_good nums k = ok r → count_good ext k = ok r' → r.val ≤ r'.val) := by
  sorry

/-- For any integer x with 1 <= x <= 1000000000 and len(nums) < 100000 such that x != nums[i] for every 0 <= i < len(nums), let ext be the slice of length len(nums)+1 with ext[i] = nums[i] for 0 <= i < len(nums) and ext[len(nums)] = x. Let S = # { l | 0 <= l < len(nums) and P(nums,l,len(nums)) >= k }, where P(nums,l,len(nums)) = # { (i,j) | l <= i < j < len(nums) and nums[i] = nums[j] }. If count_good(nums,k) returns ans and count_good(ext,k) returns ans_ext, then ans_ext = ans + S.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_9 (nums ext : Slice Std.I64) (k x : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums.val.length < 100000)
    (hxne : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ x.val)
    (hext : ext.val = nums.val ++ [x]) :
    ∀ r r', count_good nums k = ok r → count_good ext k = ok r' →
      r'.val = r.val + (startCount (vals nums) k.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums ext : Slice Std.I64) (k x : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 1000000000)
    (hlen : nums.val.length < 100000)
    (hxne : ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]'hi).val ≠ x.val)
    (hext : ext.val = nums.val ++ [x]), ∀ r r', count_good nums k = ok r → count_good ext k = ok r' →
      r'.val = r.val + (startCount (vals nums) k.val : Int)) := by
  sorry

/-- Whenever the function returns ans, ans >= # { l | 0 <= l < len(nums) and P(nums,l,len(nums)) >= k }, where P(nums,l,len(nums)) = # { (i,j) | l <= i < j < len(nums) and nums[i] = nums[j] }.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r, count_good nums k = ok r →
      r.val ≥ (startCount (vals nums) k.val : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, count_good nums k = ok r →
      r.val ≥ (startCount (vals nums) k.val : Int)) := by
  sorry

/-- Let nums2 be a non-empty contiguous subarray of nums: 1 <= len(nums2) <= len(nums) and there is an s with 0 <= s <= len(nums)-len(nums2) such that nums2[i] = nums[s+i] for all 0 <= i < len(nums2). If count_good(nums2,k) returns ans2 and count_good(nums,k) returns ans, then ans2 <= ans.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_11 (nums nums2 : Slice Std.I64) (k : Std.I64) (s : Nat)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len1 : 1 ≤ nums2.val.length) (h2len2 : nums2.val.length ≤ nums.val.length)
    (hs : s + nums2.val.length ≤ nums.val.length)
    (hsub : ∀ (i : Nat) (hi : i < nums2.val.length) (hi' : s + i < nums.val.length),
      (nums2.val[i]'hi).val = (nums.val[s + i]'hi').val) :
    ∀ r2 r, count_good nums2 k = ok r2 → count_good nums k = ok r → r2.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64) (s : Nat)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len1 : 1 ≤ nums2.val.length) (h2len2 : nums2.val.length ≤ nums.val.length)
    (hs : s + nums2.val.length ≤ nums.val.length)
    (hsub : ∀ (i : Nat) (hi : i < nums2.val.length) (hi' : s + i < nums.val.length),
      (nums2.val[i]'hi).val = (nums.val[s + i]'hi').val), ∀ r2 r, count_good nums2 k = ok r2 → count_good nums k = ok r → r2.val ≤ r.val) := by
  sorry

/-- Whenever the function returns ans, ans = 0 if and only if for every 0 <= i < j < len(nums), nums[i] != nums[j].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and k = 1. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : k.val = 1) :
    ∀ r, count_good nums k = ok r →
      (r.val = 0 ↔ ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → (nums.val[i]'hi).val ≠ (nums.val[j]'hj).val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk : k.val = 1), ∀ r, count_good nums k = ok r →
      (r.val = 0 ↔ ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → (nums.val[i]'hi).val ≠ (nums.val[j]'hj).val)) := by
  sorry

/-- Let nums2 be any slice with len(nums2) = len(nums), each nums2[i] in [1,1000000000], and for all 0 <= i,j < len(nums), if nums[i] = nums[j] then nums2[i] = nums2[j]. If count_good(nums,k) returns ans and count_good(nums2,k) returns ans2, then ans2 >= ans.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_13 (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len : nums2.val.length = nums.val.length)
    (h2range : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 1000000000)
    (h2eq : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length)
      (hi2 : i < nums2.val.length) (hj2 : j < nums2.val.length),
      (nums.val[i]'hi).val = (nums.val[j]'hj).val →
        (nums2.val[i]'hi2).val = (nums2.val[j]'hj2).val) :
    ∀ r r2, count_good nums k = ok r → count_good nums2 k = ok r2 → r2.val ≥ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
    (h2len : nums2.val.length = nums.val.length)
    (h2range : ∀ (i : Nat) (hi : i < nums2.val.length),
      1 ≤ (nums2.val[i]'hi).val ∧ (nums2.val[i]'hi).val ≤ 1000000000)
    (h2eq : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length)
      (hi2 : i < nums2.val.length) (hj2 : j < nums2.val.length),
      (nums.val[i]'hi).val = (nums.val[j]'hj).val →
        (nums2.val[i]'hi2).val = (nums2.val[j]'hj2).val), ∀ r r2, count_good nums k = ok r → count_good nums2 k = ok r2 → r2.val ≥ r.val) := by
  sorry

/-- Whenever the function returns ans, ans = 0 if and only if k > P(nums,0,len(nums)), where P(nums,0,len(nums)) = # { (i,j) | 0 <= i < j < len(nums) and nums[i] = nums[j] }. Equivalently, ans >= 1 if and only if the whole array nums is good, i.e. k <= P(nums,0,len(nums)).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000, and 1 <= k <= 1000000000. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
    ∀ r, count_good nums k = ok r →
      (r.val = 0 ↔ k.val > (pairCount (vals nums) 0 nums.val.length : Int)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000000000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, count_good nums k = ok r →
      (r.val = 0 ↔ k.val > (pairCount (vals nums) 0 nums.val.length : Int))) := by
  sorry

end AegisSpec.CountGood
