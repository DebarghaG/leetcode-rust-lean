import Aegis.SumImbalanceNumbers.Code.Funs

/-!
# Specifications of `Aegis.SumImbalanceNumbers.sum_imbalance_numbers`

LeetCode problem `sum-of-imbalance-numbers-of-all-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumImbalanceNumbers

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map fun x => x.val

  def sortedCopy (L : List ℤ) : List ℤ := List.insertionSort (· ≤ ·) L

  def imbalance (arr : List ℤ) : ℕ :=
    let s := sortedCopy arr
    ((List.range (arr.length - 1)).filter
      fun i => decide (1 < s.getD (i + 1) 0 - s.getD i 0)).length

  def subarray (L : List ℤ) (l u : ℕ) : List ℤ := (L.drop l).take (u + 1 - l)

  def totalImbalance (L : List ℤ) : ℤ :=
    Finset.sum (Finset.range L.length) fun l =>
      Finset.sum (Finset.Ico l L.length) fun u => (imbalance (subarray L l u) : ℤ)

  def gaps (L : List ℤ) : List ℤ := (L.zip L.tail).map fun p => p.2 - p.1

  def adjacentClose (L : List ℤ) : Prop := ∀ g ∈ gaps L, |g| ≤ 1

  def bigGapCount (L : List ℤ) : ℕ := (gaps L).countP fun g => decide (1 < |g|)

  def distinctCount (L : List ℤ) : ℕ := L.dedup.length

  def mixedIntervalCount (L : List ℤ) (a b : ℤ) : ℕ :=
    (((Finset.range L.length).product (Finset.range L.length)).filter
      fun p => p.1 ≤ p.2 ∧ a ∈ subarray L p.1 p.2 ∧ b ∈ subarray L p.1 p.2).card

  def ElemsInRange (nums : Slice Std.I64) : Prop :=
    ∀ z ∈ vals nums, 1 ≤ z ∧ z ≤ ((vals nums).length : ℤ)

  def PreWithMax (nums : Slice Std.I64) (maxN : ℕ) : Prop :=
    1 ≤ (vals nums).length ∧ (vals nums).length ≤ maxN ∧ ElemsInRange nums

  def Pre (nums : Slice Std.I64) : Prop := PreWithMax nums 1000

  /-- Whenever sum_imbalance_numbers(nums) returns a result r, r = sum over l from 0 to N-1 of sum over u from l to N-1 of I(nums[l..u]), where for a non-empty array arr of length m, I(arr) = #{ i | 0 <= i < m-1 and s[i+1] - s[i] > 1 }, and s is the nondecreasing sorted copy of arr. Here nums[l..u] is the contiguous subarray from index l through index u inclusive.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_1 (nums : Slice Std.I64) (hpre : Pre nums) :
      ∃ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r ∧
        r.val = totalImbalance (vals nums) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∃ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r ∧
          r.val = totalImbalance (vals nums)) := by
    sorry

  /-- For every nums satisfying the preconditions, sum_imbalance_numbers(nums) returns a result r; it does not fail with arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_2 (nums : Slice Std.I64) (hpre : Pre nums) :
      ∃ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∃ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r, 0 <= r <= N*(N-1)*(N+1)/6.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_3 (nums : Slice Std.I64) (hpre : Pre nums) :
      ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        0 ≤ r.val ∧
          r.val ≤ (((vals nums).length * ((vals nums).length - 1) *
            ((vals nums).length + 1) / 6 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          0 ≤ r.val ∧
            r.val ≤ (((vals nums).length * ((vals nums).length - 1) *
              ((vals nums).length + 1) / 6 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r, r = 0 if and only if for every i with 0 <= i < N-1, |nums[i+1] - nums[i]| <= 1.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_4 (nums : Slice Std.I64) (hpre : Pre nums) :
      ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        (r.val = 0 ↔ adjacentClose (vals nums)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          (r.val = 0 ↔ adjacentClose (vals nums))) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r, r >= #{ i | 0 <= i < N-1 and |nums[i+1] - nums[i]| > 1 }.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_5 (nums : Slice Std.I64) (hpre : Pre nums) :
      ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        (bigGapCount (vals nums) : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hpre : Pre nums), ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          (bigGapCount (vals nums) : ℤ) ≤ r.val) := by
    sorry

  /-- Let rev be the slice of length N with rev[i] = nums[N-1-i] for 0 <= i < N. Whenever sum_imbalance_numbers(nums) returns r and sum_imbalance_numbers(rev) returns r_rev, r = r_rev.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. -/
  theorem spec_6 (nums rev : Slice Std.I64) (hpre : Pre nums)
      (hrev : rev.val = nums.val.reverse) :
      ∀ r r_rev, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        Aegis.SumImbalanceNumbers.sum_imbalance_numbers rev = ok r_rev →
          r.val = r_rev.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums rev : Slice Std.I64) (hpre : Pre nums)
        (hrev : rev.val = nums.val.reverse), ∀ r r_rev, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          Aegis.SumImbalanceNumbers.sum_imbalance_numbers rev = ok r_rev →
            r.val = r_rev.val) := by
    sorry

  /-- Define shifted[i] = nums[i] + c for 0 <= i < N. Whenever sum_imbalance_numbers(nums) returns r and sum_imbalance_numbers(shifted) returns r_shifted, r = r_shifted.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. Let c be an integer such that for every i with 0 <= i < N, 1 <= nums[i] + c <= N. -/
  theorem spec_7 (nums shifted : Slice Std.I64) (c : ℤ) (hpre : Pre nums)
      (hc : ∀ z ∈ vals nums, 1 ≤ z + c ∧ z + c ≤ ((vals nums).length : ℤ))
      (hshift : vals shifted = (vals nums).map fun z => z + c) :
      ∀ r r_shifted, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        Aegis.SumImbalanceNumbers.sum_imbalance_numbers shifted = ok r_shifted →
          r.val = r_shifted.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums shifted : Slice Std.I64) (c : ℤ) (hpre : Pre nums)
        (hc : ∀ z ∈ vals nums, 1 ≤ z + c ∧ z + c ≤ ((vals nums).length : ℤ))
        (hshift : vals shifted = (vals nums).map fun z => z + c), ∀ r r_shifted, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          Aegis.SumImbalanceNumbers.sum_imbalance_numbers shifted = ok r_shifted →
            r.val = r_shifted.val) := by
    sorry

  /-- Define refl[i] = C - nums[i] for 0 <= i < N. Whenever sum_imbalance_numbers(nums) returns r and sum_imbalance_numbers(refl) returns r_refl, r = r_refl.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. Let C be an integer such that for every i with 0 <= i < N, 1 <= C - nums[i] <= N. -/
  theorem spec_8 (nums refl : Slice Std.I64) (C : ℤ) (hpre : Pre nums)
      (hC : ∀ z ∈ vals nums, 1 ≤ C - z ∧ C - z ≤ ((vals nums).length : ℤ))
      (hreflect : vals refl = (vals nums).map fun z => C - z) :
      ∀ r r_refl, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        Aegis.SumImbalanceNumbers.sum_imbalance_numbers refl = ok r_refl →
          r.val = r_refl.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums refl : Slice Std.I64) (C : ℤ) (hpre : Pre nums)
        (hC : ∀ z ∈ vals nums, 1 ≤ C - z ∧ C - z ≤ ((vals nums).length : ℤ))
        (hreflect : vals refl = (vals nums).map fun z => C - z), ∀ r r_refl, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          Aegis.SumImbalanceNumbers.sum_imbalance_numbers refl = ok r_refl →
            r.val = r_refl.val) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r and sum_imbalance_numbers(ext) returns r_ext, r_ext >= r.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 999, and for every i with 0 <= i < N, 1 <= nums[i] <= N. Let x be an integer with 1 <= x <= N+1. Define ext of length N+1 by ext[i] = nums[i] for 0 <= i < N and ext[N] = x. -/
  theorem spec_9 (nums ext : Slice Std.I64) (x : ℤ) (hpre : PreWithMax nums 999)
      (hx : 1 ≤ x ∧ x ≤ ((vals nums).length : ℤ) + 1)
      (hext : vals ext = vals nums ++ [x]) :
      ∀ r r_ext, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        Aegis.SumImbalanceNumbers.sum_imbalance_numbers ext = ok r_ext →
          r.val ≤ r_ext.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums ext : Slice Std.I64) (x : ℤ) (hpre : PreWithMax nums 999)
        (hx : 1 ≤ x ∧ x ≤ ((vals nums).length : ℤ) + 1)
        (hext : vals ext = vals nums ++ [x]), ∀ r r_ext, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          Aegis.SumImbalanceNumbers.sum_imbalance_numbers ext = ok r_ext →
            r.val ≤ r_ext.val) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r: if |a-b| <= 1 then r = 0; if |a-b| > 1 then r = #{ (l,u) | 0 <= l <= u < N, there exists i with l <= i <= u and nums[i] = a, and there exists j with l <= j <= u and nums[j] = b }.
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. Let a and b be integers such that for every i with 0 <= i < N, nums[i] = a or nums[i] = b. -/
  theorem spec_10 (nums : Slice Std.I64) (a b : ℤ) (hpre : Pre nums)
      (hab : ∀ z ∈ vals nums, z = a ∨ z = b) :
      ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        (|a - b| ≤ 1 → r.val = 0) ∧
          (1 < |a - b| → r.val = (mixedIntervalCount (vals nums) a b : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (a b : ℤ) (hpre : Pre nums)
        (hab : ∀ z ∈ vals nums, z = a ∨ z = b), ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          (|a - b| ≤ 1 → r.val = 0) ∧
            (1 < |a - b| → r.val = (mixedIntervalCount (vals nums) a b : ℤ))) := by
    sorry

  /-- Whenever sum_imbalance_numbers(nums) returns r, r <= (N*(N+1)/2) * (D-1).
    Preconditions: Let N = len(nums). N is an integer with 1 <= N <= 1000, and for every i with 0 <= i < N, 1 <= nums[i] <= N. Let D be the number of distinct values occurring among nums[0],...,nums[N-1]. -/
  theorem spec_11 (nums : Slice Std.I64) (D : ℕ) (hpre : Pre nums)
      (hD : D = distinctCount (vals nums)) :
      ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
        r.val ≤ (((vals nums).length * ((vals nums).length + 1) / 2 : ℕ) : ℤ) *
          ((D : ℤ) - 1) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (D : ℕ) (hpre : Pre nums)
        (hD : D = distinctCount (vals nums)), ∀ r, Aegis.SumImbalanceNumbers.sum_imbalance_numbers nums = ok r →
          r.val ≤ (((vals nums).length * ((vals nums).length + 1) / 2 : ℕ) : ℤ) *
            ((D : ℤ) - 1)) := by
    sorry

  end AegisSpec.SumImbalanceNumbers
