import Aegis.MinSwaps.Code.Funs

/-!
# Specifications of `Aegis.MinSwaps.min_swaps`

LeetCode problem `minimum-swaps-to-group-all-1s-together`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinSwaps

  namespace AegisSpec.MinSwaps

  def IsBitList (l : List Std.I64) : Prop :=
    ∀ (i : ℕ) (x : Std.I64), l[i]? = some x → x.val = 0 ∨ x.val = 1

  def countOnes (l : List Std.I64) : ℕ :=
    l.countP (fun x => decide (x.val = 1))

  def zerosInWindow (l : List Std.I64) (s k : ℕ) : ℕ :=
    ((l.drop s).take k).countP (fun x => decide (x.val = 0))

  def onesInWindow (l : List Std.I64) (s k : ℕ) : ℕ :=
    ((l.drop s).take k).countP (fun x => decide (x.val = 1))

  noncomputable def minZerosWindow (l : List Std.I64) (k : ℕ) : ℕ :=
    (Finset.range (l.length - k + 1)).inf' ⟨0, by simp⟩ (fun s => zerosInWindow l s k)

  noncomputable def maxOnesWindow (l : List Std.I64) (k : ℕ) : ℕ :=
    (Finset.range (l.length - k + 1)).sup' ⟨0, by simp⟩ (fun s => onesInWindow l s k)

  def windowIsExactOnes (l : List Std.I64) (s k : ℕ) : Prop :=
    ∀ (i : ℕ) (x : Std.I64), l[i]? = some x → (x.val = 1 ↔ s ≤ i ∧ i < s + k)

  def IsFirstOne (l : List Std.I64) (a : ℕ) : Prop :=
    (∃ x, l[a]? = some x ∧ x.val = 1) ∧
      ∀ (j : ℕ), j < a → ∀ x, l[j]? = some x → x.val ≠ 1

  def IsLastOne (l : List Std.I64) (b : ℕ) : Prop :=
    (∃ x, l[b]? = some x ∧ x.val = 1) ∧
      ∀ (j : ℕ), b < j → ∀ x, l[j]? = some x → x.val ≠ 1

  /-- Let k be the number of indices i with 0 <= i < n and data[i] = 1. For each integer s with 0 <= s <= n-k, define Z(s) to be the number of indices i such that s <= i < s+k and data[i] = 0; when k = 0, set Z(s) = 0 for every such s. The function returns a result r and r = min { Z(s) | 0 <= s <= n-k }.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_1 (data : Slice Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) :
      ∃ r, min_swaps data = ok r ∧
        r.val = ((minZerosWindow data.val (countOnes data.val)) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (data : Slice Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val), ∃ r, min_swaps data = ok r ∧
          r.val = ((minZerosWindow data.val (countOnes data.val)) : ℤ)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_2 (data : Slice Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) :
      ∃ r, min_swaps data = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (data : Slice Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val), ∃ r, min_swaps data = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_3 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= k, where k is the number of indices i with 0 <= i < n and data[i] = 1.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_4 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      r.val ≤ ((countOnes data.val : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), r.val ≤ ((countOnes data.val : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= n-k, where k is the number of indices i with 0 <= i < n and data[i] = 1.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_5 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      r.val ≤ (((data.val.length - countOnes data.val : ℕ)) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), r.val ≤ (((data.val.length - countOnes data.val : ℕ)) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exists an integer s with 0 <= s <= n-k such that for every i with 0 <= i < n, data[i] = 1 exactly when s <= i < s+k, where k is the number of indices i with data[i] = 1. For k = 0 this says all entries are 0.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_6 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      (r.val = 0 ↔ ∃ s, s ≤ data.val.length - countOnes data.val ∧
        windowIsExactOnes data.val s (countOnes data.val)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), (r.val = 0 ↔ ∃ s, s ≤ data.val.length - countOnes data.val ∧
          windowIsExactOnes data.val s (countOnes data.val))) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer s with 0 <= s <= n-k such that the number of indices i with s <= i < s+k and data[i] = 0 is exactly r, where k is the number of indices i with data[i] = 1. When k = 0, this number is 0.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_7 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      ∃ s, s ≤ data.val.length - countOnes data.val ∧
        ((zerosInWindow data.val s (countOnes data.val) : ℕ) : ℤ) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), ∃ s, s ≤ data.val.length - countOnes data.val ∧
          ((zerosInWindow data.val s (countOnes data.val) : ℕ) : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer s with 0 <= s <= n-k, the number of indices i with s <= i < s+k and data[i] = 0 is at least r, where k is the number of indices i with data[i] = 1. When k = 0, these numbers are 0.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_8 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      ∀ s, s ≤ data.val.length - countOnes data.val →
        r.val ≤ ((zerosInWindow data.val s (countOnes data.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), ∀ s, s ≤ data.val.length - countOnes data.val →
          r.val ≤ ((zerosInWindow data.val s (countOnes data.val) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = k - M, where k is the number of indices i with 0 <= i < n and data[i] = 1, and M is the maximum, over all integers s with 0 <= s <= n-k, of the number of indices i with s <= i < s+k and data[i] = 1. When k = 0, M = 0.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_9 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      r.val = ((countOnes data.val : ℕ) : ℤ) -
        ((maxOnesWindow data.val (countOnes data.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), r.val = ((countOnes data.val : ℕ) : ℤ) -
          ((maxOnesWindow data.val (countOnes data.val) : ℕ) : ℤ)) := by
    sorry

  /-- Let data_rev be the array of length n with data_rev[i] = data[n-1-i] for 0 <= i < n. Whenever the function returns a result r on data, r also equals the minimum over all integers s with 0 <= s <= n-k of the number of indices i with s <= i < s+k and data_rev[i] = 0, where k is the number of indices i with data[i] = 1.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_10 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      r.val = ((minZerosWindow data.val.reverse (countOnes data.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), r.val = ((minZerosWindow data.val.reverse (countOnes data.val) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r: if k = 0 then r = 0; if k > 0, let a be the smallest index with data[a] = 1 and b the largest index with data[b] = 1, let m = b-a+1, and then r equals the minimum, over all integers s with 0 <= s <= m-k, of the number of indices i with s <= i < s+k and data[a+i] = 0, where k is the number of indices i with data[i] = 1.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_11 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      (countOnes data.val = 0 → r.val = 0) ∧
        (0 < countOnes data.val → ∀ (a b : ℕ), IsFirstOne data.val a → IsLastOne data.val b →
          r.val = ((minZerosWindow ((data.val.drop a).take (b - a + 1))
            (countOnes data.val) : ℕ) : ℤ)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), (countOnes data.val = 0 → r.val = 0) ∧
          (0 < countOnes data.val → ∀ (a b : ℕ), IsFirstOne data.val a → IsLastOne data.val b →
            r.val = ((minZerosWindow ((data.val.drop a).take (b - a + 1))
              (countOnes data.val) : ℕ) : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then 0 < k < n, where k is the number of indices i with 0 <= i < n and data[i] = 1.
    Preconditions: Let n = len(data). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, data[i] = 0 or data[i] = 1. -/
  theorem spec_12 (data : Slice Std.I64) (r : Std.I64)
      (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
      (hbits : IsBitList data.val) (hres : min_swaps data = ok r) :
      0 < r.val → 0 < countOnes data.val ∧ countOnes data.val < data.val.length := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (data : Slice Std.I64) (r : Std.I64)
        (hn1 : 1 ≤ data.val.length) (hn2 : data.val.length ≤ 100000)
        (hbits : IsBitList data.val) (hres : min_swaps data = ok r), 0 < r.val → 0 < countOnes data.val ∧ countOnes data.val < data.val.length) := by
    sorry

  end AegisSpec.MinSwaps
