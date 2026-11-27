import Aegis.SumSubarrayMins.Code.Funs

/-!
# Specifications of `Aegis.SumSubarrayMins.sum_subarray_mins`

LeetCode problem `sum-of-subarray-minimums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumSubarrayMins

  def modulus : Int := 1000000007

  def length (arr : Slice Std.I64) : Nat := arr.val.length

  def entry (arr : Slice Std.I64) (i : Nat) : Int :=
    match arr.val[i]? with
    | some x => x.val
    | none => 0

  def segMin (arr : Slice Std.I64) (l r : Nat) : Int :=
    ((List.range (r + 1 - l)).map (fun k => entry arr (l + k))).min?.getD 0

  def totalMinSum (arr : Slice Std.I64) : Int :=
    ∑ l ∈ Finset.range (length arr), ∑ r ∈ Finset.range (length arr),
      if l ≤ r then segMin arr l r else 0

  def sufMin (arr : Slice Std.I64) (l : Nat) : Int :=
    ((List.range (length arr - l)).map (fun k => entry arr (l + k))).min?.getD 0

  def congMod (a b : Int) : Prop := a % modulus = b % modulus

  /-- Let M = 1000000007. Define S(arr) = sum over all pairs (l, r) with 0 <= l <= r < n of min{ arr[k] | l <= k <= r }; the inner minimum is over a nonempty contiguous segment. Whenever sum_subarray_mins arr returns a result r, r = S(arr) mod M, i.e. r is the unique integer with 0 <= r < M such that S(arr) - r is divisible by M.
    Preconditions: arr is a slice of 64-bit integers with length n, where 1 <= n <= 30000, and 1 <= arr[i] <= 30000 for every 0 <= i < n. -/
  theorem spec_1 (arr : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000) :
      ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        r.val = totalMinSum arr % modulus := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000), ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          r.val = totalMinSum arr % modulus) := by
    sorry

  /-- For every arr satisfying the preconditions, sum_subarray_mins arr returns a result r; it does not fail (no arithmetic overflow, indexing error, or panic).
    Preconditions: arr is a slice of 64-bit integers with length n, where 1 <= n <= 30000, and 1 <= arr[i] <= 30000 for every 0 <= i < n. -/
  theorem spec_2 (arr : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000) :
      ∃ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000), ∃ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r, 0 <= r < 1000000007.
    Preconditions: arr is a slice of 64-bit integers with length n, where 1 <= n <= 30000, and 1 <= arr[i] <= 30000 for every 0 <= i < n. -/
  theorem spec_3 (arr : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000) :
      ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        0 ≤ r.val ∧ r.val < modulus := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000), ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          0 ≤ r.val ∧ r.val < modulus) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r, r = (c * n * (n + 1) / 2) mod 1000000007, where n(n+1)/2 is the exact number of nonempty contiguous subarrays.
    Preconditions: n = len(arr), 1 <= n <= 30000, and there is an integer c with 1 <= c <= 30000 such that arr[i] = c for every 0 <= i < n. -/
  theorem spec_4 (arr : Slice Std.I64) (n : Nat) (c : Int)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
      (hconst : ∀ (i : Nat), i < n → entry arr i = c) :
      ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        r.val = (c * (n : Int) * ((n : Int) + 1) / 2) % modulus := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat) (c : Int)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
        (hconst : ∀ (i : Nat), i < n → entry arr i = c), ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          r.val = (c * (n : Int) * ((n : Int) + 1) / 2) % modulus) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r, r = (sum_{i=0}^{n-1} arr[i] * (n - i)) mod 1000000007.
    Preconditions: n = len(arr), 1 <= n <= 30000, 1 <= arr[i] <= 30000 for every i, and arr[0] < arr[1] < ... < arr[n-1]. -/
  theorem spec_5 (arr : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hmono : ∀ (i : Nat), i + 1 < n → entry arr i < entry arr (i + 1)) :
      ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        r.val = (∑ i ∈ Finset.range n, entry arr i * ((n : Int) - (i : Int))) % modulus := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hmono : ∀ (i : Nat), i + 1 < n → entry arr i < entry arr (i + 1)), ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          r.val = (∑ i ∈ Finset.range n, entry arr i * ((n : Int) - (i : Int))) % modulus) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r, r = (sum_{i=0}^{n-1} arr[i] * (i + 1)) mod 1000000007.
    Preconditions: n = len(arr), 1 <= n <= 30000, 1 <= arr[i] <= 30000 for every i, and arr[0] > arr[1] > ... > arr[n-1]. -/
  theorem spec_6 (arr : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hmono : ∀ (i : Nat), i + 1 < n → entry arr (i + 1) < entry arr i) :
      ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        r.val = (∑ i ∈ Finset.range n, entry arr i * ((i : Int) + 1)) % modulus := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hmono : ∀ (i : Nat), i + 1 < n → entry arr (i + 1) < entry arr i), ∀ r, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          r.val = (∑ i ∈ Finset.range n, entry arr i * ((i : Int) + 1)) % modulus) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r and sum_subarray_mins rev returns r_rev, r = r_rev.
    Preconditions: n = len(arr), 1 <= n <= 30000, 1 <= arr[i] <= 30000 for every i. Let rev be the slice of length n with rev[i] = arr[n - 1 - i] for every 0 <= i < n. -/
  theorem spec_7 (arr rev : Slice Std.I64) (n : Nat)
      (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hrev : rev.val = arr.val.reverse) :
      ∀ r r_rev, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        Aegis.SumSubarrayMins.sum_subarray_mins rev = ok r_rev → r.val = r_rev.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr rev : Slice Std.I64) (n : Nat)
        (hlen : length arr = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hrev : rev.val = arr.val.reverse), ∀ r r_rev, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          Aegis.SumSubarrayMins.sum_subarray_mins rev = ok r_rev → r.val = r_rev.val) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r and sum_subarray_mins arr2 returns r2, r2 is congruent to r + c * (n * (n + 1) / 2) modulo 1000000007.
    Preconditions: arr and arr2 are slices of the same length n, with 1 <= n <= 30000 and all their entries in [1, 30000]. There is an integer c such that arr2[i] = arr[i] + c for every 0 <= i < n. -/
  theorem spec_8 (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
      (hlen : length arr = n) (hlen2 : length arr2 = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hentries2 : ∀ (i : Nat), i < n → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
      (hshift : ∀ (i : Nat), i < n → entry arr2 i = entry arr i + c) :
      ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
        congMod r2.val (r.val + c * ((n : Int) * ((n : Int) + 1) / 2)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
        (hlen : length arr = n) (hlen2 : length arr2 = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hentries2 : ∀ (i : Nat), i < n → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
        (hshift : ∀ (i : Nat), i < n → entry arr2 i = entry arr i + c), ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
          congMod r2.val (r.val + c * ((n : Int) * ((n : Int) + 1) / 2))) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r and sum_subarray_mins arr2 returns r2, r2 is congruent to c * r modulo 1000000007.
    Preconditions: arr and arr2 are slices of the same length n, with 1 <= n <= 30000 and all their entries in [1, 30000]. There is an integer c with c >= 1 such that arr2[i] = c * arr[i] for every 0 <= i < n. -/
  theorem spec_9 (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
      (hlen : length arr = n) (hlen2 : length arr2 = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hentries2 : ∀ (i : Nat), i < n → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
      (hc : 1 ≤ c) (hscale : ∀ (i : Nat), i < n → entry arr2 i = c * entry arr i) :
      ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
        congMod r2.val (c * r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
        (hlen : length arr = n) (hlen2 : length arr2 = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 30000)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hentries2 : ∀ (i : Nat), i < n → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
        (hc : 1 ≤ c) (hscale : ∀ (i : Nat), i < n → entry arr2 i = c * entry arr i), ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
          congMod r2.val (c * r.val)) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r and sum_subarray_mins arr2 returns r2, r2 is congruent to r + c * (n + 1) modulo 1000000007.
    Preconditions: arr has length n with 1 <= n <= 29999 (so arr2 has length n+1 <= 30000), arr2 has length n+1, all entries of arr and arr2 are in [1, 30000], arr2[i] = arr[i] for 0 <= i < n, and arr2[n] = c where 1 <= c <= 30000 and c <= arr[i] for every 0 <= i < n. -/
  theorem spec_10 (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
      (hlen : length arr = n) (hlen2 : length arr2 = n + 1)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 29999)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hentries2 : ∀ (i : Nat), i < n + 1 → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
      (hcopy : ∀ (i : Nat), i < n → entry arr2 i = entry arr i)
      (hlast : entry arr2 n = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
      (hcle : ∀ (i : Nat), i < n → c ≤ entry arr i) :
      ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
        congMod r2.val (r.val + c * ((n : Int) + 1)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
        (hlen : length arr = n) (hlen2 : length arr2 = n + 1)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 29999)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hentries2 : ∀ (i : Nat), i < n + 1 → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
        (hcopy : ∀ (i : Nat), i < n → entry arr2 i = entry arr i)
        (hlast : entry arr2 n = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
        (hcle : ∀ (i : Nat), i < n → c ≤ entry arr i), ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
          congMod r2.val (r.val + c * ((n : Int) + 1))) := by
    sorry

  /-- Whenever sum_subarray_mins arr returns r and sum_subarray_mins arr2 returns r2, r2 is congruent to r + c + sum_{l=0}^{n-1} sufmin(l) modulo 1000000007.
    Preconditions: arr has length n with 1 <= n <= 29999 (so arr2 has length n+1 <= 30000), arr2 has length n+1, all entries of arr and arr2 are in [1, 30000], arr2[i] = arr[i] for 0 <= i < n, and arr2[n] = c where 1 <= c <= 30000 and c >= arr[i] for every 0 <= i < n. For 0 <= l < n let sufmin(l) = min{ arr[k] | l <= k < n }. -/
  theorem spec_11 (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
      (hlen : length arr = n) (hlen2 : length arr2 = n + 1)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 29999)
      (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
      (hentries2 : ∀ (i : Nat), i < n + 1 → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
      (hcopy : ∀ (i : Nat), i < n → entry arr2 i = entry arr i)
      (hlast : entry arr2 n = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
      (hcge : ∀ (i : Nat), i < n → entry arr i ≤ c) :
      ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
        Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
        congMod r2.val (r.val + c + ∑ l ∈ Finset.range n, sufMin arr l) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64) (n : Nat) (c : Int)
        (hlen : length arr = n) (hlen2 : length arr2 = n + 1)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 29999)
        (hentries : ∀ (i : Nat), i < n → 1 ≤ entry arr i ∧ entry arr i ≤ 30000)
        (hentries2 : ∀ (i : Nat), i < n + 1 → 1 ≤ entry arr2 i ∧ entry arr2 i ≤ 30000)
        (hcopy : ∀ (i : Nat), i < n → entry arr2 i = entry arr i)
        (hlast : entry arr2 n = c) (hc1 : 1 ≤ c) (hc2 : c ≤ 30000)
        (hcge : ∀ (i : Nat), i < n → entry arr i ≤ c), ∀ r r2, Aegis.SumSubarrayMins.sum_subarray_mins arr = ok r →
          Aegis.SumSubarrayMins.sum_subarray_mins arr2 = ok r2 →
          congMod r2.val (r.val + c + ∑ l ∈ Finset.range n, sufMin arr l)) := by
    sorry

  end AegisSpec.SumSubarrayMins
