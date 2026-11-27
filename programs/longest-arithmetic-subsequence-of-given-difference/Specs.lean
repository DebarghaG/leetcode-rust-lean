import Aegis.LongestSubsequence.Code.Funs

/-!
# Specifications of `Aegis.LongestSubsequence.longest_subsequence`

LeetCode problem `longest-arithmetic-subsequence-of-given-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LongestSubsequence

  namespace AegisSpec.LongestSubsequence

  def vals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def valAt (arr : Slice Std.I64) (i : ℕ) : ℤ := (vals arr).getD i 0

  def chainVals (arr : Slice Std.I64) (idx : List ℕ) : List ℤ :=
    idx.map (valAt arr)

  def IsDiffChain (arr : Slice Std.I64) (difference : Std.I64) (idx : List ℕ) : Prop :=
    idx.IsChain (· < ·) ∧
    (∀ i ∈ idx, i < arr.val.length) ∧
    (chainVals arr idx).IsChain (fun a b => b = a + difference.val)

  def HasChainLength (arr : Slice Std.I64) (difference : Std.I64) (k : ℕ) : Prop :=
    ∃ idx : List ℕ, IsDiffChain arr difference idx ∧ idx.length = k

  def chainLengths (arr : Slice Std.I64) (difference : Std.I64) : Set ℤ :=
    {k : ℤ | 1 ≤ k ∧ ∃ idx : List ℕ, IsDiffChain arr difference idx ∧ (idx.length : ℤ) = k}

  def IsMaxChainLength (arr : Slice Std.I64) (difference : Std.I64) (r : ℤ) : Prop :=
    IsGreatest (chainLengths arr difference) r

  def countOf (arr : Slice Std.I64) (v : ℤ) : ℕ :=
    ((vals arr).filter (fun x => x == v)).length

  def IsMaxMultiplicity (arr : Slice Std.I64) (r : ℤ) : Prop :=
    IsGreatest {c : ℤ | ∃ v : ℤ, v ∈ vals arr ∧ (countOf arr v : ℤ) = c} r

  def distinctCount (arr : Slice Std.I64) : ℕ := (vals arr).dedup.length

  def IsMinValue (arr : Slice Std.I64) (m : ℤ) : Prop :=
    m ∈ vals arr ∧ ∀ v ∈ vals arr, m ≤ v

  def IsMaxValue (arr : Slice Std.I64) (M : ℤ) : Prop :=
    M ∈ vals arr ∧ ∀ v ∈ vals arr, v ≤ M

  def IsNegI64 (d d' : Std.I64) : Prop := (-. d = ok d') ∧ d'.val = -d.val

  /-- For every such input, the function returns a result r, and r equals the maximum of the set of all k >= 1 for which there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_t < len(arr) for every t and arr[i_{j+1}] = arr[i_j] + difference for every j with 0 <= j < k-1. Length 1 is included, with the adjacency condition vacuous.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_1 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        IsMaxChainLength arr difference r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          IsMaxChainLength arr difference r.val) := by
    sorry

  /-- For every such input, the function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_2 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r) := by
    sorry

  /-- For every such input, the function returns a result r and there exists a strictly increasing sequence of indices i_0 < ... < i_{r-1} with 0 <= i_t < len(arr) for all t and arr[i_{j+1}] = arr[i_j] + difference for all j with 0 <= j < r-1. If r = 1 the adjacency condition is vacuous.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_3 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        ∃ idx : List ℕ, IsDiffChain arr difference idx ∧ (idx.length : ℤ) = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          ∃ idx : List ℕ, IsDiffChain arr difference idx ∧ (idx.length : ℤ) = r.val) := by
    sorry

  /-- For every such input, the function returns a result r and for every k >= 1 and every strictly increasing sequence of indices i_0 < ... < i_{k-1} with 0 <= i_t < len(arr) for all t and arr[i_{j+1}] = arr[i_j] + difference for all j with 0 <= j < k-1, we have k <= r.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_4 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        ∀ k : ℕ, 1 ≤ k → HasChainLength arr difference k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          ∀ k : ℕ, 1 ≤ k → HasChainLength arr difference k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- For every such input with difference = 0, the function returns a result r, and r = max { count(v) | v occurs in arr }, where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. The set of occurring v is nonempty because len(arr) >= 1.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000; difference = 0. -/
  theorem spec_5 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
      (hzero : difference.val = 0) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        IsMaxMultiplicity arr r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
        (hzero : difference.val = 0), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          IsMaxMultiplicity arr r.val) := by
    sorry

  /-- For every such input, the function returns a result r and the equivalence (r = len(arr)) if and only if (for every i with 0 <= i < len(arr)-1, arr[i+1] = arr[i] + difference) holds.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_6 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        (r.val = (arr.val.length : ℤ) ↔
          ∀ i : ℕ, i + 1 < arr.val.length → valAt arr (i + 1) = valAt arr i + difference.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          (r.val = (arr.val.length : ℤ) ↔
            ∀ i : ℕ, i + 1 < arr.val.length → valAt arr (i + 1) = valAt arr i + difference.val)) := by
    sorry

  /-- For every such input, the function returns a result r and the equivalence (r = 1) if and only if (there do not exist indices i,j with 0 <= i < j < len(arr) and arr[j] = arr[i] + difference) holds.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_7 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        (r.val = 1 ↔
          ¬ ∃ i j : ℕ, i < j ∧ j < arr.val.length ∧
            valAt arr j = valAt arr i + difference.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          (r.val = 1 ↔
            ¬ ∃ i j : ℕ, i < j ∧ j < arr.val.length ∧
              valAt arr j = valAt arr i + difference.val)) := by
    sorry

  /-- For every such input, let rev be the slice of length len(arr) with rev[i] = arr[len(arr)-1-i]. The function returns a result r on (arr, difference) and a result r' on (rev, -difference), and r = r'.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_8 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ rev : Slice Std.I64, rev.val = arr.val.reverse ∧
        ∃ d' : Std.I64, IsNegI64 difference d' ∧
          ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
            longest_subsequence rev d' = ok r' ∧ r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ rev : Slice Std.I64, rev.val = arr.val.reverse ∧
          ∃ d' : Std.I64, IsNegI64 difference d' ∧
            ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
              longest_subsequence rev d' = ok r' ∧ r = r') := by
    sorry

  /-- For every such input and c, let arrc be the slice of length len(arr) with arrc[i] = arr[i] + c. The function returns a result r on (arr, difference) and a result r' on (arrc, difference), and r = r'.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000; let c be any integer such that -10000 <= arr[i] + c <= 10000 for every i with 0 <= i < len(arr). -/
  theorem spec_9 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
      (c : ℤ) (hc : ∀ x ∈ arr.val, -10000 ≤ x.val + c ∧ x.val + c ≤ 10000) :
      ∃ arrc : Slice Std.I64, vals arrc = (vals arr).map (fun v => v + c) ∧
        ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
          longest_subsequence arrc difference = ok r' ∧ r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
        (c : ℤ) (hc : ∀ x ∈ arr.val, -10000 ≤ x.val + c ∧ x.val + c ≤ 10000), ∃ arrc : Slice Std.I64, vals arrc = (vals arr).map (fun v => v + c) ∧
          ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
            longest_subsequence arrc difference = ok r' ∧ r = r') := by
    sorry

  /-- For every such input and k, let karr be the slice of length len(arr) with karr[i] = k*arr[i]. The function returns a result r on (arr, difference) and a result r' on (karr, k*difference), and r = r'.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000; let k be any integer with k >= 1 such that -10000 <= k*arr[i] <= 10000 for every i with 0 <= i < len(arr) and -10000 <= k*difference <= 10000. -/
  theorem spec_10 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
      (k : ℤ) (hk : 1 ≤ k)
      (hkarr : ∀ x ∈ arr.val, -10000 ≤ k * x.val ∧ k * x.val ≤ 10000)
      (hkd : -10000 ≤ k * difference.val ∧ k * difference.val ≤ 10000) :
      ∃ karr : Slice Std.I64, vals karr = (vals arr).map (fun v => k * v) ∧
        ∃ d' : Std.I64, d'.val = k * difference.val ∧
          ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
            longest_subsequence karr d' = ok r' ∧ r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
        (k : ℤ) (hk : 1 ≤ k)
        (hkarr : ∀ x ∈ arr.val, -10000 ≤ k * x.val ∧ k * x.val ≤ 10000)
        (hkd : -10000 ≤ k * difference.val ∧ k * difference.val ≤ 10000), ∃ karr : Slice Std.I64, vals karr = (vals arr).map (fun v => k * v) ∧
          ∃ d' : Std.I64, d'.val = k * difference.val ∧
            ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
              longest_subsequence karr d' = ok r' ∧ r = r') := by
    sorry

  /-- For every such input with difference != 0, the function returns a result r and r <= floor((maxVal - minVal) / |difference|) + 1, where minVal = min_{0 <= i < len(arr)} arr[i] and maxVal = max_{0 <= i < len(arr)} arr[i].
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000; difference != 0. -/
  theorem spec_11 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
      (hne : difference.val ≠ 0) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        ∀ m M : ℤ, IsMinValue arr m → IsMaxValue arr M →
          r.val ≤ (M - m) / (difference.val.natAbs : ℤ) + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
        (hne : difference.val ≠ 0), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          ∀ m M : ℤ, IsMinValue arr m → IsMaxValue arr M →
            r.val ≤ (M - m) / (difference.val.natAbs : ℤ) + 1) := by
    sorry

  /-- For every such input, let negarr be the slice of length len(arr) with negarr[i] = -arr[i]. The function returns a result r on (arr, difference) and a result r' on (negarr, -difference), and r = r'.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000. -/
  theorem spec_12 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000) :
      ∃ negarr : Slice Std.I64, vals negarr = (vals arr).map (fun v => -v) ∧
        ∃ d' : Std.I64, IsNegI64 difference d' ∧
          ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
            longest_subsequence negarr d' = ok r' ∧ r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000), ∃ negarr : Slice Std.I64, vals negarr = (vals arr).map (fun v => -v) ∧
          ∃ d' : Std.I64, IsNegI64 difference d' ∧
            ∃ r r' : Std.I64, longest_subsequence arr difference = ok r ∧
              longest_subsequence negarr d' = ok r' ∧ r = r') := by
    sorry

  /-- For every such input with difference != 0, the function returns a result r and r <= |{v | there exists i with 0 <= i < len(arr) and arr[i] = v}|, i.e., the number of distinct values occurring in arr.
    Preconditions: arr is a slice with 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), -10000 <= arr[i] <= 10000; -10000 <= difference <= 10000; difference != 0. -/
  theorem spec_13 (arr : Slice Std.I64) (difference : Std.I64)
      (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
      (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
      (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
      (hne : difference.val ≠ 0) :
      ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
        r.val ≤ (distinctCount arr : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice Std.I64) (difference : Std.I64)
        (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
        (hvals : ∀ x ∈ arr.val, -10000 ≤ x.val ∧ x.val ≤ 10000)
        (hdiff : -10000 ≤ difference.val ∧ difference.val ≤ 10000)
        (hne : difference.val ≠ 0), ∃ r : Std.I64, longest_subsequence arr difference = ok r ∧
          r.val ≤ (distinctCount arr : ℤ)) := by
    sorry

  end AegisSpec.LongestSubsequence
