import Aegis.LenLongestFibSubseq.Code.Funs

/-!
# Specifications of `Aegis.LenLongestFibSubseq.len_longest_fib_subseq`

LeetCode problem `length-of-longest-fibonacci-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LenLongestFibSubseq

def elem (arr : Slice Std.I64) (i : Nat) : Int :=
  ((arr.val[i]?).map IScalar.val).getD 0

def IsFibIdxSeq (arr : Slice Std.I64) : List Nat → Prop
  | [] => True
  | a :: rest =>
      (match rest with
        | [] => True
        | b :: rest' =>
            a < b ∧ b < arr.val.length ∧
              (match rest' with
                | [] => True
                | c :: _ => elem arr a + elem arr b = elem arr c))
      ∧ IsFibIdxSeq arr rest

def HasFibIdxSeq (arr : Slice Std.I64) (k : Nat) : Prop :=
  ∃ idxs : List Nat, idxs.length = k ∧ IsFibIdxSeq arr idxs

def AdmissibleLength (arr : Slice Std.I64) (k : Nat) : Prop :=
  3 ≤ k ∧ k ≤ arr.val.length ∧ HasFibIdxSeq arr k

def IsMaxAdmissibleLength (arr : Slice Std.I64) (r : Int) : Prop :=
  (∀ k : Nat, AdmissibleLength arr k → (k : Int) ≤ r) ∧ (r = 0 ∨ AdmissibleLength arr r.toNat)

def HasFibTriple (arr : Slice Std.I64) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < arr.val.length ∧ elem arr i + elem arr j = elem arr k

def IsFibChain (arr : Slice Std.I64) : Prop :=
  ∀ i : Nat, i + 2 < arr.val.length → elem arr i + elem arr (i + 1) = elem arr (i + 2)

/-- Call an integer k an admissible length when 3 <= k <= len(arr) and there exist indices a0, a1, ..., a_{k-1} such that 0 <= a0 < a1 < ... < a_{k-1} < len(arr) and, for every t with 0 <= t < k-2, arr[a_t] + arr[a_{t+1}] = arr[a_{t+2}]. The function returns a result r such that: if there is no admissible length then r = 0; otherwise r is an admissible length and every admissible length k satisfies k <= r. Thus r is the maximum admissible length, with the maximum of the empty set taken to be 0.
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      IsMaxAdmissibleLength arr r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      IsMaxAdmissibleLength arr r.val) := by
  sorry

/-- The function returns a result r and does not fail: on every input satisfying the preconditions the Lean call produces an Ok value (no overflow, out-of-bounds access, or panic).
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= len(arr).
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (arr.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (arr.val.length : Int)) := by
  sorry

/-- The function returns a result r and either r = 0 or 3 <= r <= len(arr). In particular, the result is never 1 or 2.
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = 0 ∨ (3 ≤ r.val ∧ r.val ≤ (arr.val.length : Int))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = 0 ∨ (3 ≤ r.val ∧ r.val ≤ (arr.val.length : Int)))) := by
  sorry

/-- The function returns a result r and r = 0 if and only if there do not exist indices i, j, k with 0 <= i < j < k < len(arr) and arr[i] + arr[j] = arr[k].
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = 0 ↔ ¬ HasFibTriple arr) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = 0 ↔ ¬ HasFibTriple arr)) := by
  sorry

/-- The function returns a result r and r <= 43.
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧ r.val ≤ 43 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧ r.val ≤ 43) := by
  sorry

/-- The function returns a result r; if r >= 3, then there exist indices a0, a1, ..., a_{r-1} such that 0 <= a0 < a1 < ... < a_{r-1} < len(arr) and, for every t with 0 <= t < r-2, arr[a_t] + arr[a_{t+1}] = arr[a_{t+2}].
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (3 ≤ r.val → HasFibIdxSeq arr r.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (3 ≤ r.val → HasFibIdxSeq arr r.val.toNat)) := by
  sorry

/-- The function returns a result r; for every k >= 3 and every choice of indices a0, ..., a_{k-1} with 0 <= a0 < ... < a_{k-1} < len(arr), if for every t with 0 <= t < k-2 we have arr[a_t] + arr[a_{t+1}] = arr[a_{t+2}], then k <= r.
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      ∀ (k : Nat) (idxs : List Nat), 3 ≤ k → idxs.length = k → IsFibIdxSeq arr idxs →
        (k : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      ∀ (k : Nat) (idxs : List Nat), 3 ≤ k → idxs.length = k → IsFibIdxSeq arr idxs →
        (k : Int) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r = len(arr) if and only if for every i with 0 <= i < len(arr)-2 we have arr[i] + arr[i+1] = arr[i+2].
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_9 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = (arr.val.length : Int) ↔ IsFibChain arr) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (r.val = (arr.val.length : Int) ↔ IsFibChain arr)) := by
  sorry

/-- The function returns a result r; if r >= 3, then for every k with 3 <= k <= r there exist indices a0, ..., a_{k-1} such that 0 <= a0 < ... < a_{k-1} < len(arr) and, for every t with 0 <= t < k-2, arr[a_t] + arr[a_{t+1}] = arr[a_{t+2}].
  Preconditions: 3 <= len(arr) <= 1000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000000000; and for every i with 0 <= i < len(arr)-1, arr[i] < arr[i+1]. -/
theorem spec_10 (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)) :
    ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (3 ≤ r.val → ∀ k : Nat, 3 ≤ k → k ≤ r.val.toNat → HasFibIdxSeq arr k) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_lo : 3 ≤ arr.val.length) (hlen_hi : arr.val.length ≤ 1000)
    (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elem arr i ∧ elem arr i ≤ 1000000000)
    (hsorted : ∀ i : Nat, i + 1 < arr.val.length → elem arr i < elem arr (i + 1)), ∃ r : Std.I64, Aegis.LenLongestFibSubseq.len_longest_fib_subseq arr = ok r ∧
      (3 ≤ r.val → ∀ k : Nat, 3 ≤ k → k ≤ r.val.toNat → HasFibIdxSeq arr k)) := by
  sorry

end AegisSpec.LenLongestFibSubseq
