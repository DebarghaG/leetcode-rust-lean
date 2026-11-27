import Aegis.GetMaxRepetitions.Code.Funs

/-!
# Specifications of `Aegis.GetMaxRepetitions.get_max_repetitions`

LeetCode problem `count-the-repetitions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GetMaxRepetitions

set_option autoImplicit false

namespace AegisSpec.GetMaxRepetitions

def «repeat» (s : List Std.U8) (k : Nat) : List Std.U8 :=
  List.flatten (List.replicate k s)

def IsSubsequence (A B : List Std.U8) : Prop :=
  ∃ idx : Fin A.length → Fin B.length,
    StrictMono idx ∧ ∀ t : Fin A.length, B.get (idx t) = A.get t

def count (s : List Std.U8) (c : Nat) : Nat :=
  (s.filter (fun b => b.val = c)).length

/-- Define repeat(s,k) for integer k >= 0 as the byte sequence with len(repeat(s,k)) = k*len(s) and repeat(s,k)[i] = s[i mod len(s)] for all 0 <= i < k*len(s). Define A is a subsequence of B to mean that there are indices 0 <= j_0 < j_1 < ... < j_{len(A)-1} < len(B) with B[j_t] = A[t] for every 0 <= t < len(A); if A is empty this holds by convention. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, for every integer m >= 0, repeat(s2, n2*m) is a subsequence of repeat(s1, n1) if and only if m <= r. Thus r is the greatest m >= 0 such that [str2,m] can be obtained from [str1,n1], where str1 = [s1,n1] and str2 = [s2,n2].
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). Here len is the mathematical length of the slice; n1 and n2 are interpreted as mathematical integers. -/
theorem spec_1
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    ∀ m : Nat,
      (IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat) ↔
        (m : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), ∀ m : Nat,
      (IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat) ↔
        (m : Int) ≤ r.val)) := by
  sorry

/-- For every s1,n1,s2,n2 satisfying the preconditions, get_max_repetitions(s1,n1,s2,n2) returns Ok r for some I64 value r; it does not return Err, overflow, panic, or go out of bounds.
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_2
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : Std.I64, get_max_repetitions s1 n1 s2 n2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64, get_max_repetitions s1 n1 s2 n2 = ok r) := by
  sorry

/-- Define repeat(s,k) for integer k >= 0 as the byte sequence with len(repeat(s,k)) = k*len(s) and repeat(s,k)[i] = s[i mod len(s)] for all 0 <= i < k*len(s). Define A is a subsequence of B to mean that there are indices 0 <= j_0 < j_1 < ... < j_{len(A)-1} < len(B) with B[j_t] = A[t] for every 0 <= t < len(A); if A is empty this holds by convention. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, r >= 0 and for every integer m with 0 <= m <= r, repeat(s2, n2*m) is a subsequence of repeat(s1, n1).
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_3
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    0 ≤ r.val ∧
      ∀ m : Nat,
        (m : Int) ≤ r.val →
          IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), 0 ≤ r.val ∧
      ∀ m : Nat,
        (m : Int) ≤ r.val →
          IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat)) := by
  sorry

/-- Define repeat(s,k) for integer k >= 0 as the byte sequence with len(repeat(s,k)) = k*len(s) and repeat(s,k)[i] = s[i mod len(s)] for all 0 <= i < k*len(s). Define A is a subsequence of B to mean that there are indices 0 <= j_0 < j_1 < ... < j_{len(A)-1} < len(B) with B[j_t] = A[t] for every 0 <= t < len(A); if A is empty this holds by convention. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, for every integer m >= 0, if repeat(s2, n2*m) is a subsequence of repeat(s1, n1), then m <= r.
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_4
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    ∀ m : Nat,
      IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat) →
        (m : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), ∀ m : Nat,
      IsSubsequence («repeat» s2.val (n2.val.toNat * m)) («repeat» s1.val n1.val.toNat) →
        (m : Int) ≤ r.val) := by
  sorry

/-- Define repeat(s,k) for integer k >= 0 as the byte sequence with len(repeat(s,k)) = k*len(s) and repeat(s,k)[i] = s[i mod len(s)] for all 0 <= i < k*len(s). Define A is a subsequence of B to mean that there are indices 0 <= j_0 < j_1 < ... < j_{len(A)-1} < len(B) with B[j_t] = A[t] for every 0 <= t < len(A); if A is empty this holds by convention. Let K be the maximum integer K >= 0 such that repeat(s2,K) is a subsequence of repeat(s1,n1); K exists because len(s2) >= 1 and repeat(s1,n1) is finite. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r and K as mathematical integers, r = K / n2, where / is integer division of nonnegative integers (floor).
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_5
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (K : Nat)
    (hK : IsSubsequence («repeat» s2.val K) («repeat» s1.val n1.val.toNat))
    (hK_max : ∀ K' : Nat,
      IsSubsequence («repeat» s2.val K') («repeat» s1.val n1.val.toNat) → K' ≤ K)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    r.val = (K : Int) / n2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (K : Nat)
    (hK : IsSubsequence («repeat» s2.val K) («repeat» s1.val n1.val.toNat))
    (hK_max : ∀ K' : Nat,
      IsSubsequence («repeat» s2.val K') («repeat» s1.val n1.val.toNat) → K' ≤ K)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), r.val = (K : Int) / n2.val) := by
  sorry

/-- Let repeat(s,k) be the k-fold repetition of s. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, r >= 0 and r * n2 * len(s2) <= n1 * len(s1).
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_6
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    0 ≤ r.val ∧
      r.val * n2.val * (s2.val.length : Int) ≤ n1.val * (s1.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), 0 ≤ r.val ∧
      r.val * n2.val * (s2.val.length : Int) ≤ n1.val * (s1.val.length : Int)) := by
  sorry

/-- Let repeat(s,k) be the k-fold repetition of s. For a byte array x and byte value c, let count(x,c) be the number of indices i with 0 <= i < len(x) and x[i] = c. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, r >= 0 and for every byte value c with 0 <= c < 256, r * n2 * count(s2,c) <= n1 * count(s1,c).
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_7
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    0 ≤ r.val ∧
      ∀ c : Nat,
        c < 256 →
          r.val * n2.val * (count s2.val c : Int) ≤ n1.val * (count s1.val c : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), 0 ≤ r.val ∧
      ∀ c : Nat,
        c < 256 →
          r.val * n2.val * (count s2.val c : Int) ≤ n1.val * (count s1.val c : Int)) := by
  sorry

/-- Define repeat(s,k) for integer k >= 0 as the byte sequence with len(repeat(s,k)) = k*len(s) and repeat(s,k)[i] = s[i mod len(s)] for all 0 <= i < k*len(s). Define A is a subsequence of B to mean that there are indices 0 <= j_0 < j_1 < ... < j_{len(A)-1} < len(B) with B[j_t] = A[t] for every 0 <= t < len(A); if A is empty this holds by convention. Whenever get_max_repetitions(s1,n1,s2,n2) returns Ok r, interpreting r as a mathematical integer, r = 0 if and only if repeat(s2, n2) is not a subsequence of repeat(s1, n1).
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_8
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r) :
    (r.val = 0 ↔
      ¬ IsSubsequence («repeat» s2.val n2.val.toNat) («repeat» s1.val n1.val.toNat)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r), (r.val = 0 ↔
      ¬ IsSubsequence («repeat» s2.val n2.val.toNat) («repeat» s1.val n1.val.toNat))) := by
  sorry

/-- For every integer n1' with n1 <= n1' <= 10^6, if get_max_repetitions(s1,n1,s2,n2) returns Ok r and get_max_repetitions(s1,n1',s2,n2) returns Ok r', then interpreting r and r' as mathematical integers, r <= r'.
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_9
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (n1' : Std.I64) (hn1'_lo : n1.val ≤ n1'.val) (hn1'_hi : n1'.val ≤ 1000000)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r)
    (r' : Std.I64) (hr' : get_max_repetitions s1 n1' s2 n2 = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (n1' : Std.I64) (hn1'_lo : n1.val ≤ n1'.val) (hn1'_hi : n1'.val ≤ 1000000)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r)
    (r' : Std.I64) (hr' : get_max_repetitions s1 n1' s2 n2 = ok r'), r.val ≤ r'.val) := by
  sorry

/-- For every integer n2' with n2 <= n2' <= 10^6, if get_max_repetitions(s1,n1,s2,n2) returns Ok r and get_max_repetitions(s1,n1,s2,n2') returns Ok r', then interpreting r and r' as mathematical integers, r' <= r.
  Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 100, len(s2) <= 100, 1 <= n1 <= 10^6, 1 <= n2 <= 10^6, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
theorem spec_10
    (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (n2' : Std.I64) (hn2'_lo : n2.val ≤ n2'.val) (hn2'_hi : n2'.val ≤ 1000000)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r)
    (r' : Std.I64) (hr' : get_max_repetitions s1 n1 s2 n2' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s1 : Slice Std.U8) (n1 : Std.I64) (s2 : Slice Std.U8) (n2 : Std.I64)
    (hlen1 : 1 ≤ s1.val.length) (hlen1' : s1.val.length ≤ 100)
    (hlen2 : 1 ≤ s2.val.length) (hlen2' : s2.val.length ≤ 100)
    (hn1_lo : 1 ≤ n1.val) (hn1_hi : n1.val ≤ 1000000)
    (hn2_lo : 1 ≤ n2.val) (hn2_hi : n2.val ≤ 1000000)
    (hascii1 : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (hascii2 : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
    (n2' : Std.I64) (hn2'_lo : n2.val ≤ n2'.val) (hn2'_hi : n2'.val ≤ 1000000)
    (r : Std.I64) (hr : get_max_repetitions s1 n1 s2 n2 = ok r)
    (r' : Std.I64) (hr' : get_max_repetitions s1 n1 s2 n2' = ok r'), r'.val ≤ r.val) := by
  sorry

end AegisSpec.GetMaxRepetitions
