import Aegis.BeautifulPartitions.Code.Funs

/-!
# Specifications of `Aegis.BeautifulPartitions.beautiful_partitions`

LeetCode problem `number-of-beautiful-partitions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.BeautifulPartitions

def IsAsciiDigit (c : Std.U8) : Prop := 49 ≤ c.val ∧ c.val ≤ 57

def IsPrimeDigit (c : Std.U8) : Prop :=
  c.val = 50 ∨ c.val = 51 ∨ c.val = 53 ∨ c.val = 55

def IsNonPrimeDigit (c : Std.U8) : Prop :=
  c.val = 49 ∨ c.val = 52 ∨ c.val = 54 ∨ c.val = 56 ∨ c.val = 57

instance instDecidableIsAsciiDigit (c : Std.U8) : Decidable (IsAsciiDigit c) := by
  unfold IsAsciiDigit; infer_instance

instance instDecidableIsPrimeDigit (c : Std.U8) : Decidable (IsPrimeDigit c) := by
  unfold IsPrimeDigit; infer_instance

instance instDecidableIsNonPrimeDigit (c : Std.U8) : Decidable (IsNonPrimeDigit c) := by
  unfold IsNonPrimeDigit; infer_instance

def byteAt (s : Slice Std.U8) (i : ℕ) : Option Std.U8 := s.val[i]?

def PrimeAt (s : Slice Std.U8) (i : ℕ) : Prop := ∃ c, byteAt s i = some c ∧ IsPrimeDigit c

def NonPrimeAt (s : Slice Std.U8) (i : ℕ) : Prop := ∃ c, byteAt s i = some c ∧ IsNonPrimeDigit c

def IsBeautifulPartition (s : Slice Std.U8) (k m : ℕ) (p : Fin (k + 1) → ℕ) : Prop :=
  p ⟨0, Nat.succ_pos k⟩ = 0 ∧
    p (Fin.last k) = s.val.length ∧
    StrictMono p ∧
    ∀ j : Fin k,
      m ≤ p j.succ - p j.castSucc ∧ PrimeAt s (p j.castSucc) ∧
        NonPrimeAt s (p j.succ - 1)

noncomputable def numBeautifulPartitions (s : Slice Std.U8) (k m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun q : Fin (k + 1) → Fin (s.val.length + 1) =>
    IsBeautifulPartition s k m (fun j => (q j).val))).card

noncomputable def numTwoBlockSplits (s : Slice Std.U8) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc m (s.val.length - m)).filter (fun c : ℕ =>
    PrimeAt s 0 ∧ NonPrimeAt s (c - 1) ∧ PrimeAt s c ∧
      NonPrimeAt s (s.val.length - 1))).card

noncomputable def numNonPrimePrimeTransitions (s : Slice Std.U8) : ℕ := by
  classical
  exact ((Finset.range s.val.length).filter (fun c : ℕ =>
    1 ≤ c ∧ NonPrimeAt s (c - 1) ∧ PrimeAt s c)).card

/-- Let P(c) mean that byte c is one of the ASCII bytes '2','3','5','7' (a prime digit), and let Q(c) mean that byte c is one of '1','4','6','8','9' (a non-prime digit). Let N be the number of sequences of indices 0 = p0 < p1 < ... < pk = n such that for every j with 0 ≤ j < k, the substring s[p_j ... p_{j+1}-1] has length p_{j+1}-p_j ≥ minLength, its first byte s[p_j] satisfies P, and its last byte s[p_{j+1}-1] satisfies Q. Whenever beautiful_partitions returns a result r, r is the unique integer satisfying 0 ≤ r < 1000000007 and r ≡ N (mod 1000000007).
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_1 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val
        (numBeautifulPartitions s k.val.toNat minLength.val.toNat : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r), 0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val
        (numBeautifulPartitions s k.val.toNat minLength.val.toNat : ℤ)) := by
  sorry

/-- The function beautiful_partitions returns a result r; it does not fail, panic, overflow, or access an index out of bounds.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_2 (s : Slice Std.U8) (k minLength : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ)) :
    ∃ r : Std.I64, Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ)), ∃ r : Std.I64, Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if k * max(minLength, 2) > n, then r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_3 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hbound : s.val.length < k.val.toNat * max minLength.val.toNat 2) :
    r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hbound : s.val.length < k.val.toNat * max minLength.val.toNat 2), r.val = 0) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if s[0] is not a prime digit (i.e. s[0] is not one of '2','3','5','7'), then r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_4 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hfirst : ¬ PrimeAt s 0) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hfirst : ¬ PrimeAt s 0), r.val = 0) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if s[n-1] is not a non-prime digit (i.e. s[n-1] is not one of '1','4','6','8','9'), then r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_5 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hlast : ¬ NonPrimeAt s (s.val.length - 1)) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hlast : ¬ NonPrimeAt s (s.val.length - 1)), r.val = 0) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if k = 1, then r = 1 if s[0] is a prime digit and s[n-1] is a non-prime digit, and r = 0 otherwise.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_6 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = 1) :
    (PrimeAt s 0 ∧ NonPrimeAt s (s.val.length - 1) → r.val = 1) ∧
      (¬ (PrimeAt s 0 ∧ NonPrimeAt s (s.val.length - 1)) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = 1), (PrimeAt s 0 ∧ NonPrimeAt s (s.val.length - 1) → r.val = 1) ∧
      (¬ (PrimeAt s 0 ∧ NonPrimeAt s (s.val.length - 1)) → r.val = 0)) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if k = n, then r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_7 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = (s.val.length : ℤ)) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = (s.val.length : ℤ)), r.val = 0) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, r = 1 if for every j with 0 ≤ j < k, s[j * minLength] is a prime digit and s[(j+1) * minLength - 1] is a non-prime digit; otherwise r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n, and k * minLength = n. -/
theorem spec_8 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hprod : k.val.toNat * minLength.val.toNat = s.val.length) :
    ((∀ j : ℕ, j < k.val.toNat →
        PrimeAt s (j * minLength.val.toNat) ∧
          NonPrimeAt s ((j + 1) * minLength.val.toNat - 1)) → r.val = 1) ∧
      (¬ (∀ j : ℕ, j < k.val.toNat →
          PrimeAt s (j * minLength.val.toNat) ∧
            NonPrimeAt s ((j + 1) * minLength.val.toNat - 1)) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hprod : k.val.toNat * minLength.val.toNat = s.val.length), ((∀ j : ℕ, j < k.val.toNat →
        PrimeAt s (j * minLength.val.toNat) ∧
          NonPrimeAt s ((j + 1) * minLength.val.toNat - 1)) → r.val = 1) ∧
      (¬ (∀ j : ℕ, j < k.val.toNat →
          PrimeAt s (j * minLength.val.toNat) ∧
            NonPrimeAt s ((j + 1) * minLength.val.toNat - 1)) → r.val = 0)) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, r equals the number of integers c with minLength ≤ c ≤ n - minLength such that s[0] is a prime digit, s[c-1] is a non-prime digit, s[c] is a prime digit, and s[n-1] is a non-prime digit.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n, and k = 2. -/
theorem spec_9 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = 2) :
    r.val = (numTwoBlockSplits s minLength.val.toNat : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hk : k.val = 2), r.val = (numTwoBlockSplits s minLength.val.toNat : ℤ)) := by
  sorry

/-- Let C = { c | 1 ≤ c < n, s[c-1] is a non-prime digit, and s[c] is a prime digit }. Whenever beautiful_partitions returns a result r, if |C| < k-1, then r = 0.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_10 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hC : numNonPrimePrimeTransitions s < k.val.toNat - 1) :
    r.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hC : numNonPrimePrimeTransitions s < k.val.toNat - 1), r.val = 0) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, r is the unique integer satisfying 0 ≤ r < 1000000007 and r ≡ N' (mod 1000000007), where N' is the number of sequences 0 = p0 < p1 < ... < pk = n such that for every j with 0 ≤ j < k, p_{j+1}-p_j ≥ max(minLength, 2), s[p_j] is a prime digit, and s[p_{j+1}-1] is a non-prime digit.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_11 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val
        (numBeautifulPartitions s k.val.toNat (max minLength.val.toNat 2) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r), 0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val
        (numBeautifulPartitions s k.val.toNat (max minLength.val.toNat 2) : ℤ)) := by
  sorry

/-- Whenever beautiful_partitions(s,k,minLength) returns r_s and beautiful_partitions(t,k,minLength) returns r_t, we have r_s = r_t.
  Preconditions: Let n = len(s). Take another byte string t of the same length n. Both s and t satisfy the problem constraints: n ≥ 1, n ≤ 1000, every byte of s and of t is an ASCII digit from '1' to '9', and 1 ≤ k ≤ n, 1 ≤ minLength ≤ n. Suppose that for every i with 0 ≤ i < n, s[i] is a prime digit (one of '2','3','5','7') if and only if t[i] is a prime digit. -/
theorem spec_12 (s t : Slice Std.U8) (k minLength : Std.I64) (r_s r_t : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (htn : t.val.length = s.val.length)
    (htbytes : ∀ c ∈ t.val, IsAsciiDigit c)
    (hagree : ∀ i : ℕ, i < s.val.length → (PrimeAt s i ↔ PrimeAt t i))
    (hres_s : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r_s)
    (hres_t : Aegis.BeautifulPartitions.beautiful_partitions t k minLength = ok r_t) :
    r_s.val = r_t.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t : Slice Std.U8) (k minLength : Std.I64) (r_s r_t : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (htn : t.val.length = s.val.length)
    (htbytes : ∀ c ∈ t.val, IsAsciiDigit c)
    (hagree : ∀ i : ℕ, i < s.val.length → (PrimeAt s i ↔ PrimeAt t i))
    (hres_s : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r_s)
    (hres_t : Aegis.BeautifulPartitions.beautiful_partitions t k minLength = ok r_t), r_s.val = r_t.val) := by
  sorry

/-- Whenever beautiful_partitions returns a result r, if r ≠ 0, then there exists at least one beautiful partition of s into k substrings: there are indices 0 = p0 < p1 < ... < pk = n such that for every j with 0 ≤ j < k, p_{j+1}-p_j ≥ minLength, s[p_j] is a prime digit, and s[p_{j+1}-1] is a non-prime digit.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_13 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hne : r.val ≠ 0) :
    ∃ p : Fin (k.val.toNat + 1) → ℕ,
      IsBeautifulPartition s k.val.toNat minLength.val.toNat p := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hne : r.val ≠ 0), ∃ p : Fin (k.val.toNat + 1) → ℕ,
      IsBeautifulPartition s k.val.toNat minLength.val.toNat p) := by
  sorry

/-- Let N be the number of beautiful partitions of s into k contiguous non-overlapping substrings that cover s, each of length at least minLength, each starting with a prime digit and ending with a non-prime digit. Whenever beautiful_partitions returns a result r, if N < 1000000007 then r = N.
  Preconditions: Let n = len(s). The input satisfies the problem constraints: n ≥ 1, n ≤ 1000, every byte of s is an ASCII digit from '1' to '9', and the i64 values k and minLength satisfy 1 ≤ k ≤ n and 1 ≤ minLength ≤ n. -/
theorem spec_14 (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hN : numBeautifulPartitions s k.val.toNat minLength.val.toNat < 1000000007) :
    r.val = (numBeautifulPartitions s k.val.toNat minLength.val.toNat : ℤ) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (k minLength : Std.I64) (r : Std.I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 1000)
    (hbytes : ∀ c ∈ s.val, IsAsciiDigit c)
    (hk1 : 1 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
    (hm1 : 1 ≤ minLength.val) (hmn : minLength.val ≤ (s.val.length : ℤ))
    (hres : Aegis.BeautifulPartitions.beautiful_partitions s k minLength = ok r)
    (hN : numBeautifulPartitions s k.val.toNat minLength.val.toNat < 1000000007), r.val = (numBeautifulPartitions s k.val.toNat minLength.val.toNat : ℤ)) := by
  sorry

end AegisSpec.BeautifulPartitions
