import Aegis.MinPartitions.Code.Funs

/-!
# Specifications of `Aegis.MinPartitions.min_partitions`

LeetCode problem `partitioning-into-minimum-number-of-deci-binary-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinPartitions

def decDigits : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) % 10 :: decDigits ((n + 1) / 10)
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by norm_num)

def digitAt (n : Slice Std.U8) (i : Nat) : Nat := (n.val.getD i 0#u8).val - 48

def digitList (n : Slice Std.U8) : List Nat := n.val.map (fun b => b.val - 48)

def natValue (n : Slice Std.U8) : Nat :=
  ∑ i ∈ Finset.range n.val.length, digitAt n i * 10 ^ (n.val.length - 1 - i)

def maxDigit (n : Slice Std.U8) : Nat := (digitList n).foldr max 0

def countDigit (n : Slice Std.U8) (d : Nat) : Nat := (digitList n).count d

def IsPositiveDeciBinary (a : Nat) : Prop :=
  0 < a ∧ ∀ d ∈ decDigits a, d = 0 ∨ d = 1

def IsSumOfDeciBinary (k N : Nat) : Prop :=
  ∃ a : List Nat, a.length = k ∧ (∀ x ∈ a, IsPositiveDeciBinary x) ∧ a.sum = N

def IsLeastDeciBinaryCount (N k : Nat) : Prop :=
  0 < k ∧ IsSumOfDeciBinary k N ∧ ∀ j : Nat, 0 < j → IsSumOfDeciBinary j N → k ≤ j

/-- Whenever min_partitions(n) returns a result r, r is the least positive integer k such that there exist k positive deci-binary integers a_1, ..., a_k with a_1 + ... + a_k = N(n), where N(n) is the integer represented in decimal by n, N(n) = sum over i from 0 to len(n)-1 of (n[i]-48) * 10^(len(n)-1-i), and a positive deci-binary integer means a positive integer whose usual decimal representation has no leading zero and every digit is either 0 or 1.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48, so n has no leading zero and represents a positive integer. -/
theorem spec_1 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∃ k : Nat, r.val = (k : ℤ) ∧ IsLeastDeciBinaryCount (natValue n) k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∃ k : Nat, r.val = (k : ℤ) ∧ IsLeastDeciBinaryCount (natValue n) k) := by
  sorry

/-- The call min_partitions(n) returns a result; it does not fail due to arithmetic overflow, out-of-bounds access, or any other panic.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_2 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∃ r, Aegis.MinPartitions.min_partitions n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∃ r, Aegis.MinPartitions.min_partitions n = ok r) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, r = maxDigit(n), where maxDigit(n) = max { n[i]-48 | 0 <= i < len(n) }.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_3 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r → r.val = (maxDigit n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r → r.val = (maxDigit n : ℤ)) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, 1 <= r <= 9.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_4 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r → 1 ≤ r.val ∧ r.val ≤ 9 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r → 1 ≤ r.val ∧ r.val ≤ 9) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, for every index i with 0 <= i < len(n), n[i]-48 <= r.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_5 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∀ i (hi : i < n.val.length), ((n.val[i]'hi).val : ℤ) - 48 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∀ i (hi : i < n.val.length), ((n.val[i]'hi).val : ℤ) - 48 ≤ r.val) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, there exists an index i with 0 <= i < len(n) such that n[i]-48 = r.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_6 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∃ i : Nat, ∃ hi : i < n.val.length, ((n.val[i]'hi).val : ℤ) - 48 = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∃ i : Nat, ∃ hi : i < n.val.length, ((n.val[i]'hi).val : ℤ) - 48 = r.val) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, there exist r positive deci-binary integers a_1, ..., a_r, not necessarily distinct, such that a_1 + ... + a_r = N(n), where N(n) = sum over i from 0 to len(n)-1 of (n[i]-48) * 10^(len(n)-1-i), and deci-binary means usual decimal representation with no leading zero and all digits in {0,1}.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_7 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r → IsSumOfDeciBinary r.val.toNat (natValue n) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r → IsSumOfDeciBinary r.val.toNat (natValue n)) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, for every integer k with 1 <= k < r there do not exist k positive deci-binary integers b_1, ..., b_k such that b_1 + ... + b_k = N(n), where N(n) is the integer represented by n and deci-binary means usual decimal representation with no leading zero and all digits in {0,1}.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_8 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∀ k : Nat, 1 ≤ k → (k : ℤ) < r.val → ¬ IsSumOfDeciBinary k (natValue n) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      ∀ k : Nat, 1 ≤ k → (k : ℤ) < r.val → ¬ IsSumOfDeciBinary k (natValue n)) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, r = 1 if and only if every digit of n is 0 or 1, i.e. for every i with 0 <= i < len(n), n[i] = 48 or n[i] = 49.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_9 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      (r.val = 1 ↔ ∀ i (hi : i < n.val.length), (n.val[i]'hi).val = 48 ∨ (n.val[i]'hi).val = 49) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      (r.val = 1 ↔ ∀ i (hi : i < n.val.length), (n.val[i]'hi).val = 48 ∨ (n.val[i]'hi).val = 49)) := by
  sorry

/-- Whenever min_partitions(n) returns a result r, r = 9 if and only if there exists an index i with 0 <= i < len(n) such that n[i]-48 = 9.
  Preconditions: len(n) is an integer with 1 <= len(n) <= 100000; for every i with 0 <= i < len(n), n[i] is the ASCII code of a decimal digit, i.e. 48 <= n[i] <= 57; and n[0] != 48. -/
theorem spec_10 (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48) :
    ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      (r.val = 9 ↔ ∃ i : Nat, ∃ hi : i < n.val.length, ((n.val[i]'hi).val : ℤ) - 48 = 9) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Slice Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 100000)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48), ∀ r, Aegis.MinPartitions.min_partitions n = ok r →
      (r.val = 9 ↔ ∃ i : Nat, ∃ hi : i < n.val.length, ((n.val[i]'hi).val : ℤ) - 48 = 9)) := by
  sorry

/-- Whenever min_partitions(n) returns r and min_partitions(m) returns r', we have r' >= r.
  Preconditions: n satisfies: len(n) is between 1 and 99999, every n[i] is an ASCII digit 48..57, and n[0] != 48. c is a byte with 48 <= c <= 57. m is the slice of length len(n)+1 defined by m[i]=n[i] for 0 <= i < len(n) and m[len(n)]=c; consequently len(m) <= 100000, every m[i] is an ASCII digit 48..57, and m[0]=n[0] != 48, so m has no leading zero. -/
theorem spec_11 (n m : Slice Std.U8) (c : Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 99999)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_c : 48 ≤ c.val ∧ c.val ≤ 57)
    (h_m_len : m.val.length = n.val.length + 1)
    (h_m_prefix : ∀ i (hi : i < n.val.length), m.val[i]'(by omega) = n.val[i]'hi)
    (h_m_last : m.val[n.val.length]'(by omega) = c)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48) :
    ∀ r r', Aegis.MinPartitions.min_partitions n = ok r →
      Aegis.MinPartitions.min_partitions m = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n m : Slice Std.U8) (c : Std.U8)
    (h_len_lo : 1 ≤ n.val.length)
    (h_len_hi : n.val.length ≤ 99999)
    (h_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_c : 48 ≤ c.val ∧ c.val ≤ 57)
    (h_m_len : m.val.length = n.val.length + 1)
    (h_m_prefix : ∀ i (hi : i < n.val.length), m.val[i]'(by omega) = n.val[i]'hi)
    (h_m_last : m.val[n.val.length]'(by omega) = c)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48), ∀ r r', Aegis.MinPartitions.min_partitions n = ok r →
      Aegis.MinPartitions.min_partitions m = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If for every i with 0 <= i < len(n), n[i]-48 <= m[i]-48, then whenever min_partitions(n) returns r_n and min_partitions(m) returns r_m, r_n <= r_m.
  Preconditions: Both n and m satisfy: lengths are between 1 and 100000, all entries are ASCII digits 48..57, and the first entry is not 48; additionally len(n) = len(m). -/
theorem spec_12 (n m : Slice Std.U8)
    (h_n_len_lo : 1 ≤ n.val.length)
    (h_n_len_hi : n.val.length ≤ 100000)
    (h_n_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_n_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_m_len_lo : 1 ≤ m.val.length)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48)
    (h_len_eq : n.val.length = m.val.length)
    (h_le : ∀ i (hi : i < n.val.length),
      (n.val[i]'hi).val - 48 ≤ (m.val[i]'(by omega)).val - 48) :
    ∀ r_n r_m, Aegis.MinPartitions.min_partitions n = ok r_n →
      Aegis.MinPartitions.min_partitions m = ok r_m → r_n.val ≤ r_m.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n m : Slice Std.U8)
    (h_n_len_lo : 1 ≤ n.val.length)
    (h_n_len_hi : n.val.length ≤ 100000)
    (h_n_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_n_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_m_len_lo : 1 ≤ m.val.length)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48)
    (h_len_eq : n.val.length = m.val.length)
    (h_le : ∀ i (hi : i < n.val.length),
      (n.val[i]'hi).val - 48 ≤ (m.val[i]'(by omega)).val - 48), ∀ r_n r_m, Aegis.MinPartitions.min_partitions n = ok r_n →
      Aegis.MinPartitions.min_partitions m = ok r_m → r_n.val ≤ r_m.val) := by
  sorry

/-- Whenever min_partitions(n) returns r_n and min_partitions(m) returns r_m, r_n = r_m.
  Preconditions: n satisfies: len(n) is between 1 and 100000, every n[i] is an ASCII digit 48..57, and n[0] != 48. Also m satisfies the same byte constraints, len(m)=len(n), m[0] != 48, and for every digit value d in 0..9, the number of indices i with n[i]-48=d equals the number of indices i with m[i]-48=d. -/
theorem spec_13 (n m : Slice Std.U8)
    (h_n_len_lo : 1 ≤ n.val.length)
    (h_n_len_hi : n.val.length ≤ 100000)
    (h_n_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_n_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_m_len_lo : 1 ≤ m.val.length)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48)
    (h_len_eq : n.val.length = m.val.length)
    (h_count : ∀ d : Nat, d < 10 → countDigit n d = countDigit m d) :
    ∀ r_n r_m, Aegis.MinPartitions.min_partitions n = ok r_n →
      Aegis.MinPartitions.min_partitions m = ok r_m → r_n.val = r_m.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n m : Slice Std.U8)
    (h_n_len_lo : 1 ≤ n.val.length)
    (h_n_len_hi : n.val.length ≤ 100000)
    (h_n_digits : ∀ i (hi : i < n.val.length), 48 ≤ (n.val[i]'hi).val ∧ (n.val[i]'hi).val ≤ 57)
    (h_n_no_leading_zero : (n.val[0]'(by omega)).val ≠ 48)
    (h_m_len_lo : 1 ≤ m.val.length)
    (h_m_len_hi : m.val.length ≤ 100000)
    (h_m_digits : ∀ i (hi : i < m.val.length), 48 ≤ (m.val[i]'hi).val ∧ (m.val[i]'hi).val ≤ 57)
    (h_m_no_leading_zero : (m.val[0]'(by omega)).val ≠ 48)
    (h_len_eq : n.val.length = m.val.length)
    (h_count : ∀ d : Nat, d < 10 → countDigit n d = countDigit m d), ∀ r_n r_m, Aegis.MinPartitions.min_partitions n = ok r_n →
      Aegis.MinPartitions.min_partitions m = ok r_m → r_n.val = r_m.val) := by
  sorry

end AegisSpec.MinPartitions
