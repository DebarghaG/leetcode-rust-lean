import Aegis.FindTheLongestBalancedSubstring.Code.Funs

/-!
# Specifications of `Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring`

LeetCode problem `find-the-longest-balanced-substring-of-a-binary-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindTheLongestBalancedSubstring

  def byte_zero : Nat := 48

  def byte_one : Nat := 49

  def digitAt (l : List Std.U8) (i d : Nat) : Prop :=
    ∃ b, l[i]? = some b ∧ b.val = d

  def digitsOnly (l : List Std.U8) (n : Nat) : Prop :=
    ∀ i, i < n → digitAt l i byte_zero ∨ digitAt l i byte_one

  def IsBalanced (bytes : List Std.U8) (n start k : Nat) : Prop :=
    start + 2 * k ≤ n ∧
      (∀ t, t < k → digitAt bytes (start + t) byte_zero) ∧
      (∀ t, t < k → digitAt bytes (start + k + t) byte_one)

  def countZeros (s : Slice Std.U8) : Nat :=
    s.val.countP (fun b => b.val == byte_zero)

  def countOnes (s : Slice Std.U8) : Nat :=
    s.val.countP (fun b => b.val == byte_one)

  def IsFlippedReversal (s t : Slice Std.U8) : Prop :=
    t.val.length = s.val.length ∧
      ∀ i, i < s.val.length →
        (digitAt s.val (s.val.length - 1 - i) byte_zero ∧ digitAt t.val i byte_one) ∨
          (digitAt s.val (s.val.length - 1 - i) byte_one ∧ digitAt t.val i byte_zero)

  def OccursIn (s t : Slice Std.U8) : Prop :=
    ∃ d : Nat,
      d + s.val.length ≤ t.val.length ∧
        ∀ i, i < s.val.length → ∀ b, s.val[i]? = some b → t.val[d + i]? = some b

  /-- The function returns a result r (it does not fail), and r is the greatest integer L for which there exist integers k >= 0 and l with L = 2*k, 0 <= l, l + 2*k <= n, s[l + t] = '0' for every t with 0 <= t < k, and s[l + k + t] = '1' for every t with 0 <= t < k. The empty substring (k = 0) is allowed; hence the set of such L is nonempty and r is its maximum.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_1 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∃ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r ∧
        (∃ k start : Nat, r.val = 2 * (k : Int) ∧ IsBalanced s.val n start k) ∧
        (∀ k start : Nat, IsBalanced s.val n start k → 2 * (k : Int) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∃ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r ∧
          (∃ k start : Nat, r.val = 2 * (k : Int) ∧ IsBalanced s.val n start k) ∧
          (∀ k start : Nat, IsBalanced s.val n start k → 2 * (k : Int) ≤ r.val)) := by
    sorry

  /-- Every s satisfying the preconditions yields a returned result r; the function does not panic, does not access outside the slice, and does not fail due to arithmetic overflow.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_2 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∃ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∃ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_3 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= n.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_4 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        r.val ≤ (n : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          r.val ≤ (n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer k >= 0 such that r = 2*k; equivalently, r is even.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_5 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        ∃ k : Nat, r.val = 2 * (k : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          ∃ k : Nat, r.val = 2 * (k : Int)) := by
    sorry

  /-- Whenever the function returns a result r, there exist integers k >= 0 and l such that r = 2*k, 0 <= l, l + 2*k <= n, s[l + t] = '0' for every t with 0 <= t < k, and s[l + k + t] = '1' for every t with 0 <= t < k.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_6 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        ∃ k start : Nat, r.val = 2 * (k : Int) ∧ IsBalanced s.val n start k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          ∃ k start : Nat, r.val = 2 * (k : Int) ∧ IsBalanced s.val n start k) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k >= 0 and every integer l with 0 <= l and l + 2*k <= n, if s[l + t] = '0' for every t with 0 <= t < k and s[l + k + t] = '1' for every t with 0 <= t < k, then 2*k <= r.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_7 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        ∀ k start : Nat, IsBalanced s.val n start k → 2 * (k : Int) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          ∀ k start : Nat, IsBalanced s.val n start k → 2 * (k : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if z is the number of indices i with 0 <= i < n and s[i] = '0', and o is the number of indices i with 0 <= i < n and s[i] = '1', then r <= 2 * min(z, o).
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_8 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        r.val ≤ 2 * ((min (countZeros s) (countOnes s) : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          r.val ≤ 2 * ((min (countZeros s) (countOnes s) : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an index i with 0 <= i < n - 1 such that s[i] = '0' and s[i + 1] = '1'.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_9 (s : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        (0 < r.val ↔ ∃ i : Nat, i + 1 < n ∧ digitAt s.val i byte_zero ∧ digitAt s.val (i + 1) byte_one) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          (0 < r.val ↔ ∃ i : Nat, i + 1 < n ∧ digitAt s.val i byte_zero ∧ digitAt s.val (i + 1) byte_one)) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 * min(a, b).
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, every byte is '0' or '1', and there exist integers a >= 0 and b >= 0 with a + b = n, s[i] = '0' for every i with 0 <= i < a, and s[i] = '1' for every i with a <= i < n. -/
  theorem spec_10 (s : Slice Std.U8) (n a b : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n)
      (hab : a + b = n)
      (hzeros : ∀ i, i < a → digitAt s.val i byte_zero)
      (hones : ∀ i, a ≤ i → i < n → digitAt s.val i byte_one) :
      ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
        r.val = 2 * ((min a b : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (n a b : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n)
        (hab : a + b = n)
        (hzeros : ∀ i, i < a → digitAt s.val i byte_zero)
        (hones : ∀ i, a ≤ i → i < n → digitAt s.val i byte_one), ∀ r : Std.I64, Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r →
          r.val = 2 * ((min a b : Nat) : Int)) := by
    sorry

  /-- Let t be the byte slice of length n defined by t[i] = '1' when s[n - 1 - i] = '0', and t[i] = '0' when s[n - 1 - i] = '1', for 0 <= i < n. Whenever the calls on s and on t both return results r_s and r_t, we have r_s = r_t.
    Preconditions: s is a byte slice of length n with 1 <= n <= 50, and for every i with 0 <= i < n, s[i] is the byte encoding of either '0' or '1'. -/
  theorem spec_11 (s t : Slice Std.U8) (n : Nat)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
      (hbin : digitsOnly s.val n)
      (hrev : IsFlippedReversal s t) :
      ∀ r_s r_t : Std.I64,
        Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r_s →
        Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring t = ok r_t →
        r_s.val = r_t.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (n : Nat)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 50) (hlen : s.val.length = n)
        (hbin : digitsOnly s.val n)
        (hrev : IsFlippedReversal s t), ∀ r_s r_t : Std.I64,
          Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r_s →
          Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring t = ok r_t →
          r_s.val = r_t.val) := by
    sorry

  /-- Whenever the calls on s and on t both return results r_s and r_t, we have r_s <= r_t.
    Preconditions: s and t are byte slices satisfying the same constraints: each has length between 1 and 50 and every byte is '0' or '1'. Let n_s = len(s) and n_t = len(t). Suppose s occurs as a contiguous substring of t, i.e., there exists an integer d with 0 <= d and d + n_s <= n_t and t[d + i] = s[i] for every i with 0 <= i < n_s. -/
  theorem spec_12 (s t : Slice Std.U8) (ns nt : Nat)
      (hns_pos : 1 ≤ ns) (hns_le : ns ≤ 50) (hns_len : s.val.length = ns)
      (hns_bin : digitsOnly s.val ns)
      (hnt_pos : 1 ≤ nt) (hnt_le : nt ≤ 50) (hnt_len : t.val.length = nt)
      (hnt_bin : digitsOnly t.val nt)
      (hsub : OccursIn s t) :
      ∀ r_s r_t : Std.I64,
        Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r_s →
        Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring t = ok r_t →
        r_s.val ≤ r_t.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8) (ns nt : Nat)
        (hns_pos : 1 ≤ ns) (hns_le : ns ≤ 50) (hns_len : s.val.length = ns)
        (hns_bin : digitsOnly s.val ns)
        (hnt_pos : 1 ≤ nt) (hnt_le : nt ≤ 50) (hnt_len : t.val.length = nt)
        (hnt_bin : digitsOnly t.val nt)
        (hsub : OccursIn s t), ∀ r_s r_t : Std.I64,
          Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring s = ok r_s →
          Aegis.FindTheLongestBalancedSubstring.find_the_longest_balanced_substring t = ok r_t →
          r_s.val ≤ r_t.val) := by
    sorry

  end AegisSpec.FindTheLongestBalancedSubstring
