import Aegis.IntegerReplacement.Code.Funs

/-!
# Specifications of `Aegis.IntegerReplacement.integer_replacement`

LeetCode problem `integer-replacement`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IntegerReplacement

def ValidOpSeq (n : Int) (l : List Int) : Prop :=
  l.head? = some n ∧
  l.getLast? = some 1 ∧
  (∀ x ∈ l, 0 < x) ∧
  (∀ (i : Nat) (x : Int), l[i]? = some x → i + 1 < l.length → x ≠ 1) ∧
  (∀ (i : Nat) (x y : Int), l[i]? = some x → l[i + 1]? = some y →
    (x % 2 = 0 → y = x / 2) ∧ (x % 2 ≠ 0 → y = x + 1 ∨ y = x - 1))

def numOps (l : List Int) : Int := (l.length : Int) - 1

def ceilLog2 (n : Nat) : Nat :=
  Nat.find (p := fun k => n ≤ 2 ^ k) ⟨n, Nat.le_of_lt Nat.lt_two_pow_self⟩

/-- For every integer n satisfying the precondition, integer_replacement(n) returns a result r, and r is the least nonnegative integer k for which there exists a valid operation sequence from n to 1 of length k. A valid operation sequence from n to 1 of length k is a finite list of positive integers a_0, ..., a_k such that a_0 = n, a_k = 1, a_i != 1 for every i < k, and for every i with 0 <= i < k: if a_i is even then a_{i+1} = a_i / 2, while if a_i is odd then a_{i+1} = a_i + 1 or a_{i+1} = a_i - 1. Equivalently, r is the minimum number of allowed operations needed to turn n into 1.
  Preconditions: 1 <= n <= 2^31 - 1 (i.e. 1 <= n <= 2147483647). -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∃ r : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok r ∧
      0 ≤ r.val ∧
      (∃ l : List Int, ValidOpSeq n.val l ∧ numOps l = r.val) ∧
      (∀ l : List Int, ValidOpSeq n.val l → r.val ≤ numOps l) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∃ r : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok r ∧
      0 ≤ r.val ∧
      (∃ l : List Int, ValidOpSeq n.val l ∧ numOps l = r.val) ∧
      (∀ l : List Int, ValidOpSeq n.val l → r.val ≤ numOps l)) := by
  sorry

/-- For every integer n satisfying the precondition, integer_replacement(n) returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∃ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∃ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, 0 <= r <= 62.
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      0 ≤ r.val ∧ r.val ≤ 62 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      0 ≤ r.val ∧ r.val ≤ 62) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, r >= ceil_log2(n), where ceil_log2(n) is the least integer k >= 0 such that n <= 2^k.
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      (ceilLog2 n.val.toNat : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      (ceilLog2 n.val.toNat : Int) ≤ r.val) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, r <= 2 * ceil_log2(n), where ceil_log2(n) is the least integer k >= 0 such that n <= 2^k.
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      r.val ≤ 2 * (ceilLog2 n.val.toNat : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      r.val ≤ 2 * (ceilLog2 n.val.toNat : Int)) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, r = 0 if and only if n = 1.
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      (r.val = 0 ↔ n.val = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      (r.val = 0 ↔ n.val = 1)) := by
  sorry

/-- For every such n and k, whenever integer_replacement(n) returns a result a and integer_replacement(2^k * n) returns a result b, b = a + k.
  Preconditions: 1 <= n <= 2^31 - 1, k >= 0, and 2^k * n <= 2^31 - 1. -/
theorem spec_7 (n x : Std.I64) (k : Nat)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
    (hk : (2 : Int) ^ k * n.val ≤ 2147483647)
    (hx : x.val = (2 : Int) ^ k * n.val) :
    ∀ a b : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok a →
      Aegis.IntegerReplacement.integer_replacement x = ok b →
      b.val = a.val + (k : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n x : Std.I64) (k : Nat)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647)
    (hk : (2 : Int) ^ k * n.val ≤ 2147483647)
    (hx : x.val = (2 : Int) ^ k * n.val), ∀ a b : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok a →
      Aegis.IntegerReplacement.integer_replacement x = ok b →
      b.val = a.val + (k : Int)) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a, integer_replacement(n+1) returns b, and integer_replacement(2n+1) returns c, we have c = 2 + min(a, b).
  Preconditions: 1 <= n <= 2^30 - 1. -/
theorem spec_8 (n n1 n2 : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1073741823)
    (h1 : n1.val = n.val + 1) (h2 : n2.val = 2 * n.val + 1) :
    ∀ a b c : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok a →
      Aegis.IntegerReplacement.integer_replacement n1 = ok b →
      Aegis.IntegerReplacement.integer_replacement n2 = ok c →
      c.val = 2 + min a.val b.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n n1 n2 : Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1073741823)
    (h1 : n1.val = n.val + 1) (h2 : n2.val = 2 * n.val + 1), ∀ a b c : Std.I64,
      Aegis.IntegerReplacement.integer_replacement n = ok a →
      Aegis.IntegerReplacement.integer_replacement n1 = ok b →
      Aegis.IntegerReplacement.integer_replacement n2 = ok c →
      c.val = 2 + min a.val b.val) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, there exists a valid operation sequence from n to 1 of length r (with the same definition as in spec_1: a_0=n, a_r=1, positive entries, a_i != 1 for i < r, and each step follows the even/odd rules).
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      ∃ l : List Int, ValidOpSeq n.val l ∧ numOps l = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      ∃ l : List Int, ValidOpSeq n.val l ∧ numOps l = r.val) := by
  sorry

/-- For every integer n satisfying the precondition, whenever integer_replacement(n) returns a result r, every valid operation sequence from n to 1 has length at least r.
  Preconditions: 1 <= n <= 2^31 - 1. -/
theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647) :
    ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      ∀ l : List Int, ValidOpSeq n.val l → r.val ≤ numOps l := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 2147483647), ∀ r : Std.I64, Aegis.IntegerReplacement.integer_replacement n = ok r →
      ∀ l : List Int, ValidOpSeq n.val l → r.val ≤ numOps l) := by
  sorry

/-- Whenever integer_replacement(2147483647) returns a result r, r = 32.
  Preconditions: n = 2^31 - 1 = 2147483647. -/
theorem spec_11 :
    ∀ r : Std.I64,
      Aegis.IntegerReplacement.integer_replacement (2147483647#i64) = ok r → r.val = 32 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ r : Std.I64,
      Aegis.IntegerReplacement.integer_replacement (2147483647#i64) = ok r → r.val = 32) := by
  sorry

/-- For every such n, whenever integer_replacement(n-1) returns a, integer_replacement(n) returns b, and integer_replacement(n+1) returns c, we have b = 1 + min(a, c).
  Preconditions: 3 <= n <= 2^31 - 3 and n is odd. -/
theorem spec_12 (n nm1 np1 : Std.I64)
    (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 2147483645)
    (hodd : n.val % 2 = 1)
    (hm1 : nm1.val = n.val - 1) (hp1 : np1.val = n.val + 1) :
    ∀ a b c : Std.I64,
      Aegis.IntegerReplacement.integer_replacement nm1 = ok a →
      Aegis.IntegerReplacement.integer_replacement n = ok b →
      Aegis.IntegerReplacement.integer_replacement np1 = ok c →
      b.val = 1 + min a.val c.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n nm1 np1 : Std.I64)
    (hn1 : 3 ≤ n.val) (hn2 : n.val ≤ 2147483645)
    (hodd : n.val % 2 = 1)
    (hm1 : nm1.val = n.val - 1) (hp1 : np1.val = n.val + 1), ∀ a b c : Std.I64,
      Aegis.IntegerReplacement.integer_replacement nm1 = ok a →
      Aegis.IntegerReplacement.integer_replacement n = ok b →
      Aegis.IntegerReplacement.integer_replacement np1 = ok c →
      b.val = 1 + min a.val c.val) := by
  sorry

  end AegisSpec.IntegerReplacement
