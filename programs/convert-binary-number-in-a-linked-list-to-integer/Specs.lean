import Aegis.GetDecimalValue.Code.Funs

/-!
# Specifications of `Aegis.GetDecimalValue.get_decimal_value`

LeetCode problem `convert-binary-number-in-a-linked-list-to-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.GetDecimalValue

def nodeVals : Aegis.GetDecimalValue.List → List ℤ
  | .Nil => []
  | .Cons v rest => v.val :: nodeVals rest

def binaryValue : List ℤ → ℤ
  | [] => 0
  | b :: bs => b * (2 : ℤ) ^ bs.length + binaryValue bs

def append :
    Aegis.GetDecimalValue.List → Aegis.GetDecimalValue.List → Aegis.GetDecimalValue.List
  | .Nil, l => l
  | .Cons v rest, l => .Cons v (append rest l)

def bitAt (x : ℤ) (k : ℕ) : ℤ := (x / (2 : ℤ) ^ k) % 2

/-- The evaluation of get_decimal_value head returns a result r : i64 such that r = sum_{i=0}^{n-1} b_i * 2^(n-1-i).
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_1 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = ∑ i ∈ Finset.range (nodeVals head).length,
        (nodeVals head).getD i 0 * (2 : ℤ) ^ ((nodeVals head).length - 1 - i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = ∑ i ∈ Finset.range (nodeVals head).length,
        (nodeVals head).getD i 0 * (2 : ℤ) ^ ((nodeVals head).length - 1 - i)) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64; in particular, it does not fail, panic, or overflow.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_2 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64 such that 0 <= r <= 2^n - 1.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_3 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (2 : ℤ) ^ (nodeVals head).length - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (2 : ℤ) ^ (nodeVals head).length - 1) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64 such that 0 <= r <= 1073741823, where 1073741823 = 2^30 - 1.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_4 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 1073741823 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 1073741823) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64, and r = 0 if and only if b_i = 0 for every i with 0 <= i < n.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_5 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      (r.val = 0 ↔ ∀ i, i < (nodeVals head).length → (nodeVals head).getD i 0 = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      (r.val = 0 ↔ ∀ i, i < (nodeVals head).length → (nodeVals head).getD i 0 = 0)) := by
  sorry

/-- If b_i = 1 for every i with 0 <= i < n, then the evaluation of get_decimal_value head returns a result r : i64 with r = 2^n - 1.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_6 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hall1 : ∀ i, i < (nodeVals head).length → (nodeVals head).getD i 0 = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = (2 : ℤ) ^ (nodeVals head).length - 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hall1 : ∀ i, i < (nodeVals head).length → (nodeVals head).getD i 0 = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = (2 : ℤ) ^ (nodeVals head).length - 1) := by
  sorry

/-- If n = 1, then the evaluation of get_decimal_value head returns a result r : i64 with r = b_0.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_7 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hn_eq : (nodeVals head).length = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = (nodeVals head).getD 0 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hn_eq : (nodeVals head).length = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = (nodeVals head).getD 0 0) := by
  sorry

/-- If b_0 = 0, then the evaluation of get_decimal_value head returns a result r : i64 such that r = sum_{i=1}^{n-1} b_i * 2^(n-1-i). For n = 1 this empty sum is 0.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_8 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hb0 : (nodeVals head).getD 0 0 = 0) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = ∑ i ∈ Finset.Ico 1 (nodeVals head).length,
        (nodeVals head).getD i 0 * (2 : ℤ) ^ ((nodeVals head).length - 1 - i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hb0 : (nodeVals head).getD 0 0 = 0), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = ∑ i ∈ Finset.Ico 1 (nodeVals head).length,
        (nodeVals head).getD i 0 * (2 : ℤ) ^ ((nodeVals head).length - 1 - i)) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64 such that r mod 2 = b_{n-1}.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_9 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val % 2 = (nodeVals head).getD ((nodeVals head).length - 1) 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val % 2 = (nodeVals head).getD ((nodeVals head).length - 1) 0) := by
  sorry

/-- Suppose head is obtained by taking a list h (possibly Nil) and appending one additional final node with value b, where b is 0 or 1. Let V(h) be the binary value of h, defined by V(Nil) = 0 and, if h has m nodes with values c_0,...,c_{m-1} from head to tail, V(h) = sum_{j=0}^{m-1} c_j * 2^(m-1-j). Then the evaluation of get_decimal_value head returns a result r : i64 with r = 2 * V(h) + b.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_10 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (h : Aegis.GetDecimalValue.List) (b : I64)
    (hb : b.val = 0 ∨ b.val = 1)
    (hhead : head = append h (.Cons b .Nil)) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = 2 * binaryValue (nodeVals h) + b.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (h : Aegis.GetDecimalValue.List) (b : I64)
    (hb : b.val = 0 ∨ b.val = 1)
    (hhead : head = append h (.Cons b .Nil)), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = 2 * binaryValue (nodeVals h) + b.val) := by
  sorry

/-- Write head = Cons(b_0, tail), where tail may be Nil, and let V(tail) be the binary value of tail with V(Nil) = 0 and with the usual most-significant-at-head interpretation for nonempty tail. Then the evaluation of get_decimal_value head returns a result r : i64 with r = b_0 * 2^(n-1) + V(tail).
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_11 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (b0 : I64) (tail : Aegis.GetDecimalValue.List)
    (hhead : head = .Cons b0 tail) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = b0.val * (2 : ℤ) ^ ((nodeVals head).length - 1) + binaryValue (nodeVals tail) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (b0 : I64) (tail : Aegis.GetDecimalValue.List)
    (hhead : head = .Cons b0 tail), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      r.val = b0.val * (2 : ℤ) ^ ((nodeVals head).length - 1) + binaryValue (nodeVals tail)) := by
  sorry

/-- The evaluation of get_decimal_value head returns a result r : i64 such that, for every i with 0 <= i < n, the bit of r at position n-1-i (where bit 0 is the least significant bit) equals b_i. Equivalently, the n-bit binary expansion of r, padded on the left with zeros to length n, is b_0 b_1 ... b_{n-1}.
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_12 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      ∀ i, i < (nodeVals head).length →
        bitAt r.val ((nodeVals head).length - 1 - i) = (nodeVals head).getD i 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      ∀ i, i < (nodeVals head).length →
        bitAt r.val ((nodeVals head).length - 1 - i) = (nodeVals head).getD i 0) := by
  sorry

/-- If b_0 = 1, then the evaluation of get_decimal_value head returns a result r : i64 with r >= 2^(n-1).
  Preconditions: head is not Nil; the number n of nodes in head satisfies 1 <= n <= 30; and for every i with 0 <= i < n, the value b_i of the i-th node from the head (0-indexed) is either 0 or 1. -/
theorem spec_13 (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hb0 : (nodeVals head).getD 0 0 = 1) :
    ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      (2 : ℤ) ^ ((nodeVals head).length - 1) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (head : Aegis.GetDecimalValue.List)
    (hne : head ≠ .Nil)
    (hn1 : 1 ≤ (nodeVals head).length)
    (hn30 : (nodeVals head).length ≤ 30)
    (hbits : ∀ b ∈ nodeVals head, b = 0 ∨ b = 1)
    (hb0 : (nodeVals head).getD 0 0 = 1), ∃ r : I64, Aegis.GetDecimalValue.get_decimal_value head = ok r ∧
      (2 : ℤ) ^ ((nodeVals head).length - 1) ≤ r.val) := by
  sorry

end AegisSpec.GetDecimalValue
