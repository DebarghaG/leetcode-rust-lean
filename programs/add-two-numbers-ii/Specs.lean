import Aegis.AddTwoNumbers.Code.Funs

/-!
# Specifications of `Aegis.AddTwoNumbers.add_two_numbers`

LeetCode problem `add-two-numbers-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AddTwoNumbers

abbrev LList := Aegis.AddTwoNumbers.List

def digits : LList → List Int
  | .Nil => []
  | .Cons value next => value.val :: digits next

def len (L : LList) : Nat := (digits L).length

def val : LList → Int
  | .Nil => 0
  | .Cons value next => value.val * 10 ^ len next + val next

def firstVal (L : LList) : Option Int := (digits L).head?

def lastVal (L : LList) : Option Int := (digits L).getLast?

def digitsInRange (L : LList) : Prop := ∀ d ∈ digits L, 0 ≤ d ∧ d ≤ 9

def noLeadingZero (L : LList) : Prop :=
  ∀ (d : Int) (ds : List Int), digits L = d :: ds → ds ≠ [] → d ≠ 0

/-- Write digits(L) for the sequence of node values of a non-empty list L from head to tail, and write val(L) = sum_{i=0}^{len(L)-1} d_i * 10^{len(L)-1-i}, where d_i is the i-th value in digits(L). Let N = val(l1) + val(l2). The function returns a result r such that, writing digits(r) = [e_0, ..., e_{k-1}], we have k >= 1; 0 <= e_i <= 9 for every 0 <= i < k; if k > 1 then e_0 != 0; and N = sum_{i=0}^{k-1} e_i * 10^{k-1-i}. Equivalently, r is the unique canonical base-10 representation of N, most significant digit first.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_1 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∃ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r ∧ r ≠ .Nil ∧
      digitsInRange r ∧ noLeadingZero r ∧ val r = val l1 + val l2 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∃ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r ∧ r ≠ .Nil ∧
      digitsInRange r ∧ noLeadingZero r ∧ val r = val l1 + val l2) := by
  sorry

/-- For every l1 and l2 satisfying the preconditions, the function add_two_numbers l1 l2 returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_2 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∃ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∃ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r) := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, r is not Nil; equivalently, len(r) >= 1.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_3 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → r ≠ .Nil := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → r ≠ .Nil) := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, every node value of r is an integer between 0 and 9 inclusive.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_4 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → digitsInRange r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → digitsInRange r) := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, if len(r) > 1 then the first node value of r is not 0. Equivalently, the only one-node output allowed to begin with 0 is the list [0]; there are no leading zeros in a multi-digit output.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_5 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → noLeadingZero r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → noLeadingZero r) := by
  sorry

/-- Define digits(L) as the node-value sequence from head to tail, and for non-empty L define val(L) = sum_{i=0}^{len(L)-1} d_i * 10^{len(L)-1-i}. Whenever add_two_numbers l1 l2 returns a result r, val(r) = val(l1) + val(l2).
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_6 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → val r = val l1 + val l2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r → val r = val l1 + val l2) := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, let M = max(len(l1), len(l2)). Then len(r) = M or len(r) = M + 1. In particular, because both inputs have length at most 100, len(r) <= 101.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_7 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      (len r = Nat.max (len l1) (len l2) ∨ len r = Nat.max (len l1) (len l2) + 1) ∧
        len r ≤ 101 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      (len r = Nat.max (len l1) (len l2) ∨ len r = Nat.max (len l1) (len l2) + 1) ∧
        len r ≤ 101) := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, let M = max(len(l1), len(l2)). If len(r) = M + 1, then the first node value of r is exactly 1.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_8 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      len r = Nat.max (len l1) (len l2) + 1 → firstVal r = some 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      len r = Nat.max (len l1) (len l2) + 1 → firstVal r = some 1) := by
  sorry

/-- Define val(L) as in the numerical meaning of the list. Whenever add_two_numbers l1 l2 returns a result r, val(l1) + val(l2) = 0 if and only if r has exactly one node and that node's value is 0, i.e. digits(r) = [0]. Under the preconditions this is equivalent to both l1 and l2 being the single-node list [0].
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_9 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      (val l1 + val l2 = 0 ↔ digits r = [0]) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      (val l1 + val l2 = 0 ↔ digits r = [0])) := by
  sorry

/-- Define digits(L) as the node-value sequence from head to tail and val(L) as in the numerical meaning of the list. Whenever add_two_numbers l1 l2 returns a result r, if val(l1) = 0 then digits(r) = digits(l2); symmetrically, if val(l2) = 0 then digits(r) = digits(l1).
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_10 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      ((val l1 = 0 → digits r = digits l2) ∧ (val l2 = 0 → digits r = digits l1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      ((val l1 = 0 → digits r = digits l2) ∧ (val l2 = 0 → digits r = digits l1))) := by
  sorry

/-- For every l1 and l2 satisfying the preconditions, whenever add_two_numbers l1 l2 returns r and add_two_numbers l2 l1 returns r', the node-value sequences digits(r) and digits(r') are equal.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_11 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      ∀ r', Aegis.AddTwoNumbers.add_two_numbers l2 l1 = ok r' → digits r = digits r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      ∀ r', Aegis.AddTwoNumbers.add_two_numbers l2 l1 = ok r' → digits r = digits r') := by
  sorry

/-- Whenever add_two_numbers l1 l2 returns a result r, r is non-empty, and if a is the last node value of l1 and b is the last node value of l2, then the last node value of r is (a + b) mod 10.
  Preconditions: l1 and l2 are non-empty finite linked lists; len(l1) and len(l2) are in the range [1, 100]; every node value in l1 and l2 is an integer between 0 and 9 inclusive; and neither list has a leading zero: if len(l1) > 1 then the first node value of l1 is not 0, and if len(l2) > 1 then the first node value of l2 is not 0. -/
theorem spec_12 (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2)
    (a b : Int) (ha : lastVal l1 = some a) (hb : lastVal l2 = some b) :
    ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      r ≠ .Nil ∧ lastVal r = some ((a + b) % 10) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (l1 l2 : LList)
    (hne1 : l1 ≠ .Nil) (hne2 : l2 ≠ .Nil)
    (hlen1 : 1 ≤ len l1 ∧ len l1 ≤ 100)
    (hlen2 : 1 ≤ len l2 ∧ len l2 ≤ 100)
    (hrange1 : digitsInRange l1) (hrange2 : digitsInRange l2)
    (hnlz1 : noLeadingZero l1) (hnlz2 : noLeadingZero l2)
    (a b : Int) (ha : lastVal l1 = some a) (hb : lastVal l2 = some b), ∀ r, Aegis.AddTwoNumbers.add_two_numbers l1 l2 = ok r →
      r ≠ .Nil ∧ lastVal r = some ((a + b) % 10)) := by
  sorry

end AegisSpec.AddTwoNumbers
