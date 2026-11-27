import Aegis.PhonePrefix.Code.Funs

/-!
# Specifications of `Aegis.PhonePrefix.phone_prefix`

LeetCode problem `phone-number-prefix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.PhonePrefix

  def IsPrefixOf (a b : List Std.U8) : Prop :=
    a.length ≤ b.length ∧ ∀ k : Nat, k < a.length → a[k]? = b[k]?

  /-- Whenever phone_prefix(numbers) returns a result r, r is true if and only if for every i and j with 0 <= i < len(numbers), 0 <= j < len(numbers), and i != j, numbers[i] is not a prefix of numbers[j]. Here a byte vector a is a prefix of a byte vector b iff len(a) <= len(b) and for every k with 0 <= k < len(a), a[k] = b[k]. Equivalently, r is false if and only if there exist distinct indices i and j for which numbers[i] is a prefix of numbers[j].
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_1
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) :
      (r = true ↔ ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j → ¬ IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r), (r = true ↔ ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j → ¬ IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val)) := by
    sorry

  /-- The call phone_prefix(numbers) returns a result (either true or false); it does not fail, panic, go out of bounds, or overflow.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_2
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57) :
      ∃ r : Bool, Aegis.PhonePrefix.phone_prefix numbers = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57), ∃ r : Bool, Aegis.PhonePrefix.phone_prefix numbers = ok r) := by
    sorry

  /-- Let numbers' be any slice of byte vectors with len(numbers') = len(numbers) that is a permutation of numbers, i.e. there is a bijection pi on {0,...,len(numbers)-1} such that numbers'[k] = numbers[pi(k)] for every k with 0 <= k < len(numbers). Whenever phone_prefix(numbers) returns r and phone_prefix(numbers') returns r', we have r = r'.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_3
      (numbers numbers' : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (hlen' : numbers'.val.length = numbers.val.length)
      (pi : Nat → Nat)
      (hpi_mem : ∀ (i : Nat) (hi : i < numbers.val.length), pi i < numbers.val.length)
      (hpi_inj : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        pi i = pi j → i = j)
      (hperm : ∀ (k : Nat) (hk : k < numbers.val.length),
        (numbers'.val[k]).val = (numbers.val[pi k]'(hpi_mem k hk)).val)
      (r r' : Bool)
      (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r)
      (hr' : Aegis.PhonePrefix.phone_prefix numbers' = ok r') :
      r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (numbers numbers' : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (hlen' : numbers'.val.length = numbers.val.length)
        (pi : Nat → Nat)
        (hpi_mem : ∀ (i : Nat) (hi : i < numbers.val.length), pi i < numbers.val.length)
        (hpi_inj : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          pi i = pi j → i = j)
        (hperm : ∀ (k : Nat) (hk : k < numbers.val.length),
          (numbers'.val[k]).val = (numbers.val[pi k]'(hpi_mem k hk)).val)
        (r r' : Bool)
        (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r)
        (hr' : Aegis.PhonePrefix.phone_prefix numbers' = ok r'), r = r') := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r and phone_prefix(numbers') returns r', we have r = r'.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). Let d be an ASCII digit byte (48 <= d <= 57). Suppose numbers' is the slice with len(numbers') = len(numbers) and, for every i, numbers'[i] is obtained by prepending d to numbers[i], so len(numbers'[i]) = len(numbers[i]) + 1, numbers'[i][0] = d, and numbers'[i][k+1] = numbers[i][k] for every 0 <= k < len(numbers[i]). Assume also that every numbers'[i] has length at most 50 (this holds in particular if every numbers[i] has length at most 49). -/
  theorem spec_4
      (numbers numbers' : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (d : Std.U8) (hd : 48 ≤ d.val ∧ d.val ≤ 57)
      (hlen' : numbers'.val.length = numbers.val.length)
      (hprep : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers'.val[i]).val = d :: (numbers.val[i]).val)
      (hlen'_vec : ∀ (i : Nat) (hi : i < numbers'.val.length),
        (numbers'.val[i]).val.length ≤ 50)
      (r r' : Bool)
      (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r)
      (hr' : Aegis.PhonePrefix.phone_prefix numbers' = ok r') :
      r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (numbers numbers' : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (d : Std.U8) (hd : 48 ≤ d.val ∧ d.val ≤ 57)
        (hlen' : numbers'.val.length = numbers.val.length)
        (hprep : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers'.val[i]).val = d :: (numbers.val[i]).val)
        (hlen'_vec : ∀ (i : Nat) (hi : i < numbers'.val.length),
          (numbers'.val[i]).val.length ≤ 50)
        (r r' : Bool)
        (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r)
        (hr' : Aegis.PhonePrefix.phone_prefix numbers' = ok r'), r = r') := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r and r is false, there exist indices i and j with 0 <= i < j < len(numbers) such that either numbers[i] is a prefix of numbers[j] or numbers[j] is a prefix of numbers[i]. Here a is a prefix of b iff len(a) <= len(b) and a[k] = b[k] for every k with 0 <= k < len(a).
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_5
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false) :
      ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i < j ∧ (IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val ∨
                 IsPrefixOf (numbers.val[j]).val (numbers.val[i]).val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false), ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i < j ∧ (IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val ∨
                   IsPrefixOf (numbers.val[j]).val (numbers.val[i]).val)) := by
    sorry

  /-- If there exist indices i and j with 0 <= i < len(numbers), 0 <= j < len(numbers), and i != j such that numbers[i] = numbers[j] (the two byte vectors are identical), then whenever phone_prefix(numbers) returns r, r is false.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_6
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (hdup : ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j ∧ (numbers.val[i]).val = (numbers.val[j]).val)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) :
      r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (hdup : ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j ∧ (numbers.val[i]).val = (numbers.val[j]).val)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r), r = false) := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r, r is true.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). All byte vectors numbers[i] have the same length L (i.e. there exists L such that len(numbers[i]) = L for every i), and no two entries are equal (for all i != j, numbers[i] != numbers[j]). -/
  theorem spec_7
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (hlen_all : ∃ L : Nat, ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length = L)
      (hnodup : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j → (numbers.val[i]).val ≠ (numbers.val[j]).val)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) :
      r = true := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (hlen_all : ∃ L : Nat, ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length = L)
        (hnodup : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j → (numbers.val[i]).val ≠ (numbers.val[j]).val)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r), r = true) := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r, r is true if and only if for every i and j with 0 <= i < len(numbers), 0 <= j < len(numbers), and i != j, numbers[i][0] != numbers[j][0]. In other words, all one-byte phone numbers are pairwise different.
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). For every i, len(numbers[i]) = 1. -/
  theorem spec_8
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (hlen_one : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length = 1)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) :
      (r = true ↔ ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j →
          (numbers.val[i]).val[0]'(by have h := hlen_one i hi; omega) ≠
            (numbers.val[j]).val[0]'(by have h := hlen_one j hj; omega)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (hlen_one : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length = 1)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r), (r = true ↔ ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j →
            (numbers.val[i]).val[0]'(by have h := hlen_one i hi; omega) ≠
              (numbers.val[j]).val[0]'(by have h := hlen_one j hj; omega))) := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r and r is false, there exist indices i and j with 0 <= i < j < len(numbers) such that numbers[i][0] = numbers[j][0].
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). -/
  theorem spec_9
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false) :
      ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i < j ∧
          (numbers.val[i]).val[0]'(by have h := hne_nil i hi; omega) =
            (numbers.val[j]).val[0]'(by have h := hne_nil j hj; omega) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false), ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i < j ∧
            (numbers.val[i]).val[0]'(by have h := hne_nil i hi; omega) =
              (numbers.val[j]).val[0]'(by have h := hne_nil j hj; omega)) := by
    sorry

  /-- Whenever phone_prefix(numbers) returns r and r is false, there exist indices i and j with 0 <= i < len(numbers), 0 <= j < len(numbers), i != j, len(numbers[i]) < len(numbers[j]), and numbers[i] is a prefix of numbers[j]. Here prefix means len(numbers[i]) <= len(numbers[j]) and numbers[i][k] = numbers[j][k] for every 0 <= k < len(numbers[i]).
    Preconditions: numbers is a slice of byte vectors satisfying the problem constraints: 2 <= len(numbers) <= 50; for every i with 0 <= i < len(numbers), 1 <= len(numbers[i]) <= 50; and every byte numbers[i][k] is an ASCII digit '0'..'9' (48 <= numbers[i][k] <= 57). No two entries are equal: for all i != j, numbers[i] != numbers[j]. -/
  theorem spec_10
      (numbers : Slice (alloc.vec.Vec Std.U8))
      (hlen_ge : 2 ≤ numbers.val.length)
      (hlen_le : numbers.val.length ≤ 50)
      (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
        1 ≤ (numbers.val[i]).val.length)
      (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
        (numbers.val[i]).val.length ≤ 50)
      (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
        (hk : k < (numbers.val[i]).val.length),
        48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
      (hnodup : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j → (numbers.val[i]).val ≠ (numbers.val[j]).val)
      (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false) :
      ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
        i ≠ j ∧ (numbers.val[i]).val.length < (numbers.val[j]).val.length ∧
          IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (numbers : Slice (alloc.vec.Vec Std.U8))
        (hlen_ge : 2 ≤ numbers.val.length)
        (hlen_le : numbers.val.length ≤ 50)
        (hne_nil : ∀ (i : Nat) (hi : i < numbers.val.length),
          1 ≤ (numbers.val[i]).val.length)
        (hlen_vec : ∀ (i : Nat) (hi : i < numbers.val.length),
          (numbers.val[i]).val.length ≤ 50)
        (hdigits : ∀ (i : Nat) (hi : i < numbers.val.length) (k : Nat)
          (hk : k < (numbers.val[i]).val.length),
          48 ≤ ((numbers.val[i]).val[k]).val ∧ ((numbers.val[i]).val[k]).val ≤ 57)
        (hnodup : ∀ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j → (numbers.val[i]).val ≠ (numbers.val[j]).val)
        (r : Bool) (hr : Aegis.PhonePrefix.phone_prefix numbers = ok r) (hrf : r = false), ∃ (i j : Nat) (hi : i < numbers.val.length) (hj : j < numbers.val.length),
          i ≠ j ∧ (numbers.val[i]).val.length < (numbers.val[j]).val.length ∧
            IsPrefixOf (numbers.val[i]).val (numbers.val[j]).val) := by
    sorry

  end AegisSpec.PhonePrefix
