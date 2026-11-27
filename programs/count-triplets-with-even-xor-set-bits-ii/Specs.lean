import Aegis.TripletCount.Code.Funs

/-!
# Specifications of `Aegis.TripletCount.triplet_count`

LeetCode problem `count-triplets-with-even-xor-set-bits-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.TripletCount (triplet_count)

namespace AegisSpec.TripletCount

def popcount (z : Int) : Nat := (List.range (z.toNat + 1)).countP fun i => z.toNat.testBit i

def EvenPopcount (z : Int) : Prop := popcount z % 2 = 0

def OddPopcount (z : Int) : Prop := popcount z % 2 = 1

instance decidableEvenPopcount (z : Int) : Decidable (EvenPopcount z) :=
  inferInstanceAs (Decidable (popcount z % 2 = 0))

instance decidableOddPopcount (z : Int) : Decidable (OddPopcount z) :=
  inferInstanceAs (Decidable (popcount z % 2 = 1))

def tripleXor (a b c : Slice Std.I64) (i j k : Nat) : Int :=
  ((((a.val[i]!).val).toNat ^^^ (((b.val[j]!).val).toNat ^^^ ((c.val[k]!).val).toNat) : Nat) : Int)

def pairXor (b c : Slice Std.I64) (j k : Nat) : Int :=
  ((((b.val[j]!).val).toNat ^^^ ((c.val[k]!).val).toNat : Nat) : Int)

def countEvenTriples (a b c : Slice Std.I64) : Nat :=
  ((List.range a.val.length).flatMap fun i =>
      (List.range b.val.length).flatMap fun j =>
        (List.range c.val.length).map fun k => (i, j, k)).countP
    fun t => popcount (tripleXor a b c t.1 t.2.1 t.2.2) % 2 == 0

def countEvenPairs (b c : Slice Std.I64) : Nat :=
  ((List.range b.val.length).flatMap fun j =>
      (List.range c.val.length).map fun k => (j, k)).countP
    fun t => popcount (pairXor b c t.1 t.2) % 2 == 0

def countOdd (s : Slice Std.I64) : Nat := s.val.countP fun x => popcount x.val % 2 == 1

def LengthWithinBounds (s : Slice Std.I64) : Prop := 1 ≤ s.val.length ∧ s.val.length ≤ 100000

def EntriesWithinBounds (s : Slice Std.I64) : Prop := ∀ x ∈ s.val, 0 ≤ x.val ∧ x.val ≤ 1000000000

def IsPermutation3 (a b c p q s : Slice Std.I64) : Prop := [p, q, s].Perm [a, b, c]

/-- triplet_count returns a result r, and r is the number of ordered triples (i,j,k) of indices with 0 <= i < len(a), 0 <= j < len(b), and 0 <= k < len(c) such that the integer x = a[i] XOR b[j] XOR c[k] has an even number of 1-bits in its binary representation. Here popcount(0)=0, and triples with equal values but different indices are counted separately.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_1 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c) :
    ∃ r : Std.I64, triplet_count a b c = ok r ∧ r.val = (countEvenTriples a b c : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c), ∃ r : Std.I64, triplet_count a b c = ok r ∧ r.val = (countEvenTriples a b c : Int)) := by
  sorry

/-- triplet_count returns a result r; in particular, it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_2 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c) :
    ∃ r : Std.I64, triplet_count a b c = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c), ∃ r : Std.I64, triplet_count a b c = ok r) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, 0 <= r.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_3 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r <= len(a) * len(b) * len(c).
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_4 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val ≤ (a.val.length : Int) * (b.val.length : Int) * (c.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val ≤ (a.val.length : Int) * (b.val.length : Int) * (c.val.length : Int)) := by
  sorry

/-- Let Oa be the number of indices i with 0 <= i < len(a) for which popcount(a[i]) is odd, and let Ea = len(a) - Oa. Define Ob,Eb,Oc,Ec analogously for b and c. Whenever triplet_count(a,b,c) returns a result r, r = Ea*Eb*Ec + Oa*Ob*Ec + Oa*Eb*Oc + Ea*Ob*Oc, where popcount(x) is the number of 1-bits in the binary representation of the nonnegative integer x.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_5 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val = (((a.val.length - countOdd a) * (b.val.length - countOdd b) *
                (c.val.length - countOdd c) +
              countOdd a * countOdd b * (c.val.length - countOdd c) +
              countOdd a * (b.val.length - countOdd b) * countOdd c +
              (a.val.length - countOdd a) * countOdd b * countOdd c : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val = (((a.val.length - countOdd a) * (b.val.length - countOdd b) *
                (c.val.length - countOdd c) +
              countOdd a * countOdd b * (c.val.length - countOdd c) +
              countOdd a * (b.val.length - countOdd b) * countOdd c +
              (a.val.length - countOdd a) * countOdd b * countOdd c : Nat) : Int)) := by
  sorry

/-- If triplet_count(a,b,c) returns r and triplet_count(a',b,c) returns r', then r = r'. Thus changing any entry of a to another nonnegative value with the same parity of popcount does not change the count.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. Also a' is a slice with len(a')=len(a), every a'[i] lies between 0 and 1000000000 inclusive, and popcount(a'[i]) mod 2 = popcount(a[i]) mod 2 for every i with 0 <= i < len(a). -/
theorem spec_6 (a b c a' : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha'_len : a'.val.length = a.val.length)
    (ha'_val : EntriesWithinBounds a')
    (ha'_parity : ∀ i, i < a.val.length →
      popcount ((a'.val[i]!).val) % 2 = popcount ((a.val[i]!).val) % 2)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count a' b c = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b c a' : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha'_len : a'.val.length = a.val.length)
    (ha'_val : EntriesWithinBounds a')
    (ha'_parity : ∀ i, i < a.val.length →
      popcount ((a'.val[i]!).val) % 2 = popcount ((a.val[i]!).val) % 2)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count a' b c = ok r'), r.val = r'.val) := by
  sorry

/-- If triplet_count(a,b,c) returns r and triplet_count(a',b',c') returns r', then r = r'. That is, the result depends only on the multisets of values in the three arrays, not on the order of their entries.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. Also a', b', and c' are reorderings of a, b, and c respectively: len(a')=len(a), len(b')=len(b), len(c')=len(c), and their entries have the same multisets of values as a, b, and c respectively. -/
theorem spec_7 (a b c a' b' c' : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha'_perm : a'.val.Perm a.val) (hb'_perm : b'.val.Perm b.val)
    (hc'_perm : c'.val.Perm c.val)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count a' b' c' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b c a' b' c' : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha'_perm : a'.val.Perm a.val) (hb'_perm : b'.val.Perm b.val)
    (hc'_perm : c'.val.Perm c.val)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count a' b' c' = ok r'), r.val = r'.val) := by
  sorry

/-- For every permutation (p,q,s) of the three sequences (a,b,c), if triplet_count(a,b,c) returns r and triplet_count(p,q,s) returns r', then r = r'. That is, the result is symmetric in the three array arguments.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_8 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (p q s : Slice Std.I64) (hperm : IsPermutation3 a b c p q s)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count p q s = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (p q s : Slice Std.I64) (hperm : IsPermutation3 a b c p q s)
    (r r' : Std.I64) (hr : triplet_count a b c = ok r)
    (hr' : triplet_count p q s = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns r and triplet_count(a2,b,c) returns r2, r2 = 2*r.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, every element of a, b, and c lies between 0 and 1000000000 inclusive, and len(a) <= 50000. Let a2 be the slice obtained by concatenating a with itself, so len(a2)=2*len(a), a2[i]=a[i] for 0 <= i < len(a), and a2[len(a)+i]=a[i] for 0 <= i < len(a). -/
theorem spec_9 (a b c a2 : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_len_le : a.val.length ≤ 50000)
    (ha2 : a2.val = a.val ++ a.val)
    (r r2 : Std.I64) (hr : triplet_count a b c = ok r)
    (hr2 : triplet_count a2 b c = ok r2) :
    r2.val = 2 * r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b c a2 : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_len_le : a.val.length ≤ 50000)
    (ha2 : a2.val = a.val ++ a.val)
    (r r2 : Std.I64) (hr : triplet_count a b c = ok r)
    (hr2 : triplet_count a2 b c = ok r2), r2.val = 2 * r.val) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r = len(a) * len(b) * len(c).
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. Also every element of a, every element of b, and every element of c has an even number of 1-bits in its binary representation. -/
theorem spec_10 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_even : ∀ x ∈ a.val, EvenPopcount x.val)
    (hb_even : ∀ x ∈ b.val, EvenPopcount x.val)
    (hc_even : ∀ x ∈ c.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val = (a.val.length : Int) * (b.val.length : Int) * (c.val.length : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_even : ∀ x ∈ a.val, EvenPopcount x.val)
    (hb_even : ∀ x ∈ b.val, EvenPopcount x.val)
    (hc_even : ∀ x ∈ c.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val = (a.val.length : Int) * (b.val.length : Int) * (c.val.length : Int)) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r = len(a) * N, where N is the number of ordered pairs (j,k) with 0 <= j < len(b) and 0 <= k < len(c) such that popcount(b[j] XOR c[k]) is even.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. Also every element of a has an even number of 1-bits in its binary representation. -/
theorem spec_11 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_even : ∀ x ∈ a.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val = (a.val.length : Int) * (countEvenPairs b c : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_even : ∀ x ∈ a.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val = (a.val.length : Int) * (countEvenPairs b c : Int)) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r = 1 if popcount(a[0] XOR b[0] XOR c[0]) is even, and r = 0 otherwise.
  Preconditions: len(a)=len(b)=len(c)=1, and the single element of each array lies between 0 and 1000000000 inclusive. -/
theorem spec_12 (a b c : Slice Std.I64)
    (ha_len : a.val.length = 1) (hb_len : b.val.length = 1) (hc_len : c.val.length = 1)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val = if EvenPopcount (tripleXor a b c 0 0 0) then 1 else 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : a.val.length = 1) (hb_len : b.val.length = 1) (hc_len : c.val.length = 1)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val = if EvenPopcount (tripleXor a b c 0 0 0) then 1 else 0) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r = 0 if and only if for every index triple (i,j,k) with 0 <= i < len(a), 0 <= j < len(b), and 0 <= k < len(c), the integer a[i] XOR b[j] XOR c[k] has an odd number of 1-bits. Equivalently, r > 0 if and only if at least one such index triple has an even number of 1-bits in its XOR.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. -/
theorem spec_13 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    (r.val = 0 ↔ ∀ i j k, i < a.val.length → j < b.val.length → k < c.val.length →
      OddPopcount (tripleXor a b c i j k)) ∧
    (0 < r.val ↔ ∃ i j k, i < a.val.length ∧ j < b.val.length ∧ k < c.val.length ∧
      EvenPopcount (tripleXor a b c i j k)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (r : Std.I64) (hr : triplet_count a b c = ok r), (r.val = 0 ↔ ∀ i j k, i < a.val.length → j < b.val.length → k < c.val.length →
      OddPopcount (tripleXor a b c i j k)) ∧
    (0 < r.val ↔ ∃ i j k, i < a.val.length ∧ j < b.val.length ∧ k < c.val.length ∧
      EvenPopcount (tripleXor a b c i j k))) := by
  sorry

/-- Whenever triplet_count(a,b,c) returns a result r, r = 0.
  Preconditions: len(a), len(b), and len(c) are each between 1 and 100000 inclusive, and every element of a, b, and c lies between 0 and 1000000000 inclusive. Also every element of a has an odd number of 1-bits, every element of b has an even number of 1-bits, and every element of c has an even number of 1-bits. -/
theorem spec_14 (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_odd : ∀ x ∈ a.val, OddPopcount x.val)
    (hb_even : ∀ x ∈ b.val, EvenPopcount x.val)
    (hc_even : ∀ x ∈ c.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r) :
    r.val = 0 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (a b c : Slice Std.I64)
    (ha_len : LengthWithinBounds a) (hb_len : LengthWithinBounds b)
    (hc_len : LengthWithinBounds c)
    (ha_val : EntriesWithinBounds a) (hb_val : EntriesWithinBounds b)
    (hc_val : EntriesWithinBounds c)
    (ha_odd : ∀ x ∈ a.val, OddPopcount x.val)
    (hb_even : ∀ x ∈ b.val, EvenPopcount x.val)
    (hc_even : ∀ x ∈ c.val, EvenPopcount x.val)
    (r : Std.I64) (hr : triplet_count a b c = ok r), r.val = 0) := by
  sorry

end AegisSpec.TripletCount
