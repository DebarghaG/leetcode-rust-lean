import Aegis.TripletCount.Code.Funs

/-!
# Specifications of `Aegis.TripletCount.triplet_count`

LeetCode problem `count-triplets-with-even-xor-set-bits-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.TripletCount

open Aeneas.Std
open Aegis.TripletCount

def popcount (n : ℕ) : ℕ := ((List.range (n + 1)).filter (fun k => n.testBit k)).length

def evenPopcountNat (n : ℕ) : Prop := popcount n % 2 = 0

instance evenPopcountNat.decidable (n : ℕ) : Decidable (evenPopcountNat n) := by
  unfold evenPopcountNat
  infer_instance

def evenPopcount (x : ℤ) : Prop := evenPopcountNat x.toNat

instance evenPopcount.decidable (x : ℤ) : Decidable (evenPopcount x) := by
  unfold evenPopcount evenPopcountNat
  infer_instance

def xor3 (x y z : ℤ) : ℕ := Nat.xor (Nat.xor x.toNat y.toNat) z.toNat

def evenParity3 (x y z : ℤ) : Prop := evenPopcountNat (xor3 x y z)

instance evenParity3.decidable (x y z : ℤ) : Decidable (evenParity3 x y z) := by
  unfold evenParity3 evenPopcountNat
  infer_instance

def countEvenTriples (a b c : Slice I64) : ℕ :=
  ((a.val.product b.val).product c.val).countP
    (fun p => decide (evenParity3 p.1.1.val p.1.2.val p.2.val))

def countEvenPairsWith (x : ℤ) (b c : Slice I64) : ℕ :=
  (b.val.product c.val).countP (fun p => decide (evenParity3 x p.1.val p.2.val))

def countEvenEntries (s : Slice I64) : ℕ :=
  s.val.countP (fun x => decide (evenPopcount x.val))

def sumOverA (a b c : Slice I64) : ℕ :=
  ((List.finRange a.length).map (fun i => countEvenPairsWith (a.val.get i).val b c)).sum

def entriesWithin (s : Slice I64) (lo hi : ℤ) : Prop :=
  ∀ (i : ℕ) (h : i < s.length), lo ≤ (s.val[i]'h).val ∧ (s.val[i]'h).val ≤ hi

def SameTripleUpToOrder (x y z a b c : Slice I64) : Prop :=
  (x = a ∧ y = b ∧ z = c) ∨ (x = a ∧ y = c ∧ z = b) ∨ (x = b ∧ y = a ∧ z = c) ∨
    (x = b ∧ y = c ∧ z = a) ∨ (x = c ∧ y = a ∧ z = b) ∨ (x = c ∧ y = b ∧ z = a)

/-- Whenever triplet_count(a, b, c) returns a result r, r equals the number of ordered index triples (i, j, k) such that 0 <= i < len(a), 0 <= j < len(b), 0 <= k < len(c), and the integer a[i] XOR b[j] XOR c[k] has an even number of set bits, i.e. the number of 1s in its binary representation is even.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_1 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r → r.val = ↑(countEvenTriples a b c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r → r.val = ↑(countEvenTriples a b c)) := by
  sorry

/-- For every input satisfying the preconditions, triplet_count(a, b, c) returns some result r; it does not fail by overflow, out-of-bounds access, panic, or any other failure.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_2 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∃ r : I64, triplet_count a b c = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∃ r : I64, triplet_count a b c = ok r) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r, 0 <= r.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_3 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r, r <= len(a) * len(b) * len(c).
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_4 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r → r.val ≤ ↑(a.length * b.length * c.length) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r → r.val ≤ ↑(a.length * b.length * c.length)) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r, r = len(a) * len(b) * len(c) if and only if for every index triple (i, j, k) with 0 <= i < len(a), 0 <= j < len(b), 0 <= k < len(c), the integer a[i] XOR b[j] XOR c[k] has an even number of set bits.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_5 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r →
      (r.val = ↑(a.length * b.length * c.length) ↔
        ∀ (i : ℕ) (hi : i < a.length) (j : ℕ) (hj : j < b.length) (k : ℕ) (hk : k < c.length),
          evenParity3 (a.val[i]'hi).val (b.val[j]'hj).val (c.val[k]'hk).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r →
      (r.val = ↑(a.length * b.length * c.length) ↔
        ∀ (i : ℕ) (hi : i < a.length) (j : ℕ) (hj : j < b.length) (k : ℕ) (hk : k < c.length),
          evenParity3 (a.val[i]'hi).val (b.val[j]'hj).val (c.val[k]'hk).val)) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r, r = 0 if and only if there is no ordered index triple (i, j, k) with 0 <= i < len(a), 0 <= j < len(b), 0 <= k < len(c) such that a[i] XOR b[j] XOR c[k] has an even number of set bits. Equivalently, r > 0 if and only if at least one such even-parity triple exists.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_6 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r →
      (r.val = 0 ↔
        ¬ ∃ (i : ℕ) (hi : i < a.length) (j : ℕ) (hj : j < b.length) (k : ℕ) (hk : k < c.length),
          evenParity3 (a.val[i]'hi).val (b.val[j]'hj).val (c.val[k]'hk).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r →
      (r.val = 0 ↔
        ¬ ∃ (i : ℕ) (hi : i < a.length) (j : ℕ) (hj : j < b.length) (k : ℕ) (hk : k < c.length),
          evenParity3 (a.val[i]'hi).val (b.val[j]'hj).val (c.val[k]'hk).val)) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r and triplet_count(a', b', c') returns a result r', we have r = r'.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. Let a', b', c' be slices with len(a') = len(a), len(b') = len(b), len(c') = len(c), every entry in 0..100, and each of a', b', c' is a permutation of the corresponding original list: there exist bijections pi_a, pi_b, pi_c on the index sets such that a'[i] = a[pi_a(i)] for all 0 <= i < len(a), b'[j] = b[pi_b(j)] for all 0 <= j < len(b), and c'[k] = c[pi_c(k)] for all 0 <= k < len(c). -/
theorem spec_7 (a b c a' b' c' : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (ha' : a'.val.Perm a.val) (hb' : b'.val.Perm b.val) (hc' : c'.val.Perm c.val) :
    ∀ r r' : I64, triplet_count a b c = ok r → triplet_count a' b' c' = ok r' → r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b c a' b' c' : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (ha' : a'.val.Perm a.val) (hb' : b'.val.Perm b.val) (hc' : c'.val.Perm c.val), ∀ r r' : I64, triplet_count a b c = ok r → triplet_count a' b' c' = ok r' → r.val = r'.val) := by
  sorry

/-- For any permutation (x, y, z) of the three lists (a, b, c), i.e. any of the six orders, whenever triplet_count(a, b, c) returns a result r and triplet_count(x, y, z) returns a result r', we have r = r'.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_8 (a b c x y z : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (horder : SameTripleUpToOrder x y z a b c) :
    ∀ r r' : I64, triplet_count a b c = ok r → triplet_count x y z = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b c x y z : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (horder : SameTripleUpToOrder x y z a b c), ∀ r r' : I64, triplet_count a b c = ok r → triplet_count x y z = ok r' → r.val = r'.val) := by
  sorry

/-- Define E_a to be the number of indices i with 0 <= i < len(a) for which the number of set bits of a[i] is even, and O_a = len(a) - E_a. Define E_b, O_b, E_c, O_c analogously. Whenever triplet_count(a, b, c) returns a result r, r = E_a * E_b * E_c + E_a * O_b * O_c + O_a * E_b * O_c + O_a * O_b * E_c.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_9 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r →
      r.val = ↑(countEvenEntries a * countEvenEntries b * countEvenEntries c +
        countEvenEntries a * (b.length - countEvenEntries b) *
          (c.length - countEvenEntries c) +
        (a.length - countEvenEntries a) * countEvenEntries b *
          (c.length - countEvenEntries c) +
        (a.length - countEvenEntries a) * (b.length - countEvenEntries b) *
          countEvenEntries c) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r →
      r.val = ↑(countEvenEntries a * countEvenEntries b * countEvenEntries c +
        countEvenEntries a * (b.length - countEvenEntries b) *
          (c.length - countEvenEntries c) +
        (a.length - countEvenEntries a) * countEvenEntries b *
          (c.length - countEvenEntries c) +
        (a.length - countEvenEntries a) * (b.length - countEvenEntries b) *
          countEvenEntries c)) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r and triplet_count(a', b, c) returns a result r', we have r' = r + m.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) < 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. Additionally x is an integer with 0 <= x <= 100. Let a' be the slice obtained by appending x to a: len(a') = len(a) + 1, a'[i] = a[i] for 0 <= i < len(a), and a'[len(a)] = x. Let m be the number of pairs (j, k) with 0 <= j < len(b) and 0 <= k < len(c) such that x XOR b[j] XOR c[k] has an even number of set bits. -/
theorem spec_10 (a b c a' : Slice I64) (x : ℤ) (v : I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length < 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (hx0 : 0 ≤ x) (hx100 : x ≤ 100) (hv : v.val = x)
    (happend : a'.val = a.val ++ [v]) :
    ∀ r r' : I64, triplet_count a b c = ok r → triplet_count a' b c = ok r' →
      r'.val = r.val + ↑(countEvenPairsWith x b c) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b c a' : Slice I64) (x : ℤ) (v : I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length < 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (hx0 : 0 ≤ x) (hx100 : x ≤ 100) (hv : v.val = x)
    (happend : a'.val = a.val ++ [v]), ∀ r r' : I64, triplet_count a b c = ok r → triplet_count a' b c = ok r' →
      r'.val = r.val + ↑(countEvenPairsWith x b c)) := by
  sorry

/-- Whenever triplet_count(a, b, c1) returns a result r1, triplet_count(a, b, c2) returns a result r2, and triplet_count(a, b, c) returns a result r, we have r = r1 + r2.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. Let c1 and c2 be nonempty slices such that c = c1 ++ c2 (concatenation); in particular len(c1) >= 1, len(c2) >= 1, len(c1) + len(c2) = len(c), and all entries of c1 and c2 are between 0 and 100. -/
theorem spec_11 (a b c c1 c2 : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (hc1_ne : 1 ≤ c1.length) (hc2_ne : 1 ≤ c2.length)
    (hsplit : c.val = c1.val ++ c2.val) :
    ∀ r1 r2 r : I64, triplet_count a b c1 = ok r1 → triplet_count a b c2 = ok r2 →
      triplet_count a b c = ok r → r.val = r1.val + r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b c c1 c2 : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100)
    (hc1_ne : 1 ≤ c1.length) (hc2_ne : 1 ≤ c2.length)
    (hsplit : c.val = c1.val ++ c2.val), ∀ r1 r2 r : I64, triplet_count a b c1 = ok r1 → triplet_count a b c2 = ok r2 →
      triplet_count a b c = ok r → r.val = r1.val + r2.val) := by
  sorry

/-- Whenever triplet_count(a, b, c) returns a result r, r = the sum over i from 0 to len(a)-1 of m_i, where for each i, m_i is the number of pairs (j, k) with 0 <= j < len(b) and 0 <= k < len(c) such that a[i] XOR b[j] XOR c[k] has an even number of set bits.
  Preconditions: a, b, and c are slices of 64-bit integers with 1 <= len(a) <= 100, 1 <= len(b) <= 100, 1 <= len(c) <= 100, and for every index i with 0 <= i < len(a), 0 <= a[i] <= 100; for every index j with 0 <= j < len(b), 0 <= b[j] <= 100; for every index k with 0 <= k < len(c), 0 <= c[k] <= 100. -/
theorem spec_12 (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100) :
    ∀ r : I64, triplet_count a b c = ok r → r.val = ↑(sumOverA a b c) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (a b c : Slice I64)
    (ha1 : 1 ≤ a.length) (ha2 : a.length ≤ 100)
    (hb1 : 1 ≤ b.length) (hb2 : b.length ≤ 100)
    (hc1 : 1 ≤ c.length) (hc2 : c.length ≤ 100)
    (hA : entriesWithin a 0 100) (hB : entriesWithin b 0 100) (hC : entriesWithin c 0 100), ∀ r : I64, triplet_count a b c = ok r → r.val = ↑(sumOverA a b c)) := by
  sorry

end AegisSpec.TripletCount
