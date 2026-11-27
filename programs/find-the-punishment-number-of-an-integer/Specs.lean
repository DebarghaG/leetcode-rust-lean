import Aegis.PunishmentNumber.Code.Funs

/-!
# Specifications of `Aegis.PunishmentNumber.punishment_number`

LeetCode problem `find-the-punishment-number-of-an-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PunishmentNumber

open Aegis.PunishmentNumber

def revDigitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x = 0 then [] else (x % 10) :: revDigitsAux fuel (x / 10)

def decDigits (x : Nat) : List Nat := (revDigitsAux (x + 1) x).reverse

def decValue : List Nat → Nat
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + decValue ds

def Chunks (l : List Nat) (cs : List (List Nat)) : Prop :=
  cs ≠ [] ∧ (∀ c ∈ cs, c ≠ []) ∧ cs.flatten = l

def Good (i : Nat) : Prop :=
  1 ≤ i ∧ ∃ cs : List (List Nat), Chunks (decDigits (i * i)) cs ∧ (cs.map decValue).sum = i

noncomputable instance decidableGood (i : Nat) : Decidable (Good i) := Classical.propDecidable _

/-- Let good(i) mean: i >= 1 and the decimal string d of i*i (written without leading zeros, as usual) admits indices 0 = p0 < p1 < ... < pk = len(d) for some k >= 1 such that each substring d[p_{j-1}..p_j) is nonempty, is interpreted as a decimal integer (leading zeros inside a substring are allowed and contribute the usual value), and the sum of these k substring values equals i. Whenever punishment_number(n) returns a result r, r = sum_{i=1}^{n} (i*i if good(i) else 0).
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Std.I64, punishment_number n = ok r →
      r.val = ∑ i ∈ Finset.Icc 1 n.val.toNat, if Good i then ((i * i : Nat) : ℤ) else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, punishment_number n = ok r →
      r.val = ∑ i ∈ Finset.Icc 1 n.val.toNat, if Good i then ((i * i : Nat) : ℤ) else 0) := by
  sorry

/-- punishment_number(n) returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∃ r : Std.I64, punishment_number n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∃ r : Std.I64, punishment_number n = ok r) := by
  sorry

/-- Whenever punishment_number(n) returns a result r, r >= 1.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Std.I64, punishment_number n = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, punishment_number n = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever punishment_number(n) returns a result r, r <= sum_{i=1}^{n} i*i.
  Preconditions: n is an integer with 1 <= n <= 1000. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Std.I64, punishment_number n = ok r →
      r.val ≤ ∑ i ∈ Finset.Icc 1 n.val.toNat, ((i * i : Nat) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, punishment_number n = ok r →
      r.val ≤ ∑ i ∈ Finset.Icc 1 n.val.toNat, ((i * i : Nat) : ℤ)) := by
  sorry

/-- Whenever punishment_number(n) returns r_n and punishment_number(m) returns r_m, r_n <= r_m.
  Preconditions: n and m are integers with 1 <= n <= m <= 1000. -/
theorem spec_5 (n m : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm2 : m.val ≤ 1000) :
    ∀ rn rm : Std.I64, punishment_number n = ok rn → punishment_number m = ok rm →
      rn.val ≤ rm.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n m : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm2 : m.val ≤ 1000), ∀ rn rm : Std.I64, punishment_number n = ok rn → punishment_number m = ok rm →
      rn.val ≤ rm.val) := by
  sorry

/-- Whenever punishment_number(n) returns r_n and punishment_number(n-1) returns r_{n-1}, and good(n) means the decimal representation of n*n can be partitioned into contiguous nonempty substrings whose integer values sum to n, we have: r_n - r_{n-1} equals n*n when good(n) holds, and equals 0 when good(n) does not hold.
  Preconditions: n is an integer with 2 <= n <= 1000. -/
theorem spec_6 (n nm1 : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hsub : n - 1#i64 = ok nm1) :
    ∀ rn rnm1 : Std.I64, punishment_number n = ok rn → punishment_number nm1 = ok rnm1 →
      rn.val - rnm1.val =
        if Good n.val.toNat then (((n.val.toNat) * (n.val.toNat) : Nat) : ℤ) else 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n nm1 : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 1000)
    (hsub : n - 1#i64 = ok nm1), ∀ rn rnm1 : Std.I64, punishment_number n = ok rn → punishment_number nm1 = ok rnm1 →
      rn.val - rnm1.val =
        if Good n.val.toNat then (((n.val.toNat) * (n.val.toNat) : Nat) : ℤ) else 0) := by
  sorry

/-- Whenever punishment_number(n) returns a result r, r = 1.
  Preconditions: n is an integer with 1 <= n <= 8. -/
theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 8) :
    ∀ r : Std.I64, punishment_number n = ok r → r.val = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 8), ∀ r : Std.I64, punishment_number n = ok r → r.val = 1) := by
  sorry

/-- punishment_number(9) returns a result r and r = 82.
  Preconditions: n = 9. -/
theorem spec_8 : ∃ r : Std.I64, punishment_number 9#i64 = ok r ∧ r.val = 82 := by
  sorry

theorem spec_8_neg :
    ¬ (∃ r : Std.I64, punishment_number 9#i64 = ok r ∧ r.val = 82) := by
  sorry

/-- punishment_number(10) returns a result r and r = 182.
  Preconditions: n = 10. -/
theorem spec_9 : ∃ r : Std.I64, punishment_number 10#i64 = ok r ∧ r.val = 182 := by
  sorry

theorem spec_9_neg :
    ¬ (∃ r : Std.I64, punishment_number 10#i64 = ok r ∧ r.val = 182) := by
  sorry

/-- punishment_number(37) returns a result r and r = 1478.
  Preconditions: n = 37. -/
theorem spec_10 : ∃ r : Std.I64, punishment_number 37#i64 = ok r ∧ r.val = 1478 := by
  sorry

theorem spec_10_neg :
    ¬ (∃ r : Std.I64, punishment_number 37#i64 = ok r ∧ r.val = 1478) := by
  sorry

/-- punishment_number(100) returns a result r and r = 41334.
  Preconditions: n = 100. -/
theorem spec_11 : ∃ r : Std.I64, punishment_number 100#i64 = ok r ∧ r.val = 41334 := by
  sorry

theorem spec_11_neg :
    ¬ (∃ r : Std.I64, punishment_number 100#i64 = ok r ∧ r.val = 41334) := by
  sorry

/-- punishment_number(600) returns a result r and r = 772866.
  Preconditions: n = 600. -/
theorem spec_12 : ∃ r : Std.I64, punishment_number 600#i64 = ok r ∧ r.val = 772866 := by
  sorry

theorem spec_12_neg :
    ¬ (∃ r : Std.I64, punishment_number 600#i64 = ok r ∧ r.val = 772866) := by
  sorry

/-- punishment_number(700) returns a result r and r = 1660140.
  Preconditions: n = 700. -/
theorem spec_13 : ∃ r : Std.I64, punishment_number 700#i64 = ok r ∧ r.val = 1660140 := by
  sorry

theorem spec_13_neg :
    ¬ (∃ r : Std.I64, punishment_number 700#i64 = ok r ∧ r.val = 1660140) := by
  sorry

/-- punishment_number(800) returns a result r and r = 3353149.
  Preconditions: n = 800. -/
theorem spec_14 : ∃ r : Std.I64, punishment_number 800#i64 = ok r ∧ r.val = 3353149 := by
  sorry

theorem spec_14_neg :
    ¬ (∃ r : Std.I64, punishment_number 800#i64 = ok r ∧ r.val = 3353149) := by
  sorry

/-- Whenever punishment_number(n) returns a result r, r >= 1478.
  Preconditions: n is an integer with 36 <= n <= 1000. -/
theorem spec_15 (n : Std.I64) (hn1 : 36 ≤ n.val) (hn2 : n.val ≤ 1000) :
    ∀ r : Std.I64, punishment_number n = ok r → 1478 ≤ r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 36 ≤ n.val) (hn2 : n.val ≤ 1000), ∀ r : Std.I64, punishment_number n = ok r → 1478 ≤ r.val) := by
  sorry

/-- punishment_number(1000) returns a result r and r = 10804657.
  Preconditions: n = 1000. -/
theorem spec_16 : ∃ r : Std.I64, punishment_number 1000#i64 = ok r ∧ r.val = 10804657 := by
  sorry

theorem spec_16_neg :
    ¬ (∃ r : Std.I64, punishment_number 1000#i64 = ok r ∧ r.val = 10804657) := by
  sorry

end AegisSpec.PunishmentNumber
