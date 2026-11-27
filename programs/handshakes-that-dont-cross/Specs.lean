import Aegis.NumberOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumberOfWays.number_of_ways`

LeetCode problem `handshakes-that-dont-cross`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfWays

def OnClockwiseArc (n a b x : Nat) : Prop :=
  0 < (x + n - a) % n ∧ (x + n - a) % n < (b + n - a) % n

def PairsCross (n a b c d : Nat) : Prop :=
  Xor (OnClockwiseArc n a b c) (OnClockwiseArc n a b d)

def IsHandshakeArrangement (n : Nat) (P : Finset (Finset (Fin n))) : Prop :=
  (∀ p ∈ P, p.card = 2) ∧ ∀ i : Fin n, ∃! p, p ∈ P ∧ i ∈ p

def IsNoncrossingArrangement (n : Nat) (P : Finset (Finset (Fin n))) : Prop :=
  IsHandshakeArrangement n P ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ a ∈ p, ∀ b ∈ p, ∀ c ∈ q, ∀ d ∈ q,
      a ≠ b → c ≠ d → ¬ PairsCross n a.val b.val c.val d.val

noncomputable def count (n : Nat) : Nat :=
  Nat.card { P : Finset (Finset (Fin n)) // IsNoncrossingArrangement n P }

def catalan : Nat → Nat
  | 0 => 1
  | (k + 1) => ∑ i ∈ (Finset.range (k + 1)).attach, catalan i.1 * catalan (k - i.1)
termination_by n => n
decreasing_by
  all_goals
    have h := Finset.mem_range.mp i.2
    omega

def dyckSteps (k : Nat) (f : Fin (2 * k) → Bool) : List Int :=
  List.ofFn fun i : Fin (2 * k) => if f i then 1 else -1

def IsDyckPath (k : Nat) (f : Fin (2 * k) → Bool) : Prop :=
  (dyckSteps k f).sum = 0 ∧ ∀ j : Fin (2 * k + 1), 0 ≤ ((dyckSteps k f).take j.val).sum

noncomputable def dyckCount (k : Nat) : Nat :=
  Nat.card { f : Fin (2 * k) → Bool // IsDyckPath k f }

/-- Let n = numPeople and M = 1000000007. A handshake arrangement is a set of n/2 unordered pairs {a,b} with a,b in {1,...,n}, a != b, such that every i in {1,...,n} occurs in exactly one pair. Two pairs {a,b} and {c,d} cross if, when the numbers 1,2,...,n are placed in cyclic order around a circle, the endpoints alternate; equivalently, after choosing the clockwise direction from a to b, exactly one of c,d lies in the open arc from a to b. Let Count(n) be the number of handshake arrangements with no crossing pair. The function returns a result r such that r is the unique integer with 0 <= r < M and r congruent to Count(n) modulo M.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_1 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∃ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val (count numPeople.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∃ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          Int.ModEq 1000000007 r.val (count numPeople.val.toNat)) := by
  sorry

/-- For every numPeople satisfying the preconditions, the call number_of_ways(numPeople) returns a result r; it does not fail, panic, go out of bounds, or overflow. No particular value of r is claimed by this specification.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_2 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways numPeople = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∃ r : Std.I64, Aegis.NumberOfWays.number_of_ways numPeople = ok r) := by
  sorry

/-- For every numPeople satisfying the preconditions, whenever number_of_ways(numPeople) returns a result r, the integer value of r satisfies 0 <= r < 1000000007.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_3 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- For every numPeople satisfying the preconditions, whenever number_of_ways(numPeople) returns a result r, r is congruent modulo 1000000007 to C_{numPeople/2}, where C_0 = 1 and C_{k+1} = sum_{i=0}^{k} C_i * C_{k-i} for k >= 0.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_4 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Int.ModEq 1000000007 r.val (catalan (numPeople.val.toNat / 2)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Int.ModEq 1000000007 r.val (catalan (numPeople.val.toNat / 2))) := by
  sorry

/-- Let k = numPeople/2 and M = 1000000007. Whenever number_of_ways(numPeople) returns a result r, r is congruent modulo M to binom(numPeople,k) * (k+1)^{-1}, where binom is the ordinary binomial coefficient and (k+1)^{-1} is the multiplicative inverse of k+1 modulo M; this inverse exists because 0 < k+1 <= 501 < M.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_5 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        ∃ u : Int,
          Int.ModEq 1000000007 ((numPeople.val / 2 + 1) * u) 1 ∧
            Int.ModEq 1000000007 r.val
              ((Nat.choose numPeople.val.toNat (numPeople.val.toNat / 2) : Nat) * u) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        ∃ u : Int,
          Int.ModEq 1000000007 ((numPeople.val / 2 + 1) * u) 1 ∧
            Int.ModEq 1000000007 r.val
              ((Nat.choose numPeople.val.toNat (numPeople.val.toNat / 2) : Nat) * u)) := by
  sorry

/-- Let k = numPeople/2. Whenever number_of_ways(numPeople) returns r and number_of_ways(numPeople-2) returns r_prev, the congruence (k+1) * r is congruent modulo 1000000007 to (4*k - 2) * r_prev.
  Preconditions: numPeople is an even integer satisfying 4 <= numPeople <= 1000. -/
theorem spec_6 (numPeople prev : Std.I64)
    (hprev : prev.val = numPeople.val - 2)
    (hlo : 4 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r rprev : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Aegis.NumberOfWays.number_of_ways prev = ok rprev →
          Int.ModEq 1000000007 ((numPeople.val / 2 + 1) * r.val)
            ((4 * (numPeople.val / 2) - 2) * rprev.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (numPeople prev : Std.I64)
    (hprev : prev.val = numPeople.val - 2)
    (hlo : 4 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r rprev : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Aegis.NumberOfWays.number_of_ways prev = ok rprev →
          Int.ModEq 1000000007 ((numPeople.val / 2 + 1) * r.val)
            ((4 * (numPeople.val / 2) - 2) * rprev.val)) := by
  sorry

/-- Whenever number_of_ways(numPeople) returns a result r, r equals C_{numPeople/2} as an ordinary integer, not merely modulo 1000000007.
  Preconditions: numPeople is an even integer satisfying 2 <= numPeople <= 36. -/
theorem spec_7 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 36) (heven : Even numPeople.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        r.val = (catalan (numPeople.val.toNat / 2) : Nat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 36) (heven : Even numPeople.val), ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        r.val = (catalan (numPeople.val.toNat / 2) : Nat)) := by
  sorry

/-- For every numPeople satisfying the preconditions, whenever number_of_ways(numPeople) returns a result r, the integer value of r satisfies r != 0. Equivalently, with k = numPeople/2, the residue C_k mod 1000000007 is nonzero because 2k < 1000000007 and k+1 < 1000000007, so C_k ≡ binom(2k,k) * (k+1)^{-1} is a product of nonzero residues modulo the prime 1000000007.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_8 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r : Std.I64, Aegis.NumberOfWays.number_of_ways numPeople = ok r → r.val ≠ 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r : Std.I64, Aegis.NumberOfWays.number_of_ways numPeople = ok r → r.val ≠ 0) := by
  sorry

/-- Let k = numPeople/2, and let D_k be the number of Dyck paths from (0,0) to (2k,0) using steps (1,1) and (1,-1) that never go below the horizontal axis. Whenever number_of_ways(numPeople) returns a result r, r is congruent modulo 1000000007 to D_k.
  Preconditions: numPeople is an integer satisfying 2 <= numPeople <= 1000 and numPeople is even. -/
theorem spec_9 (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val) :
    ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Int.ModEq 1000000007 r.val (dyckCount (numPeople.val.toNat / 2)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (numPeople : Std.I64)
    (hlo : 2 ≤ numPeople.val) (hhi : numPeople.val ≤ 1000) (heven : Even numPeople.val), ∀ r : Std.I64,
      Aegis.NumberOfWays.number_of_ways numPeople = ok r →
        Int.ModEq 1000000007 r.val (dyckCount (numPeople.val.toNat / 2))) := by
  sorry

end AegisSpec.NumberOfWays
