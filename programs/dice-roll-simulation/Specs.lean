import Aegis.DieSimulator.Code.Funs

/-!
# Specifications of `Aegis.DieSimulator.die_simulator`

LeetCode problem `dice-roll-simulation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DieSimulator

abbrev modulus : Int := 1000000007

def rollMaxEntry (rollMax : Slice Std.I64) (i : Nat) : Int :=
  (rollMax.val.getD i 0#i64).val

def rollMaxLimit (rollMax : Slice Std.I64) (f : Nat) : Nat :=
  (rollMaxEntry rollMax (f - 1)).toNat

def Admissible (n : Nat) (rollMax : Slice Std.I64) (s : Fin n → Fin 6) : Prop :=
  ∀ (f p : Nat), 1 ≤ f → f ≤ 6 → ∀ (hp : p + rollMaxLimit rollMax f < n),
    ¬ (∀ (j : Nat) (hj : j ≤ rollMaxLimit rollMax f),
        (s ⟨p + j, Nat.lt_of_le_of_lt (Nat.add_le_add_left hj p) hp⟩).val + 1 = f)

noncomputable def admissibleSeqs (n : Nat) (rollMax : Slice Std.I64) :
    Finset (Fin n → Fin 6) := by
  classical
  exact Finset.univ.filter (fun s => Admissible n rollMax s)

noncomputable def countAdmissible (n : Nat) (rollMax : Slice Std.I64) : Nat :=
  (admissibleSeqs n rollMax).card

def countRollMaxOne (rollMax : Slice Std.I64) : Nat :=
  ((Finset.range 6).filter (fun i => rollMaxEntry rollMax i = 1)).card

/-- Let M = 1000000007. A length-n sequence s with entries in {1,2,3,4,5,6} is admissible when, for every face f in {1,2,3,4,5,6}, setting m = rollMax[f-1], there is no start position p with 0 <= p and p + m < n such that s[p] = s[p+1] = ... = s[p+m] = f; equivalently, no face f appears in a run of more than rollMax[f-1] consecutive positions. Let C be the number of admissible sequences. Whenever die_simulator(n, rollMax) returns a result r, r is the unique integer satisfying 0 <= r < M and r is congruent to C modulo M.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15. -/
theorem spec_1 (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15) :
    ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ (countAdmissible n.val.toNat rollMax : Int) [ZMOD modulus] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15), ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ (countAdmissible n.val.toNat rollMax : Int) [ZMOD modulus]) := by
  sorry

/-- Under the preconditions, die_simulator(n, rollMax) returns a result; it does not panic, index out of bounds, or fail because of arithmetic overflow.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15. -/
theorem spec_2 (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15) :
    ∃ r : Std.I64, Aegis.DieSimulator.die_simulator n rollMax = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15), ∃ r : Std.I64, Aegis.DieSimulator.die_simulator n rollMax = ok r) := by
  sorry

/-- Whenever die_simulator(1, rollMax) returns a result r, r = 6.
  Preconditions: n = 1; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15. -/
theorem spec_3 (rollMax : Slice Std.I64)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15) :
    ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator 1#i64 rollMax = ok r → r.val = 6 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rollMax : Slice Std.I64)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15), ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator 1#i64 rollMax = ok r → r.val = 6) := by
  sorry

/-- Whenever die_simulator(2, rollMax) returns a result r, r = 36 - k, where k is the number of indices i with 0 <= i < 6 and rollMax[i] = 1.
  Preconditions: n = 2; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15. -/
theorem spec_4 (rollMax : Slice Std.I64)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15) :
    ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator 2#i64 rollMax = ok r →
      r.val = 36 - (countRollMaxOne rollMax : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rollMax : Slice Std.I64)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15), ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator 2#i64 rollMax = ok r →
      r.val = 36 - (countRollMaxOne rollMax : Int)) := by
  sorry

/-- Whenever die_simulator(n, rollMax) returns a result r, r is the canonical remainder of 6^n modulo 1000000007.
  Preconditions: 2 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15; for every i with 0 <= i < 6, n <= rollMax[i]. -/
theorem spec_5 (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hbig : ∀ (i : Nat), i < 6 → n.val ≤ rollMaxEntry rollMax i) :
    ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧ r.val ≡ (6 : Int) ^ n.val.toNat [ZMOD modulus] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 2 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hbig : ∀ (i : Nat), i < 6 → n.val ≤ rollMaxEntry rollMax i), ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧ r.val ≡ (6 : Int) ^ n.val.toNat [ZMOD modulus]) := by
  sorry

/-- Whenever die_simulator(n, rollMax) returns a result r, r is the canonical remainder of 6 * 5^(n-1) modulo 1000000007.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, rollMax[i] = 1. -/
theorem spec_6 (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hone : ∀ (i : Nat), i < 6 → rollMaxEntry rollMax i = 1) :
    ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ 6 * 5 ^ (n.val.toNat - 1) [ZMOD modulus] := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (rollMax : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hone : ∀ (i : Nat), i < 6 → rollMaxEntry rollMax i = 1), ∀ (r : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ 6 * 5 ^ (n.val.toNat - 1) [ZMOD modulus]) := by
  sorry

/-- Whenever die_simulator(n, rollMax) returns r and die_simulator(n, rollMaxPi) returns rPi, we have r = rPi.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15; pi is a permutation of {0,1,2,3,4,5}; rollMaxPi is the length-6 slice with rollMaxPi[i] = rollMax[pi(i)] for every i with 0 <= i < 6. -/
theorem spec_7 (n : Std.I64) (rollMax rollMaxPi : Slice Std.I64) (π : Equiv.Perm (Fin 6))
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hlenPi : rollMaxPi.val.length = 6)
    (hPi : ∀ (i : Nat) (hi : i < 6),
      rollMaxEntry rollMaxPi i = rollMaxEntry rollMax (π ⟨i, hi⟩).val) :
    ∀ (r rPi : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      Aegis.DieSimulator.die_simulator n rollMaxPi = ok rPi → r.val = rPi.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (rollMax rollMaxPi : Slice Std.I64) (π : Equiv.Perm (Fin 6))
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hlenPi : rollMaxPi.val.length = 6)
    (hPi : ∀ (i : Nat) (hi : i < 6),
      rollMaxEntry rollMaxPi i = rollMaxEntry rollMax (π ⟨i, hi⟩).val), ∀ (r rPi : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      Aegis.DieSimulator.die_simulator n rollMaxPi = ok rPi → r.val = rPi.val) := by
  sorry

/-- Whenever die_simulator(n, rollMax) returns r and die_simulator(n, rollMaxCap) returns rCap, we have r = rCap.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= 15; rollMaxCap is the length-6 slice with rollMaxCap[i] = min(rollMax[i], n) for every i with 0 <= i < 6. -/
theorem spec_8 (n : Std.I64) (rollMax rollMaxCap : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hlenCap : rollMaxCap.val.length = 6)
    (hCap : ∀ (i : Nat), i < 6 →
      rollMaxEntry rollMaxCap i = min (rollMaxEntry rollMax i) n.val) :
    ∀ (r rCap : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      Aegis.DieSimulator.die_simulator n rollMaxCap = ok rCap → r.val = rCap.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (rollMax rollMaxCap : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i ∧ rollMaxEntry rollMax i ≤ 15)
    (hlenCap : rollMaxCap.val.length = 6)
    (hCap : ∀ (i : Nat), i < 6 →
      rollMaxEntry rollMaxCap i = min (rollMaxEntry rollMax i) n.val), ∀ (r rCap : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
      Aegis.DieSimulator.die_simulator n rollMaxCap = ok rCap → r.val = rCap.val) := by
  sorry

/-- C <= C2. Moreover, if C < 1000000007 and C2 < 1000000007, then whenever die_simulator(n, rollMax) returns r and die_simulator(n, rollMax2) returns r2, we have r <= r2.
  Preconditions: 1 <= n <= 5000; len(rollMax) = 6; len(rollMax2) = 6; for every i with 0 <= i < 6, 1 <= rollMax[i] <= rollMax2[i] <= 15. Let C and spec_9 be the true counts of admissible length-n sequences for rollMax and rollMax2 respectively. -/
theorem spec_9 (n : Std.I64) (rollMax rollMax2 : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hlen2 : rollMax2.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i)
    (hmono : ∀ (i : Nat), i < 6 →
      rollMaxEntry rollMax i ≤ rollMaxEntry rollMax2 i ∧ rollMaxEntry rollMax2 i ≤ 15) :
    countAdmissible n.val.toNat rollMax ≤ countAdmissible n.val.toNat rollMax2 ∧
      (countAdmissible n.val.toNat rollMax < 1000000007 →
        countAdmissible n.val.toNat rollMax2 < 1000000007 →
        ∀ (r r2 : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
          Aegis.DieSimulator.die_simulator n rollMax2 = ok r2 → r.val ≤ r2.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (rollMax rollMax2 : Slice Std.I64)
    (hn_low : 1 ≤ n.val) (hn_high : n.val ≤ 5000)
    (hlen : rollMax.val.length = 6)
    (hlen2 : rollMax2.val.length = 6)
    (hbound : ∀ (i : Nat), i < 6 → 1 ≤ rollMaxEntry rollMax i)
    (hmono : ∀ (i : Nat), i < 6 →
      rollMaxEntry rollMax i ≤ rollMaxEntry rollMax2 i ∧ rollMaxEntry rollMax2 i ≤ 15), countAdmissible n.val.toNat rollMax ≤ countAdmissible n.val.toNat rollMax2 ∧
      (countAdmissible n.val.toNat rollMax < 1000000007 →
        countAdmissible n.val.toNat rollMax2 < 1000000007 →
        ∀ (r r2 : Std.I64), Aegis.DieSimulator.die_simulator n rollMax = ok r →
          Aegis.DieSimulator.die_simulator n rollMax2 = ok r2 → r.val ≤ r2.val)) := by
  sorry

end AegisSpec.DieSimulator
