import Aegis.DistinctSequences.Code.Funs

/-!
# Specifications of `Aegis.DistinctSequences.distinct_sequences`

LeetCode problem `number-of-distinct-roll-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistinctSequences

open Classical

def M : Int := 1000000007

def digitVal (d : Fin 6) : Int := (d : Nat) + 1

def digitsToList (n : Nat) (f : Fin n → Fin 6) : List Int :=
  (List.finRange n).map (fun i => digitVal (f i))

def ValidSeq (s : List Int) : Prop :=
  (∀ (i : Nat) (hi : i < s.length), 1 ≤ s[i] ∧ s[i] ≤ 6) ∧
    (∀ (i : Nat) (hi : i < s.length) (hi' : i + 1 < s.length),
      Int.gcd (s[i]) (s[i + 1]) = 1) ∧
      ∀ (i j : Nat) (hij : i < j) (hj : j < s.length), s[i] = s[j] → 2 < j - i

noncomputable def C (n : Nat) : Nat :=
  (Finset.univ.filter (fun f : Fin n → Fin 6 => ValidSeq (digitsToList n f))).card

/-- Let M = 1000000007. For a length-n list s of integers, define s to be valid iff: (1) for every i with 0 <= i < n, 1 <= s[i] <= 6; (2) for every i with 0 <= i < n-1, gcd(s[i], s[i+1]) = 1; (3) for all i,j with 0 <= i < j < n, if s[i] = s[j] then j - i > 2. Let C(n) be the number of valid length-n lists. The function returns a result r such that r is the unique integer with 0 <= r < M and r is congruent to C(n) modulo M.
  Preconditions: n is an integer satisfying 1 <= n <= 10000. -/
theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000) :
    ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
        r.val ≡ (C n.val.toNat : Int) [ZMOD M] ∧
          ∀ r' : Int, 0 ≤ r' → r' < M → r' ≡ (C n.val.toNat : Int) [ZMOD M] → r' = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000), ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ 0 ≤ r.val ∧ r.val < M ∧
        r.val ≡ (C n.val.toNat : Int) [ZMOD M] ∧
          ∀ r' : Int, 0 ≤ r' → r' < M → r' ≡ (C n.val.toNat : Int) [ZMOD M] → r' = r.val) := by
  sorry

/-- For every n with 1 <= n <= 10000, whenever the function returns a result r, the integer r satisfies 0 <= r < 1000000007.
  Preconditions: n is an integer satisfying 1 <= n <= 10000. -/
theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000) :
    ∀ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r → 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000), ∀ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r → 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- For every n with 1 <= n <= 10000, the function returns a result; it does not fail with Err.
  Preconditions: n is an integer satisfying 1 <= n <= 10000. -/
theorem spec_3 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000) :
    ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000), ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r) := by
  sorry

/-- The function returns r = 6.
  Preconditions: n = 1. -/
theorem spec_4 (n : Std.I64) (hn : n.val = 1) :
    ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 6 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 6) := by
  sorry

/-- The function returns r = 22.
  Preconditions: n = 2. -/
theorem spec_5 (n : Std.I64) (hn : n.val = 2) :
    ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 22 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 22) := by
  sorry

/-- The function returns r = 66.
  Preconditions: n = 3. -/
theorem spec_6 (n : Std.I64) (hn : n.val = 3) :
    ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 66 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 3), ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 66) := by
  sorry

/-- The function returns r = 184.
  Preconditions: n = 4. -/
theorem spec_7 (n : Std.I64) (hn : n.val = 4) :
    ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 184 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 4), ∃ r : Std.I64, Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 184) := by
  sorry

/-- The function returns r = 534856607.
  Preconditions: n = 100. -/
theorem spec_8 (n : Std.I64) (hn : n.val = 100) :
    ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 534856607 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 534856607) := by
  sorry

/-- The function returns r = 874574246.
  Preconditions: n = 10000. -/
theorem spec_9 (n : Std.I64) (hn : n.val = 10000) :
    ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 874574246 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 10000), ∃ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r ∧ r.val = 874574246) := by
  sorry

/-- Let C(n) be the number of valid length-n lists as defined in spec_1: lists s with 1 <= s[i] <= 6 for all 0 <= i < n, gcd(s[i],s[i+1])=1 for all 0 <= i < n-1, and s[i]=s[j] with 0 <= i < j < n only when j-i>2. For every n with 1 <= n <= 10000, whenever the function returns a result r, r is congruent to C(n) modulo 1000000007.
  Preconditions: n is an integer satisfying 1 <= n <= 10000. -/
theorem spec_10 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000) :
    ∀ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r →
        r.val ≡ (C n.val.toNat : Int) [ZMOD M] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10000), ∀ r : Std.I64,
      Aegis.DistinctSequences.distinct_sequences n = ok r →
        r.val ≡ (C n.val.toNat : Int) [ZMOD M]) := by
  sorry

end AegisSpec.DistinctSequences
