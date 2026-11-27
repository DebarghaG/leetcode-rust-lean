import Aegis.NumWays.Code.Funs

/-!
# Specifications of `Aegis.NumWays.num_ways`

LeetCode problem `number-of-ways-to-stay-in-the-same-place-after-some-steps`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumWays

  def stepVal (j : Fin 3) : ℤ := (j : ℤ) - 1

  def prefixSums (d : List ℤ) : List ℤ := d.scanl (· + ·) 0

  def InBounds (L : ℕ) (d : List ℤ) : Prop :=
    ∀ p ∈ prefixSums d, 0 ≤ p ∧ p ≤ (L : ℤ) - 1

  def Nonneg (d : List ℤ) : Prop :=
    ∀ p ∈ prefixSums d, 0 ≤ p

  def ReturnsToZero (d : List ℤ) : Prop := d.sum = 0

  def walkSeq (steps : ℕ) (f : Fin steps → Fin 3) : List ℤ :=
    List.ofFn (fun i => stepVal (f i))

  instance instDecidableInBounds (L : ℕ) (d : List ℤ) : Decidable (InBounds L d) :=
    List.decidableBAll (fun p => 0 ≤ p ∧ p ≤ (L : ℤ) - 1) (prefixSums d)

  instance instDecidableNonneg (d : List ℤ) : Decidable (Nonneg d) :=
    List.decidableBAll (fun p => 0 ≤ (p : ℤ)) (prefixSums d)

  instance instDecidableReturnsToZero (d : List ℤ) : Decidable (ReturnsToZero d) :=
    inferInstanceAs (Decidable (d.sum = 0))

  def countBounded (steps L : ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin steps → Fin 3)).filter
        (fun f => InBounds L (walkSeq steps f) ∧ ReturnsToZero (walkSeq steps f))).card

  def countNonneg (steps : ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin steps → Fin 3)).filter
        (fun f => Nonneg (walkSeq steps f) ∧ ReturnsToZero (walkSeq steps f))).card

  def IsResidue (P : ℕ) (x c : ℤ) : Prop :=
    0 ≤ x ∧ x < (P : ℤ) ∧ x ≡ c [ZMOD (P : ℤ)] ∧
      ∀ y : ℤ, 0 ≤ y → y < (P : ℤ) → y ≡ c [ZMOD (P : ℤ)] → y = x

  /-- The function returns a result r, and r is the unique integer with 0 <= r < 1000000007 such that r is congruent modulo 1000000007 to the number c of sequences (d_1, ..., d_steps) of length steps with each d_i in {-1, 0, 1} and with the property that, defining p_0 = 0 and p_k = d_1 + ... + d_k for 1 <= k <= steps, one has 0 <= p_k <= arrLen - 1 for every k with 0 <= k <= steps, and p_steps = 0.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 1 <= arrLen <= 10^6. -/
  theorem spec_1 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∃ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r ∧
          IsResidue 1000000007 r.val
            ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∃ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r ∧
            IsResidue 1000000007 r.val
              ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- For every steps and arrLen satisfying the preconditions, the function returns a result r without failing: it does not overflow, panic, or attempt an out-of-bounds access.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 1 <= arrLen <= 10^6. -/
  theorem spec_2 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∃ r : Std.I64, Aegis.NumWays.num_ways steps arrLen = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∃ r : Std.I64, Aegis.NumWays.num_ways steps arrLen = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 1000000006.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 1 <= arrLen <= 10^6. -/
  theorem spec_3 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and arrLen = 1. -/
  theorem spec_4 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_eq : arrLen.val = 1) :
      ∀ r : Std.I64, Aegis.NumWays.num_ways steps arrLen = ok r → r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_eq : arrLen.val = 1), ∀ r : Std.I64, Aegis.NumWays.num_ways steps arrLen = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r is the unique integer with 0 <= r < 1000000007 congruent modulo 1000000007 to 2^{steps-1}.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and arrLen = 2. -/
  theorem spec_5 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_eq : arrLen.val = 2) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          IsResidue 1000000007 r.val ((2 : ℤ) ^ (steps.val.toNat - 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_eq : arrLen.val = 2), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            IsResidue 1000000007 r.val ((2 : ℤ) ^ (steps.val.toNat - 1))) := by
    sorry

  /-- Whenever the function returns a result r, r is the unique integer with 0 <= r < 1000000007 congruent modulo 1000000007 to the number c' of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that, with p_0 = 0 and p_k = d_1 + ... + d_k, one has 0 <= p_k <= L' - 1 for every k with 0 <= k <= steps, and p_steps = 0.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 1 <= arrLen <= 10^6. Let L' = min(arrLen, floor(steps/2) + 1). -/
  theorem spec_6 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          IsResidue 1000000007 r.val
            ((countBounded steps.val.toNat
                (min arrLen.val.toNat (steps.val.toNat / 2 + 1)) : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            IsResidue 1000000007 r.val
              ((countBounded steps.val.toNat
                  (min arrLen.val.toNat (steps.val.toNat / 2 + 1)) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r is the unique integer with 0 <= r < 1000000007 congruent modulo 1000000007 to the number m of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that, with p_0 = 0 and p_k = d_1 + ... + d_k, one has p_k >= 0 for every k with 0 <= k <= steps, and p_steps = 0 (no upper bound is imposed).
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500, 1 <= arrLen <= 10^6, and arrLen >= floor(steps/2) + 1. -/
  theorem spec_7 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000)
      (harrLen_ge : steps.val.toNat / 2 + 1 ≤ arrLen.val.toNat) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          IsResidue 1000000007 r.val ((countNonneg steps.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000)
        (harrLen_ge : steps.val.toNat / 2 + 1 ≤ arrLen.val.toNat), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            IsResidue 1000000007 r.val ((countNonneg steps.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the exact number c of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that, with p_0 = 0 and p_k = d_1 + ... + d_k, one has 0 <= p_k <= arrLen - 1 for every k with 0 <= k <= steps, and p_steps = 0; that is, r = c rather than merely r being congruent to c modulo 1000000007. Consequently 1 <= r <= 3^steps <= 387420489.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 18 and 1 <= arrLen <= 10^6. -/
  theorem spec_8 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 18)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          r.val = ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) ∧
            1 ≤ r.val ∧ r.val ≤ (3 : ℤ) ^ steps.val.toNat ∧
              (3 : ℤ) ^ steps.val.toNat ≤ 387420489 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 18)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            r.val = ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) ∧
              1 ≤ r.val ∧ r.val ≤ (3 : ℤ) ^ steps.val.toNat ∧
                (3 : ℤ) ^ steps.val.toNat ≤ 387420489) := by
    sorry

  /-- Whenever the function returns a result r, r = min(arrLen, 2).
    Preconditions: steps and arrLen are integers with steps = 2 and 1 <= arrLen <= 10^6. -/
  theorem spec_9 (steps arrLen : Std.I64)
      (hsteps_eq : steps.val = 2)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r → r.val = min arrLen.val 2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_eq : steps.val = 2)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r → r.val = min arrLen.val 2) := by
    sorry

  /-- Whenever the function returns a result r, let c be the number of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that, with p_0 = 0 and p_k = d_1 + ... + d_k, one has 0 <= p_k <= arrLen - 1 for every k with 0 <= k <= steps, and p_steps = 0; then r is congruent to c modulo 1000000007 and c >= 2^{steps-1}.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 2 <= arrLen <= 10^6. -/
  theorem spec_10 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 2 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          r.val ≡ ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) [ZMOD 1000000007] ∧
            2 ^ (steps.val.toNat - 1) ≤ countBounded steps.val.toNat arrLen.val.toNat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 2 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            r.val ≡ ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) [ZMOD 1000000007] ∧
              2 ^ (steps.val.toNat - 1) ≤ countBounded steps.val.toNat arrLen.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, let c be the number of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that, with p_0 = 0 and p_k = d_1 + ... + d_k, one has 0 <= p_k <= arrLen - 1 for every k with 0 <= k <= steps, and p_steps = 0; then r is congruent to c modulo 1000000007 and c <= m, where m is the number of sequences (d_1, ..., d_steps) with each d_i in {-1, 0, 1} such that p_k >= 0 for every k with 0 <= k <= steps, and p_steps = 0.
    Preconditions: steps and arrLen are integers with 1 <= steps <= 500 and 1 <= arrLen <= 10^6. -/
  theorem spec_11 (steps arrLen : Std.I64)
      (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
      (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000) :
      ∀ r : Std.I64,
        Aegis.NumWays.num_ways steps arrLen = ok r →
          r.val ≡ ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) [ZMOD 1000000007] ∧
            countBounded steps.val.toNat arrLen.val.toNat ≤ countNonneg steps.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (steps arrLen : Std.I64)
        (hsteps_lo : 1 ≤ steps.val) (hsteps_hi : steps.val ≤ 500)
        (harrLen_lo : 1 ≤ arrLen.val) (harrLen_hi : arrLen.val ≤ 1000000), ∀ r : Std.I64,
          Aegis.NumWays.num_ways steps arrLen = ok r →
            r.val ≡ ((countBounded steps.val.toNat arrLen.val.toNat : ℕ) : ℤ) [ZMOD 1000000007] ∧
              countBounded steps.val.toNat arrLen.val.toNat ≤ countNonneg steps.val.toNat) := by
    sorry

  end AegisSpec.NumWays
