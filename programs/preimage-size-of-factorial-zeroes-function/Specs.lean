import Aegis.PreimageSizeFzf.Code.Funs

/-!
# Specifications of `Aegis.PreimageSizeFzf.preimage_size_fzf`

LeetCode problem `preimage-size-of-factorial-zeroes-function`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.Result

  namespace AegisSpec.PreimageSizeFzf

  abbrev I64 := Aeneas.Std.I64

  def fzfNat (x : Nat) : Nat := ∑ i ∈ Finset.Icc 1 x, x / 5 ^ i

  def fzf (x : Int) : Int := (fzfNat x.toNat : Int)

  def preimageSet (k : Int) : Set Int := {x | 0 ≤ x ∧ fzf x = k}

  def preimageSetFive (k : Int) : Set Int := {x | 0 ≤ x ∧ x % 5 = 0 ∧ fzf x = k}

  /-- Let f(x) be the number of trailing zeroes of x! (the largest integer z >= 0 such that 10^z divides x!, with 0! = 1; equivalently f(x) = sum_{i>=1} floor(x/5^i)). The function returns a result r and r = |{ x : integer, x >= 0, and f(x) = k }|.
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_1 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∃ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r ∧
        r.val = ((preimageSet k.val).ncard : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∃ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r ∧
          r.val = ((preimageSet k.val).ncard : Int)) := by
    sorry

  /-- The function returns a result r (it does not panic, overflow, or get stuck).
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_2 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∃ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∃ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= 5.
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_3 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
        0 ≤ r.val ∧ r.val ≤ 5 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
          0 ≤ r.val ∧ r.val ≤ 5) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 or r = 5.
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_4 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
        r.val = 0 ∨ r.val = 5 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
          r.val = 0 ∨ r.val = 5) := by
    sorry

  /-- Whenever the function returns a result r, r = 5 if and only if there exists a non-negative integer x such that f(x) = k, where f(x) is the number of trailing zeroes of x! (as defined in spec_1).
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_5 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
        (r.val = 5 ↔ ∃ x : Int, 0 ≤ x ∧ fzf x = k.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
          (r.val = 5 ↔ ∃ x : Int, 0 ≤ x ∧ fzf x = k.val)) := by
    sorry

  /-- Whenever the function returns a result r, if r = 5 then there exists an integer x0 with 0 <= x0, x0 mod 5 = 0, such that for every non-negative integer x, f(x) = k if and only if x0 <= x <= x0+4, where f(x) is the number of trailing zeroes of x! (as defined in spec_1).
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_6 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r → r.val = 5 →
        ∃ x0 : Int, 0 ≤ x0 ∧ x0 % 5 = 0 ∧
          ∀ x : Int, 0 ≤ x → (fzf x = k.val ↔ x0 ≤ x ∧ x ≤ x0 + 4) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r → r.val = 5 →
          ∃ x0 : Int, 0 ≤ x0 ∧ x0 % 5 = 0 ∧
            ∀ x : Int, 0 ≤ x → (fzf x = k.val ↔ x0 ≤ x ∧ x ≤ x0 + 4)) := by
    sorry

  /-- Whenever the function returns a result r, r = 5 * n, where n is the number of non-negative integers x such that x mod 5 = 0 and f(x) = k, with f(x) defined as in spec_1.
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_7 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
        r.val = 5 * ((preimageSetFive k.val).ncard : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
          r.val = 5 * ((preimageSetFive k.val).ncard : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if r = 5 then there is exactly one non-negative integer x with x mod 5 = 0 and f(x) = k, where f(x) is defined as in spec_1.
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_8 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r → r.val = 5 →
        ∃! x : Int, 0 ≤ x ∧ x % 5 = 0 ∧ fzf x = k.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r → r.val = 5 →
          ∃! x : Int, 0 ≤ x ∧ x % 5 = 0 ∧ fzf x = k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 5 if and only if there exists a non-negative integer x such that x mod 5 = 0 and f(x) = k, where f(x) is the number of trailing zeroes of x! (as defined in spec_1).
    Preconditions: 0 <= k <= 1_000_000_000. -/
  theorem spec_9 (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000) :
      ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
        (r.val = 5 ↔ ∃ x : Int, 0 ≤ x ∧ x % 5 = 0 ∧ fzf x = k.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k : I64) (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ 1000000000), ∀ r : I64, Aegis.PreimageSizeFzf.preimage_size_fzf k = ok r →
          (r.val = 5 ↔ ∃ x : Int, 0 ≤ x ∧ x % 5 = 0 ∧ fzf x = k.val)) := by
    sorry

  end AegisSpec.PreimageSizeFzf
