import Aegis.NumberOfChild.Code.Funs

/-!
# Specifications of `Aegis.NumberOfChild.number_of_child`

LeetCode problem `find-the-child-who-has-the-ball-after-k-seconds`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfChild

  namespace AegisSpec.NumberOfChild

  /-- The function returns a result r and r = min(s, 2*(n-1) - s), where s = k mod (2*(n-1)). Here mod denotes the mathematical modulo operation, so s is the unique integer with 0 <= s < 2*(n-1) and k = q*(2*(n-1)) + s for some integer q. Equivalently, r = s if s < n, and r = 2*(n-1) - s otherwise.
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k <= 50. -/
  theorem spec_1 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∃ r, number_of_child n k = ok r ∧
        r.val = min (k.val % (2 * (n.val - 1)))
          (2 * (n.val - 1) - k.val % (2 * (n.val - 1))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∃ r, number_of_child n k = ok r ∧
          r.val = min (k.val % (2 * (n.val - 1)))
            (2 * (n.val - 1) - k.val % (2 * (n.val - 1)))) := by
    sorry

  /-- Whenever the function returns a result r, it holds that 0 <= r <= n-1.
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k <= 50. -/
  theorem spec_2 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r, number_of_child n k = ok r → 0 ≤ r.val ∧ r.val ≤ n.val - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r, number_of_child n k = ok r → 0 ≤ r.val ∧ r.val ≤ n.val - 1) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow).
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k <= 50. -/
  theorem spec_3 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∃ r, number_of_child n k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∃ r, number_of_child n k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r = k.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and k < n. -/
  theorem spec_4 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hkn : k.val < n.val) :
      ∀ r, number_of_child n k = ok r → r.val = k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hkn : k.val < n.val), ∀ r, number_of_child n k = ok r → r.val = k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = n-2.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and k = n. -/
  theorem spec_5 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hkn : k.val = n.val) :
      ∀ r, number_of_child n k = ok r → r.val = n.val - 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hkn : k.val = n.val), ∀ r, number_of_child n k = ok r → r.val = n.val - 2) := by
    sorry

  /-- If the function returns r1 on input (n, k1) and r2 on input (n, k2), then r1 = r2.
    Preconditions: n, k1, k2 are integers with 2 <= n <= 50, 1 <= k1 <= 50, 1 <= k2 <= 50, and k1 ≡ k2 (mod 2*(n-1)). -/
  theorem spec_6 (n k1 k2 : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 50)
      (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 50)
      (hcongr : k1.val % (2 * (n.val - 1)) = k2.val % (2 * (n.val - 1))) :
      ∀ r1 r2, number_of_child n k1 = ok r1 → number_of_child n k2 = ok r2 → r1 = r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k1 k2 : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 50)
        (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 50)
        (hcongr : k1.val % (2 * (n.val - 1)) = k2.val % (2 * (n.val - 1))), ∀ r1 r2, number_of_child n k1 = ok r1 → number_of_child n k2 = ok r2 → r1 = r2) := by
    sorry

  /-- If the function returns r1 on input (n, k) and r2 on input (n, 2*(n-1) - k), then r1 = r2.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and 1 <= 2*(n-1) - k <= 50. -/
  theorem spec_7 (n k k' : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hk' : k'.val = 2 * (n.val - 1) - k.val)
      (hk'_lo : 1 ≤ k'.val) (hk'_hi : k'.val ≤ 50) :
      ∀ r1 r2, number_of_child n k = ok r1 → number_of_child n k' = ok r2 → r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k k' : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hk' : k'.val = 2 * (n.val - 1) - k.val)
        (hk'_lo : 1 ≤ k'.val) (hk'_hi : k'.val ≤ 50), ∀ r1 r2, number_of_child n k = ok r1 → number_of_child n k' = ok r2 → r1 = r2) := by
    sorry

  /-- If the function returns r1 on input (n, k) and r2 on input (n, k+1), then |r2 - r1| = 1.
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k < 50. -/
  theorem spec_8 (n k k' : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val < 50)
      (hk' : k'.val = k.val + 1) :
      ∀ r1 r2, number_of_child n k = ok r1 → number_of_child n k' = ok r2 →
        (r2.val - r1.val).natAbs = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k k' : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val < 50)
        (hk' : k'.val = k.val + 1), ∀ r1 r2, number_of_child n k = ok r1 → number_of_child n k' = ok r2 →
          (r2.val - r1.val).natAbs = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and k mod (2*(n-1)) = 0. -/
  theorem spec_9 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hmod : k.val % (2 * (n.val - 1)) = 0) :
      ∀ r, number_of_child n k = ok r → r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hmod : k.val % (2 * (n.val - 1)) = 0), ∀ r, number_of_child n k = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = n-1.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and k mod (2*(n-1)) = n-1. -/
  theorem spec_10 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hmod : k.val % (2 * (n.val - 1)) = n.val - 1) :
      ∀ r, number_of_child n k = ok r → r.val = n.val - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hmod : k.val % (2 * (n.val - 1)) = n.val - 1), ∀ r, number_of_child n k = ok r → r.val = n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = k mod 2.
    Preconditions: n and k are integers with n = 2 and 1 <= k <= 50. -/
  theorem spec_11 (n k : Std.I64)
      (hn : n.val = 2)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r, number_of_child n k = ok r → r.val = k.val % 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64)
        (hn : n.val = 2)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r, number_of_child n k = ok r → r.val = k.val % 2) := by
    sorry

  /-- Whenever the function returns a result r, if r = n-1 then k mod (2*(n-1)) = n-1.
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k <= 50. -/
  theorem spec_12 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r, number_of_child n k = ok r → r.val = n.val - 1 →
        k.val % (2 * (n.val - 1)) = n.val - 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r, number_of_child n k = ok r → r.val = n.val - 1 →
          k.val % (2 * (n.val - 1)) = n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, if r = 0 then k mod (2*(n-1)) = 0.
    Preconditions: n and k are integers with 2 <= n <= 50 and 1 <= k <= 50. -/
  theorem spec_13 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50) :
      ∀ r, number_of_child n k = ok r → r.val = 0 →
        k.val % (2 * (n.val - 1)) = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50), ∀ r, number_of_child n k = ok r → r.val = 0 →
          k.val % (2 * (n.val - 1)) = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: n and k are integers with 2 <= n <= 50, 1 <= k <= 50, and k = 2*(n-1) - 1. -/
  theorem spec_14 (n k : Std.I64)
      (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
      (hk : k.val = 2 * (n.val - 1) - 1) :
      ∀ r, number_of_child n k = ok r → r.val = 1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n k : Std.I64)
        (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 50)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 50)
        (hk : k.val = 2 * (n.val - 1) - 1), ∀ r, number_of_child n k = ok r → r.val = 1) := by
    sorry

  end AegisSpec.NumberOfChild
