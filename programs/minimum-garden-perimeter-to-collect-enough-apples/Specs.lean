import Aegis.MinimumPerimeter.Code.Funs

/-!
# Specifications of `Aegis.MinimumPerimeter.minimum_perimeter`

LeetCode problem `minimum-garden-perimeter-to-collect-enough-apples`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumPerimeter

def appleCount (t : ℤ) : ℤ := 2 * t * (t + 1) * (2 * t + 1)

def squareApples (s : ℤ) : ℤ := appleCount s

/-- Whenever the function returns a result r, there exists an integer k with 0 <= k such that r = 8*k, A(k) >= neededApples, and A(j) < neededApples for every integer j with 0 <= j < k, where A(t) = 2*t*(t+1)*(2*t+1) is the number of apples in the closed square [-t,t] x [-t,t].
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_1 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k ∧ appleCount k ≥ neededApples.val ∧
        ∀ j : ℤ, 0 ≤ j → j < k → appleCount j < neededApples.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k ∧ appleCount k ≥ neededApples.val ∧
        ∀ j : ℤ, 0 ≤ j → j < k → appleCount j < neededApples.val) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, or panic) for every neededApples satisfying the precondition.
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_2 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∃ r : Std.I64, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∃ r : Std.I64, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r) := by
  sorry

/-- Whenever the function returns a result r, there is an integer k >= 0 such that r = 8*k; in particular r is nonnegative and divisible by 8.
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_3 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k >= 0 such that r = 8*k and A(k) >= neededApples, where A(t) = 2*t*(t+1)*(2*t+1).
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_4 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k ∧ appleCount k ≥ neededApples.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 0 ≤ k ∧ r.val = 8 * k ∧ appleCount k ≥ neededApples.val) := by
  sorry

/-- Whenever the function returns a result r, for every real number s with 0 <= s < r/8, the closed square [-s,s] x [-s,s] contains fewer than neededApples apples; equivalently, A(floor(s)) < neededApples, where A(t) = 2*t*(t+1)*(2*t+1) and floor(s) is the greatest integer <= s.
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_5 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∀ s : ℤ, 0 ≤ s → 8 * s < r.val → squareApples s < neededApples.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∀ s : ℤ, 0 ≤ s → 8 * s < r.val → squareApples s < neededApples.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer k >= 1 such that r = 8*k and A(k-1) < neededApples <= A(k), where A(t) = 2*t*(t+1)*(2*t+1).
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_6 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 1 ≤ k ∧ r.val = 8 * k ∧ appleCount (k - 1) < neededApples.val ∧
        neededApples.val ≤ appleCount k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r →
      ∃ k : ℤ, 1 ≤ k ∧ r.val = 8 * k ∧ appleCount (k - 1) < neededApples.val ∧
        neededApples.val ≤ appleCount k) := by
  sorry

/-- Whenever the function returns a result r, r <= 503968.
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_7 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r → r.val ≤ 503968 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r → r.val ≤ 503968) := by
  sorry

/-- Whenever the function returns a result r, r >= 8.
  Preconditions: neededApples is an integer with 1 <= neededApples <= 10^15. -/
theorem spec_8 (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15) :
    ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r → 8 ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (neededApples : Std.I64)
    (hlo : 1 ≤ neededApples.val) (hhi : neededApples.val ≤ 10 ^ 15), ∀ r, Aegis.MinimumPerimeter.minimum_perimeter neededApples = ok r → 8 ≤ r.val) := by
  sorry

/-- Whenever the function returns r1 on input neededApples1 and r2 on input neededApples2, we have r1 <= r2.
  Preconditions: 1 <= neededApples1 <= neededApples2 <= 10^15. -/
theorem spec_9 (neededApples1 neededApples2 : Std.I64)
    (h1 : 1 ≤ neededApples1.val) (h12 : neededApples1.val ≤ neededApples2.val)
    (h2 : neededApples2.val ≤ 10 ^ 15) :
    ∀ r1 r2, Aegis.MinimumPerimeter.minimum_perimeter neededApples1 = ok r1 →
      Aegis.MinimumPerimeter.minimum_perimeter neededApples2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (neededApples1 neededApples2 : Std.I64)
    (h1 : 1 ≤ neededApples1.val) (h12 : neededApples1.val ≤ neededApples2.val)
    (h2 : neededApples2.val ≤ 10 ^ 15), ∀ r1 r2, Aegis.MinimumPerimeter.minimum_perimeter neededApples1 = ok r1 →
      Aegis.MinimumPerimeter.minimum_perimeter neededApples2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns r1 on neededApples1 and r2 on neededApples2, r1 = r2 = 8*k.
  Preconditions: 1 <= neededApples1 <= neededApples2 <= 10^15 and k is an integer with k >= 1 and A(k-1) < neededApples1 <= neededApples2 <= A(k), where A(t)=2*t*(t+1)*(2*t+1). -/
theorem spec_10 (neededApples1 neededApples2 : Std.I64) (k : ℤ)
    (h1 : 1 ≤ neededApples1.val) (h12 : neededApples1.val ≤ neededApples2.val)
    (h2 : neededApples2.val ≤ 10 ^ 15) (hk : 1 ≤ k)
    (hprev : appleCount (k - 1) < neededApples1.val)
    (hcover : neededApples2.val ≤ appleCount k) :
    ∀ r1 r2, Aegis.MinimumPerimeter.minimum_perimeter neededApples1 = ok r1 →
      Aegis.MinimumPerimeter.minimum_perimeter neededApples2 = ok r2 →
      r1.val = 8 * k ∧ r2.val = 8 * k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (neededApples1 neededApples2 : Std.I64) (k : ℤ)
    (h1 : 1 ≤ neededApples1.val) (h12 : neededApples1.val ≤ neededApples2.val)
    (h2 : neededApples2.val ≤ 10 ^ 15) (hk : 1 ≤ k)
    (hprev : appleCount (k - 1) < neededApples1.val)
    (hcover : neededApples2.val ≤ appleCount k), ∀ r1 r2, Aegis.MinimumPerimeter.minimum_perimeter neededApples1 = ok r1 →
      Aegis.MinimumPerimeter.minimum_perimeter neededApples2 = ok r2 →
      r1.val = 8 * k ∧ r2.val = 8 * k) := by
  sorry

end AegisSpec.MinimumPerimeter
