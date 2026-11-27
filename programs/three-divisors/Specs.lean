import Aegis.IsThree.Code.Funs

/-!
# Specifications of `Aegis.IsThree.is_three`

LeetCode problem `three-divisors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsThree (is_three)

namespace AegisSpec.IsThree

def PosDiv (n d : Int) : Prop :=
  1 ≤ d ∧ d ≤ n ∧ ∃ k : Int, n = k * d

def HasExactlyThreePosDivs (n : Int) : Prop :=
  ∃ a b c : Int,
    PosDiv n a ∧ PosDiv n b ∧ PosDiv n c ∧ a < b ∧ b < c ∧
      ∀ d : Int, PosDiv n d → d = a ∨ d = b ∨ d = c

def IsPrimeInt (p : Int) : Prop :=
  2 ≤ p ∧ ∀ d : Int, PosDiv p d → d = 1 ∨ d = p

/-- Whenever is_three n returns a result r, r = true if and only if n has exactly three positive divisors; a positive divisor of n means an integer d with 1 <= d <= n and n = k*d for some integer k.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∀ r : Bool, is_three n = ok r → (r = true ↔ HasExactlyThreePosDivs n.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∀ r : Bool, is_three n = ok r → (r = true ↔ HasExactlyThreePosDivs n.val)) := by
  sorry

/-- is_three n returns a result (some Bool); it does not fail for any n in this range.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∃ r : Bool, is_three n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∃ r : Bool, is_three n = ok r) := by
  sorry

/-- Whenever is_three n returns a result r with r = true, there exists a prime p such that n = p*p; here p is prime means p >= 2 and the only positive divisors of p are 1 and p.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∀ r : Bool, is_three n = ok r → r = true →
      ∃ p : Int, IsPrimeInt p ∧ n.val = p * p := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∀ r : Bool, is_three n = ok r → r = true →
      ∃ p : Int, IsPrimeInt p ∧ n.val = p * p) := by
  sorry

/-- Whenever is_three n returns a result r, if there exists a prime p such that n = p*p, then r = true.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∀ r : Bool, is_three n = ok r →
      (∃ p : Int, IsPrimeInt p ∧ n.val = p * p) → r = true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∀ r : Bool, is_three n = ok r →
      (∃ p : Int, IsPrimeInt p ∧ n.val = p * p) → r = true) := by
  sorry

/-- Whenever is_three n returns a result r with r = true, there exists an integer d such that 1 < d < n, d*d = n, and d is the only positive divisor of n strictly between 1 and n.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∀ r : Bool, is_three n = ok r → r = true →
      ∃ d : Int,
        1 < d ∧ d < n.val ∧ d * d = n.val ∧
          ∀ e : Int, PosDiv n.val e → 1 < e → e < n.val → e = d := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∀ r : Bool, is_three n = ok r → r = true →
      ∃ d : Int,
        1 < d ∧ d < n.val ∧ d * d = n.val ∧
          ∀ e : Int, PosDiv n.val e → 1 < e → e < n.val → e = d) := by
  sorry

/-- Whenever is_three n returns a result r with r = true, there exists a prime p such that n = p*p and, for every prime q, if q divides n, then q = p.
  Preconditions: 1 <= n <= 10000. -/
theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
    ∀ r : Bool, is_three n = ok r → r = true →
      ∃ p : Int,
        IsPrimeInt p ∧ n.val = p * p ∧ ∀ q : Int, IsPrimeInt q → q ∣ n.val → q = p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∀ r : Bool, is_three n = ok r → r = true →
      ∃ p : Int,
        IsPrimeInt p ∧ n.val = p * p ∧ ∀ q : Int, IsPrimeInt q → q ∣ n.val → q = p) := by
  sorry

end AegisSpec.IsThree
