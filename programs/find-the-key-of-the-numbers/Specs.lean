import Aegis.GenerateKey.Code.Funs

/-!
# Specifications of `Aegis.GenerateKey.generate_key`

LeetCode problem `find-the-key-of-the-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GenerateKey

def D (n : Int) (i : Nat) : Int := n / (10 : Int) ^ (3 - i) % 10

def K (r : Int) (i : Nat) : Int := r / (10 : Int) ^ (3 - i) % 10

def fromDigits (d0 d1 d2 d3 : Int) : Int := 1000 * d0 + 100 * d1 + 10 * d2 + d3

def minDigit (n1 n2 n3 : Int) (i : Nat) : Int := min (D n1 i) (min (D n2 i) (D n3 i))

def IsPerm3 (a b c n1 n2 n3 : I64) : Prop := List.Perm [a, b, c] [n1, n2, n3]

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3; these are the decimal digits of n padded on the left to exactly four digits, from most significant (i=0) to least significant (i=3). Whenever generate_key(num1,num2,num3) returns a result r, r = 1000·m0 + 100·m1 + 10·m2 + m3, where m_i = min(D_i(num1), D_i(num2), D_i(num3)) for i = 0,1,2,3.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_1 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      r.val = fromDigits (minDigit num1.val num2.val num3.val 0)
                         (minDigit num1.val num2.val num3.val 1)
                         (minDigit num1.val num2.val num3.val 2)
                         (minDigit num1.val num2.val num3.val 3) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      r.val = fromDigits (minDigit num1.val num2.val num3.val 0)
                         (minDigit num1.val num2.val num3.val 1)
                         (minDigit num1.val num2.val num3.val 2)
                         (minDigit num1.val num2.val num3.val 3)) := by
  sorry

/-- For every num1, num2, num3 satisfying the preconditions, generate_key(num1,num2,num3) returns a result r; the call does not fail, overflow, panic, or go out of bounds.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_2 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∃ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∃ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, 0 ≤ r ≤ 9999.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_3 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r → 0 ≤ r.val ∧ r.val ≤ 9999 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r → 0 ≤ r.val ∧ r.val ≤ 9999) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, for every permutation (a,b,c) of the triple (num1,num2,num3), the call generate_key(a,b,c) also returns r.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_4 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ (a b c : I64), IsPerm3 a b c num1 num2 num3 →
        Aegis.GenerateKey.generate_key a b c = ok r := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ (a b c : I64), IsPerm3 a b c num1 num2 num3 →
        Aegis.GenerateKey.generate_key a b c = ok r) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, r ≤ num1, r ≤ num2, and r ≤ num3.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_5 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      r.val ≤ num1.val ∧ r.val ≤ num2.val ∧ r.val ≤ num3.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      r.val ≤ num1.val ∧ r.val ≤ num2.val ∧ r.val ≤ num3.val) := by
  sorry

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3, and for a returned result r let K_i(r) be the i-th digit of r after padding r on the left with zeros to four digits. Whenever generate_key(num1,num2,num3) returns r, for every i ∈ {0,1,2,3} and every j ∈ {1,2,3}, K_i(r) ≤ D_i(num_j).
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_6 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ i : Fin 4, K r.val i ≤ D num1.val i ∧ K r.val i ≤ D num2.val i ∧
        K r.val i ≤ D num3.val i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ i : Fin 4, K r.val i ≤ D num1.val i ∧ K r.val i ≤ D num2.val i ∧
        K r.val i ≤ D num3.val i) := by
  sorry

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3, and for a returned result r let K_i(r) be the i-th digit of r after padding r on the left with zeros to four digits. Whenever generate_key(num1,num2,num3) returns r, for every i ∈ {0,1,2,3} there exists j ∈ {1,2,3} such that K_i(r) = D_i(num_j).
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_7 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ i : Fin 4, K r.val i = D num1.val i ∨ K r.val i = D num2.val i ∨
        K r.val i = D num3.val i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ i : Fin 4, K r.val i = D num1.val i ∨ K r.val i = D num2.val i ∨
        K r.val i = D num3.val i) := by
  sorry

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3. Whenever generate_key(num1,num2,num3) returns a result r, r = 0 if and only if for every i ∈ {0,1,2,3}, at least one of D_i(num1), D_i(num2), D_i(num3) is 0.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_8 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (r.val = 0 ↔ ∀ i : Fin 4,
        D num1.val i = 0 ∨ D num2.val i = 0 ∨ D num3.val i = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (r.val = 0 ↔ ∀ i : Fin 4,
        D num1.val i = 0 ∨ D num2.val i = 0 ∨ D num3.val i = 0)) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, if 1000 ≤ num1, 1000 ≤ num2, and 1000 ≤ num3, then 1000 ≤ r.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_9 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      1000 ≤ num1.val → 1000 ≤ num2.val → 1000 ≤ num3.val → 1000 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      1000 ≤ num1.val → 1000 ≤ num2.val → 1000 ≤ num3.val → 1000 ≤ r.val) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, if at least one of num1, num2, num3 is less than 1000, then r ≤ 999.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_10 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (num1.val < 1000 ∨ num2.val < 1000 ∨ num3.val < 1000) → r.val ≤ 999 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (num1.val < 1000 ∨ num2.val < 1000 ∨ num3.val < 1000) → r.val ≤ 999) := by
  sorry

/-- Whenever generate_key(num1,num2,num3) returns a result r, if 1 ≤ num1 ≤ 9, 1 ≤ num2 ≤ 9, and 1 ≤ num3 ≤ 9, then r = min(num1,num2,num3).
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_11 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      1 ≤ num1.val → num1.val ≤ 9 → 1 ≤ num2.val → num2.val ≤ 9 →
        1 ≤ num3.val → num3.val ≤ 9 → r.val = min num1.val (min num2.val num3.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      1 ≤ num1.val → num1.val ≤ 9 → 1 ≤ num2.val → num2.val ≤ 9 →
        1 ≤ num3.val → num3.val ≤ 9 → r.val = min num1.val (min num2.val num3.val)) := by
  sorry

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3. Whenever generate_key(num1,num2,num3) returns a result r, r = num1 if and only if for every i ∈ {0,1,2,3}, D_i(num1) ≤ D_i(num2) and D_i(num1) ≤ D_i(num3).
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_12 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (r.val = num1.val ↔ ∀ i : Fin 4,
        D num1.val i ≤ D num2.val i ∧ D num1.val i ≤ D num3.val i) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      (r.val = num1.val ↔ ∀ i : Fin 4,
        D num1.val i ≤ D num2.val i ∧ D num1.val i ≤ D num3.val i)) := by
  sorry

/-- Let D_i(n) = floor(n / 10^(3-i)) mod 10 for i = 0,1,2,3. Whenever generate_key(num1,num2,num3) returns a result r, then for every a, b, c with 1 ≤ a,b,c ≤ 9999 and D_i(a) ≤ D_i(num1), D_i(b) ≤ D_i(num2), D_i(c) ≤ D_i(num3) for all i ∈ {0,1,2,3}, if generate_key(a,b,c) returns a result r', then r' ≤ r.
  Preconditions: 1 ≤ num1 ≤ 9999, 1 ≤ num2 ≤ 9999, and 1 ≤ num3 ≤ 9999. -/
theorem spec_13 (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999) :
    ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ (a b c : I64),
        1 ≤ a.val → a.val ≤ 9999 → 1 ≤ b.val → b.val ≤ 9999 →
          1 ≤ c.val → c.val ≤ 9999 →
            (∀ i : Fin 4, D a.val i ≤ D num1.val i) →
            (∀ i : Fin 4, D b.val i ≤ D num2.val i) →
            (∀ i : Fin 4, D c.val i ≤ D num3.val i) →
            ∀ r', Aegis.GenerateKey.generate_key a b c = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (num1 num2 num3 : I64)
    (h1 : 1 ≤ num1.val) (h1u : num1.val ≤ 9999)
    (h2 : 1 ≤ num2.val) (h2u : num2.val ≤ 9999)
    (h3 : 1 ≤ num3.val) (h3u : num3.val ≤ 9999), ∀ r, Aegis.GenerateKey.generate_key num1 num2 num3 = ok r →
      ∀ (a b c : I64),
        1 ≤ a.val → a.val ≤ 9999 → 1 ≤ b.val → b.val ≤ 9999 →
          1 ≤ c.val → c.val ≤ 9999 →
            (∀ i : Fin 4, D a.val i ≤ D num1.val i) →
            (∀ i : Fin 4, D b.val i ≤ D num2.val i) →
            (∀ i : Fin 4, D c.val i ≤ D num3.val i) →
            ∀ r', Aegis.GenerateKey.generate_key a b c = ok r' → r'.val ≤ r.val) := by
  sorry

end AegisSpec.GenerateKey
