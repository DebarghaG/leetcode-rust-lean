import Aegis.CountPrimeSetBits.Code.Funs

/-!
# Specifications of `Aegis.CountPrimeSetBits.count_prime_set_bits`

LeetCode problem `prime-number-of-set-bits-in-binary-representation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountPrimeSetBits

  namespace AegisSpec.CountPrimeSetBits

  def popcount (n : Nat) : Nat :=
    if n = 0 then 0 else n % 2 + popcount (n / 2)
  termination_by n
  decreasing_by omega

  def popcountInt (n : Int) : Nat := popcount n.toNat

  def countPrimePopcountAux (left : Int) : Nat → Nat
    | 0 => 0
    | k + 1 => countPrimePopcountAux left k +
        (if Nat.Prime (popcountInt (left + k)) then 1 else 0)

  def countPrimePopcount (left right : Int) : Nat :=
    countPrimePopcountAux left (right - left + 1).toNat

  /-- The function returns a result r, and r = |{ n : left ≤ n ≤ right and prime(popcount(n)) }|, where popcount(n) is the number of 1 bits in the binary representation of n and prime(p) means p has exactly two positive divisors, 1 and p.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000 and right - left ≤ 10000. -/
  theorem spec_1 (left right : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000) :
      ∃ r : I64, count_prime_set_bits left right = ok r ∧
        r.val = (countPrimePopcount left.val right.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000), ∃ r : I64, count_prime_set_bits left right = ok r ∧
          r.val = (countPrimePopcount left.val right.val : Int)) := by
    sorry

  /-- For every left and right satisfying the preconditions, the function returns a result r; in particular, no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000 and right - left ≤ 10000. -/
  theorem spec_2 (left right : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000) :
      ∃ r : I64, count_prime_set_bits left right = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000), ∃ r : I64, count_prime_set_bits left right = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 ≤ r ≤ right - left + 1.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000 and right - left ≤ 10000. -/
  theorem spec_3 (left right r : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
      (hr : count_prime_set_bits left right = ok r) :
      0 ≤ r.val ∧ r.val ≤ right.val - left.val + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (left right r : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
        (hr : count_prime_set_bits left right = ok r), 0 ≤ r.val ∧ r.val ≤ right.val - left.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = right - left + 1 if and only if for every integer n with left ≤ n ≤ right, prime(popcount(n)) holds, where popcount(n) is the number of 1 bits in the binary representation of n and prime(p) means p has exactly two positive divisors, 1 and p.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000 and right - left ≤ 10000. -/
  theorem spec_4 (left right r : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
      (hr : count_prime_set_bits left right = ok r) :
      (r.val = right.val - left.val + 1 ↔
        ∀ n : Int, left.val ≤ n → n ≤ right.val → Nat.Prime (popcountInt n)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (left right r : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
        (hr : count_prime_set_bits left right = ok r), (r.val = right.val - left.val + 1 ↔
          ∀ n : Int, left.val ≤ n → n ≤ right.val → Nat.Prime (popcountInt n))) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every integer n with left ≤ n ≤ right, popcount(n) is not prime, where popcount(n) is the number of 1 bits in the binary representation of n and prime(p) means p has exactly two positive divisors, 1 and p.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000 and right - left ≤ 10000. -/
  theorem spec_5 (left right r : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
      (hr : count_prime_set_bits left right = ok r) :
      (r.val = 0 ↔
        ∀ n : Int, left.val ≤ n → n ≤ right.val → ¬ Nat.Prime (popcountInt n)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (left right r : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
        (hr : count_prime_set_bits left right = ok r), (r.val = 0 ↔
          ∀ n : Int, left.val ≤ n → n ≤ right.val → ¬ Nat.Prime (popcountInt n))) := by
    sorry

  /-- If the function returns r on (left, right), r1 on (left, m), and r2 on (m+1, right), then r = r1 + r2.
    Preconditions: 1 ≤ left ≤ right ≤ 1000000, right - left ≤ 10000, and m is an integer with left ≤ m < right. -/
  theorem spec_6 (left right m m1 r r1 r2 : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
      (hm_lower : left.val ≤ m.val) (hm_upper : m.val < right.val)
      (hm1 : m1.val = m.val + 1)
      (hr : count_prime_set_bits left right = ok r)
      (hr1 : count_prime_set_bits left m = ok r1)
      (hr2 : count_prime_set_bits m1 right = ok r2) :
      r.val = r1.val + r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (left right m m1 r r1 r2 : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 10000)
        (hm_lower : left.val ≤ m.val) (hm_upper : m.val < right.val)
        (hm1 : m1.val = m.val + 1)
        (hr : count_prime_set_bits left right = ok r)
        (hr1 : count_prime_set_bits left m = ok r1)
        (hr2 : count_prime_set_bits m1 right = ok r2), r.val = r1.val + r2.val) := by
    sorry

  /-- If the function returns r on (left, right) and r' on (left, right+1), then r' = r + 1 when prime(popcount(right+1)) holds, and r' = r otherwise, where popcount(n) is the number of 1 bits in the binary representation of n and prime(p) means p has exactly two positive divisors, 1 and p.
    Preconditions: 1 ≤ left ≤ right < 1000000 and right - left ≤ 9999. -/
  theorem spec_7 (left right right1 r r' : I64)
      (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val < 1000000) (hgap : right.val - left.val ≤ 9999)
      (hright1 : right1.val = right.val + 1)
      (hr : count_prime_set_bits left right = ok r)
      (hr' : count_prime_set_bits left right1 = ok r') :
      r'.val = if Nat.Prime (popcountInt (right.val + 1)) then r.val + 1 else r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (left right right1 r r' : I64)
        (hleft : 1 ≤ left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val < 1000000) (hgap : right.val - left.val ≤ 9999)
        (hright1 : right1.val = right.val + 1)
        (hr : count_prime_set_bits left right = ok r)
        (hr' : count_prime_set_bits left right1 = ok r'), r'.val = if Nat.Prime (popcountInt (right.val + 1)) then r.val + 1 else r.val) := by
    sorry

  /-- If the function returns r on (left, right) and r' on (left-1, right), then r' = r + 1 when prime(popcount(left-1)) holds, and r' = r otherwise, where popcount(n) is the number of 1 bits in the binary representation of n and prime(p) means p has exactly two positive divisors, 1 and p.
    Preconditions: 1 < left ≤ right ≤ 1000000 and right - left ≤ 9999. -/
  theorem spec_8 (left left1 right r r' : I64)
      (hleft : 1 < left.val) (hleft_right : left.val ≤ right.val)
      (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 9999)
      (hleft1 : left1.val = left.val - 1)
      (hr : count_prime_set_bits left right = ok r)
      (hr' : count_prime_set_bits left1 right = ok r') :
      r'.val = if Nat.Prime (popcountInt (left.val - 1)) then r.val + 1 else r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (left left1 right r r' : I64)
        (hleft : 1 < left.val) (hleft_right : left.val ≤ right.val)
        (hright : right.val ≤ 1000000) (hgap : right.val - left.val ≤ 9999)
        (hleft1 : left1.val = left.val - 1)
        (hr : count_prime_set_bits left right = ok r)
        (hr' : count_prime_set_bits left1 right = ok r'), r'.val = if Nat.Prime (popcountInt (left.val - 1)) then r.val + 1 else r.val) := by
    sorry

  /-- If the function returns r1 on (left, right1) and r2 on (left, right2), then r1 ≤ r2.
    Preconditions: 1 ≤ left ≤ right1 ≤ right2 ≤ 1000000, right1 - left ≤ 10000, and right2 - left ≤ 10000. -/
  theorem spec_9 (left right1 right2 r1 r2 : I64)
      (hleft : 1 ≤ left.val) (hleft_right1 : left.val ≤ right1.val)
      (hright1_right2 : right1.val ≤ right2.val) (hright2 : right2.val ≤ 1000000)
      (hgap1 : right1.val - left.val ≤ 10000) (hgap2 : right2.val - left.val ≤ 10000)
      (hr1 : count_prime_set_bits left right1 = ok r1)
      (hr2 : count_prime_set_bits left right2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (left right1 right2 r1 r2 : I64)
        (hleft : 1 ≤ left.val) (hleft_right1 : left.val ≤ right1.val)
        (hright1_right2 : right1.val ≤ right2.val) (hright2 : right2.val ≤ 1000000)
        (hgap1 : right1.val - left.val ≤ 10000) (hgap2 : right2.val - left.val ≤ 10000)
        (hr1 : count_prime_set_bits left right1 = ok r1)
        (hr2 : count_prime_set_bits left right2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If the function returns r1 on (left1, right) and r2 on (left2, right), then r1 ≥ r2.
    Preconditions: 1 ≤ left1 ≤ left2 ≤ right ≤ 1000000, right - left1 ≤ 10000, and right - left2 ≤ 10000. -/
  theorem spec_10 (left1 left2 right r1 r2 : I64)
      (hleft1 : 1 ≤ left1.val) (hleft1_left2 : left1.val ≤ left2.val)
      (hleft2_right : left2.val ≤ right.val) (hright : right.val ≤ 1000000)
      (hgap1 : right.val - left1.val ≤ 10000) (hgap2 : right.val - left2.val ≤ 10000)
      (hr1 : count_prime_set_bits left1 right = ok r1)
      (hr2 : count_prime_set_bits left2 right = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (left1 left2 right r1 r2 : I64)
        (hleft1 : 1 ≤ left1.val) (hleft1_left2 : left1.val ≤ left2.val)
        (hleft2_right : left2.val ≤ right.val) (hright : right.val ≤ 1000000)
        (hgap1 : right.val - left1.val ≤ 10000) (hgap2 : right.val - left2.val ≤ 10000)
        (hr1 : count_prime_set_bits left1 right = ok r1)
        (hr2 : count_prime_set_bits left2 right = ok r2), r2.val ≤ r1.val) := by
    sorry

  end AegisSpec.CountPrimeSetBits
