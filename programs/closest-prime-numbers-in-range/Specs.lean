import Aegis.ClosestPrimes.Code.Funs

/-!
# Specifications of `Aegis.ClosestPrimes.closest_primes`

LeetCode problem `closest-prime-numbers-in-range`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ClosestPrimes

  abbrev I64 := Aeneas.Std.I64

  abbrev I64Vec := Aeneas.Std.alloc.vec.Vec I64

  def IsPrimeInt (n : Int) : Prop :=
    2 ≤ n ∧ ∀ d : Int, 0 < d → d ∣ n → d = 1 ∨ d = n

  def primeInterval (left right : Int) : Set Int := {p | IsPrimeInt p ∧ left ≤ p ∧ p ≤ right}

  def vals (r : I64Vec) : List Int := r.val.map (fun x => x.val)

  def getI (r : I64Vec) (i : Nat) : Int := ((vals r)[i]?).getD 0

  /-- Let P be the set of prime integers p satisfying left <= p <= right. The function returns a result r such that len(r) = 2, and: (a) if |P| < 2, then r[0] = -1 and r[1] = -1; (b) if |P| >= 2, then, writing a = r[0] and b = r[1], (i) a and b are prime, (ii) left <= a < b <= right, (iii) for every pair of primes x,y with left <= x < y <= right, b - a <= y - x, and (iv) for every pair of primes x,y with left <= x < y <= right and y - x = b - a, a <= x.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_1 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000) :
      ∃ r : I64Vec,
        Aegis.ClosestPrimes.closest_primes left right = ok r ∧
          (vals r).length = 2 ∧
          ((primeInterval left.val right.val).ncard < 2 →
            getI r 0 = -1 ∧ getI r 1 = -1) ∧
          (2 ≤ (primeInterval left.val right.val).ncard →
            IsPrimeInt (getI r 0) ∧
              IsPrimeInt (getI r 1) ∧
                (left.val ≤ getI r 0 ∧ getI r 0 < getI r 1 ∧ getI r 1 ≤ right.val) ∧
                (∀ x y : Int,
                  IsPrimeInt x → IsPrimeInt y → left.val ≤ x → x < y → y ≤ right.val →
                    getI r 1 - getI r 0 ≤ y - x) ∧
                  (∀ x y : Int,
                    IsPrimeInt x → IsPrimeInt y → left.val ≤ x → x < y → y ≤ right.val →
                      y - x = getI r 1 - getI r 0 → getI r 0 ≤ x)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000), ∃ r : I64Vec,
          Aegis.ClosestPrimes.closest_primes left right = ok r ∧
            (vals r).length = 2 ∧
            ((primeInterval left.val right.val).ncard < 2 →
              getI r 0 = -1 ∧ getI r 1 = -1) ∧
            (2 ≤ (primeInterval left.val right.val).ncard →
              IsPrimeInt (getI r 0) ∧
                IsPrimeInt (getI r 1) ∧
                  (left.val ≤ getI r 0 ∧ getI r 0 < getI r 1 ∧ getI r 1 ≤ right.val) ∧
                  (∀ x y : Int,
                    IsPrimeInt x → IsPrimeInt y → left.val ≤ x → x < y → y ≤ right.val →
                      getI r 1 - getI r 0 ≤ y - x) ∧
                    (∀ x y : Int,
                      IsPrimeInt x → IsPrimeInt y → left.val ≤ x → x < y → y ≤ right.val →
                        y - x = getI r 1 - getI r 0 → getI r 0 ≤ x))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. -/
  theorem spec_2 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000) :
      ∃ r : I64Vec, Aegis.ClosestPrimes.closest_primes left right = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000), ∃ r : I64Vec, Aegis.ClosestPrimes.closest_primes left right = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. -/
  theorem spec_3 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r) :
      (vals r).length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r), (vals r).length = 2) := by
    sorry

  /-- Let P be the set of prime integers p satisfying left <= p <= right. Whenever the function returns a result r, r = [-1, -1] if and only if |P| < 2.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_4 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r) :
      vals r = [-1, -1] ↔ (primeInterval left.val right.val).ncard < 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r), vals r = [-1, -1] ↔ (primeInterval left.val right.val).ncard < 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], both r[0] and r[1] are prime integers.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_5 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]) :
      IsPrimeInt (getI r 0) ∧ IsPrimeInt (getI r 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]), IsPrimeInt (getI r 0) ∧ IsPrimeInt (getI r 1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], both r[0] and r[1] lie in the inclusive interval [left, right].
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. -/
  theorem spec_6 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]) :
      left.val ≤ getI r 0 ∧ getI r 0 ≤ right.val ∧ left.val ≤ getI r 1 ∧
        getI r 1 ≤ right.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]), left.val ≤ getI r 0 ∧ getI r 0 ≤ right.val ∧ left.val ≤ getI r 1 ∧
          getI r 1 ≤ right.val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], r[0] < r[1].
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. -/
  theorem spec_7 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]) :
      getI r 0 < getI r 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]), getI r 0 < getI r 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], for every pair of prime integers x,y with left <= x < y <= right, r[1] - r[0] <= y - x.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_8 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1])
      (x y : Int) (hx : IsPrimeInt x) (hy : IsPrimeInt y)
      (hxy_left : left.val ≤ x) (hxy : x < y) (hxy_right : y ≤ right.val) :
      getI r 1 - getI r 0 ≤ y - x := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1])
        (x y : Int) (hx : IsPrimeInt x) (hy : IsPrimeInt y)
        (hxy_left : left.val ≤ x) (hxy : x < y) (hxy_right : y ≤ right.val), getI r 1 - getI r 0 ≤ y - x) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], for every pair of prime integers x,y with left <= x < y <= right and y - x = r[1] - r[0], we have r[0] <= x.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_9 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1])
      (x y : Int) (hx : IsPrimeInt x) (hy : IsPrimeInt y)
      (hxy_left : left.val ≤ x) (hxy : x < y) (hxy_right : y ≤ right.val)
      (hgap : y - x = getI r 1 - getI r 0) :
      getI r 0 ≤ x := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1])
        (x y : Int) (hx : IsPrimeInt x) (hy : IsPrimeInt y)
        (hxy_left : left.val ≤ x) (hxy : x < y) (hxy_right : y ≤ right.val)
        (hgap : y - x = getI r 1 - getI r 0), getI r 0 ≤ x) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r != [-1, -1], there is no prime integer p satisfying left <= p <= right and r[0] < p < r[1].
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_10 (left right : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]) :
      ¬ ∃ p : Int, IsPrimeInt p ∧ left.val ≤ p ∧ p ≤ right.val ∧ getI r 0 < p ∧ p < getI r 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (left right : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (r : I64Vec) (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hlen : (vals r).length = 2) (hne : vals r ≠ [-1, -1]), ¬ ∃ p : Int, IsPrimeInt p ∧ left.val ≤ p ∧ p ≤ right.val ∧ getI r 0 < p ∧ p < getI r 1) := by
    sorry

  /-- For any second pair left', right' of 64-bit integers also satisfying 1 <= left' <= right' <= 1000000, if the set of prime integers p with left <= p <= right equals the set of prime integers p with left' <= p <= right', then whenever the function returns r on (left,right) and r' on (left',right'), we have r = r'.
    Preconditions: left and right are 64-bit integers satisfying 1 <= left <= right <= 1000000. An integer n is prime iff n >= 2 and its only positive divisors are 1 and n. -/
  theorem spec_11 (left right left' right' : I64)
      (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
      (hleft' : 1 ≤ left'.val) (hright_le' : left'.val ≤ right'.val)
      (hright' : right'.val ≤ 1000000)
      (hset : primeInterval left.val right.val = primeInterval left'.val right'.val)
      (r r' : I64Vec)
      (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
      (hret' : Aegis.ClosestPrimes.closest_primes left' right' = ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (left right left' right' : I64)
        (hleft : 1 ≤ left.val) (hright_le : left.val ≤ right.val) (hright : right.val ≤ 1000000)
        (hleft' : 1 ≤ left'.val) (hright_le' : left'.val ≤ right'.val)
        (hright' : right'.val ≤ 1000000)
        (hset : primeInterval left.val right.val = primeInterval left'.val right'.val)
        (r r' : I64Vec)
        (hret : Aegis.ClosestPrimes.closest_primes left right = ok r)
        (hret' : Aegis.ClosestPrimes.closest_primes left' right' = ok r'), r = r') := by
    sorry

  end AegisSpec.ClosestPrimes
