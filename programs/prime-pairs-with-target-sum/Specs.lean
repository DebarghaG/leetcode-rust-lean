import Aegis.FindPrimePairs.Code.Funs

/-!
# Specifications of `Aegis.FindPrimePairs.find_prime_pairs`

LeetCode problem `prime-pairs-with-target-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindPrimePairs

  namespace AegisSpec.FindPrimePairs

  def PrimeInt (z : ℤ) : Prop := 1 < z ∧ ∀ d : ℤ, 0 < d → d ∣ z → d = 1 ∨ d = z

  def ints (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun z => z.val)

  def rows (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) := r.val.map ints

  def rowAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (ℤ × ℤ) :=
    match (rows r)[i]? with
    | some [x, y] => some (x, y)
    | _ => none

  def IsPrimePairX (n x : ℤ) : Prop := 2 ≤ x ∧ x ≤ n - x ∧ PrimeInt x ∧ PrimeInt (n - x)

  noncomputable def primePairCount (n : ℤ) : ℕ := Nat.card {x : ℤ // IsPrimePairX n x}

  /-- Whenever find_prime_pairs n returns a result r, r is exactly the sorted list of all prime pairs for n: len(r) is the number of integers x such that 2 <= x <= n - x and both x and n - x are prime; for every i with 0 <= i < len(r), len(r[i]) = 2, writing x_i = r[i][0] and y_i = r[i][1], we have x_i <= y_i, x_i + y_i = n, and x_i and y_i are prime; the first coordinates are strictly increasing with i; and every integer x with 2 <= x <= n - x such that x and n - x are prime occurs as the first coordinate of exactly one entry r[i], with r[i][1] = n - x.
    Preconditions: n is an integer with 1 <= n <= 1000000. The argument is a Std.I64, but it is identified here with its mathematical integer value. Indices are 0-based. An integer z is prime iff z > 1 and the only positive divisors of z are 1 and z. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          r.val.length = primePairCount n.val ∧
          (∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val.length = 2) ∧
          (∀ (i : ℕ) (x y : ℤ), i < r.val.length → rowAt r i = some (x, y) →
            x ≤ y ∧ x + y = n.val ∧ PrimeInt x ∧ PrimeInt y) ∧
          (∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
            rowAt r i = some (x, y) → rowAt r j = some (x', y') → x < x') ∧
          (∀ x : ℤ, IsPrimePairX n.val x →
            ∃! i : ℕ, i < r.val.length ∧ rowAt r i = some (x, n.val - x)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            r.val.length = primePairCount n.val ∧
            (∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val.length = 2) ∧
            (∀ (i : ℕ) (x y : ℤ), i < r.val.length → rowAt r i = some (x, y) →
              x ≤ y ∧ x + y = n.val ∧ PrimeInt x ∧ PrimeInt y) ∧
            (∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
              rowAt r i = some (x, y) → rowAt r j = some (x', y') → x < x') ∧
            (∀ x : ℤ, IsPrimePairX n.val x →
              ∃! i : ℕ, i < r.val.length ∧ rowAt r i = some (x, n.val - x))) := by
    sorry

  /-- For every integer n with 1 <= n <= 1000000, find_prime_pairs n returns a result r; equivalently, the call does not fail, panic, overflow, or go out of bounds.
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), find_prime_pairs n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), find_prime_pairs n = ok r) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, every entry of the outer vector has exactly two coordinates: for every i with 0 <= i < len(r), len(r[i]) = 2.
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ (i : ℕ) (hi : i < r.val.length), (r.val[i]'hi).val.length = 2) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, every entry of r is a pair [x, y] of integers satisfying 1 <= x <= y <= n.
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ 1 ≤ x ∧ x ≤ y ∧ y ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ 1 ≤ x ∧ x ≤ y ∧ y ≤ n.val) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, every entry of r is a pair [x, y] with x + y = n, using ordinary mathematical integer addition.
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ x + y = n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ x + y = n.val) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, for every entry [x, y] of r, the first coordinate x is prime.
    Preconditions: n is an integer with 1 <= n <= 1000000. An integer z is prime iff z > 1 and its only positive divisors are 1 and z. -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ PrimeInt x := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ PrimeInt x) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, for every entry [x, y] of r, the second coordinate y is prime.
    Preconditions: n is an integer with 1 <= n <= 1000000. An integer z is prime iff z > 1 and its only positive divisors are 1 and z. -/
  theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ PrimeInt y := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ e ∈ r.val, ∃ x y : ℤ, ints e = [x, y] ∧ PrimeInt y) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, the entries are strictly increasing in their first coordinate: for every i and j with 0 <= i < j < len(r), r[i][0] < r[j][0].
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
            rowAt r i = some (x, y) → rowAt r j = some (x', y') → x < x' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
              rowAt r i = some (x, y) → rowAt r j = some (x', y') → x < x') := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, for every integer x satisfying 2 <= x <= n - x such that x and n - x are both prime, there exists exactly one index i with 0 <= i < len(r) such that r[i][0] = x and r[i][1] = n - x.
    Preconditions: n is an integer with 1 <= n <= 1000000. An integer z is prime iff z > 1 and its only positive divisors are 1 and z. -/
  theorem spec_9 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ x : ℤ, 2 ≤ x → x ≤ n.val - x → PrimeInt x → PrimeInt (n.val - x) →
            ∃! i : ℕ, i < r.val.length ∧ rowAt r i = some (x, n.val - x) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ x : ℤ, 2 ≤ x → x ≤ n.val - x → PrimeInt x → PrimeInt (n.val - x) →
              ∃! i : ℕ, i < r.val.length ∧ rowAt r i = some (x, n.val - x)) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, the second coordinates are strictly decreasing: for every i and j with 0 <= i < j < len(r), r[i][1] > r[j][1].
    Preconditions: n is an integer with 1 <= n <= 1000000. -/
  theorem spec_10 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
            rowAt r i = some (x, y) → rowAt r j = some (x', y') → y > y' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ (i j : ℕ) (x y x' y' : ℤ), i < j → i < r.val.length → j < r.val.length →
              rowAt r i = some (x, y) → rowAt r j = some (x', y') → y > y') := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, len(r) equals the number of integers x such that 2 <= x <= n - x, x is prime, and n - x is prime.
    Preconditions: n is an integer with 1 <= n <= 1000000. An integer z is prime iff z > 1 and its only positive divisors are 1 and z. -/
  theorem spec_11 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r → r.val.length = primePairCount n.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r → r.val.length = primePairCount n.val) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, len(r) = 0 if and only if there is no integer x with 2 <= x <= n - x such that both x and n - x are prime.
    Preconditions: n is an integer with 1 <= n <= 1000000. An integer z is prime iff z > 1 and its only positive divisors are 1 and z. -/
  theorem spec_12 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          (r.val.length = 0 ↔ ¬ ∃ x : ℤ, IsPrimePairX n.val x) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            (r.val.length = 0 ↔ ¬ ∃ x : ℤ, IsPrimePairX n.val x)) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, every entry [x, y] of r has x = 2.
    Preconditions: n is an odd integer with 1 <= n <= 1000000. -/
  theorem spec_13 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) (hodd : Odd n.val) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r →
          ∀ e ∈ r.val, ∃ y : ℤ, ints e = [2, y] := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000) (hodd : Odd n.val), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r →
            ∀ e ∈ r.val, ∃ y : ℤ, ints e = [2, y]) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, len(r) = 0.
    Preconditions: n is an integer with 1 <= n <= 3. -/
  theorem spec_14 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 3) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r → r.val.length = 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 3), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r → r.val.length = 0) := by
    sorry

  /-- Whenever find_prime_pairs n returns a result r, r has exactly one entry, namely r[0][0] = 2 and r[0][1] = 2.
    Preconditions: n = 4. -/
  theorem spec_15 (n : Std.I64) (hn : n.val = 4) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        find_prime_pairs n = ok r → r.val.length = 1 ∧ rowAt r 0 = some (2, 2) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 4), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          find_prime_pairs n = ok r → r.val.length = 1 ∧ rowAt r 0 = some (2, 2)) := by
    sorry

  end AegisSpec.FindPrimePairs
