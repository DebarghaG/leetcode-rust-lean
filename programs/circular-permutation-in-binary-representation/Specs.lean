import Aegis.CircularPermutation.Code.Funs

/-!
# Specifications of `Aegis.CircularPermutation.circular_permutation`

LeetCode problem `circular-permutation-in-binary-representation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CircularPermutation

open Aegis.CircularPermutation

def N (n : Std.I64) : ℕ := 2 ^ n.val.toNat

def vals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun v => v.val)

def bit (x : ℤ) (k : ℕ) : ℕ := (x.natAbs / 2 ^ k) % 2

def differInOneBit (n : ℕ) (a b : ℤ) : Prop := ∃! k : ℕ, k < n ∧ bit a k ≠ bit b k

def lastFirstAdjacent (n : ℕ) (l : List ℤ) : Prop :=
  ∃ a b : ℤ, l.getLast? = some a ∧ l[0]? = some b ∧ differInOneBit n a b

/-- The function returns a result r (it does not fail). The result r satisfies all of the following: len(r) = N; r[0] = start; for every i with 0 <= i < len(r), 0 <= r[i] < N; for all i and j with 0 <= i < j < len(r), r[i] != r[j]; for every i with 0 <= i < len(r)-1, the n-bit binary representations of r[i] and r[i+1] differ in exactly one bit position; and the n-bit binary representations of r[len(r)-1] and r[0] differ in exactly one bit position. Here two values have n-bit binary representations differing in exactly one bit position when there is exactly one k with 0 <= k < n such that their k-th least significant bits differ.
  Preconditions: Let N = 2^n, using mathematical exponentiation (under the stated bounds N is at most 65536). The parameter n is an integer with 1 <= n <= 16, and the parameter start is an integer with 0 <= start < N. -/
theorem spec_1 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∃ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r ∧
      (vals r).length = N n ∧
      (vals r)[0]? = some start.val ∧
      (∀ (i : ℕ) (hi : i < (vals r).length),
        0 ≤ (vals r)[i] ∧ (vals r)[i] < (N n : ℤ)) ∧
      (∀ (i j : ℕ) (hij : i < j) (hj : j < (vals r).length),
        (vals r)[i]'(by omega) ≠ (vals r)[j]) ∧
      (∀ (i : ℕ) (hi : i + 1 < (vals r).length),
        differInOneBit n.val.toNat (vals r)[i] (vals r)[i + 1]) ∧
      lastFirstAdjacent n.val.toNat (vals r) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∃ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r ∧
      (vals r).length = N n ∧
      (vals r)[0]? = some start.val ∧
      (∀ (i : ℕ) (hi : i < (vals r).length),
        0 ≤ (vals r)[i] ∧ (vals r)[i] < (N n : ℤ)) ∧
      (∀ (i j : ℕ) (hij : i < j) (hj : j < (vals r).length),
        (vals r)[i]'(by omega) ≠ (vals r)[j]) ∧
      (∀ (i : ℕ) (hi : i + 1 < (vals r).length),
        differInOneBit n.val.toNat (vals r)[i] (vals r)[i + 1]) ∧
      lastFirstAdjacent n.val.toNat (vals r)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, panic, or out-of-bounds access).
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_2 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∃ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∃ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 2^n.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_3 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → (vals r).length = N n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → (vals r).length = N n) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i].
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_4 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i < (vals r).length), 0 ≤ (vals r)[i] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i < (vals r).length), 0 ≤ (vals r)[i]) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] < 2^n.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_5 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i < (vals r).length), (vals r)[i] < (N n : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i < (vals r).length), (vals r)[i] < (N n : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for all indices i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_6 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i j : ℕ) (hij : i < j) (hj : j < (vals r).length),
        (vals r)[i]'(by omega) ≠ (vals r)[j] := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i j : ℕ) (hij : i < j) (hj : j < (vals r).length),
        (vals r)[i]'(by omega) ≠ (vals r)[j]) := by
  sorry

/-- Whenever the function returns a result r, for every integer x with 0 <= x < 2^n there is exactly one index i with 0 <= i < len(r) such that r[i] = x.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_7 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ x : ℤ, 0 ≤ x → x < (N n : ℤ) →
        ∃! i : ℕ, i < (vals r).length ∧ (vals r)[i]? = some x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ x : ℤ, 0 ≤ x → x < (N n : ℤ) →
        ∃! i : ℕ, i < (vals r).length ∧ (vals r)[i]? = some x) := by
  sorry

/-- Whenever the function returns a result r, r[0] = start.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_8 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → (vals r)[0]? = some start.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → (vals r)[0]? = some start.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, the n-bit binary representations of r[i] and r[i+1] differ in exactly one bit position; that is, there is exactly one k with 0 <= k < n such that the k-th least significant bits of r[i] and r[i+1] are different.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_9 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i + 1 < (vals r).length),
        differInOneBit n.val.toNat (vals r)[i] (vals r)[i + 1] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (i : ℕ) (hi : i + 1 < (vals r).length),
        differInOneBit n.val.toNat (vals r)[i] (vals r)[i + 1]) := by
  sorry

/-- Whenever the function returns a result r, the n-bit binary representations of r[len(r)-1] and r[0] differ in exactly one bit position; that is, there is exactly one k with 0 <= k < n such that the k-th least significant bits of r[len(r)-1] and r[0] are different.
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_10 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → lastFirstAdjacent n.val.toNat (vals r) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64,
      circular_permutation n start = ok r → lastFirstAdjacent n.val.toNat (vals r)) := by
  sorry

/-- Whenever the function returns a result r with len(r) > 0, for every bit position k with 0 <= k < n there exists an index i with 0 <= i < len(r) such that the k-th least significant bit of r[i] differs from the k-th least significant bit of r[(i+1) mod len(r)].
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_11 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (hpos : 0 < (vals r).length), ∀ k : ℕ, k < n.val.toNat →
        ∃ (i : ℕ) (hi : i < (vals r).length),
          bit ((vals r)[i]'(hi)) k ≠
            bit ((vals r)[(i + 1) % (vals r).length]'(Nat.mod_lt _ hpos)) k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ (hpos : 0 < (vals r).length), ∀ k : ℕ, k < n.val.toNat →
        ∃ (i : ℕ) (hi : i < (vals r).length),
          bit ((vals r)[i]'(hi)) k ≠
            bit ((vals r)[(i + 1) % (vals r).length]'(Nat.mod_lt _ hpos)) k) := by
  sorry

/-- Whenever the function returns a result r, for every bit position k with 0 <= k < n, the number of indices i with 0 <= i < len(r) whose r[i] has its k-th least significant bit equal to 1 is exactly 2^(n-1).
  Preconditions: Let N = 2^n, using mathematical exponentiation. The parameter n is an integer with 1 <= n <= 16, and start is an integer with 0 <= start < N. -/
theorem spec_12 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)) :
    ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ k : ℕ, k < n.val.toNat →
        (vals r).countP (fun x => bit x k == 1) = 2 ^ (n.val.toNat - 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn16 : n.val ≤ 16)
    (hs0 : 0 ≤ start.val) (hsN : start.val < (N n : ℤ)), ∀ r : alloc.vec.Vec Std.I64, circular_permutation n start = ok r →
      ∀ k : ℕ, k < n.val.toNat →
        (vals r).countP (fun x => bit x k == 1) = 2 ^ (n.val.toNat - 1)) := by
  sorry

end AegisSpec.CircularPermutation
