import Aegis.CountVowelPermutation.Code.Funs

/-!
# Specifications of `Aegis.CountVowelPermutation.count_vowel_permutation`

LeetCode problem `count-vowels-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountVowelPermutation

open Aegis.CountVowelPermutation (count_vowel_permutation)

inductive Vowel : Type where
  | a
  | e
  | i
  | o
  | u
  deriving DecidableEq, Repr

instance : Fintype Vowel where
  elems := {Vowel.a, Vowel.e, Vowel.i, Vowel.o, Vowel.u}
  complete := by intro x; cases x <;> simp

def allowedPairs : Finset (Vowel × Vowel) :=
  {(Vowel.a, Vowel.e), (Vowel.e, Vowel.a), (Vowel.e, Vowel.i), (Vowel.i, Vowel.a),
    (Vowel.i, Vowel.e), (Vowel.i, Vowel.o), (Vowel.i, Vowel.u), (Vowel.o, Vowel.i),
    (Vowel.o, Vowel.u), (Vowel.u, Vowel.a)}

def Allows (x y : Vowel) : Prop := (x, y) ∈ allowedPairs

def ValidSeq {n : ℕ} (s : Fin n → Vowel) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n), Allows (s j) (s ⟨j.val + 1, h⟩)

noncomputable def C (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Fin n → Vowel => ValidSeq s)).card

/-- The function returns a result r and r = C(n) mod M, where M = 1000000007 and C(n) is the number of sequences s of length n such that each s[j] is one of 'a', 'e', 'i', 'o', 'u' and, for every j with 0 <= j < n-1, the ordered pair (s[j], s[j+1]) belongs to {(a,e),(e,a),(e,i),(i,a),(i,e),(i,o),(i,u),(o,i),(o,u),(u,a)}. Here x mod M denotes the unique integer in [0, M-1] congruent to x modulo M.
  Preconditions: 1 <= n <= 20000. -/
theorem spec_1 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) :
    ∃ r : I64,
      count_vowel_permutation n = ok r ∧
        r.val = ((C n.val.toNat : ℤ) % 1000000007) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000), ∃ r : I64,
      count_vowel_permutation n = ok r ∧
        r.val = ((C n.val.toNat : ℤ) % 1000000007)) := by
  sorry

/-- For every integer n with 1 <= n <= 20000, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= n <= 20000. -/
theorem spec_2 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) :
    ∃ r : I64, count_vowel_permutation n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000), ∃ r : I64, count_vowel_permutation n = ok r) := by
  sorry

/-- Whenever the function returns a result r for an input n with 1 <= n <= 20000, we have 0 <= r < 1000000007.
  Preconditions: 1 <= n <= 20000. -/
theorem spec_3 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) (r : I64)
    (hr : count_vowel_permutation n = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) (r : I64)
    (hr : count_vowel_permutation n = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Whenever the function returns a result r for an input n with 1 <= n <= 20000, there exists a nonnegative integer q such that C(n) = r + q * 1000000007, where C(n) is the number of valid vowel strings of length n as defined in spec_1.
  Preconditions: 1 <= n <= 20000. -/
theorem spec_4 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) (r : I64)
    (hr : count_vowel_permutation n = ok r) :
    ∃ q : ℕ, (C n.val.toNat : ℤ) = r.val + (q : ℤ) * 1000000007 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 20000) (r : I64)
    (hr : count_vowel_permutation n = ok r), ∃ q : ℕ, (C n.val.toNat : ℤ) = r.val + (q : ℤ) * 1000000007) := by
  sorry

end AegisSpec.CountVowelPermutation
