import Aegis.CountVowelStrings.Code.Funs

/-!
# Specifications of `Aegis.CountVowelStrings.count_vowel_strings`

LeetCode problem `count-sorted-vowel-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountVowelStrings

  namespace AegisSpec.CountVowelStrings

  abbrev Vowel : Type := Fin 5

  abbrev VowelString (n : Nat) : Type := Fin n → Vowel

  def VowelString.IsWeaklyIncreasing {n : Nat} (s : VowelString n) : Prop :=
    ∀ i : Fin n, ∀ j : Fin n, (i : Nat) + 1 = (j : Nat) → s i ≤ s j

  def weaklyIncreasingVowelStrings (n : Nat) : Finset (VowelString n) :=
    Finset.univ.filter
      (fun s : VowelString n => ∀ i : Fin n, ∀ j : Fin n, (i : Nat) + 1 = (j : Nat) → s i ≤ s j)

  theorem mem_weaklyIncreasingVowelStrings_iff {n : Nat} (s : VowelString n) :
      s ∈ weaklyIncreasingVowelStrings n ↔ s.IsWeaklyIncreasing := by
    simp [weaklyIncreasingVowelStrings, VowelString.IsWeaklyIncreasing]

  def countWeaklyIncreasingVowelStrings (n : Nat) : Nat :=
    (weaklyIncreasingVowelStrings n).card

  def orderedNonnegTupleCount (n : Nat) : Nat :=
    (Finset.univ.filter (fun t : Fin 5 → Fin (n + 1) => ∑ i : Fin 5, (t i : Nat) = n)).card

  def sumChooseShift (n : Nat) : Nat :=
    ∑ j ∈ Finset.range 5, (n + j - 1).choose (n - 1)

  def sumChooseThree (n : Nat) : Nat :=
    ∑ a ∈ Finset.range (n + 1), (n - a + 3).choose 3

  def i64Succ (x : Std.I64) : Std.I64 := ⟨x.bv + BitVec.ofNat 64 1⟩

  def i64Pred (x : Std.I64) : Std.I64 := ⟨x.bv - BitVec.ofNat 64 1⟩

  /-- The function returns a result r, and r is the number of strings s of length n such that every character of s is one of the five vowel characters a, e, i, o, u and, for every i with 0 <= i < n-1, the vowel at position i is the same as or precedes the vowel at position i+1 in the alphabet order a < e < i < o < u.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧
        r.val = (countWeaklyIncreasingVowelStrings n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧
          r.val = (countWeaklyIncreasingVowelStrings n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r and r = (n+1)*(n+2)*(n+3)*(n+4)/24, where the arithmetic is in mathematical integers and the division is exact.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧
        r.val = (n.val + 1) * (n.val + 2) * (n.val + 3) * (n.val + 4) / 24 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧
          r.val = (n.val + 1) * (n.val + 2) * (n.val + 3) * (n.val + 4) / 24) := by
    sorry

  /-- The function returns a result r, and r equals the number of ordered 5-tuples (a,e,i,o,u) of nonnegative integers such that a+e+i+o+u = n.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧
        r.val = (orderedNonnegTupleCount n.val.toNat : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧
          r.val = (orderedNonnegTupleCount n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r with r >= 5.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_4 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧ 5 ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧ 5 ≤ r.val) := by
    sorry

  /-- The function returns a result r with r <= 316251.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_5 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧ r.val ≤ 316251 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧ r.val ≤ 316251) := by
    sorry

  /-- The function returns a result r; in particular, it does not fail, panic, or overflow on any input satisfying the precondition.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_6 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r) := by
    sorry

  /-- Let r be the result returned by the function on input n and let r_next be the result returned by the function on input n+1. Then r < r_next.
    Preconditions: n is an integer with 1 <= n <= 49. -/
  theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 49) :
      ∀ r r_next : Std.I64, count_vowel_strings n = ok r →
        count_vowel_strings (i64Succ n) = ok r_next → r.val < r_next.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 49), ∀ r r_next : Std.I64, count_vowel_strings n = ok r →
          count_vowel_strings (i64Succ n) = ok r_next → r.val < r_next.val) := by
    sorry

  /-- Let r be the result returned by the function on input n and let r_prev be the result returned by the function on input n-1. Then n*r = (n+4)*r_prev, with multiplication in mathematical integers.
    Preconditions: n is an integer with 2 <= n <= 50. -/
  theorem spec_8 (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 50) :
      ∀ r r_prev : Std.I64, count_vowel_strings n = ok r →
        count_vowel_strings (i64Pred n) = ok r_prev → n.val * r.val = (n.val + 4) * r_prev.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 50), ∀ r r_prev : Std.I64, count_vowel_strings n = ok r →
          count_vowel_strings (i64Pred n) = ok r_prev → n.val * r.val = (n.val + 4) * r_prev.val) := by
    sorry

  /-- The function returns a result r, and r = sum_{j=0}^{4} C(n+j-1, n-1), where C(m,k) denotes the number of k-element subsets of an m-element set.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_9 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧
        r.val = (sumChooseShift n.val.toNat : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧
          r.val = (sumChooseShift n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r, and r = sum_{a=0}^{n} C(n-a+3, 3), where C(m,k) denotes the number of k-element subsets of an m-element set.
    Preconditions: n is an integer with 1 <= n <= 50. -/
  theorem spec_10 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50) :
      ∃ r : Std.I64, count_vowel_strings n = ok r ∧
        r.val = (sumChooseThree n.val.toNat : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 50), ∃ r : Std.I64, count_vowel_strings n = ok r ∧
          r.val = (sumChooseThree n.val.toNat : Int)) := by
    sorry

  end AegisSpec.CountVowelStrings
