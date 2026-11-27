import Aegis.StringCount.Code.Funs

/-!
# Specifications of `Aegis.StringCount.string_count`

LeetCode problem `number-of-strings-which-can-be-rearranged-to-contain-substring`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.StringCount

  def MOD : ℤ := 1000000007

  def alphabet : List Char := "abcdefghijklmnopqrstuvwxyz".toList

  theorem alphabet_length : alphabet.length = 26 := by decide

  def eLetter : Fin 26 := ⟨4, by decide⟩

  def lLetter : Fin 26 := ⟨11, by decide⟩

  def tLetter : Fin 26 := ⟨19, by decide⟩

  theorem alphabet_eLetter : alphabet[4]? = some 'e' := by decide

  theorem alphabet_lLetter : alphabet[11]? = some 'l' := by decide

  theorem alphabet_tLetter : alphabet[19]? = some 't' := by decide

  def occursIn (a : Fin 26) (s : List (Fin 26)) : Nat :=
    (s.filter (fun c => c = a)).length

  def occ {n : Nat} (a : Fin 26) (w : Fin n → Fin 26) : Nat :=
    occursIn a (List.ofFn w)

  def wordSet (n : Nat) : Finset (Fin n → Fin 26) := Finset.univ

  def G (n : Nat) : Nat :=
    ((wordSet n).filter
      (fun w => 2 ≤ occ eLetter w ∧ 1 ≤ occ lLetter w ∧ 1 ≤ occ tLetter w)).card

  def B (n : Nat) : Nat :=
    ((wordSet n).filter
      (fun w => occ eLetter w ≤ 1 ∨ occ lLetter w = 0 ∨ occ tLetter w = 0)).card

  def closedForm9 (n : Nat) : ℤ :=
    (26 : ℤ) ^ n - ((25 : ℤ) ^ n + (n : ℤ) * (25 : ℤ) ^ (n - 1))
      - 2 * (25 : ℤ) ^ n + 2 * ((24 : ℤ) ^ n + (n : ℤ) * (24 : ℤ) ^ (n - 1))
      + (24 : ℤ) ^ n - ((23 : ℤ) ^ n + (n : ℤ) * (23 : ℤ) ^ (n - 1))

  def binomialSum10 (n : Nat) : ℤ :=
    ∑ j ∈ Finset.Icc 2 n,
      (n.choose j : ℤ) * ((25 : ℤ) ^ (n - j) - 2 * (24 : ℤ) ^ (n - j) + (23 : ℤ) ^ (n - j))

  def IsLeastResidue (M x r : ℤ) : Prop :=
    0 ≤ r ∧ r < M ∧ x ≡ r [ZMOD M] ∧
      ∀ k : ℤ, 0 ≤ k → k < M → x ≡ k [ZMOD M] → k = r

  /-- Let Sigma be the 26 lowercase English letters, and let G(n) be the number of strings s of length n over Sigma such that s has at least two occurrences of 'e', at least one occurrence of 'l', and at least one occurrence of 't'. Let M = 1000000007. Whenever string_count(n) returns r, r is the unique integer with 0 <= r < M and r ≡ G(n) (mod M).
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_1 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∀ r : I64, Aegis.StringCount.string_count n = ok r →
        IsLeastResidue MOD ((G n.val.toNat : ℤ)) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∀ r : I64, Aegis.StringCount.string_count n = ok r →
          IsLeastResidue MOD ((G n.val.toNat : ℤ)) r.val) := by
    sorry

  /-- For every I64 value n with 1 <= n <= 100000, string_count(n) returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_2 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∃ r : I64, Aegis.StringCount.string_count n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∃ r : I64, Aegis.StringCount.string_count n = ok r) := by
    sorry

  /-- Whenever string_count(n) returns r, 0 <= r < 1000000007.
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_3 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∀ r : I64, Aegis.StringCount.string_count n = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∀ r : I64, Aegis.StringCount.string_count n = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Let M = 1000000007. Let B(n) be the number of length-n strings over the 26 lowercase English letters that satisfy at least one of the following: the number of 'e' occurrences is at most 1; the number of 'l' occurrences is 0; the number of 't' occurrences is 0. Whenever string_count(n) returns r, r is the unique integer with 0 <= r < M and r ≡ 26^n - B(n) (mod M).
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_4 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∀ r : I64, Aegis.StringCount.string_count n = ok r →
        IsLeastResidue MOD ((26 : ℤ) ^ n.val.toNat - (B n.val.toNat : ℤ)) r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∀ r : I64, Aegis.StringCount.string_count n = ok r →
          IsLeastResidue MOD ((26 : ℤ) ^ n.val.toNat - (B n.val.toNat : ℤ)) r.val) := by
    sorry

  /-- Let M = 1000000007. Whenever string_count(n) returns r, r is the unique integer with 0 <= r < M and r ≡ 26^n - (25^n + n*25^(n-1)) - 2*25^n + 2*(24^n + n*24^(n-1)) + 24^n - (23^n + n*23^(n-1)) (mod M).
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_5 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∀ r : I64, Aegis.StringCount.string_count n = ok r →
        IsLeastResidue MOD (closedForm9 n.val.toNat) r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∀ r : I64, Aegis.StringCount.string_count n = ok r →
          IsLeastResidue MOD (closedForm9 n.val.toNat) r.val) := by
    sorry

  /-- Let M = 1000000007, and let C(n,j) denote the binomial coefficient. Whenever string_count(n) returns r, r is the unique integer with 0 <= r < M and r ≡ sum_{j=2}^{n} C(n,j) * (25^(n-j) - 2*24^(n-j) + 23^(n-j)) (mod M), where the sum is 0 when n < 2 and a^0 = 1 for every nonzero a.
    Preconditions: n is an I64 value with 1 <= n <= 100000. -/
  theorem spec_6 (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000) :
      ∀ r : I64, Aegis.StringCount.string_count n = ok r →
        IsLeastResidue MOD (binomialSum10 n.val.toNat) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (hn_pos : 1 ≤ n.val) (hn_le : n.val ≤ 100000), ∀ r : I64, Aegis.StringCount.string_count n = ok r →
          IsLeastResidue MOD (binomialSum10 n.val.toNat) r.val) := by
    sorry

  end AegisSpec.StringCount
