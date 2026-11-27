import Aegis.CountTriples.Code.Funs

/-!
# Specifications of `Aegis.CountTriples.count_triples`

LeetCode problem `count-square-sum-triples`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountTriples

  def tripleSet (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
    (Finset.Icc 1 n ×ˢ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n)).filter
      (fun p => p.1 ^ 2 + p.2.1 ^ 2 = p.2.2 ^ 2)

  def tripleCount (n : ℕ) : ℕ := (tripleSet n).card

  def pairSet (n : ℕ) : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun p => p.1 < p.2 ∧ ∃ c ∈ Finset.Icc 1 n, p.1 ^ 2 + p.2 ^ 2 = c ^ 2)

  def pairCount (n : ℕ) : ℕ := (pairSet n).card

  /-- The function returns a result r, and r is the number of ordered triples (a,b,c) of integers such that 1 <= a <= n, 1 <= b <= n, 1 <= c <= n, and a^2 + b^2 = c^2.
    Preconditions: n is an integer satisfying 1 <= n <= 250. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64,
        Aegis.CountTriples.count_triples n = ok r ∧ r.val = (tripleCount n.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64,
          Aegis.CountTriples.count_triples n = ok r ∧ r.val = (tripleCount n.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r for every n satisfying 1 <= n <= 250; it does not fail from arithmetic overflow, an out-of-range index, a panic, or any other runtime error.
    Preconditions: n is an integer satisfying 1 <= n <= 250. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r) := by
    sorry

  /-- The returned value r satisfies 0 <= r <= 330.
    Preconditions: n is an integer satisfying 1 <= n <= 250. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 330 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ 330) := by
    sorry

  /-- The returned value r is even; that is, r = 2*k for some integer k.
    Preconditions: n is an integer satisfying 1 <= n <= 250. -/
  theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ ∃ k : ℤ, r.val = 2 * k := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ ∃ k : ℤ, r.val = 2 * k) := by
    sorry

  /-- The returned value r equals twice the number of unordered pairs {a,b} with 1 <= a < b <= n for which there exists an integer c with 1 <= c <= n and a^2 + b^2 = c^2.
    Preconditions: n is an integer satisfying 1 <= n <= 250. -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64,
        Aegis.CountTriples.count_triples n = ok r ∧ r.val = 2 * (pairCount n.val.toNat : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64,
          Aegis.CountTriples.count_triples n = ok r ∧ r.val = 2 * (pairCount n.val.toNat : ℤ)) := by
    sorry

  /-- Let r_n be the result returned by the function on input n and r_m the result returned by the function on input m. Then r_n <= r_m.
    Preconditions: n and m are integers satisfying 1 <= n <= m <= 250. -/
  theorem spec_6 (n m : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm2 : m.val ≤ 250) :
      ∃ rn rm : Std.I64,
        Aegis.CountTriples.count_triples n = ok rn ∧
          Aegis.CountTriples.count_triples m = ok rm ∧ rn.val ≤ rm.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m : Std.I64) (hn1 : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm2 : m.val ≤ 250), ∃ rn rm : Std.I64,
          Aegis.CountTriples.count_triples n = ok rn ∧
            Aegis.CountTriples.count_triples m = ok rm ∧ rn.val ≤ rm.val) := by
    sorry

  /-- The function returns r = 0.
    Preconditions: n is an integer satisfying 1 <= n <= 4. -/
  theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 4) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 4), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a value r with r >= 2.
    Preconditions: n is an integer satisfying 5 <= n <= 250. -/
  theorem spec_8 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 2 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 2 ≤ r.val) := by
    sorry

  /-- The function returns a value r with r >= 4.
    Preconditions: n is an integer satisfying 10 <= n <= 250. -/
  theorem spec_9 (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 4 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ 4 ≤ r.val) := by
    sorry

  /-- The function returns r = 2.
    Preconditions: n is an integer satisfying 5 <= n <= 9. -/
  theorem spec_10 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 9) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 9), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 2) := by
    sorry

  /-- The function returns r = 4.
    Preconditions: n is an integer satisfying 10 <= n <= 12. -/
  theorem spec_11 (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 12) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 4 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 10 ≤ n.val) (hn2 : n.val ≤ 12), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 4) := by
    sorry

  /-- The function returns r = 8.
    Preconditions: n is an integer satisfying 15 <= n <= 16. -/
  theorem spec_12 (n : Std.I64) (hn1 : 15 ≤ n.val) (hn2 : n.val ≤ 16) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 8 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 15 ≤ n.val) (hn2 : n.val ≤ 16), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 8) := by
    sorry

  /-- The function returns r = 254.
    Preconditions: n is an integer and n = 200. -/
  theorem spec_13 (n : Std.I64) (hn : n.val = 200) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 254 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 200), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 254) := by
    sorry

  /-- The function returns r = 330.
    Preconditions: n is an integer and n = 250. -/
  theorem spec_14 (n : Std.I64) (hn : n.val = 250) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 330 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 250), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 330) := by
    sorry

  /-- The function returns r = 12.
    Preconditions: n is an integer and n = 20. -/
  theorem spec_15 (n : Std.I64) (hn : n.val = 20) :
      ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 12 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 20), ∃ r : Std.I64, Aegis.CountTriples.count_triples n = ok r ∧ r.val = 12) := by
    sorry

  end AegisSpec.CountTriples
