import Aegis.DistributeCandies.Code.Funs

/-!
# Specifications of `Aegis.DistributeCandies.distribute_candies`

LeetCode problem `distribute-candies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.DistributeCandies

def numDistinct (s : Slice Std.I64) : ℕ :=
  (s.val.map (fun x => x.val)).toFinset.card

def Occurs (v : ℤ) (s : Slice Std.I64) : Prop :=
  v ∈ s.val.map (fun x => x.val)

def valuesAt (s : Slice Std.I64) (I : Finset (Fin s.val.length)) : Finset ℤ :=
  I.image fun i => (s.val.get i).val

/-- Let D be the cardinality of the set {candyType[i] | 0 <= i < n}. The function returns a result r and r = min(D, n/2).
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_1
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r ∧
        r.val = ((min (numDistinct candyType) (n / 2) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∃ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r ∧
        r.val = ((min (numDistinct candyType) (n / 2) : ℕ) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access an out-of-bounds index.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_2
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∃ r : Std.I64, Aegis.DistributeCandies.distribute_candies candyType = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∃ r : Std.I64, Aegis.DistributeCandies.distribute_candies candyType = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n/2.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_3
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val ≤ ((n / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val ≤ ((n / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_4
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r → 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r → 1 ≤ r.val) := by
  sorry

/-- Let D be the cardinality of the set {candyType[i] | 0 <= i < n}. Whenever the function returns a result r, r <= D.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_5
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val ≤ ((numDistinct candyType : ℕ) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val ≤ ((numDistinct candyType : ℕ) : ℤ)) := by
  sorry

/-- Let D be the cardinality of the set {candyType[i] | 0 <= i < n}. If D <= n/2, then whenever the function returns a result r, r = D.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_6
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (hD : numDistinct candyType ≤ n / 2) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val = ((numDistinct candyType : ℕ) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (hD : numDistinct candyType ≤ n / 2), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val = ((numDistinct candyType : ℕ) : ℤ)) := by
  sorry

/-- Let D be the cardinality of the set {candyType[i] | 0 <= i < n}. If D >= n/2, then whenever the function returns a result r, r = n/2.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_7
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (hD : n / 2 ≤ numDistinct candyType) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val = ((n / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (hD : n / 2 ≤ numDistinct candyType), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        r.val = ((n / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exist pairwise distinct indices i_0, ..., i_{n/2-1} with 0 <= i_j < n for every j with 0 <= j < n/2 such that the set {candyType[i_j] | 0 <= j < n/2} has cardinality r.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_8
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        ∃ idx : Fin (n / 2) → Fin candyType.val.length,
          Function.Injective idx ∧
            ((valuesAt candyType (Finset.univ.image idx)).card : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        ∃ idx : Fin (n / 2) → Fin candyType.val.length,
          Function.Injective idx ∧
            ((valuesAt candyType (Finset.univ.image idx)).card : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every set S of pairwise distinct indices with S subset of {0, ..., n-1} and |S| = n/2, the set {candyType[i] | i in S} has cardinality at most r.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_9
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000) :
    ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        ∀ S : Finset (Fin candyType.val.length), S.card = n / 2 →
          ((valuesAt candyType S).card : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000), ∀ r : Std.I64,
      Aegis.DistributeCandies.distribute_candies candyType = ok r →
        ∀ S : Finset (Fin candyType.val.length), S.card = n / 2 →
          ((valuesAt candyType S).card : ℤ) ≤ r.val) := by
  sorry

/-- For any slice b with len(b) = n, if there is a bijection p on {0, ..., n-1} such that b[i] = candyType[p(i)] for every i with 0 <= i < n, and if distribute_candies candyType returns r and distribute_candies b returns r_b, then r_b = r.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_10
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (b : Slice Std.I64) (hb : b.val.length = n)
    (p : Equiv.Perm (Fin n))
    (hp : ∀ i : Fin n,
      b.val.get ⟨i.val, by omega⟩ = candyType.val.get ⟨(p i).val, by omega⟩)
    (r : Std.I64) (hr : Aegis.DistributeCandies.distribute_candies candyType = ok r)
    (rb : Std.I64) (hrb : Aegis.DistributeCandies.distribute_candies b = ok rb) :
    rb = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (b : Slice Std.I64) (hb : b.val.length = n)
    (p : Equiv.Perm (Fin n))
    (hp : ∀ i : Fin n,
      b.val.get ⟨i.val, by omega⟩ = candyType.val.get ⟨(p i).val, by omega⟩)
    (r : Std.I64) (hr : Aegis.DistributeCandies.distribute_candies candyType = ok r)
    (rb : Std.I64) (hrb : Aegis.DistributeCandies.distribute_candies b = ok rb), rb = r) := by
  sorry

/-- Let D be the cardinality of the set {candyType[i] | 0 <= i < n}. For any slice b with len(b) = n and entries in [-100000, 100000], if the number of distinct values occurring in b is at least D, and if distribute_candies candyType returns r and distribute_candies b returns r_b, then r_b >= r.
  Preconditions: n = len(candyType); 2 <= n <= 10000; n is even; for every i with 0 <= i < n, -100000 <= candyType[i] <= 100000. -/
theorem spec_11
    (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (b : Slice Std.I64) (hb : b.val.length = n)
    (hbounds_b : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (b.val[i]'(by omega)).val ∧ (b.val[i]'(by omega)).val ≤ 100000)
    (hD : numDistinct candyType ≤ numDistinct b)
    (r : Std.I64) (hr : Aegis.DistributeCandies.distribute_candies candyType = ok r)
    (rb : Std.I64) (hrb : Aegis.DistributeCandies.distribute_candies b = ok rb) :
    r.val ≤ rb.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (candyType : Slice Std.I64) (n : ℕ) (hn : n = candyType.val.length)
    (hn2 : 2 ≤ n) (hn10000 : n ≤ 10000) (heven : n % 2 = 0)
    (hbounds : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (candyType.val[i]'(by omega)).val ∧
        (candyType.val[i]'(by omega)).val ≤ 100000)
    (b : Slice Std.I64) (hb : b.val.length = n)
    (hbounds_b : ∀ (i : ℕ) (hi : i < n),
      -100000 ≤ (b.val[i]'(by omega)).val ∧ (b.val[i]'(by omega)).val ≤ 100000)
    (hD : numDistinct candyType ≤ numDistinct b)
    (r : Std.I64) (hr : Aegis.DistributeCandies.distribute_candies candyType = ok r)
    (rb : Std.I64) (hrb : Aegis.DistributeCandies.distribute_candies b = ok rb), r.val ≤ rb.val) := by
  sorry

end AegisSpec.DistributeCandies
