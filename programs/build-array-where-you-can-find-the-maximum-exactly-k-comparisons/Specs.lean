import Aegis.NumOfArrays.Code.Funs

/-!
# Specifications of `Aegis.NumOfArrays.num_of_arrays`

LeetCode problem `build-array-where-you-can-find-the-maximum-exactly-k-comparisons`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open scoped BigOperators

  namespace AegisSpec.NumOfArrays

  def IsRecordIndex {n m : ℕ} (f : Fin n → Fin m) (i : Fin n) : Prop :=
    ∀ j : Fin n, j < i → f j < f i

  noncomputable def numRecordIndices {n m : ℕ} (f : Fin n → Fin m) : ℕ := by
    classical exact (Finset.univ.filter (fun i : Fin n => IsRecordIndex f i)).card

  noncomputable def countArrays (n m k : ℕ) : ℕ := by
    classical exact (Finset.univ.filter (fun f : Fin n → Fin m => numRecordIndices f = k)).card

  def i64OfNat (j : ℕ) : Std.I64 := ⟨BitVec.ofNat 64 j⟩

  /-- The function returns a result r such that 0 <= r < 1000000007 and r is the least nonnegative residue modulo 1000000007 of the number of ordered arrays arr of length n with every entry in {1,2,...,m} for which the number of record indices i is exactly k, where an index i is a record index iff 0 <= i < n and arr[i] > arr[j] for every j with 0 <= j < i.
    Preconditions: n, m, k are integers satisfying 1 <= n <= 50, 1 <= m <= 100, and 0 <= k <= n. -/
  theorem spec_1 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = ((countArrays n.val.toNat m.val.toNat k.val.toNat : ℕ) : ℤ) % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val = ((countArrays n.val.toNat m.val.toNat k.val.toNat : ℕ) : ℤ) % 1000000007) := by
    sorry

  /-- For every n, m, k satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
    Preconditions: n, m, k satisfy 1 <= n <= 50, 1 <= m <= 100, and 0 <= k <= n. -/
  theorem spec_2 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val) :
      ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m k = ok r) := by
    sorry

  /-- Whenever the function returns a result r for inputs satisfying the preconditions, the integer r satisfies 0 <= r < 1000000007.
    Preconditions: n, m, k satisfy 1 <= n <= 50, 1 <= m <= 100, and 0 <= k <= n. -/
  theorem spec_3 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val) :
      ∀ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r → 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val), ∀ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r → 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- The function returns a result r with r = 0.
    Preconditions: 1 <= n <= 50, 1 <= m <= 100, and k = 0. -/
  theorem spec_4 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk : k.val = 0) :
      ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk : k.val = 0), ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r with r = 1 if k = 1, and r = 0 otherwise, i.e. for k = 0 or k >= 2.
    Preconditions: 1 <= n <= 50, m = 1, and 0 <= k <= n. -/
  theorem spec_5 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm : m.val = 1)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val = if k.val = 1 then 1 else 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm : m.val = 1)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val = if k.val = 1 then 1 else 0) := by
    sorry

  /-- The function returns a result r with r = m if k = 1, and r = 0 if k = 0.
    Preconditions: n = 1, 1 <= m <= 100, and 0 <= k <= 1. -/
  theorem spec_6 (n m k : Std.I64)
      (hn : n.val = 1)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 1) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val = if k.val = 1 then m.val else 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn : n.val = 1)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 1), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val = if k.val = 1 then m.val else 0) := by
    sorry

  /-- The function returns a result r that is the least nonnegative residue modulo 1000000007 of the sum from a = 1 to m of a^(n-1).
    Preconditions: 1 <= n <= 50, 1 <= m <= 100, and k = 1. -/
  theorem spec_7 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk : k.val = 1) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val =
            (∑ a ∈ Finset.Icc 1 m.val.toNat, (a : ℤ) ^ (n.val.toNat - 1)) % 1000000007 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk : k.val = 1), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val =
              (∑ a ∈ Finset.Icc 1 m.val.toNat, (a : ℤ) ^ (n.val.toNat - 1)) % 1000000007) := by
    sorry

  /-- The function returns a result r such that r is the least nonnegative residue modulo 1000000007 of binomial(m,n) when m >= n, and r = 0 when m < n.
    Preconditions: 1 <= n <= 50, 1 <= m <= 100, and k = n. -/
  theorem spec_8 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk : k.val = n.val) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val =
            (if n.val ≤ m.val
             then ((m.val.toNat.choose n.val.toNat : ℕ) : ℤ) % 1000000007
             else 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk : k.val = n.val), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val =
              (if n.val ≤ m.val
               then ((m.val.toNat.choose n.val.toNat : ℕ) : ℤ) % 1000000007
               else 0)) := by
    sorry

  /-- For every integer j with 0 <= j <= n, let r_j be the result returned by the function on inputs (n, m, j). Each such call returns a result, and the congruence sum from j = 0 to n of r_j ≡ m^n (mod 1000000007) holds.
    Preconditions: 1 <= n <= 50 and 1 <= m <= 100. -/
  theorem spec_9 (n m : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100) :
      (∀ j : ℕ, j ≤ n.val.toNat →
          ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m (i64OfNat j) = ok r) ∧
        (∀ r : ℕ → Std.I64,
          (∀ j : ℕ, j ≤ n.val.toNat →
              Aegis.NumOfArrays.num_of_arrays n m (i64OfNat j) = ok (r j)) →
            (∑ j ∈ Finset.range (n.val.toNat + 1), (r j).val) % 1000000007
              = (m.val ^ n.val.toNat) % 1000000007) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n m : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100), (∀ j : ℕ, j ≤ n.val.toNat →
            ∃ r : Std.I64, Aegis.NumOfArrays.num_of_arrays n m (i64OfNat j) = ok r) ∧
          (∀ r : ℕ → Std.I64,
            (∀ j : ℕ, j ≤ n.val.toNat →
                Aegis.NumOfArrays.num_of_arrays n m (i64OfNat j) = ok (r j)) →
              (∑ j ∈ Finset.range (n.val.toNat + 1), (r j).val) % 1000000007
                = (m.val ^ n.val.toNat) % 1000000007)) := by
    sorry

  /-- The function returns a result r with the following values: r = 0 if k = 0; r is the least nonnegative residue modulo 1000000007 of m(m+1)/2 if k = 1; and r is the least nonnegative residue modulo 1000000007 of m(m-1)/2 if k = 2.
    Preconditions: n = 2, 1 <= m <= 100, and 0 <= k <= 2. -/
  theorem spec_10 (n m k : Std.I64)
      (hn : n.val = 2)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 2) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val =
            (if k.val = 0 then 0
             else if k.val = 1 then
               (((m.val.toNat * (m.val.toNat + 1)) / 2 : ℕ) : ℤ) % 1000000007
             else (((m.val.toNat * (m.val.toNat - 1)) / 2 : ℕ) : ℤ) % 1000000007) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn : n.val = 2)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ 2), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val =
              (if k.val = 0 then 0
               else if k.val = 1 then
                 (((m.val.toNat * (m.val.toNat + 1)) / 2 : ℕ) : ℤ) % 1000000007
               else (((m.val.toNat * (m.val.toNat - 1)) / 2 : ℕ) : ℤ) % 1000000007)) := by
    sorry

  /-- The function returns a result r such that: r = 0 if k = 0 or k >= 3; r is the least nonnegative residue modulo 1000000007 of 1 + 2^(n-1) if k = 1; and r is the least nonnegative residue modulo 1000000007 of 2^(n-1) - 1 if k = 2.
    Preconditions: 1 <= n <= 50, m = 2, and 0 <= k <= n. -/
  theorem spec_11 (n m k : Std.I64)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
      (hm : m.val = 2)
      (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val) :
      ∃ r : Std.I64,
        Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
          r.val =
            (if k.val = 0 then 0
             else if k.val = 1 then (1 + 2 ^ (n.val.toNat - 1)) % 1000000007
             else if k.val = 2 then (2 ^ (n.val.toNat - 1) - 1) % 1000000007
             else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n m k : Std.I64)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 50)
        (hm : m.val = 2)
        (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ n.val), ∃ r : Std.I64,
          Aegis.NumOfArrays.num_of_arrays n m k = ok r ∧
            r.val =
              (if k.val = 0 then 0
               else if k.val = 1 then (1 + 2 ^ (n.val.toNat - 1)) % 1000000007
               else if k.val = 2 then (2 ^ (n.val.toNat - 1) - 1) % 1000000007
               else 0)) := by
    sorry

  end AegisSpec.NumOfArrays
