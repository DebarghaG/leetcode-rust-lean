import Aegis.DistanceSum.Code.Funs

/-!
# Specifications of `Aegis.DistanceSum.distance_sum`

LeetCode problem `manhattan-distances-of-all-arrangements-of-pieces`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open scoped BigOperators

  namespace AegisSpec.DistanceSum

  def MOD : ℤ := 1000000007

  def iota (m : ℤ) : Finset ℤ := (Finset.range m.toNat).image (fun i : ℕ => (i : ℤ))

  def grid (m n : ℤ) : Finset (ℤ × ℤ) := iota m ×ˢ iota n

  def cellDist (p q : ℤ × ℤ) : ℤ := ((p.1 - q.1).natAbs : ℤ) + ((p.2 - q.2).natAbs : ℤ)

  def cellLt (p q : ℤ × ℤ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

  instance decCellLt : DecidableRel cellLt := fun p q => by unfold cellLt; infer_instance

  def pairDistSum (A : Finset (ℤ × ℤ)) : ℤ :=
    ∑ p ∈ A, ∑ q ∈ A, if cellLt p q then cellDist p q else 0

  def T (m n k : ℤ) : ℤ := ∑ A ∈ (grid m n).powersetCard k.toNat, pairDistSum A

  def S (m n : ℤ) : ℤ := pairDistSum (grid m n)

  def binomCoeff (a b : ℤ) : ℤ := (Nat.choose a.toNat b.toNat : ℤ)

  def closedFormPairSum (m n : ℤ) : ℤ :=
    n ^ 2 * (m ^ 3 - m) / 6 + m ^ 2 * (n ^ 3 - n) / 6

  /-- The function returns a result r such that 0 <= r < M and r ≡ T(m,n,k) (mod M), where T(m,n,k) is the sum over all k-element subsets A of the set of cells { (x,y) | 0 <= x < m, 0 <= y < n } of the sum over all unordered pairs {p,q} of distinct elements of A of (|p.x - q.x| + |p.y - q.y|).
    Preconditions: m, n, k are integers such that 1 <= m <= 100000, 1 <= n <= 100000, 2 <= m*n <= 100000, and 2 <= k <= m*n. Let M = 1000000007. -/
  theorem spec_1 (m n k : Std.I64)
      (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
      (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val) :
      ∃ r : Std.I64,
        Aegis.DistanceSum.distance_sum m n k = ok r ∧
          0 ≤ r.val ∧ r.val < MOD ∧ Int.ModEq MOD r.val (T m.val n.val k.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n k : Std.I64)
        (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
        (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
        (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
        (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val), ∃ r : Std.I64,
          Aegis.DistanceSum.distance_sum m n k = ok r ∧
            0 ≤ r.val ∧ r.val < MOD ∧ Int.ModEq MOD r.val (T m.val n.val k.val)) := by
    sorry

  /-- The function returns a result (i.e., it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: m, n, k are integers such that 1 <= m <= 100000, 1 <= n <= 100000, 2 <= m*n <= 100000, and 2 <= k <= m*n. -/
  theorem spec_2 (m n k : Std.I64)
      (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
      (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val) :
      ∃ r : Std.I64, Aegis.DistanceSum.distance_sum m n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n k : Std.I64)
        (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
        (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
        (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
        (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val), ∃ r : Std.I64, Aegis.DistanceSum.distance_sum m n k = ok r) := by
    sorry

  /-- For every valid (m,n,k), if r1 = distance_sum(m,n,k) and r2 = distance_sum(n,m,k), then r1 ≡ r2 (mod 1000000007).
    Preconditions: m, n, k are integers such that 1 <= m <= 100000, 1 <= n <= 100000, 2 <= m*n <= 100000, and 2 <= k <= m*n. -/
  theorem spec_3 (m n k : Std.I64)
      (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
      (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val) :
      ∀ r1 r2 : Std.I64,
        Aegis.DistanceSum.distance_sum m n k = ok r1 →
          Aegis.DistanceSum.distance_sum n m k = ok r2 → Int.ModEq MOD r1.val r2.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n k : Std.I64)
        (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
        (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
        (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
        (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val), ∀ r1 r2 : Std.I64,
          Aegis.DistanceSum.distance_sum m n k = ok r1 →
            Aegis.DistanceSum.distance_sum n m k = ok r2 → Int.ModEq MOD r1.val r2.val) := by
    sorry

  /-- Let N = m*n and let S(m,n) = sum over all unordered pairs of distinct cells {p,q} in { (x,y) | 0 <= x < m, 0 <= y < n } of (|p.x - q.x| + |p.y - q.y|). Then the returned r satisfies r ≡ C(N-2, k-2) * S(m,n) (mod 1000000007), where C(a,b) denotes the binomial coefficient (number of b-element subsets of an a-element set).
    Preconditions: m, n, k are integers such that 1 <= m <= 100000, 1 <= n <= 100000, 2 <= m*n <= 100000, and 2 <= k <= m*n. -/
  theorem spec_4 (m n k : Std.I64)
      (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
      (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val) :
      ∃ r : Std.I64,
        Aegis.DistanceSum.distance_sum m n k = ok r ∧
          Int.ModEq MOD r.val (binomCoeff (m.val * n.val - 2) (k.val - 2) * S m.val n.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n k : Std.I64)
        (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
        (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
        (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
        (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val), ∃ r : Std.I64,
          Aegis.DistanceSum.distance_sum m n k = ok r ∧
            Int.ModEq MOD r.val (binomCoeff (m.val * n.val - 2) (k.val - 2) * S m.val n.val)) := by
    sorry

  /-- The returned r satisfies r ≡ C(m*n - 2, k-2) * ( n^2 * (m^3 - m) / 6 + m^2 * (n^3 - n) / 6 ) (mod 1000000007), where the divisions are integer divisions (the numerators are always divisible by 6).
    Preconditions: m, n, k are integers such that 1 <= m <= 100000, 1 <= n <= 100000, 2 <= m*n <= 100000, and 2 <= k <= m*n. -/
  theorem spec_5 (m n k : Std.I64)
      (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
      (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
      (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
      (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val) :
      ∃ r : Std.I64,
        Aegis.DistanceSum.distance_sum m n k = ok r ∧
          Int.ModEq MOD r.val
            (binomCoeff (m.val * n.val - 2) (k.val - 2) * closedFormPairSum m.val n.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n k : Std.I64)
        (hm_lower : 1 ≤ m.val) (hm_upper : m.val ≤ 100000)
        (hn_lower : 1 ≤ n.val) (hn_upper : n.val ≤ 100000)
        (hmn_lower : 2 ≤ m.val * n.val) (hmn_upper : m.val * n.val ≤ 100000)
        (hk_lower : 2 ≤ k.val) (hk_upper : k.val ≤ m.val * n.val), ∃ r : Std.I64,
          Aegis.DistanceSum.distance_sum m n k = ok r ∧
            Int.ModEq MOD r.val
              (binomCoeff (m.val * n.val - 2) (k.val - 2) * closedFormPairSum m.val n.val)) := by
    sorry

  /-- The function returns r = 8.
    Preconditions: m = 2, n = 2, k = 2. -/
  theorem spec_6 : Aegis.DistanceSum.distance_sum 2#i64 2#i64 2#i64 = ok 8#i64 := by
    sorry

  theorem spec_6_neg :
      ¬ (Aegis.DistanceSum.distance_sum 2#i64 2#i64 2#i64 = ok 8#i64) := by
    sorry

  /-- The function returns r = 20.
    Preconditions: m = 1, n = 4, k = 3. -/
  theorem spec_7 : Aegis.DistanceSum.distance_sum 1#i64 4#i64 3#i64 = ok 20#i64 := by
    sorry

  theorem spec_7_neg :
      ¬ (Aegis.DistanceSum.distance_sum 1#i64 4#i64 3#i64 = ok 20#i64) := by
    sorry

  /-- The function returns r = 1771000.
    Preconditions: m = 5, n = 5, k = 5. -/
  theorem spec_8 : Aegis.DistanceSum.distance_sum 5#i64 5#i64 5#i64 = ok 1771000#i64 := by
    sorry

  theorem spec_8_neg :
      ¬ (Aegis.DistanceSum.distance_sum 5#i64 5#i64 5#i64 = ok 1771000#i64) := by
    sorry

  /-- The function returns r = 384963906.
    Preconditions: m = 100, n = 100, k = 10. -/
  theorem spec_9 : Aegis.DistanceSum.distance_sum 100#i64 100#i64 10#i64 = ok 384963906#i64 := by
    sorry

  theorem spec_9_neg :
      ¬ (Aegis.DistanceSum.distance_sum 100#i64 100#i64 10#i64 = ok 384963906#i64) := by
    sorry

  /-- The function returns r = 80781589.
    Preconditions: m = 10, n = 10, k = 20. -/
  theorem spec_10 : Aegis.DistanceSum.distance_sum 10#i64 10#i64 20#i64 = ok 80781589#i64 := by
    sorry

  theorem spec_10_neg :
      ¬ (Aegis.DistanceSum.distance_sum 10#i64 10#i64 20#i64 = ok 80781589#i64) := by
    sorry

  /-- The function returns r = 800580356.
    Preconditions: m = 10, n = 10, k = 10. -/
  theorem spec_11 : Aegis.DistanceSum.distance_sum 10#i64 10#i64 10#i64 = ok 800580356#i64 := by
    sorry

  theorem spec_11_neg :
      ¬ (Aegis.DistanceSum.distance_sum 10#i64 10#i64 10#i64 = ok 800580356#i64) := by
    sorry

  /-- The function returns r = 1.
    Preconditions: m = 1, n = 2, k = 2. -/
  theorem spec_12 : Aegis.DistanceSum.distance_sum 1#i64 2#i64 2#i64 = ok 1#i64 := by
    sorry

  theorem spec_12_neg :
      ¬ (Aegis.DistanceSum.distance_sum 1#i64 2#i64 2#i64 = ok 1#i64) := by
    sorry

  /-- The function returns r = 4.
    Preconditions: m = 1, n = 3, k = 2. -/
  theorem spec_13 : Aegis.DistanceSum.distance_sum 1#i64 3#i64 2#i64 = ok 4#i64 := by
    sorry

  theorem spec_13_neg :
      ¬ (Aegis.DistanceSum.distance_sum 1#i64 3#i64 2#i64 = ok 4#i64) := by
    sorry

  /-- The function returns r = 16.
    Preconditions: m = 2, n = 2, k = 3. -/
  theorem spec_14 : Aegis.DistanceSum.distance_sum 2#i64 2#i64 3#i64 = ok 16#i64 := by
    sorry

  theorem spec_14_neg :
      ¬ (Aegis.DistanceSum.distance_sum 2#i64 2#i64 3#i64 = ok 16#i64) := by
    sorry

  /-- The function returns r = 25.
    Preconditions: m = 2, n = 3, k = 2. -/
  theorem spec_15 : Aegis.DistanceSum.distance_sum 2#i64 3#i64 2#i64 = ok 25#i64 := by
    sorry

  theorem spec_15_neg :
      ¬ (Aegis.DistanceSum.distance_sum 2#i64 3#i64 2#i64 = ok 25#i64) := by
    sorry

  /-- The function returns r = 72.
    Preconditions: m = 3, n = 3, k = 2. -/
  theorem spec_16 : Aegis.DistanceSum.distance_sum 3#i64 3#i64 2#i64 = ok 72#i64 := by
    sorry

  theorem spec_16_neg :
      ¬ (Aegis.DistanceSum.distance_sum 3#i64 3#i64 2#i64 = ok 72#i64) := by
    sorry

  end AegisSpec.DistanceSum
