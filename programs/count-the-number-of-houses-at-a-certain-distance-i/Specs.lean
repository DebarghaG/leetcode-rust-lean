import Aegis.CountOfPairs.Code.Funs

/-!
# Specifications of `Aegis.CountOfPairs.count_of_pairs`

LeetCode problem `count-the-number-of-houses-at-a-certain-distance-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountOfPairs

  def Adj (n x y a b : ℕ) : Prop :=
    1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧
      (b = a + 1 ∨ a = b + 1 ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))

  def Walk (n x y : ℕ) : ℕ → ℕ → ℕ → Prop
    | 0, a, b => a = b ∧ 1 ≤ a ∧ a ≤ n
    | k + 1, a, b => ∃ c : ℕ, Walk n x y k a c ∧ Adj n x y c b

  noncomputable def dist (n x y a b : ℕ) : ℕ := sInf {k : ℕ | Walk n x y k a b}

  noncomputable def pairCount (n x y : ℕ) (d : ℕ) : ℕ := by
    classical
    exact (((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter
      (fun p : ℕ × ℕ => dist n x y p.1 p.2 = d)).card

  noncomputable def maxDist (n x y : ℕ) : ℕ :=
    ((Finset.Icc 1 n).product (Finset.Icc 1 n)).sup (fun p : ℕ × ℕ => dist n x y p.1 p.2)

  def vecGet (v : alloc.vec.Vec I64) (i : ℕ) : Option ℤ := (v.val[i]?).map (fun a => a.val)

  def chord (x y : ℤ) : ℤ := if x ≠ y ∧ x - y ≠ 1 ∧ y - x ≠ 1 then 1 else 0

  def nearEdge (x y : ℤ) : ℤ := if x = y ∨ x - y = 1 ∨ y - x = 1 then 2 else 0

  def i64OfInt (v : ℤ) : I64 := IScalar.mk (BitVec.ofInt 64 v)

  /-- The function returns a result vector r and does not fail. Let G be the undirected graph on vertices {1,...,n} whose edges are {i,i+1} for every 1 <= i < n, together with the extra edge joining x and y (if x = y this is a self-loop and does not affect distances). For vertices a,b let dist(a,b) be the minimum number of edges on a path from a to b in G. Then len(r) = n, and for every i with 0 <= i < n, r[i] is the number of ordered pairs (a,b) such that 1 <= a <= n, 1 <= b <= n, and dist(a,b) = i+1.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_1 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        (r.val.length : ℤ) = n.val ∧
        ∀ i : ℕ, i < n.val.toNat →
          vecGet r i = some ↑(pairCount n.val.toNat x.val.toNat y.val.toNat (i + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          (r.val.length : ℤ) = n.val ∧
          ∀ i : ℕ, i < n.val.toNat →
            vecGet r i = some ↑(pairCount n.val.toNat x.val.toNat y.val.toNat (i + 1))) := by
    sorry

  /-- The function returns a result r with len(r) = n.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_2 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        (r.val.length : ℤ) = n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          (r.val.length : ℤ) = n.val) := by
    sorry

  /-- The function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_3 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < n, 0 <= r[i] <= n * (n - 1).
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_4 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        ∀ i : ℕ, i < n.val.toNat →
          ∃ v : ℤ, vecGet r i = some v ∧ 0 ≤ v ∧ v ≤ n.val * (n.val - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          ∀ i : ℕ, i < n.val.toNat →
            ∃ v : ℤ, vecGet r i = some v ∧ 0 ≤ v ∧ v ≤ n.val * (n.val - 1)) := by
    sorry

  /-- The function returns a result r and sum_{i=0}^{n-1} r[i] = n * (n - 1).
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_5 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧

        (r.val.length : ℤ) = n.val ∧
        Finset.sum (Finset.range n.val.toNat) (fun i => (vecGet r i).getD 0) =
          n.val * (n.val - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧

          (r.val.length : ℤ) = n.val ∧
          Finset.sum (Finset.range n.val.toNat) (fun i => (vecGet r i).getD 0) =
            n.val * (n.val - 1)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < n, r[i] is even.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_6 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        ∀ i : ℕ, i < n.val.toNat → ∃ k : ℤ, vecGet r i = some (2 * k) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          ∀ i : ℕ, i < n.val.toNat → ∃ k : ℤ, vecGet r i = some (2 * k)) := by
    sorry

  /-- The function returns a result r and r[n-1] = 0.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_7 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        vecGet r (n.val.toNat - 1) = some 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          vecGet r (n.val.toNat - 1) = some 0) := by
    sorry

  /-- The function returns a result r and r[0] = 2 * ((n - 1) + c), where c = 1 if x != y and |x-y| != 1, and c = 0 otherwise.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_8 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        vecGet r 0 = some (2 * ((n.val - 1) + chord x.val y.val)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          vecGet r 0 = some (2 * ((n.val - 1) + chord x.val y.val))) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < n, r[i] = 2 * (n - 1 - i).
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, 1 <= y <= n, and either x = y or |x-y| = 1. -/
  theorem spec_9 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val)
      (hxy : x.val = y.val ∨ x.val - y.val = 1 ∨ y.val - x.val = 1) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        ∀ i : ℕ, i < n.val.toNat →
          vecGet r i = some (2 * (n.val - 1 - (i : ℤ))) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val)
        (hxy : x.val = y.val ∨ x.val - y.val = 1 ∨ y.val - x.val = 1), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          ∀ i : ℕ, i < n.val.toNat →
            vecGet r i = some (2 * (n.val - 1 - (i : ℤ)))) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < n, letting k = i+1, we have r[i] = 2*n if 2*k < n, r[i] = n if 2*k = n, and r[i] = 0 if 2*k > n.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, 1 <= y <= n, and either (x = 1 and y = n) or (x = n and y = 1). -/
  theorem spec_10 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val)
      (hxy : (x.val = 1 ∧ y.val = n.val) ∨ (x.val = n.val ∧ y.val = 1)) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        ∀ i : ℕ, i < n.val.toNat →
          vecGet r i = some (if 2 * ((i : ℤ) + 1) < n.val then 2 * n.val
                            else if 2 * ((i : ℤ) + 1) = n.val then n.val else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val)
        (hxy : (x.val = 1 ∧ y.val = n.val) ∨ (x.val = n.val ∧ y.val = 1)), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          ∀ i : ℕ, i < n.val.toNat →
            vecGet r i = some (if 2 * ((i : ℤ) + 1) < n.val then 2 * n.val
                              else if 2 * ((i : ℤ) + 1) = n.val then n.val else 0)) := by
    sorry

  /-- The function returns a result r. Let D be the maximum of dist(a,b) over all 1 <= a <= n and 1 <= b <= n, where dist is the graph distance from spec_1. Then for every i with 0 <= i < n, r[i] > 0 if and only if i+1 <= D.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_11 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        (r.val.length : ℤ) = n.val ∧
        ∀ i : ℕ, i < n.val.toNat →
          ((∃ v : ℤ, vecGet r i = some v ∧ 0 < v) ↔
            i + 1 ≤ maxDist n.val.toNat x.val.toNat y.val.toNat) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          (r.val.length : ℤ) = n.val ∧
          ∀ i : ℕ, i < n.val.toNat →
            ((∃ v : ℤ, vecGet r i = some v ∧ 0 < v) ↔
              i + 1 ≤ maxDist n.val.toNat x.val.toNat y.val.toNat)) := by
    sorry

  /-- Let r be the result returned for (n,x,y) and let r' be the result returned for (n,y,x). Then len(r) = len(r') = n and, for every i with 0 <= i < n, r[i] = r'[i].
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_12 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r r' : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        Aegis.CountOfPairs.count_of_pairs n y x = ok r' ∧
        (r.val.length : ℤ) = n.val ∧
        (r'.val.length : ℤ) = n.val ∧
        ∀ i : ℕ, i < n.val.toNat → vecGet r i = vecGet r' i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r r' : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          Aegis.CountOfPairs.count_of_pairs n y x = ok r' ∧
          (r.val.length : ℤ) = n.val ∧
          (r'.val.length : ℤ) = n.val ∧
          ∀ i : ℕ, i < n.val.toNat → vecGet r i = vecGet r' i) := by
    sorry

  /-- Let r be the result returned for (n,x,y) and let r' be the result returned for (n, n+1-x, n+1-y). Then len(r) = len(r') = n and, for every i with 0 <= i < n, r[i] = r'[i].
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_13 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r r' : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        Aegis.CountOfPairs.count_of_pairs n (i64OfInt (n.val + 1 - x.val))
          (i64OfInt (n.val + 1 - y.val)) = ok r' ∧
        (r.val.length : ℤ) = n.val ∧
        (r'.val.length : ℤ) = n.val ∧
        ∀ i : ℕ, i < n.val.toNat → vecGet r i = vecGet r' i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r r' : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          Aegis.CountOfPairs.count_of_pairs n (i64OfInt (n.val + 1 - x.val))
            (i64OfInt (n.val + 1 - y.val)) = ok r' ∧
          (r.val.length : ℤ) = n.val ∧
          (r'.val.length : ℤ) = n.val ∧
          ∀ i : ℕ, i < n.val.toNat → vecGet r i = vecGet r' i) := by
    sorry

  /-- The function returns a result r and r[n-2] = 2 if x = y or |x-y| = 1, and r[n-2] = 0 otherwise.
    Preconditions: n, x, and y are integers with 2 <= n <= 100, 1 <= x <= n, and 1 <= y <= n. -/
  theorem spec_14 (n x y : I64)
      (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
      (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
      (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
        vecGet r (n.val.toNat - 2) = some (nearEdge x.val y.val) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n x y : I64)
        (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 100)
        (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ n.val)
        (hy1 : 1 ≤ y.val) (hy2 : y.val ≤ n.val), ∃ r : alloc.vec.Vec I64,
          Aegis.CountOfPairs.count_of_pairs n x y = ok r ∧
          vecGet r (n.val.toNat - 2) = some (nearEdge x.val y.val)) := by
    sorry

  end AegisSpec.CountOfPairs
