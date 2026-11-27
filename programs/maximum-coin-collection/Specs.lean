import Aegis.MaxCoins.Code.Funs

/-!
# Specifications of `Aegis.MaxCoins.max_coins`

LeetCode problem `maximum-coin-collection`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxCoins

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def valAt (s : Slice Std.I64) (i : ℕ) : ℤ := (vals s).getD i 0

def maxOf (s : Finset ℤ) : ℤ := if h : s.Nonempty then s.max' h else 0

def maxEntry (xs : List ℤ) : ℤ := maxOf xs.toFinset

abbrev Lane (n : ℕ) := Fin n → Bool

def Lane.toFun {n : ℕ} (a : Lane n) : ℕ → Bool :=
  fun i => if h : i < n then a ⟨i, h⟩ else false

def switches {n : ℕ} (a : Lane n) (l r : ℕ) : ℕ :=
  (if a.toFun l then 1 else 0) +
    ((Finset.Ico l r).filter (fun i => a.toFun i ≠ a.toFun (i + 1))).card

def collection (xs ys : List ℤ) {n : ℕ} (a : Lane n) (l r : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ico l (r + 1), (if a.toFun i then ys.getD i 0 else xs.getD i 0)

def Admissible {n : ℕ} (a : Lane n) (l r : ℕ) : Prop :=
  l ≤ r ∧ r < n ∧ switches a l r ≤ 2

def itineraryCollections (xs ys : List ℤ) : Finset ℤ :=
  (((Finset.range xs.length).product (Finset.range xs.length)).product Finset.univ
    |>.filter (fun p : (ℕ × ℕ) × Lane xs.length =>
        p.1.1 ≤ p.1.2 ∧ switches p.2 p.1.1 p.1.2 ≤ 2)
    |>.image (fun p : (ℕ × ℕ) × Lane xs.length =>
        collection xs ys p.2 p.1.1 p.1.2))

def maxCollection (xs ys : List ℤ) : ℤ := maxOf (itineraryCollections xs ys)

def fullCollection (xs ys : List ℤ) (a : Lane xs.length) : ℤ :=
  collection xs ys a 0 (xs.length - 1)

def fullCollections (xs ys : List ℤ) : Finset ℤ :=
  (Finset.univ.filter (fun a : Lane xs.length => switches a 0 (xs.length - 1) ≤ 2)
    |>.image (fun a => fullCollection xs ys a))

def maxFullCollection (xs ys : List ℤ) : ℤ := maxOf (fullCollections xs ys)

def subarraySums (xs : List ℤ) : Finset ℤ :=
  ((Finset.range xs.length).product (Finset.range xs.length)
      |>.filter (fun p : ℕ × ℕ => p.1 ≤ p.2)
      |>.image (fun p : ℕ × ℕ => ∑ i ∈ Finset.Ico p.1 (p.2 + 1), xs.getD i 0))

def MSS (xs : List ℤ) : ℤ := maxOf (subarraySums xs)

def laneMax (xs ys : List ℤ) : List ℤ := xs.zipWith max ys

/-- The function returns a result r, and r equals the maximum collection over all admissible itineraries. An admissible itinerary consists of an interval [l,r] with 0 <= l <= r < n and a lane choice a(i) in {1,2} for each i in [l,r], whose switch count is at most 2. The switch count is (1 if a(l)=2 else 0) plus the number of indices i with l <= i < r and a(i) != a(i+1). The collection is the sum over i from l to r of lane1[i] if a(i)=1, and lane2[i] if a(i)=2. The maximum is over all such intervals and lane choices.
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_1 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxCollection (vals lane1) (vals lane2) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxCollection (vals lane1) (vals lane2)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic) on any input satisfying the preconditions.
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_2 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.MaxCoins.max_coins lane1 lane2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64, Aegis.MaxCoins.max_coins lane1 lane2 = ok r) := by
  sorry

/-- Let M be the length-n array with M[i] = max(lane1[i], lane2[i]) for 0 <= i < n, and let MSS(M) = max_{0 <= l <= r < n} sum_{i=l}^r M[i]. The function returns a result r and r <= MSS(M).
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_3 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val ≤ MSS (laneMax (vals lane1) (vals lane2)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val ≤ MSS (laneMax (vals lane1) (vals lane2))) := by
  sorry

/-- The function returns a result r and r >= MSS(lane1), where MSS(xs) = max_{0 <= l <= r < len(xs)} sum_{i=l}^r xs[i].
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_4 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ MSS (vals lane1) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ MSS (vals lane1) ≤ r.val) := by
  sorry

/-- The function returns a result r and r >= MSS(lane2), where MSS(xs) = max_{0 <= l <= r < len(xs)} sum_{i=l}^r xs[i].
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_5 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ MSS (vals lane2) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ MSS (vals lane2) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = max(lane1[0], lane2[0]).
  Preconditions: len(lane1) = len(lane2) = n, n = 1, and -1000000000 <= lane1[0] <= 1000000000 and -1000000000 <= lane2[0] <= 1000000000. -/
theorem spec_6 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : n = 1)
    (hb1 : -1000000000 ≤ valAt lane1 0 ∧ valAt lane1 0 ≤ 1000000000)
    (hb2 : -1000000000 ≤ valAt lane2 0 ∧ valAt lane2 0 ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = max (valAt lane1 0) (valAt lane2 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : n = 1)
    (hb1 : -1000000000 ≤ valAt lane1 0 ∧ valAt lane1 0 ≤ 1000000000)
    (hb2 : -1000000000 ≤ valAt lane2 0 ∧ valAt lane2 0 ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = max (valAt lane1 0) (valAt lane2 0)) := by
  sorry

/-- The function returns a result r and r = max_{0 <= i < n} max(lane1[i], lane2[i]).
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 0 and -1000000000 <= lane2[i] <= 0. All indices are 0-based. -/
theorem spec_7 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 0)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 0) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxEntry (laneMax (vals lane1) (vals lane2)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 0)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 0), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxEntry (laneMax (vals lane1) (vals lane2))) := by
  sorry

/-- The function returns a result r and r equals the maximum collection over all lane choices a: {0,...,n-1} -> {1,2} whose switch count (1 if a(0)=2 else 0) plus the number of i with 0 <= i < n-1 and a(i) != a(i+1) is at most 2, where the collection is sum_{i=0}^{n-1} (lane1[i] if a(i)=1 else lane2[i]). Equivalently, some optimal itinerary covers every mile from 0 through n-1.
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= lane1[i] <= 1000000000 and 0 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_8 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → 0 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → 0 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxFullCollection (vals lane1) (vals lane2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → 0 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → 0 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        r.val = maxFullCollection (vals lane1) (vals lane2)) := by
  sorry

/-- The function returns a result r and r = MSS(lane1), where MSS(xs) = max_{0 <= l <= r < len(xs)} sum_{i=l}^r xs[i].
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000, and for every i with 0 <= i < n, lane1[i] >= lane2[i]. All indices are 0-based. -/
theorem spec_9 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (hle : ∀ i, i < n → valAt lane2 i ≤ valAt lane1 i) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ r.val = MSS (vals lane1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (hle : ∀ i, i < n → valAt lane2 i ≤ valAt lane1 i), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ r.val = MSS (vals lane1)) := by
  sorry

/-- The function returns a result r and r = MSS(lane2), where MSS(xs) = max_{0 <= l <= r < len(xs)} sum_{i=l}^r xs[i].
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000, and for every i with 0 <= i < n, lane2[i] >= lane1[i]. All indices are 0-based. -/
theorem spec_10 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (hle : ∀ i, i < n → valAt lane1 i ≤ valAt lane2 i) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ r.val = MSS (vals lane2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (hle : ∀ i, i < n → valAt lane1 i ≤ valAt lane2 i), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧ r.val = MSS (vals lane2)) := by
  sorry

/-- The function returns a result r, and there exists an admissible itinerary whose collection equals r. Here an admissible itinerary means an interval [l,r] with 0 <= l <= r < n and a lane choice a(i) in {1,2} for each i in [l,r], whose switch count (1 if a(l)=2 else 0) plus the number of i with l <= i < r and a(i) != a(i+1) is at most 2; its collection is sum_{i=l}^r (lane1[i] if a(i)=1 else lane2[i]).
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_11 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        ∃ (l r' : ℕ) (a : Lane (vals lane1).length),
          Admissible a l r' ∧ collection (vals lane1) (vals lane2) a l r' = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000), ∃ r : Std.I64,
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        ∃ (l r' : ℕ) (a : Lane (vals lane1).length),
          Admissible a l r' ∧ collection (vals lane1) (vals lane2) a l r' = r.val) := by
  sorry

/-- For every index i with 0 <= i < n and every length-n array lane1' such that lane1'[j] = lane1[j] for all j != i and lane1[i] <= lane1'[i] <= 1000000000, the function returns a result r for (lane1,lane2), returns a result r' for (lane1',lane2), and r' >= r.
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_12 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (i : ℕ) (hi : i < n) (lane1' : Slice Std.I64)
    (h1' : lane1'.val.length = n)
    (hsame : ∀ j, j < n → j ≠ i → valAt lane1' j = valAt lane1 j)
    (hmono : valAt lane1 i ≤ valAt lane1' i)
    (hup : valAt lane1' i ≤ 1000000000) :
    ∃ (r r' : Std.I64),
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        Aegis.MaxCoins.max_coins lane1' lane2 = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (i : ℕ) (hi : i < n) (lane1' : Slice Std.I64)
    (h1' : lane1'.val.length = n)
    (hsame : ∀ j, j < n → j ≠ i → valAt lane1' j = valAt lane1 j)
    (hmono : valAt lane1 i ≤ valAt lane1' i)
    (hup : valAt lane1' i ≤ 1000000000), ∃ (r r' : Std.I64),
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        Aegis.MaxCoins.max_coins lane1' lane2 = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- For every index i with 0 <= i < n and every length-n array lane2' such that lane2'[j] = lane2[j] for all j != i and lane2[i] <= lane2'[i] <= 1000000000, the function returns a result r for (lane1,lane2), returns a result r' for (lane1,lane2'), and r' >= r.
  Preconditions: len(lane1) = len(lane2) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, -1000000000 <= lane1[i] <= 1000000000 and -1000000000 <= lane2[i] <= 1000000000. All indices are 0-based. -/
theorem spec_13 (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (i : ℕ) (hi : i < n) (lane2' : Slice Std.I64)
    (h2' : lane2'.val.length = n)
    (hsame : ∀ j, j < n → j ≠ i → valAt lane2' j = valAt lane2 j)
    (hmono : valAt lane2 i ≤ valAt lane2' i)
    (hup : valAt lane2' i ≤ 1000000000) :
    ∃ (r r' : Std.I64),
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        Aegis.MaxCoins.max_coins lane1 lane2' = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (lane1 lane2 : Slice Std.I64) (n : ℕ)
    (h1 : lane1.val.length = n) (h2 : lane2.val.length = n)
    (hn : 1 ≤ n) (hn' : n ≤ 100000)
    (hb1 : ∀ i, i < n → -1000000000 ≤ valAt lane1 i ∧ valAt lane1 i ≤ 1000000000)
    (hb2 : ∀ i, i < n → -1000000000 ≤ valAt lane2 i ∧ valAt lane2 i ≤ 1000000000)
    (i : ℕ) (hi : i < n) (lane2' : Slice Std.I64)
    (h2' : lane2'.val.length = n)
    (hsame : ∀ j, j < n → j ≠ i → valAt lane2' j = valAt lane2 j)
    (hmono : valAt lane2 i ≤ valAt lane2' i)
    (hup : valAt lane2' i ≤ 1000000000), ∃ (r r' : Std.I64),
      Aegis.MaxCoins.max_coins lane1 lane2 = ok r ∧
        Aegis.MaxCoins.max_coins lane1 lane2' = ok r' ∧ r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxCoins
