import Aegis.MinimumRelativeLosses.Code.Funs

/-!
# Specifications of `Aegis.MinimumRelativeLosses.minimum_relative_losses`

LeetCode problem `minimum-relative-loss-after-buying-chocolates`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumRelativeLosses

namespace AegisSpec.MinimumRelativeLosses

def relLoss (k p : ℤ) : ℤ :=
  if p ≤ k then p else 2 * k - p

def priceList (prices : Slice I64) : List ℤ := prices.val.map (fun x => x.val)

def resList (r : alloc.vec.Vec I64) : List ℤ := r.val.map (fun x => x.val)

def lossList (prices : Slice I64) (k : ℤ) : List ℤ := (priceList prices).map (relLoss k)

def sumSmallest (l : List ℤ) (m : ℕ) : ℤ := ((l.mergeSort (· ≤ ·)).take m).sum

def sumLargest (l : List ℤ) (m : ℕ) : ℤ := ((l.mergeSort (· ≥ ·)).take m).sum

def queryRows (queries : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
  queries.val.map (fun v => v.val.map (fun x => x.val))

def rowK (row : List ℤ) : ℤ := row[0]!

def rowM (row : List ℤ) : ℤ := row[1]!

def queryK (queries : Slice (alloc.vec.Vec I64)) (i : Fin (queryRows queries).length) : ℤ :=
  rowK ((queryRows queries).get i)

def queryM (queries : Slice (alloc.vec.Vec I64)) (i : Fin (queryRows queries).length) : ℤ :=
  rowM ((queryRows queries).get i)

def queryMn (queries : Slice (alloc.vec.Vec I64)) (i : Fin (queryRows queries).length) : ℕ :=
  (queryM queries i).toNat

def PricesOk (prices : Slice I64) : Prop :=
  ∀ j : Fin prices.val.length, 1 ≤ (prices.val.get j).val ∧ (prices.val.get j).val ≤ 1000000000

def QueriesOk (queries : Slice (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
  ∀ i : Fin (queryRows queries).length,
    ((queryRows queries).get i).length = 2 ∧
      1 ≤ queryK queries i ∧
        queryK queries i ≤ 1000000000 ∧
          1 ≤ queryM queries i ∧ queryM queries i ≤ (n : ℤ)

def lossSum (prices : Slice I64) (k : ℤ) (S : Finset (Fin prices.val.length)) : ℤ :=
  S.sum (fun j => relLoss k (prices.val.get j).val)

def lossValues (prices : Slice I64) (k : ℤ) (m : ℕ) : Set ℤ :=
  {v | ∃ S : Finset (Fin prices.val.length), S.card = m ∧ lossSum prices k S = v}

def IsMinLoss (prices : Slice I64) (k : ℤ) (m : ℕ) (v : ℤ) : Prop :=
  IsLeast (lossValues prices k m) v

def relLossValues (prices : Slice I64) (k : ℤ) : Set ℤ :=
  {w | ∃ j : Fin prices.val.length, w = relLoss k (prices.val.get j).val}

def IsMinRelLoss (prices : Slice I64) (k : ℤ) (w : ℤ) : Prop :=
  IsLeast (relLossValues prices k) w

/-- Whenever the function returns a result r, let n = len(prices). For every i with 0 <= i < len(queries), let k = queries[i][0] and m = queries[i][1]. For any set S of indices with S subset of {0,...,n-1} and |S| = m, define L_i(S) = sum over j in S of (prices[j] if prices[j] <= k else 2*k - prices[j]). Then len(r) = len(queries) and r[i] = min { L_i(S) : S subset of {0,...,n-1}, |S| = m }.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_1 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    r.val.length = queries.val.length ∧
      ∀ (i : Fin (queryRows queries).length) (v : ℤ),
        (resList r)[i.val]? = some v →
          IsMinLoss prices (queryK queries i) (queryMn queries i) v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), r.val.length = queries.val.length ∧
      ∀ (i : Fin (queryRows queries).length) (v : ℤ),
        (resList r)[i.val]? = some v →
          IsMinLoss prices (queryK queries i) (queryMn queries i) v) := by
  sorry

/-- The function returns a result r (i.e. it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_2 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn1 : 1 ≤ prices.val.length) (hn2 : prices.val.length ≤ 100000)
    (hprices : PricesOk prices)
    (hq1 : 1 ≤ queries.val.length) (hq2 : queries.val.length ≤ 100000)
    (hqueries : QueriesOk queries prices.val.length) :
    ∃ r : alloc.vec.Vec I64, minimum_relative_losses prices queries = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (hn1 : 1 ≤ prices.val.length) (hn2 : prices.val.length ≤ 100000)
    (hprices : PricesOk prices)
    (hq1 : 1 ≤ queries.val.length) (hq2 : queries.val.length ≤ 100000)
    (hqueries : QueriesOk queries prices.val.length), ∃ r : alloc.vec.Vec I64, minimum_relative_losses prices queries = ok r) := by
  sorry

/-- Whenever the calls on (prices, queries) and (prices, queries') return results r and r', respectively, we have len(r') = q and for every i with 0 <= i < q, r'[i] = r[i].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. Let q be an integer with 1 <= q <= len(queries), and let queries' be the slice consisting of the first q entries of queries, so len(queries') = q and queries'[i] = queries[i] for 0 <= i < q. -/
theorem spec_3 (prices : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64) (q : ℕ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hq1 : 1 ≤ q) (hq2 : q ≤ queries.val.length)
    (hprefix : queries'.val = queries.val.take q)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices queries' = ok r') :
    r'.val.length = q ∧ ∀ i : ℕ, i < q → (resList r')[i]? = (resList r)[i]? := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (prices : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64) (q : ℕ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hq1 : 1 ≤ q) (hq2 : q ≤ queries.val.length)
    (hprefix : queries'.val = queries.val.take q)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices queries' = ok r'), r'.val.length = q ∧ ∀ i : ℕ, i < q → (resList r')[i]? = (resList r)[i]?) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), let m = queries[i][1] and let L be the sum of the m largest elements of the multiset {prices[0],...,prices[n-1]}, counting multiplicities. Then r[i] >= -L.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_4 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        -(sumLargest (priceList prices) (queryMn queries i)) ≤ v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        -(sumLargest (priceList prices) (queryMn queries i)) ≤ v) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), r[i] <= queries[i][1] * queries[i][0].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_5 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v ≤ queryM queries i * queryK queries i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v ≤ queryM queries i * queryK queries i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), let m = queries[i][1] and let U be the sum of the m smallest elements of the multiset {prices[0],...,prices[n-1]}, counting multiplicities. Then r[i] <= U.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_6 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v ≤ sumSmallest (priceList prices) (queryMn queries i) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v ≤ sumSmallest (priceList prices) (queryMn queries i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and queries[i][1] = n, let k = queries[i][0]; then r[i] = sum over j from 0 to n-1 of (prices[j] if prices[j] <= k else 2*k - prices[j]).
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_7 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      queryMn queries i = prices.val.length →
        (resList r)[i.val]? = some v →
          v = lossSum prices (queryK queries i) Finset.univ := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      queryMn queries i = prices.val.length →
        (resList r)[i.val]? = some v →
          v = lossSum prices (queryK queries i) Finset.univ) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) such that queries[i][0] >= max_{0 <= j < n} prices[j], let m = queries[i][1] and let U be the sum of the m smallest elements of the multiset {prices[0],...,prices[n-1]}, counting multiplicities; then r[i] = U.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_8 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (∀ j : Fin prices.val.length, (prices.val.get j).val ≤ queryK queries i) →
        (resList r)[i.val]? = some v →
          v = sumSmallest (priceList prices) (queryMn queries i) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (∀ j : Fin prices.val.length, (prices.val.get j).val ≤ queryK queries i) →
        (resList r)[i.val]? = some v →
          v = sumSmallest (priceList prices) (queryMn queries i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) such that queries[i][0] <= min_{0 <= j < n} prices[j], let k = queries[i][0], m = queries[i][1], and let L be the sum of the m largest elements of the multiset {prices[0],...,prices[n-1]}, counting multiplicities; then r[i] = 2*m*k - L.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_9 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (∀ j : Fin prices.val.length, queryK queries i ≤ (prices.val.get j).val) →
        (resList r)[i.val]? = some v →
          v = 2 * queryM queries i * queryK queries i -
            sumLargest (priceList prices) (queryMn queries i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (∀ j : Fin prices.val.length, queryK queries i ≤ (prices.val.get j).val) →
        (resList r)[i.val]? = some v →
          v = 2 * queryM queries i * queryK queries i -
            sumLargest (priceList prices) (queryMn queries i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and queries[i][1] = 1, let k = queries[i][0]; then r[i] = min_{0 <= j < n} (prices[j] if prices[j] <= k else 2*k - prices[j]).
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_10 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      queryMn queries i = 1 →
        (resList r)[i.val]? = some v → IsMinRelLoss prices (queryK queries i) v := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      queryMn queries i = 1 →
        (resList r)[i.val]? = some v → IsMinRelLoss prices (queryK queries i) v) := by
  sorry

/-- Whenever the function returns a result r, for any two query indices i and j with 0 <= i < len(queries) and 0 <= j < len(queries), if queries[i][1] = queries[j][1] and queries[i][0] <= queries[j][0], then r[i] <= r[j].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_11 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i j : Fin (queryRows queries).length) (vi vj : ℤ),
      queryM queries i = queryM queries j →
        queryK queries i ≤ queryK queries j →
          (resList r)[i.val]? = some vi →
            (resList r)[j.val]? = some vj → vi ≤ vj := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i j : Fin (queryRows queries).length) (vi vj : ℤ),
      queryM queries i = queryM queries j →
        queryK queries i ≤ queryK queries j →
          (resList r)[i.val]? = some vi →
            (resList r)[j.val]? = some vj → vi ≤ vj) := by
  sorry

/-- Whenever the calls on (prices, queries) and (prices', queries) return results r and r', respectively, len(r') = len(r) and for every i with 0 <= i < len(queries), r'[i] = r[i].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. Additionally, prices' is a slice of length n with 1 <= prices'[j] <= 1000000000 for every j, and there is a bijection pi from {0,...,n-1} to itself such that prices'[j] = prices[pi(j)] for every j. The same queries slice is used for both calls. -/
theorem spec_12 (prices prices' : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hprices_len : prices'.val.length = prices.val.length)
    (hprices' : PricesOk prices')
    (hperm : List.Perm (priceList prices') (priceList prices))
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices' queries = ok r') :
    r'.val.length = r.val.length ∧
      ∀ i : Fin (queryRows queries).length, (resList r')[i.val]? = (resList r)[i.val]? := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (prices prices' : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hprices_len : prices'.val.length = prices.val.length)
    (hprices' : PricesOk prices')
    (hperm : List.Perm (priceList prices') (priceList prices))
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices' queries = ok r'), r'.val.length = r.val.length ∧
      ∀ i : Fin (queryRows queries).length, (resList r')[i.val]? = (resList r)[i.val]?) := by
  sorry

/-- Whenever the calls on (prices, queries) and (prices', queries') return results r and r', respectively, for every i with 0 <= i < len(queries), r'[i] = r[i] + queries[i][1] * c.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. Additionally, c is an integer, prices' is a slice of length n with prices'[j] = prices[j] + c for every j, and queries' is a slice of the same length as queries with len(queries'[i]) = 2, queries'[i][0] = queries[i][0] + c, and queries'[i][1] = queries[i][1] for every i. Suppose (prices', queries') also satisfies the problem constraints. -/
theorem spec_13 (prices prices' : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64) (c : ℤ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hprices_len : prices'.val.length = prices.val.length)
    (hprices_shift : priceList prices' = (priceList prices).map (· + c))
    (hprices' : PricesOk prices')
    (hqueries : QueriesOk queries prices.val.length)
    (hqueries_len : queries'.val.length = queries.val.length)
    (hqueries_shift : queryRows queries' =
      (queryRows queries).map (fun row => row.set 0 (rowK row + c)))
    (hqueries' : QueriesOk queries' prices'.val.length)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices' queries' = ok r') :
    ∀ (i : Fin (queryRows queries).length) (vi vi' : ℤ),
      (resList r)[i.val]? = some vi →
        (resList r')[i.val]? = some vi' → vi' = vi + queryM queries i * c := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (prices prices' : Slice I64) (queries queries' : Slice (alloc.vec.Vec I64))
    (r r' : alloc.vec.Vec I64) (c : ℤ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hprices_len : prices'.val.length = prices.val.length)
    (hprices_shift : priceList prices' = (priceList prices).map (· + c))
    (hprices' : PricesOk prices')
    (hqueries : QueriesOk queries prices.val.length)
    (hqueries_len : queries'.val.length = queries.val.length)
    (hqueries_shift : queryRows queries' =
      (queryRows queries).map (fun row => row.set 0 (rowK row + c)))
    (hqueries' : QueriesOk queries' prices'.val.length)
    (hres : minimum_relative_losses prices queries = ok r)
    (hres' : minimum_relative_losses prices' queries' = ok r'), ∀ (i : Fin (queryRows queries).length) (vi vi' : ℤ),
      (resList r)[i.val]? = some vi →
        (resList r')[i.val]? = some vi' → vi' = vi + queryM queries i * c) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), there exists a set S_i subset of {0,...,n-1} with |S_i| = queries[i][1] such that sum over j in S_i of (prices[j] if prices[j] <= queries[i][0] else 2*queries[i][0] - prices[j]) = r[i].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_14 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        ∃ S : Finset (Fin prices.val.length), S.card = queryMn queries i ∧
          lossSum prices (queryK queries i) S = v := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        ∃ S : Finset (Fin prices.val.length), S.card = queryMn queries i ∧
          lossSum prices (queryK queries i) S = v) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) and every set S subset of {0,...,n-1} with |S| = queries[i][1], sum over j in S of (prices[j] if prices[j] <= queries[i][0] else 2*queries[i][0] - prices[j]) >= r[i].
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_15 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        ∀ S : Finset (Fin prices.val.length), S.card = queryMn queries i →
          v ≤ lossSum prices (queryK queries i) S := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        ∀ S : Finset (Fin prices.val.length), S.card = queryMn queries i →
          v ≤ lossSum prices (queryK queries i) S) := by
  sorry

/-- Whenever the function returns a result r, if there is an integer p such that prices[j] = p for every j with 0 <= j < n, then for every i with 0 <= i < len(queries), let k = queries[i][0] and m = queries[i][1]; r[i] = m * (p if p <= k else 2*k - p).
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: n >= 1; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_16 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64) (p : ℤ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hconst : ∀ j : Fin prices.val.length, (prices.val.get j).val = p)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v = queryM queries i * relLoss (queryK queries i) p := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64) (p : ℤ)
    (hn : 1 ≤ prices.val.length)
    (hprices : PricesOk prices)
    (hqueries : QueriesOk queries prices.val.length)
    (hconst : ∀ j : Fin prices.val.length, (prices.val.get j).val = p)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v → v = queryM queries i * relLoss (queryK queries i) p) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), let k = queries[i][0], m = queries[i][1], and for each j with 0 <= j < n let v_j = prices[j] if prices[j] <= k else 2*k - prices[j]. Then r[i] is the sum of the m smallest elements of the multiset {v_0,...,v_{n-1}}, counting multiplicities.
  Preconditions: Let n = len(prices). The inputs satisfy the problem constraints: 1 <= n <= 100000; for every j with 0 <= j < n, 1 <= prices[j] <= 1000000000; 1 <= len(queries) <= 100000; for every i with 0 <= i < len(queries), len(queries[i]) = 2, 1 <= queries[i][0] <= 1000000000, and 1 <= queries[i][1] <= n. -/
theorem spec_17 (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn1 : 1 ≤ prices.val.length) (hn2 : prices.val.length ≤ 100000)
    (hprices : PricesOk prices)
    (hq1 : 1 ≤ queries.val.length) (hq2 : queries.val.length ≤ 100000)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r) :
    ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        v = sumSmallest (lossList prices (queryK queries i)) (queryMn queries i) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (prices : Slice I64) (queries : Slice (alloc.vec.Vec I64))
    (r : alloc.vec.Vec I64)
    (hn1 : 1 ≤ prices.val.length) (hn2 : prices.val.length ≤ 100000)
    (hprices : PricesOk prices)
    (hq1 : 1 ≤ queries.val.length) (hq2 : queries.val.length ≤ 100000)
    (hqueries : QueriesOk queries prices.val.length)
    (hres : minimum_relative_losses prices queries = ok r), ∀ (i : Fin (queryRows queries).length) (v : ℤ),
      (resList r)[i.val]? = some v →
        v = sumSmallest (lossList prices (queryK queries i)) (queryMn queries i)) := by
  sorry

end AegisSpec.MinimumRelativeLosses
