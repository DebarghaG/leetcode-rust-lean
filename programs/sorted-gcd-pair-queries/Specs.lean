import Aegis.GcdValues.Code.Funs

/-!
# Specifications of `Aegis.GcdValues.gcd_values`

LeetCode problem `sorted-gcd-pair-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GcdValues

  def vals (s : Slice Std.I64) : List ℤ := s.val.map IScalar.val

  def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map IScalar.val

  def nth (l : List ℤ) (i : ℕ) : ℤ := l[i]?.getD 0

  def n (nums : Slice Std.I64) : ℕ := (vals nums).length

  def m (nums : Slice Std.I64) : ℕ := n nums * (n nums - 1) / 2

  def entry (nums : Slice Std.I64) (i : ℕ) : ℤ := nth (vals nums) i

  def query (queries : Slice Std.I64) (k : ℕ) : ℤ := nth (vals queries) k

  def ans (r : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ := nth (vecVals r) k

  def gcdAt (nums : Slice Std.I64) (i j : ℕ) : ℕ :=
    Nat.gcd (entry nums i).natAbs (entry nums j).natAbs

  def pairGcds (nums : Slice Std.I64) : List ℕ :=
    (List.range (n nums)).flatMap fun i =>
      (List.range (n nums)).filterMap fun j =>
        if i < j then some (gcdAt nums i j) else none

  def C (nums : Slice Std.I64) (v : ℕ) : ℕ := (pairGcds nums).count v

  def L (nums : Slice Std.I64) (v : ℕ) : ℕ := (Finset.Ico 1 v).sum fun d => C nums d

  def minGcd (nums : Slice Std.I64) : ℕ := (pairGcds nums).min?.getD 0

  def maxGcd (nums : Slice Std.I64) : ℕ := (pairGcds nums).max?.getD 0

  def maxEntry (nums : Slice Std.I64) : ℤ := (vals nums).max?.getD 0

  def sortedGcds (nums : Slice Std.I64) : List ℕ := (pairGcds nums).insertionSort (· ≤ ·)

  def sortedGcdsZ (nums : Slice Std.I64) : List ℤ := (sortedGcds nums).map fun v => (v : ℤ)

  /-- Let C(v) be the number of pairs (i,j) with 0 <= i < j < n and gcd(nums[i], nums[j]) = v, and let L(v) = sum_{d=1}^{v-1} C(d) for every positive integer v. The function returns a result r (so it does not fail), with len(r) = len(queries), and for every k with 0 <= k < len(queries), if q = queries[k] then L(r[k]) <= q < L(r[k]) + C(r[k]). Equivalently, r[k] is the element at 0-based index q in the nondecreasing list of all m values gcd(nums[i], nums[j]) for 0 <= i < j < n.
    Preconditions: Let n = len(nums) and m = n*(n-1)/2 (mathematical integers). The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. Slice entries are interpreted as mathematical integers. -/
  theorem spec_1 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∃ r, Aegis.GcdValues.gcd_values nums queries = ok r ∧
        (vecVals r).length = (vals queries).length ∧
        ∀ k, k < (vals queries).length →
          (L nums (ans r k).toNat : ℤ) ≤ query queries k ∧
          query queries k < (L nums (ans r k).toNat : ℤ) + (C nums (ans r k).toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∃ r, Aegis.GcdValues.gcd_values nums queries = ok r ∧
          (vecVals r).length = (vals queries).length ∧
          ∀ k, k < (vals queries).length →
            (L nums (ans r k).toNat : ℤ) ≤ query queries k ∧
            query queries k < (L nums (ans r k).toNat : ℤ) + (C nums (ans r k).toNat : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the evaluation of gcd_values returns a successful result Result.ok r; it does not panic, index outside nums or queries, or fail from 64-bit arithmetic overflow.
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_2 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∃ r, Aegis.GcdValues.gcd_values nums queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∃ r, Aegis.GcdValues.gcd_values nums queries = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the returned vector has exactly one entry per query: len(r) = len(queries).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_3 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        (vecVals r).length = (vals queries).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          (vecVals r).length = (vals queries).length) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), there exist indices i and j such that 0 <= i < j < n and r[k] = gcd(nums[i], nums[j]).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_4 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ k, k < (vals queries).length →
          ∃ i j, i < j ∧ j < n nums ∧ ans r k = (gcdAt nums i j : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ k, k < (vals queries).length →
            ∃ i j, i < j ∧ j < n nums ∧ ans r k = (gcdAt nums i j : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), 1 <= r[k] <= max_{0 <= i < n} nums[i].
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_5 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ k, k < (vals queries).length → 1 ≤ ans r k ∧ ans r k ≤ maxEntry nums := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ k, k < (vals queries).length → 1 ≤ ans r k ∧ ans r k ≤ maxEntry nums) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), there exist two distinct indices i and j with 0 <= i < j < n such that r[k] divides nums[i] and r[k] divides nums[j].
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_6 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ k, k < (vals queries).length →
          ∃ i j, i < j ∧ j < n nums ∧ ans r k ∣ entry nums i ∧ ans r k ∣ entry nums j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ k, k < (vals queries).length →
            ∃ i j, i < j ∧ j < n nums ∧ ans r k ∣ entry nums i ∧ ans r k ∣ entry nums j) := by
    sorry

  /-- Whenever the function returns a result r, for all p and q with 0 <= p,q < len(queries), if queries[p] <= queries[q] then r[p] <= r[q].
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_7 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ p q, p < (vals queries).length → q < (vals queries).length →
          query queries p ≤ query queries q → ans r p ≤ ans r q := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ p q, p < (vals queries).length → q < (vals queries).length →
            query queries p ≤ query queries q → ans r p ≤ ans r q) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), if queries[k] = 0 then r[k] = min { gcd(nums[i], nums[j]) | 0 <= i < j < n }.
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_8 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ k, k < (vals queries).length → query queries k = 0 →
          ans r k = (minGcd nums : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ k, k < (vals queries).length → query queries k = 0 →
            ans r k = (minGcd nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(queries), if queries[k] = m-1 then r[k] = max { gcd(nums[i], nums[j]) | 0 <= i < j < n }.
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_9 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ k, k < (vals queries).length → query queries k = (m nums : ℤ) - 1 →
          ans r k = (maxGcd nums : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ k, k < (vals queries).length → query queries k = (m nums : ℤ) - 1 →
            ans r k = (maxGcd nums : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v >= 1, let C(v) be the number of pairs (i,j) with 0 <= i < j < n and gcd(nums[i], nums[j]) = v, and let L(v) = sum_{d=1}^{v-1} C(d). Then the number of indices k with r[k] = v equals the number of indices k with 0 <= k < len(queries) and L(v) <= queries[k] < L(v) + C(v).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_10 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ v : ℕ, 1 ≤ v →
          ((Finset.range (vals queries).length).filter fun k => ans r k = (v : ℤ)).card =
            ((Finset.range (vals queries).length).filter fun k =>
              (L nums v : ℤ) ≤ query queries k ∧
                query queries k < (L nums v : ℤ) + (C nums v : ℤ)).card := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ v : ℕ, 1 ≤ v →
            ((Finset.range (vals queries).length).filter fun k => ans r k = (v : ℤ)).card =
              ((Finset.range (vals queries).length).filter fun k =>
                (L nums v : ℤ) ≤ query queries k ∧
                  query queries k < (L nums v : ℤ) + (C nums v : ℤ)).card) := by
    sorry

  /-- Whenever the function returns a result r, if there is an integer c such that nums[i] = c for every i with 0 <= i < n, then r[k] = c for every k with 0 <= k < len(queries).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_11 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ c : ℤ, (∀ i, i < n nums → entry nums i = c) →
          ∀ k, k < (vals queries).length → ans r k = c := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ c : ℤ, (∀ i, i < n nums → entry nums i = c) →
            ∀ k, k < (vals queries).length → ans r k = c) := by
    sorry

  /-- Whenever the function returns a result r, if n = 2 then for every k with 0 <= k < len(queries), r[k] = gcd(nums[0], nums[1]).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_12 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r → n nums = 2 →
        ∀ k, k < (vals queries).length → ans r k = (gcdAt nums 0 1 : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r → n nums = 2 →
          ∀ k, k < (vals queries).length → ans r k = (gcdAt nums 0 1 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if len(queries) = m and queries[k] = k for every k with 0 <= k < m, then len(r) = m and r is the nondecreasing list of all m gcd values: for every k with 0 <= k < m, r[k] is the k-th smallest value, with multiplicity, among { gcd(nums[i], nums[j]) | 0 <= i < j < n }.
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_13 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        (vals queries).length = m nums →
          (∀ k, k < m nums → query queries k = (k : ℤ)) →
            (vecVals r).length = m nums ∧
              ∀ k, k < m nums → ans r k = nth (sortedGcdsZ nums) k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          (vals queries).length = m nums →
            (∀ k, k < m nums → query queries k = (k : ℤ)) →
              (vecVals r).length = m nums ∧
                ∀ k, k < m nums → ans r k = nth (sortedGcdsZ nums) k) := by
    sorry

  /-- Whenever the function returns a result r, for every integer d >= 1, if d divides nums[i] for every i with 0 <= i < n, then d divides r[k] for every k with 0 <= k < len(queries).
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. -/
  theorem spec_14 (nums queries : Slice Std.I64)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ)) :
      ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
        ∀ d : ℤ, 1 ≤ d → (∀ i, i < n nums → d ∣ entry nums i) →
          ∀ k, k < (vals queries).length → d ∣ ans r k := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums queries : Slice Std.I64)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ)), ∀ r, Aegis.GcdValues.gcd_values nums queries = ok r →
          ∀ d : ℤ, 1 ≤ d → (∀ i, i < n nums → d ∣ entry nums i) →
            ∀ k, k < (vals queries).length → d ∣ ans r k) := by
    sorry

  /-- If the function returns r for (nums, queries) and returns r' for (nums, queries'), then for every k with 0 <= k < len(queries), r'[k] = r[pi(k)].
    Preconditions: For a given input, let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. Let pi be any permutation of {0,...,len(queries)-1}, and let queries' be the slice defined by queries'[k] = queries[pi(k)] for every k. -/
  theorem spec_15 (nums queries queries' : Slice Std.I64)
      (pi : Equiv.Perm (Fin (vals queries).length))
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
      (hq'_len : (vals queries').length = (vals queries).length)
      (hq'_val : ∀ k : Fin (vals queries).length,
        query queries' (k : ℕ) = query queries (pi k : ℕ)) :
      ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
        Aegis.GcdValues.gcd_values nums queries' = ok r' →
          ∀ k : Fin (vals queries).length, ans r' (k : ℕ) = ans r (pi k : ℕ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums queries queries' : Slice Std.I64)
        (pi : Equiv.Perm (Fin (vals queries).length))
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
        (hq'_len : (vals queries').length = (vals queries).length)
        (hq'_val : ∀ k : Fin (vals queries).length,
          query queries' (k : ℕ) = query queries (pi k : ℕ)), ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
          Aegis.GcdValues.gcd_values nums queries' = ok r' →
            ∀ k : Fin (vals queries).length, ans r' (k : ℕ) = ans r (pi k : ℕ)) := by
    sorry

  /-- If the function returns r for (nums, queries) and returns r' for (nums', queries), then len(r') = len(queries) and for every k with 0 <= k < len(queries), r'[k] = r[k].
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. Let pi be any permutation of {0,...,n-1}, and let nums' be the slice defined by nums'[i] = nums[pi(i)] for every i with 0 <= i < n. -/
  theorem spec_16 (nums nums' queries : Slice Std.I64)
      (pi : Equiv.Perm (Fin (n nums)))
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
      (hn'_len : n nums' = n nums)
      (hn'_val : ∀ i : Fin (n nums), entry nums' (i : ℕ) = entry nums (pi i : ℕ)) :
      ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
        Aegis.GcdValues.gcd_values nums' queries = ok r' →
          (vecVals r').length = (vals queries).length ∧
            ∀ k, k < (vals queries).length → ans r' k = ans r k := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums nums' queries : Slice Std.I64)
        (pi : Equiv.Perm (Fin (n nums)))
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
        (hn'_len : n nums' = n nums)
        (hn'_val : ∀ i : Fin (n nums), entry nums' (i : ℕ) = entry nums (pi i : ℕ)), ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
          Aegis.GcdValues.gcd_values nums' queries = ok r' →
            (vecVals r').length = (vals queries).length ∧
              ∀ k, k < (vals queries).length → ans r' k = ans r k) := by
    sorry

  /-- If the function returns r for (nums, queries) and returns r' for (nums', queries), then len(r') = len(queries) and for every k with 0 <= k < len(queries), r'[k] = c * r[k].
    Preconditions: Let n = len(nums) and m = n*(n-1)/2. The input satisfies 2 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 50000; 1 <= len(queries) <= 100000; and for every k with 0 <= k < len(queries), 0 <= queries[k] < m. Let c >= 1 be an integer such that c*nums[i] <= 50000 for every i with 0 <= i < n, and let nums' be the slice defined by nums'[i] = c*nums[i] for every i. -/
  theorem spec_17 (nums nums' queries : Slice Std.I64) (c : ℤ)
      (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
      (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
      (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
      (hq : ∀ k, k < (vals queries).length →
        0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
      (hc : 1 ≤ c)
      (hn'_len : n nums' = n nums)
      (hn'_val : ∀ i, i < n nums → entry nums' i = c * entry nums i)
      (hn'_bnd : ∀ i, i < n nums → c * entry nums i ≤ 50000) :
      ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
        Aegis.GcdValues.gcd_values nums' queries = ok r' →
          (vecVals r').length = (vals queries).length ∧
            ∀ k, k < (vals queries).length → ans r' k = c * ans r k := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (nums nums' queries : Slice Std.I64) (c : ℤ)
        (hn_lo : 2 ≤ n nums) (hn_hi : n nums ≤ 100000)
        (hnums : ∀ i, i < n nums → 1 ≤ entry nums i ∧ entry nums i ≤ 50000)
        (hq_lo : 1 ≤ (vals queries).length) (hq_hi : (vals queries).length ≤ 100000)
        (hq : ∀ k, k < (vals queries).length →
          0 ≤ query queries k ∧ query queries k < (m nums : ℤ))
        (hc : 1 ≤ c)
        (hn'_len : n nums' = n nums)
        (hn'_val : ∀ i, i < n nums → entry nums' i = c * entry nums i)
        (hn'_bnd : ∀ i, i < n nums → c * entry nums i ≤ 50000), ∀ r r', Aegis.GcdValues.gcd_values nums queries = ok r →
          Aegis.GcdValues.gcd_values nums' queries = ok r' →
            (vecVals r').length = (vals queries).length ∧
              ∀ k, k < (vals queries).length → ans r' k = c * ans r k) := by
    sorry

  end AegisSpec.GcdValues
