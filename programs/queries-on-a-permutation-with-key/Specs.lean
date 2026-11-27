import Aegis.ProcessQueries.Code.Funs

/-!
# Specifications of `Aegis.ProcessQueries.process_queries`

LeetCode problem `queries-on-a-permutation-with-key`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ProcessQueries (process_queries)

namespace AegisSpec.ProcessQueries

def qlen (queries : Slice I64) : Nat := queries.val.length

def qvals (queries : Slice I64) : List Int := queries.val.map (fun x => x.val)

def outvals (r : alloc.vec.Vec I64) : List Int := r.val.map (fun x => x.val)

def initPerm (m : Int) : List Int := (List.range m.toNat).map (fun j => (j : Int) + 1)

def moveToFront (l : List Int) (p : Nat) : List Int :=
  l.getD p 0 :: (l.take p ++ l.drop (p + 1))

def permSeq (m : Int) (qs : List Int) : Nat → List Int
  | 0 => initPerm m
  | i + 1 => moveToFront (permSeq m qs i) ((permSeq m qs i).idxOf (qs.getD i 0))

def permAt (queries : Slice I64) (m : I64) (i : Nat) : List Int :=
  permSeq m.val (qvals queries) i

def pIdx (m : Int) (qs : List Int) (i : Nat) : Nat := (permSeq m qs i).idxOf (qs.getD i 0)

def qprefix (qs : List Int) (i : Nat) : List Int := qs.take i

def seenSet (qs : List Int) (i : Nat) : Finset Int := (qs.take i).toFinset

def lastIdx : List Int → Int → Option Nat
  | [], _ => none
  | a :: t, x =>
    match lastIdx t x with
    | some j => some (j + 1)
    | none => if a = x then some 0 else none

def occursBefore (l : List Int) (x y : Int) : Prop :=
  ∃ (a b : Nat), a < b ∧ l[a]? = some x ∧ l[b]? = some y

def distinctByLastOcc (l : List Int) : List Int :=
  l.foldl (fun acc a => a :: acc.filter (fun v => decide (v ≠ a))) ([] : List Int)

def withoutSet (l : List Int) (s : Finset Int) : List Int :=
  l.filter (fun v => decide (v ∉ s))

/-- The function returns a result r (it does not fail). Let P_0 be the length-m sequence [1,2,...,m], so P_0[j] = j+1 for 0 <= j < m. For each i with 0 <= i < n, let p_i be the unique index with 0 <= p_i < m and P_i[p_i] = queries[i], and let P_{i+1} be the length-m sequence obtained by moving the element at index p_i of P_i to the front: P_{i+1}[0] = queries[i], P_{i+1}[j] = P_i[j-1] for 1 <= j <= p_i, and P_{i+1}[j] = P_i[j] for p_i < j < m. Then len(r) = n and for every i with 0 <= i < n, r[i] = p_i.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_1 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∃ r, process_queries queries m = ok r ∧
      (outvals r).length = qlen queries ∧
      ∀ i, i < qlen queries →
        (outvals r).getD i 0 = (pIdx m.val (qvals queries) i : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∃ r, process_queries queries m = ok r ∧
      (outvals r).length = qlen queries ∧
      ∀ i, i < qlen queries →
        (outvals r).getD i 0 = (pIdx m.val (qvals queries) i : Int)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail with a panic, arithmetic overflow, or out-of-bounds access on these inputs.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_2 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∃ r, process_queries queries m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∃ r, process_queries queries m = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(queries).
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_3 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r → (outvals r).length = qlen queries := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r → (outvals r).length = qlen queries) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), 0 <= r[i] < m.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_4 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      ∀ i, i < (outvals r).length → 0 ≤ (outvals r).getD i 0 ∧ (outvals r).getD i 0 < m.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      ∀ i, i < (outvals r).length → 0 ≤ (outvals r).getD i 0 ∧ (outvals r).getD i 0 < m.val) := by
  sorry

/-- Whenever the function returns a result r, r[0] = queries[0] - 1.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_5 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      (outvals r).getD 0 0 = (qvals queries).getD 0 0 - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      (outvals r).getD 0 0 = (qvals queries).getD 0 0 - 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 1 <= i < len(queries), if queries[i] = queries[i-1], then r[i] = 0.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_6 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      ∀ i, 1 ≤ i → i < qlen queries →
        (qvals queries).getD i 0 = (qvals queries).getD (i - 1) 0 →
        (outvals r).getD i 0 = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      ∀ i, 1 ≤ i → i < qlen queries →
        (qvals queries).getD i 0 = (qvals queries).getD (i - 1) 0 →
        (outvals r).getD i 0 = 0) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries), if queries[i] does not occur among queries[0],...,queries[i-1], then r[i] = (queries[i] - 1) + D_i, where D_i is the number of distinct values v with queries[i] < v <= m that occur among queries[0],...,queries[i-1].
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_7 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        (qvals queries).getD i 0 ∉ seenSet (qvals queries) i →
        (outvals r).getD i 0 =
          ((qvals queries).getD i 0 - 1) +
            (((seenSet (qvals queries) i).filter
              (fun v => (qvals queries).getD i 0 < v ∧ v ≤ m.val)).card : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        (qvals queries).getD i 0 ∉ seenSet (qvals queries) i →
        (outvals r).getD i 0 =
          ((qvals queries).getD i 0 - 1) +
            (((seenSet (qvals queries) i).filter
              (fun v => (qvals queries).getD i 0 < v ∧ v ≤ m.val)).card : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(queries) such that q = queries[i] occurs earlier in queries, let j be the largest index with 0 <= j < i and queries[j] = q. Then r[i] equals the number of distinct values that occur among queries[j+1],...,queries[i-1]; this number is 0 when j+1 > i-1.
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_8 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        ∀ j : Nat,
          lastIdx (qprefix (qvals queries) i) ((qvals queries).getD i 0) = some j →
          (outvals r).getD i 0 =
            (((qprefix (qvals queries) i).drop (j + 1)).toFinset.card : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        ∀ j : Nat,
          lastIdx (qprefix (qvals queries) i) ((qvals queries).getD i 0) = some j →
          (outvals r).getD i 0 =
            (((qprefix (qvals queries) i).drop (j + 1)).toFinset.card : Int)) := by
  sorry

/-- Let n = len(queries) and define P_0,...,P_n by the move-to-front rule starting from P_0 = [1,2,...,m]. Whenever the function returns a result r, for every i with 0 <= i < n, r[i] is a valid index into P_i and P_i[r[i]] = queries[i].
  Preconditions: m is an integer with 1 <= m <= 1000; n = len(queries) satisfies 1 <= n <= m; and for every i with 0 <= i < n, 1 <= queries[i] <= m. -/
theorem spec_9 (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val) :
    ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        ∃ k : Nat,
          (outvals r).getD i 0 = (k : Int) ∧
          k < (permAt queries m i).length ∧
          (permAt queries m i)[k]? = some ((qvals queries).getD i 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (queries : Slice I64) (m : I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 1000)
    (hn1 : 1 ≤ qlen queries) (hn2 : (qlen queries : Int) ≤ m.val)
    (hq : ∀ i, i < qlen queries →
      1 ≤ (qvals queries).getD i 0 ∧ (qvals queries).getD i 0 ≤ m.val), ∀ r, process_queries queries m = ok r →
      ∀ i, i < qlen queries →
        ∃ k : Nat,
          (outvals r).getD i 0 = (k : Int) ∧
          k < (permAt queries m i).length ∧
          (permAt queries m i)[k]? = some ((qvals queries).getD i 0)) := by
  sorry

end AegisSpec.ProcessQueries
