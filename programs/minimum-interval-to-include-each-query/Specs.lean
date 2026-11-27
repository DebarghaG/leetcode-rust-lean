import Aegis.MinInterval.Code.Funs

/-!
# Specifications of `Aegis.MinInterval.min_interval`

LeetCode problem `minimum-interval-to-include-each-query`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinInterval

  def row (intervals : Slice (alloc.vec.Vec I64)) (i : ℕ) : Option (List I64) :=
    (intervals.val[i]?).map (fun v => v.val)

  def entryAt (l : List I64) (k : ℕ) : Option ℤ :=
    (l[k]?).map (fun x => x.val)

  def queryAt (queries : Slice I64) (j : ℕ) : Option ℤ :=
    entryAt queries.val j

  def answerAt (r : alloc.vec.Vec I64) (j : ℕ) : Option ℤ :=
    entryAt r.val j

  def IsInterval (intervals : Slice (alloc.vec.Vec I64)) (i : ℕ) (lo hi : ℤ) : Prop :=
    ∃ iv : List I64,
      row intervals i = some iv ∧ iv.length = 2 ∧
        entryAt iv 0 = some lo ∧ entryAt iv 1 = some hi

  def Covers (intervals : Slice (alloc.vec.Vec I64)) (i : ℕ) (q : ℤ) : Prop :=
    ∃ lo hi : ℤ, IsInterval intervals i lo hi ∧ lo ≤ q ∧ q ≤ hi

  def IsLen (intervals : Slice (alloc.vec.Vec I64)) (i : ℕ) (v : ℤ) : Prop :=
    ∃ lo hi : ℤ, IsInterval intervals i lo hi ∧ v = hi - lo + 1

  def Pre (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64) : Prop :=
    1 ≤ intervals.val.length ∧ intervals.val.length ≤ 100000 ∧
      1 ≤ queries.val.length ∧ queries.val.length ≤ 100000 ∧
        (∀ i, i < intervals.val.length →
          ∃ lo hi : ℤ, IsInterval intervals i lo hi ∧ 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 10000000) ∧
          (∀ j, j < queries.val.length →
            ∀ q : ℤ, queryAt queries j = some q → 1 ≤ q ∧ q ≤ 10000000)

  /-- Whenever min_interval(intervals, queries) returns a result r, len(r) = m and for every j with 0 <= j < m: if there exists i with 0 <= i < n and intervals[i][0] <= queries[j] <= intervals[i][1], then r[j] = min { intervals[i][1] - intervals[i][0] + 1 | 0 <= i < n and intervals[i][0] <= queries[j] <= intervals[i][1] }; otherwise r[j] = -1.
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_1
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      r.val.length = queries.val.length ∧
        (∀ (j : ℕ) (q : ℤ), j < queries.val.length → queryAt queries j = some q →
          ((∃ i, i < intervals.val.length ∧ Covers intervals i q) →
              ∃ v : ℤ, answerAt r j = some v ∧
                (∃ i, i < intervals.val.length ∧ Covers intervals i q ∧
                  IsLen intervals i v) ∧
                (∀ i, i < intervals.val.length → Covers intervals i q →
                  ∀ w : ℤ, IsLen intervals i w → v ≤ w)) ∧
            ((¬ ∃ i, i < intervals.val.length ∧ Covers intervals i q) →
              answerAt r j = some (-1))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), r.val.length = queries.val.length ∧
          (∀ (j : ℕ) (q : ℤ), j < queries.val.length → queryAt queries j = some q →
            ((∃ i, i < intervals.val.length ∧ Covers intervals i q) →
                ∃ v : ℤ, answerAt r j = some v ∧
                  (∃ i, i < intervals.val.length ∧ Covers intervals i q ∧
                    IsLen intervals i v) ∧
                  (∀ i, i < intervals.val.length → Covers intervals i q →
                    ∀ w : ℤ, IsLen intervals i w → v ≤ w)) ∧
              ((¬ ∃ i, i < intervals.val.length ∧ Covers intervals i q) →
                answerAt r j = some (-1)))) := by
    sorry

  /-- min_interval(intervals, queries) returns a result r; it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_2
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (hpre : Pre intervals queries) :
      ∃ r : alloc.vec.Vec I64, Aegis.MinInterval.min_interval intervals queries = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (hpre : Pre intervals queries), ∃ r : alloc.vec.Vec I64, Aegis.MinInterval.min_interval intervals queries = ok r) := by
    sorry

  /-- Whenever min_interval(intervals, queries) returns a result r, for every j with 0 <= j < m, either r[j] = -1 or 1 <= r[j] <= 10000000.
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_3
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ j : ℕ, j < queries.val.length →
        (answerAt r j = some (-1) ∨
          ∃ v : ℤ, answerAt r j = some v ∧ 1 ≤ v ∧ v ≤ 10000000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ j : ℕ, j < queries.val.length →
          (answerAt r j = some (-1) ∨
            ∃ v : ℤ, answerAt r j = some v ∧ 1 ≤ v ∧ v ≤ 10000000)) := by
    sorry

  /-- Whenever min_interval(intervals, queries) returns a result r, for every j with 0 <= j < m and r[j] != -1, there exists i with 0 <= i < n such that intervals[i][0] <= queries[j] <= intervals[i][1] and r[j] = intervals[i][1] - intervals[i][0] + 1.
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_4
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (j : ℕ) (q v : ℤ), j < queries.val.length → queryAt queries j = some q →
        answerAt r j = some v → v ≠ -1 →
          ∃ i, i < intervals.val.length ∧ Covers intervals i q ∧ IsLen intervals i v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (j : ℕ) (q v : ℤ), j < queries.val.length → queryAt queries j = some q →
          answerAt r j = some v → v ≠ -1 →
            ∃ i, i < intervals.val.length ∧ Covers intervals i q ∧ IsLen intervals i v) := by
    sorry

  /-- Whenever min_interval(intervals, queries) returns a result r, for every j with 0 <= j < m and r[j] != -1, and for every i with 0 <= i < n, if intervals[i][0] <= queries[j] <= intervals[i][1], then r[j] <= intervals[i][1] - intervals[i][0] + 1.
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_5
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (j : ℕ) (q v : ℤ), j < queries.val.length → queryAt queries j = some q →
        answerAt r j = some v → v ≠ -1 →
          ∀ i, i < intervals.val.length → Covers intervals i q →
            ∀ w : ℤ, IsLen intervals i w → v ≤ w := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (j : ℕ) (q v : ℤ), j < queries.val.length → queryAt queries j = some q →
          answerAt r j = some v → v ≠ -1 →
            ∀ i, i < intervals.val.length → Covers intervals i q →
              ∀ w : ℤ, IsLen intervals i w → v ≤ w) := by
    sorry

  /-- Whenever min_interval(intervals, queries) returns a result r, for every a and b with 0 <= a < m and 0 <= b < m, if queries[a] = queries[b], then r[a] = r[b].
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_6
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (a b : ℕ) (q : ℤ), a < queries.val.length → b < queries.val.length →
        queryAt queries a = some q → queryAt queries b = some q →
          answerAt r a = answerAt r b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (a b : ℕ) (q : ℤ), a < queries.val.length → b < queries.val.length →
          queryAt queries a = some q → queryAt queries b = some q →
            answerAt r a = answerAt r b) := by
    sorry

  /-- For every interval array intervals' satisfying the same preconditions with n' = len(intervals') = n and whose entries are a permutation of the entries of intervals, whenever min_interval(intervals, queries) returns r and min_interval(intervals', queries) returns r', we have len(r) = m and len(r') = m, and for every j with 0 <= j < m, r[j] = r'[j].
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_7
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (intervals' : Slice (alloc.vec.Vec I64)) (r' : alloc.vec.Vec I64),
        Pre intervals' queries →
          intervals'.val.length = intervals.val.length →
            List.Perm (intervals'.val.map (fun v => v.val))
              (intervals.val.map (fun v => v.val)) →
              Aegis.MinInterval.min_interval intervals' queries = ok r' →
                r.val.length = queries.val.length ∧
                  r'.val.length = queries.val.length ∧
                    (∀ j : ℕ, j < queries.val.length →
                      answerAt r j = answerAt r' j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (intervals' : Slice (alloc.vec.Vec I64)) (r' : alloc.vec.Vec I64),
          Pre intervals' queries →
            intervals'.val.length = intervals.val.length →
              List.Perm (intervals'.val.map (fun v => v.val))
                (intervals.val.map (fun v => v.val)) →
                Aegis.MinInterval.min_interval intervals' queries = ok r' →
                  r.val.length = queries.val.length ∧
                    r'.val.length = queries.val.length ∧
                      (∀ j : ℕ, j < queries.val.length →
                        answerAt r j = answerAt r' j)) := by
    sorry

  /-- For every interval array intervals' satisfying the same preconditions such that every entry of intervals occurs in intervals' at least as many times as in intervals, whenever min_interval(intervals, queries) returns r and min_interval(intervals', queries) returns r', we have len(r) = m and len(r') = m, and for every j with 0 <= j < m: if r[j] = -1 then r'[j] = -1 or 1 <= r'[j]; and if r[j] != -1 then r'[j] != -1 and r'[j] <= r[j].
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_8
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (intervals' : Slice (alloc.vec.Vec I64)) (r' : alloc.vec.Vec I64),
        Pre intervals' queries →
          (∀ iv ∈ intervals.val.map (fun v => v.val),
            Multiset.count iv (intervals.val.map (fun v => v.val) : Multiset (List I64)) ≤
              Multiset.count iv
                (intervals'.val.map (fun v => v.val) : Multiset (List I64))) →
            Aegis.MinInterval.min_interval intervals' queries = ok r' →
              r.val.length = queries.val.length ∧
                r'.val.length = queries.val.length ∧
                  (∀ j : ℕ, j < queries.val.length →
                    (answerAt r j = some (-1) →
                        (answerAt r' j = some (-1) ∨
                          ∃ v' : ℤ, answerAt r' j = some v' ∧ 1 ≤ v')) ∧
                      (∀ v : ℤ, answerAt r j = some v → v ≠ -1 →
                        (∀ v' : ℤ, answerAt r' j = some v' → v' ≠ -1) ∧
                          (∀ v' : ℤ, answerAt r' j = some v' → v' ≤ v))) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (intervals' : Slice (alloc.vec.Vec I64)) (r' : alloc.vec.Vec I64),
          Pre intervals' queries →
            (∀ iv ∈ intervals.val.map (fun v => v.val),
              Multiset.count iv (intervals.val.map (fun v => v.val) : Multiset (List I64)) ≤
                Multiset.count iv
                  (intervals'.val.map (fun v => v.val) : Multiset (List I64))) →
              Aegis.MinInterval.min_interval intervals' queries = ok r' →
                r.val.length = queries.val.length ∧
                  r'.val.length = queries.val.length ∧
                    (∀ j : ℕ, j < queries.val.length →
                      (answerAt r j = some (-1) →
                          (answerAt r' j = some (-1) ∨
                            ∃ v' : ℤ, answerAt r' j = some v' ∧ 1 ≤ v')) ∧
                        (∀ v : ℤ, answerAt r j = some v → v ≠ -1 →
                          (∀ v' : ℤ, answerAt r' j = some v' → v' ≠ -1) ∧
                            (∀ v' : ℤ, answerAt r' j = some v' → v' ≤ v)))) := by
    sorry

  /-- Whenever min_interval(intervals, queries) returns a result r, for every j with 0 <= j < m, every queries' satisfying the preconditions with len(queries') = m and queries'[j] = queries[j], and every result r' returned by min_interval(intervals, queries'), we have r[j] = r'[j].
    Preconditions: Let n = len(intervals) and m = len(queries). The input satisfies: 1 <= n <= 100000, 1 <= m <= 100000; for every i with 0 <= i < n, len(intervals[i]) = 2, and writing intervals[i][0] and intervals[i][1] for its entries, 1 <= intervals[i][0] <= intervals[i][1] <= 10000000; for every j with 0 <= j < m, 1 <= queries[j] <= 10000000. -/
  theorem spec_9
      (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
      (r : alloc.vec.Vec I64)
      (hpre : Pre intervals queries)
      (hr : Aegis.MinInterval.min_interval intervals queries = ok r) :
      ∀ (j : ℕ) (q : ℤ), j < queries.val.length → queryAt queries j = some q →
        ∀ (queries' : Slice I64) (r' : alloc.vec.Vec I64),
          Pre intervals queries' →
            queries'.val.length = queries.val.length →
              queryAt queries' j = some q →
                Aegis.MinInterval.min_interval intervals queries' = ok r' →
                  answerAt r j = answerAt r' j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (intervals : Slice (alloc.vec.Vec I64)) (queries : Slice I64)
        (r : alloc.vec.Vec I64)
        (hpre : Pre intervals queries)
        (hr : Aegis.MinInterval.min_interval intervals queries = ok r), ∀ (j : ℕ) (q : ℤ), j < queries.val.length → queryAt queries j = some q →
          ∀ (queries' : Slice I64) (r' : alloc.vec.Vec I64),
            Pre intervals queries' →
              queries'.val.length = queries.val.length →
                queryAt queries' j = some q →
                  Aegis.MinInterval.min_interval intervals queries' = ok r' →
                    answerAt r j = answerAt r' j) := by
    sorry

  end AegisSpec.MinInterval
