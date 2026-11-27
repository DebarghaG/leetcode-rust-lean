import Aegis.MaxSatisfaction.Code.Funs

/-!
# Specifications of `Aegis.MaxSatisfaction.max_satisfaction`

LeetCode problem `reducing-dishes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSatisfaction

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def elem (s : Slice Std.I64) (i : ℕ) : ℤ := (vals s).getD i 0

def weightedSumAux : ℕ → List ℤ → ℤ
  | _, [] => 0
  | w, x :: xs => (w : ℤ) * x + weightedSumAux (w + 1) xs

def weightedSum (l : List ℤ) : ℤ := weightedSumAux 1 l

def seqValue (s : Slice Std.I64) (idx : List ℕ) : ℤ := weightedSum (idx.map (elem s))

def IsIndexSeq (s : Slice Std.I64) (idx : List ℕ) : Prop :=
  idx.Nodup ∧ ∀ i ∈ idx, i < s.val.length

def IsMaxObjective (s : Slice Std.I64) (r : ℤ) : Prop :=
  (∀ idx, IsIndexSeq s idx → seqValue s idx ≤ r) ∧
  (∃ idx, IsIndexSeq s idx ∧ seqValue s idx = r)

def IsMaxObjectiveOfLength (s : Slice Std.I64) (k : ℕ) (r : ℤ) : Prop :=
  (∀ idx, IsIndexSeq s idx → idx.length = k → seqValue s idx ≤ r) ∧
  (∃ idx, IsIndexSeq s idx ∧ idx.length = k ∧ seqValue s idx = r)

def positiveSum (l : List ℤ) : ℤ := (l.map (fun x => max 0 x)).sum

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldl max x

def SortedAsc (l : List ℤ) : Prop := l.Pairwise (· ≤ ·)

def SortedDesc (l : List ℤ) : Prop := l.Pairwise (· ≥ ·)

def prefixPositiveSum (b : List ℤ) : ℤ :=
  ((List.range b.length).map (fun k => max 0 ((b.take (k + 1)).sum))).sum

def bestOverLengths (a : List ℤ) : ℤ :=
  listMax ((List.range (a.length + 1)).map (fun k => weightedSum (a.drop (a.length - k))))

/-- The function returns a result r, and r is the maximum over all integers k with 0 <= k <= n and all injective sequences (i_1, i_2, ..., i_k) of indices in [0, n) of the value sum_{j=1}^{k} j * satisfaction[i_j]. (For k = 0, the empty sum is 0.)
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_1 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ IsMaxObjective s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ IsMaxObjective s r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_2 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r) := by
  sorry

/-- The function returns a result r, and r <= 1000 * n * (n + 1) / 2, where n = len(satisfaction).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_3 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val ≤ 1000 * (n : ℤ) * ((n : ℤ) + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val ≤ 1000 * (n : ℤ) * ((n : ℤ) + 1) / 2) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if for every i with 0 <= i < n, satisfaction[i] <= 0.
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_4 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      (r.val = 0 ↔ ∀ i, i < n → elem s i ≤ 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      (r.val = 0 ↔ ∀ i, i < n → elem s i ≤ 0)) := by
  sorry

/-- If the function returns r for satisfaction and r' for satisfaction', then r = r'.
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. Let satisfaction' be any array of length n that is a permutation of satisfaction (i.e., there exists a bijection π: {0,...,n-1} -> {0,...,n-1} such that satisfaction'[i] = satisfaction[π(i)] for all i). -/
theorem spec_5 (s s' : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hlen' : s'.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (hperm : ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n, elem s' ↑i = elem s ↑(π i)) :
    ∀ r r', Aegis.MaxSatisfaction.max_satisfaction s = ok r →
      Aegis.MaxSatisfaction.max_satisfaction s' = ok r' → r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s s' : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hlen' : s'.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (hperm : ∃ π : Equiv.Perm (Fin n), ∀ i : Fin n, elem s' ↑i = elem s ↑(π i)), ∀ r r', Aegis.MaxSatisfaction.max_satisfaction s = ok r →
      Aegis.MaxSatisfaction.max_satisfaction s' = ok r' → r.val = r'.val) := by
  sorry

/-- If the function returns r_x for x and r_y for y, then r_x <= r_y.
  Preconditions: Let n be an integer with 1 <= n <= 500. Let x and y be arrays of length n such that for all i in [0, n), -1000 <= x[i] <= y[i] <= 1000. -/
theorem spec_6 (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (x y : Slice Std.I64) (hxlen : x.val.length = n) (hylen : y.val.length = n)
    (hrange : ∀ i, i < n → -1000 ≤ elem x i ∧ elem x i ≤ elem y i ∧ elem y i ≤ 1000) :
    ∀ rx ry, Aegis.MaxSatisfaction.max_satisfaction x = ok rx →
      Aegis.MaxSatisfaction.max_satisfaction y = ok ry → rx.val ≤ ry.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (x y : Slice Std.I64) (hxlen : x.val.length = n) (hylen : y.val.length = n)
    (hrange : ∀ i, i < n → -1000 ≤ elem x i ∧ elem x i ≤ elem y i ∧ elem y i ≤ 1000), ∀ rx ry, Aegis.MaxSatisfaction.max_satisfaction x = ok rx →
      Aegis.MaxSatisfaction.max_satisfaction y = ok ry → rx.val ≤ ry.val) := by
  sorry

/-- Let b be the array satisfaction sorted in non-increasing order: b_1 >= b_2 >= ... >= b_n (1-indexed). For 1 <= k <= n, let P_k = sum_{j=1}^{k} b_j. Then the function returns a result r, and r = sum_{k=1}^{n} max(0, P_k).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_7 (s : Slice Std.I64) (n : ℕ) (b : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (hb_perm : b.Perm (vals s)) (hb_sorted : SortedDesc b) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ r.val = prefixPositiveSum b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ) (b : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (hb_perm : b.Perm (vals s)) (hb_sorted : SortedDesc b), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ r.val = prefixPositiveSum b) := by
  sorry

/-- The function returns a result r, and r >= max(0, max_{0 <= i < n} satisfaction[i]).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_8 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      max 0 (listMax (vals s)) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      max 0 (listMax (vals s)) ≤ r.val) := by
  sorry

/-- The function returns a result r, and r >= sum_{j=1}^{n} j * a_j, where a is the array satisfaction sorted in non-decreasing order (a_1 <= a_2 <= ... <= a_n, 1-indexed).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_9 (s : Slice Std.I64) (n : ℕ) (a : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (ha_sorted : SortedAsc a) (ha_val : (a : Multiset ℤ) = (vals s : Multiset ℤ)) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ weightedSum a ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ) (a : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (ha_sorted : SortedAsc a) (ha_val : (a : Multiset ℤ) = (vals s : Multiset ℤ)), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧ weightedSum a ≤ r.val) := by
  sorry

/-- If the function returns r_x for x and r_y for y, then r_y >= r_x.
  Preconditions: Let n be an integer with 1 <= n < 500. Let x be an array of length n such that -1000 <= x[i] <= 1000 for all i in [0, n). Let v be an integer with -1000 <= v <= 1000. Let y be the array of length n+1 with y[i] = x[i] for 0 <= i < n and y[n] = v. -/
theorem spec_10 (n : ℕ) (hn : 1 ≤ n) (hn' : n < 500)
    (x y : Slice Std.I64) (v : ℤ)
    (hxlen : x.val.length = n) (hylen : y.val.length = n + 1)
    (hrange : ∀ i, i < n → -1000 ≤ elem x i ∧ elem x i ≤ 1000)
    (hv : -1000 ≤ v ∧ v ≤ 1000)
    (hy_prefix : ∀ i, i < n → elem y i = elem x i) (hy_last : elem y n = v) :
    ∀ rx ry, Aegis.MaxSatisfaction.max_satisfaction x = ok rx →
      Aegis.MaxSatisfaction.max_satisfaction y = ok ry → rx.val ≤ ry.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : ℕ) (hn : 1 ≤ n) (hn' : n < 500)
    (x y : Slice Std.I64) (v : ℤ)
    (hxlen : x.val.length = n) (hylen : y.val.length = n + 1)
    (hrange : ∀ i, i < n → -1000 ≤ elem x i ∧ elem x i ≤ 1000)
    (hv : -1000 ≤ v ∧ v ≤ 1000)
    (hy_prefix : ∀ i, i < n → elem y i = elem x i) (hy_last : elem y n = v), ∀ rx ry, Aegis.MaxSatisfaction.max_satisfaction x = ok rx →
      Aegis.MaxSatisfaction.max_satisfaction y = ok ry → rx.val ≤ ry.val) := by
  sorry

/-- For each k with 0 <= k <= n, let f(k) be the maximum over all injective sequences (i_1, ..., i_k) of indices in [0, n) of sum_{j=1}^{k} j * satisfaction[i_j]. The function returns a result r, and r = max_{0 <= k <= n} f(k). Moreover, for each k, f(k) = sum_{j=1}^{k} j * a_{n-k+j}, where a is the array satisfaction sorted in non-decreasing order (1-indexed).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_11 (s : Slice Std.I64) (n : ℕ) (a : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (ha_sorted : SortedAsc a) (ha_val : (a : Multiset ℤ) = (vals s : Multiset ℤ)) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val = bestOverLengths a ∧
      ∀ k, k ≤ n → IsMaxObjectiveOfLength s k (weightedSum (a.drop (n - k))) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ) (a : List ℤ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000)
    (ha_sorted : SortedAsc a) (ha_val : (a : Multiset ℤ) = (vals s : Multiset ℤ)), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val = bestOverLengths a ∧
      ∀ k, k ≤ n → IsMaxObjectiveOfLength s k (weightedSum (a.drop (n - k)))) := by
  sorry

/-- The function returns a result r, and there exists an integer k with 0 <= k <= n and an injective sequence (i_1, ..., i_k) of indices in [0, n) such that r = sum_{j=1}^{k} j * satisfaction[i_j].
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_12 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      ∃ (k : ℕ) (idx : List ℕ), k ≤ n ∧ idx.length = k ∧ IsIndexSeq s idx ∧
        r.val = seqValue s idx := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      ∃ (k : ℕ) (idx : List ℕ), k ≤ n ∧ idx.length = k ∧ IsIndexSeq s idx ∧
        r.val = seqValue s idx) := by
  sorry

/-- The function returns a result r, and r <= n * sum_{i=0}^{n-1} max(0, satisfaction[i]).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_13 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val ≤ (n : ℤ) * positiveSum (vals s) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      r.val ≤ (n : ℤ) * positiveSum (vals s)) := by
  sorry

/-- The function returns a result r, and r >= sum_{i=0}^{n-1} max(0, satisfaction[i]).
  Preconditions: Let n = len(satisfaction). The preconditions are: 1 <= n <= 500, and for every i with 0 <= i < n, -1000 <= satisfaction[i] <= 1000. -/
theorem spec_14 (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000) :
    ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      positiveSum (vals s) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.I64) (n : ℕ)
    (hlen : s.val.length = n) (hn : 1 ≤ n) (hn' : n ≤ 500)
    (hrange : ∀ i, i < n → -1000 ≤ elem s i ∧ elem s i ≤ 1000), ∃ r, Aegis.MaxSatisfaction.max_satisfaction s = ok r ∧
      positiveSum (vals s) ≤ r.val) := by
  sorry

end AegisSpec.MaxSatisfaction
