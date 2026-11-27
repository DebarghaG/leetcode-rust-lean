import Aegis.ConstructArray.Code.Funs

/-!
# Specifications of `Aegis.ConstructArray.construct_array`

LeetCode problem `beautiful-arrangement-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ConstructArray

  def entries (r : alloc.vec.Vec Std.I64) : List ℤ :=
    r.val.map (fun x => x.val)

  def entryAt (r : alloc.vec.Vec Std.I64) (i : ℕ) (hi : i < r.val.length) : ℤ :=
    (r.val[i]'hi).val

  def adjDiffs (r : alloc.vec.Vec Std.I64) : List ℤ :=
    List.zipWith (fun a b => |a.val - b.val|) r.val r.val.tail

  def adjDiffSet (r : alloc.vec.Vec Std.I64) : Finset ℤ :=
    (adjDiffs r).toFinset

  theorem adjDiffs_length (r : alloc.vec.Vec Std.I64) :
      (adjDiffs r).length = r.val.length - 1 := by
    unfold adjDiffs
    rw [List.length_zipWith, List.length_tail]
    omega

  theorem adjDiffs_getElem (r : alloc.vec.Vec Std.I64) (i : ℕ) (hi : i + 1 < r.val.length) :
      (adjDiffs r).get ⟨i, by rw [adjDiffs_length]; omega⟩
        = |(r.val[i]'(by omega)).val - (r.val[i + 1]'hi).val| := by
    unfold adjDiffs
    rw [List.get_eq_getElem, List.getElem_zipWith]
    simp [List.getElem_tail]

  def occursOnce (v : ℤ) (r : alloc.vec.Vec Std.I64) : Prop :=
    ∃! i : ℕ, (r.val[i]?).map (fun x => x.val) = some v

  def isMinEntry (v : ℤ) (r : alloc.vec.Vec Std.I64) : Prop :=
    (entries r).min? = some v

  def isMaxEntry (v : ℤ) (r : alloc.vec.Vec Std.I64) : Prop :=
    (entries r).max? = some v

  /-- construct_array n k returns a result r, and the following hold: (a) len(r) = n; (b) for every i with 0 <= i < len(r), 1 <= r[i] <= n; (c) for all i, j with 0 <= i < j < len(r), r[i] != r[j]; (d) for D = { |r[i] - r[i+1]| : 0 <= i < len(r)-1 }, the cardinality |D| is exactly k. Consequently r is a permutation of the integers 1,2,...,n and the adjacent absolute differences have exactly k distinct values.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_1 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.ConstructArray.construct_array n k = ok r ∧
          (r.val.length : ℤ) = n.val ∧
          (∀ (i : ℕ) (hi : i < r.val.length), 1 ≤ entryAt r i hi ∧ entryAt r i hi ≤ n.val) ∧
          (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
            i < j → entryAt r i hi ≠ entryAt r j hj) ∧
          ((adjDiffSet r).card : ℤ) = k.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.ConstructArray.construct_array n k = ok r ∧
            (r.val.length : ℤ) = n.val ∧
            (∀ (i : ℕ) (hi : i < r.val.length), 1 ≤ entryAt r i hi ∧ entryAt r i hi ≤ n.val) ∧
            (∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
              i < j → entryAt r i hi ≠ entryAt r j hj) ∧
            ((adjDiffSet r).card : ℤ) = k.val) := by
    sorry

  /-- For every such n and k, construct_array n k returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_2 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.ConstructArray.construct_array n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64, Aegis.ConstructArray.construct_array n k = ok r) := by
    sorry

  /-- Whenever construct_array n k returns a result r, len(r) = n.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_3 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      (r.val.length : ℤ) = n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), (r.val.length : ℤ) = n.val) := by
    sorry

  /-- Whenever construct_array n k returns a result r, for every index i with 0 <= i < len(r), we have 1 <= r[i] <= n.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_4 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∀ (i : ℕ) (hi : i < r.val.length), 1 ≤ entryAt r i hi ∧ entryAt r i hi ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∀ (i : ℕ) (hi : i < r.val.length), 1 ≤ entryAt r i hi ∧ entryAt r i hi ≤ n.val) := by
    sorry

  /-- Whenever construct_array n k returns a result r, for all indices i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_5 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
        i < j → entryAt r i hi ≠ entryAt r j hj := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∀ (i j : ℕ) (hi : i < r.val.length) (hj : j < r.val.length),
          i < j → entryAt r i hi ≠ entryAt r j hj) := by
    sorry

  /-- Whenever construct_array n k returns a result r, for every value v with 1 <= v <= n there exists exactly one index i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_6 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∀ v : ℤ, 1 ≤ v → v ≤ n.val → occursOnce v r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∀ v : ℤ, 1 ≤ v → v ≤ n.val → occursOnce v r) := by
    sorry

  /-- Whenever construct_array n k returns a result r, for every i with 0 <= i < len(r)-1, |r[i] - r[i+1]| > 0.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_7 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∀ d ∈ adjDiffs r, 0 < d := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∀ d ∈ adjDiffs r, 0 < d) := by
    sorry

  /-- Whenever construct_array n k returns a result r, for every i with 0 <= i < len(r)-1, |r[i] - r[i+1]| <= n-1.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_8 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∀ d ∈ adjDiffs r, d ≤ n.val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∀ d ∈ adjDiffs r, d ≤ n.val - 1) := by
    sorry

  /-- Whenever construct_array n k returns a result r, there exists a finite set T of positive integers such that |T| <= k and for every i with 0 <= i < len(r)-1, |r[i] - r[i+1]| is an element of T.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_9 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      ∃ T : Finset ℤ, (T.card : ℤ) ≤ k.val ∧ (∀ x ∈ T, 0 < x) ∧
        ∀ d ∈ adjDiffs r, d ∈ T := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), ∃ T : Finset ℤ, (T.card : ℤ) ≤ k.val ∧ (∀ x ∈ T, 0 < x) ∧
          ∀ d ∈ adjDiffs r, d ∈ T) := by
    sorry

  /-- Whenever construct_array n k returns a result r, let D = { |r[i] - r[i+1]| : 0 <= i < len(r)-1 }. Then |D| >= k.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_10 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      k.val ≤ ((adjDiffSet r).card : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), k.val ≤ ((adjDiffSet r).card : ℤ)) := by
    sorry

  /-- Whenever construct_array n k returns a result r, the sum of all entries of r, interpreted as mathematical integers, satisfies sum_{i=0}^{len(r)-1} r[i] = n*(n+1)/2.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_11 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      (entries r).sum = n.val * (n.val + 1) / 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), (entries r).sum = n.val * (n.val + 1) / 2) := by
    sorry

  /-- Whenever construct_array n k returns a result r, the minimum entry of r is 1 and the maximum entry of r is n.
    Preconditions: n and k are Std.I64 values satisfying 1 <= k < n <= 10000. -/
  theorem spec_12 (n k : Std.I64)
      (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
      (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r) :
      isMinEntry 1 r ∧ isMaxEntry n.val r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n k : Std.I64)
        (hk : 1 ≤ k.val) (hkn : k.val < n.val) (hn : n.val ≤ 10000)
        (r : alloc.vec.Vec Std.I64) (hr : Aegis.ConstructArray.construct_array n k = ok r), isMinEntry 1 r ∧ isMaxEntry n.val r) := by
    sorry

  end AegisSpec.ConstructArray
