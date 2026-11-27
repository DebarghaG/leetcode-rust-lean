import Aegis.MaxNumberOfApples.Code.Funs

/-!
# Specifications of `Aegis.MaxNumberOfApples.max_number_of_apples`

LeetCode problem `how-many-apples-can-you-put-into-the-basket`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxNumberOfApples

  open Aeneas Aeneas.Std Result
  open Aegis.MaxNumberOfApples

  def weightAt (weight : Slice Std.I64) (i : ℕ) : ℤ :=
    match weight.val[i]? with
    | some x => x.val
    | none => 0

  def weightSum (weight : Slice Std.I64) (S : Finset ℕ) : ℤ :=
    ∑ i ∈ S, weightAt weight i

  def prefixSum (s : List Std.I64) (k : ℕ) : ℤ :=
    ((s.take k).map (fun x => x.val)).sum

  def IsSortedArrangement (l s : List Std.I64) : Prop :=
    s.length = l.length ∧ s.Perm l ∧ s.Pairwise (fun x y => x ≤ y)

  /-- The function returns a result r. Let I = {i | 0 <= i < len(weight)}. For a set S of indices, define sum(S) to be the sum of weight[i] over all i in S, with sum(empty) = 0. Then r is the maximum cardinality of a subset S of I such that sum(S) <= 5000. Equivalently: (1) there exists S subset of I with |S| = r and sum(S) <= 5000; and (2) for every T subset of I with sum(T) <= 5000, |T| <= r.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_1 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
        (∃ S : Finset ℕ, S ⊆ Finset.range weight.val.length ∧ (S.card : ℤ) = r.val ∧
          weightSum weight S ≤ 5000) ∧
        (∀ T : Finset ℕ, T ⊆ Finset.range weight.val.length → weightSum weight T ≤ 5000 →
          (T.card : ℤ) ≤ r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
          (∃ S : Finset ℕ, S ⊆ Finset.range weight.val.length ∧ (S.card : ℤ) = r.val ∧
            weightSum weight S ≤ 5000) ∧
          (∀ T : Finset ℕ, T ⊆ Finset.range weight.val.length → weightSum weight T ≤ 5000 →
            (T.card : ℤ) ≤ r.val)) := by
    sorry

  /-- The function returns a result r; in particular it does not fail, panic, overflow, or access an out-of-range index on any input satisfying the preconditions.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_2 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r) := by
    sorry

  /-- Whenever the function returns a result r, interpreting r as a natural number, 0 <= r <= len(weight).
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_3 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∀ r : Std.I64, max_number_of_apples weight = ok r →
        0 ≤ r.val ∧ r.val ≤ (weight.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∀ r : Std.I64, max_number_of_apples weight = ok r →
          0 ≤ r.val ∧ r.val ≤ (weight.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k <= r there exists a subset S of {i | 0 <= i < len(weight)} such that |S| = k and sum_{i in S} weight[i] <= 5000.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_4 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∀ r : Std.I64, max_number_of_apples weight = ok r →
        ∀ k : ℤ, 0 ≤ k → k ≤ r.val →
          ∃ S : Finset ℕ, S ⊆ Finset.range weight.val.length ∧ (S.card : ℤ) = k ∧
            weightSum weight S ≤ 5000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∀ r : Std.I64, max_number_of_apples weight = ok r →
          ∀ k : ℤ, 0 ≤ k → k ≤ r.val →
            ∃ S : Finset ℕ, S ⊆ Finset.range weight.val.length ∧ (S.card : ℤ) = k ∧
              weightSum weight S ≤ 5000) := by
    sorry

  /-- Whenever the function returns a result r, every subset T of {i | 0 <= i < len(weight)} with |T| = r + 1 has sum_{i in T} weight[i] > 5000. If r + 1 > len(weight), there are no such T and the condition is vacuous.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_5 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∀ r : Std.I64, max_number_of_apples weight = ok r →
        ∀ T : Finset ℕ, T ⊆ Finset.range weight.val.length → (T.card : ℤ) = r.val + 1 →
          5000 < weightSum weight T := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∀ r : Std.I64, max_number_of_apples weight = ok r →
          ∀ T : Finset ℕ, T ⊆ Finset.range weight.val.length → (T.card : ℤ) = r.val + 1 →
            5000 < weightSum weight T) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_6 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = min(len(weight), 5).
    Preconditions: 1 <= len(weight) <= 10^3 (1000), for every i with 0 <= i < len(weight), weight[i] = 1000. -/
  theorem spec_7 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → weightAt weight i = 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
        r.val = min (weight.val.length : ℤ) 5 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → weightAt weight i = 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
          r.val = min (weight.val.length : ℤ) 5) := by
    sorry

  /-- The function returns a result r, and r = len(weight) if and only if sum_{i=0}^{len(weight)-1} weight[i] <= 5000.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_8 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
        (r.val = (weight.val.length : ℤ) ↔
          weightSum weight (Finset.range weight.val.length) ≤ 5000) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
          (r.val = (weight.val.length : ℤ) ↔
            weightSum weight (Finset.range weight.val.length) ≤ 5000)) := by
    sorry

  /-- Whenever the call on weight returns r and the call on weight' returns r', we have r <= r' <= r + 1.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000); p is an integer with 1 <= p <= 1000; and len(weight) + 1 <= 1000. Let weight' be the slice with len(weight') = len(weight) + 1, weight'[i] = weight[i] for 0 <= i < len(weight), and weight'[len(weight)] = p. -/
  theorem spec_9 (weight weight' : Slice Std.I64) (p : Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
      (hp_lo : 1 ≤ p.val) (hp_hi : p.val ≤ 1000)
      (hlen_succ : weight.val.length + 1 ≤ 1000)
      (hweight' : weight'.val = weight.val ++ [p]) :
      ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
        max_number_of_apples weight' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (weight weight' : Slice Std.I64) (p : Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
        (hp_lo : 1 ≤ p.val) (hp_hi : p.val ≤ 1000)
        (hlen_succ : weight.val.length + 1 ≤ 1000)
        (hweight' : weight'.val = weight.val ++ [p]), ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
          max_number_of_apples weight' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
    sorry

  /-- Whenever the call on weight returns r and the call on weight' returns r', we have r' <= r.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). Let weight' be another slice with the same length such that for every i with 0 <= i < len(weight), 1 <= weight'[i] <= 1000 and weight[i] <= weight'[i]. -/
  theorem spec_10 (weight weight' : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
      (hlen_eq : weight'.val.length = weight.val.length)
      (hw' : ∀ i, i < weight'.val.length → 1 ≤ weightAt weight' i ∧ weightAt weight' i ≤ 1000)
      (hle : ∀ i, i < weight.val.length → weightAt weight i ≤ weightAt weight' i) :
      ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
        max_number_of_apples weight' = ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (weight weight' : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
        (hlen_eq : weight'.val.length = weight.val.length)
        (hw' : ∀ i, i < weight'.val.length → 1 ≤ weightAt weight' i ∧ weightAt weight' i ≤ 1000)
        (hle : ∀ i, i < weight.val.length → weightAt weight i ≤ weightAt weight' i), ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
          max_number_of_apples weight' = ok r' → r'.val ≤ r.val) := by
    sorry

  /-- Whenever the call on weight returns r and the call on weight' returns r', we have r = r'.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). Let weight' be another slice of the same length such that there is a bijection pi from {0,...,len(weight)-1} to itself with weight'[i] = weight[pi(i)] for every i. -/
  theorem spec_11 (weight weight' : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
      (hlen_eq : weight'.val.length = weight.val.length)
      (hperm : ∃ σ : Equiv.Perm (Fin weight.val.length),
        weight'.val = List.ofFn (fun i => weight.val.get (σ i))) :
      ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
        max_number_of_apples weight' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (weight weight' : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000)
        (hlen_eq : weight'.val.length = weight.val.length)
        (hperm : ∃ σ : Equiv.Perm (Fin weight.val.length),
          weight'.val = List.ofFn (fun i => weight.val.get (σ i))), ∀ r r' : Std.I64, max_number_of_apples weight = ok r →
          max_number_of_apples weight' = ok r' → r.val = r'.val) := by
    sorry

  /-- The function returns a result r. Let s be the list obtained by sorting the entries of weight in nondecreasing order, so len(s) = len(weight) and s has the same multiset of values as weight. Then the sum s[0] + ... + s[r-1] is at most 5000 (this sum is empty and equals 0 if r = 0), and if r < len(weight), then also s[0] + ... + s[r] is greater than 5000.
    Preconditions: 1 <= len(weight) <= 10^3 (1000), and for every i with 0 <= i < len(weight), 1 <= weight[i] <= 10^3 (1000). -/
  theorem spec_12 (weight : Slice Std.I64)
      (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
      (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000) :
      ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
        ∃ s : List Std.I64, IsSortedArrangement weight.val s ∧
          prefixSum s r.val.toNat ≤ 5000 ∧
          (r.val < (weight.val.length : ℤ) → 5000 < prefixSum s (r.val.toNat + 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (weight : Slice Std.I64)
        (hlen_pos : 1 ≤ weight.val.length) (hlen_le : weight.val.length ≤ 1000)
        (hw : ∀ i, i < weight.val.length → 1 ≤ weightAt weight i ∧ weightAt weight i ≤ 1000), ∃ r : Std.I64, max_number_of_apples weight = ok r ∧
          ∃ s : List Std.I64, IsSortedArrangement weight.val s ∧
            prefixSum s r.val.toNat ≤ 5000 ∧
            (r.val < (weight.val.length : ℤ) → 5000 < prefixSum s (r.val.toNat + 1))) := by
    sorry

  end AegisSpec.MaxNumberOfApples
