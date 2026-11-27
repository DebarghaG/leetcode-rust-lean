import Aegis.GroupThePeople.Code.Funs

/-!
# Specifications of `Aegis.GroupThePeople.group_the_people`

LeetCode problem `group-the-people-given-the-group-size-they-belong-to`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.GroupThePeople (group_the_people)

namespace AegisSpec.GroupThePeople

def countVal (l : List I64) (k : Int) : Nat :=
  (l.filter (fun p => p.val = k)).length

def countEq (groupSizes : Slice I64) (k : Int) : Nat :=
  countVal groupSizes.val k

def sliceGetInt (groupSizes : Slice I64) (i : Int) : Int :=
  match groupSizes.get? i.toNat with
  | some s => s.val
  | none => 0

def flattenOut (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List I64 :=
  r.val.flatMap (fun g => g.val)

/-- Let n = len(groupSizes). Whenever the function returns a result r (i.e. Ok r), the following hold: (a) for every index a with 0 <= a < len(r), len(r[a]) >= 1; (b) for every index a and j with 0 <= a < len(r) and 0 <= j < len(r[a]), 0 <= r[a][j] < n and len(r[a]) = groupSizes[r[a][j]]; (c) for every person i with 0 <= i < n, the number of pairs (a,j) with 0 <= a < len(r), 0 <= j < len(r[a]), and r[a][j] = i is exactly 1.
  Preconditions: Let n = len(groupSizes). 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, if C_k is the number of indices i with 0 <= i < n and groupSizes[i] = k, then C_k is a multiple of k. -/
theorem spec_1 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    (∀ (a : Nat) (ha : a < r.val.length), 1 ≤ (r.val[a]).val.length) ∧
    (∀ (a : Nat) (ha : a < r.val.length) (j : Nat) (hj : j < (r.val[a]).val.length),
      0 ≤ (r.val[a]).val[j].val ∧
      (r.val[a]).val[j].val < (groupSizes.val.length : Int) ∧
      ((r.val[a]).val.length : Int) = sliceGetInt groupSizes ((r.val[a]).val[j]).val) ∧
    (∀ (i : Nat), i < groupSizes.val.length → countVal (flattenOut r) (i : Int) = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), (∀ (a : Nat) (ha : a < r.val.length), 1 ≤ (r.val[a]).val.length) ∧
    (∀ (a : Nat) (ha : a < r.val.length) (j : Nat) (hj : j < (r.val[a]).val.length),
      0 ≤ (r.val[a]).val[j].val ∧
      (r.val[a]).val[j].val < (groupSizes.val.length : Int) ∧
      ((r.val[a]).val.length : Int) = sliceGetInt groupSizes ((r.val[a]).val[j]).val) ∧
    (∀ (i : Nat), i < groupSizes.val.length → countVal (flattenOut r) (i : Int) = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every group g in r and every element p of g, 0 <= p < n.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_2 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (p : I64), p ∈ g.val →
      0 ≤ p.val ∧ p.val < (groupSizes.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (p : I64), p ∈ g.val →
      0 ≤ p.val ∧ p.val < (groupSizes.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every group g in r, len(g) >= 1.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_3 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (g : alloc.vec.Vec I64), g ∈ r.val → 1 ≤ g.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (g : alloc.vec.Vec I64), g ∈ r.val → 1 ≤ g.val.length) := by
  sorry

/-- Whenever the function returns a result r, 1 <= len(r) <= n.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_4 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    1 ≤ r.val.length ∧ r.val.length ≤ groupSizes.val.length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), 1 ≤ r.val.length ∧ r.val.length ≤ groupSizes.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every group g in r and every element p of g, len(g) = groupSizes[p].
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_5 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (p : I64), p ∈ g.val →
      (g.val.length : Int) = sliceGetInt groupSizes p.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (p : I64), p ∈ g.val →
      (g.val.length : Int) = sliceGetInt groupSizes p.val) := by
  sorry

/-- Whenever the function returns a result r, for every two distinct groups g1 and g2 in r (i.e., at distinct positions in r), there is no person p such that p is an element of both g1 and g2.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_6 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (a₁ a₂ : Nat) (h₁ : a₁ < r.val.length) (h₂ : a₂ < r.val.length), a₁ ≠ a₂ →
      ∀ (p : I64), p ∈ (r.val[a₁]).val → p ∈ (r.val[a₂]).val → False := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (a₁ a₂ : Nat) (h₁ : a₁ < r.val.length) (h₂ : a₂ < r.val.length), a₁ ≠ a₂ →
      ∀ (p : I64), p ∈ (r.val[a₁]).val → p ∈ (r.val[a₂]).val → False) := by
  sorry

/-- Whenever the function returns a result r, for every person i with 0 <= i < n, there exists a group g in r and an index j with 0 <= j < len(g) such that g[j] = i.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_7 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (i : Nat), i < groupSizes.val.length →
      ∃ (g : alloc.vec.Vec I64), g ∈ r.val ∧
        ∃ (j : Nat) (hj : j < g.val.length), g.val[j].val = (i : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (i : Nat), i < groupSizes.val.length →
      ∃ (g : alloc.vec.Vec I64), g ∈ r.val ∧
        ∃ (j : Nat) (hj : j < g.val.length), g.val[j].val = (i : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every group g in r, for every two indices j1 and j2 with 0 <= j1 < j2 < len(g), g[j1] != g[j2].
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_8 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (j₁ j₂ : Nat) (h₁ : j₁ < g.val.length)
      (h₂ : j₂ < g.val.length), j₁ < j₂ → g.val[j₁] ≠ g.val[j₂] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (g : alloc.vec.Vec I64), g ∈ r.val → ∀ (j₁ j₂ : Nat) (h₁ : j₁ < g.val.length)
      (h₂ : j₂ < g.val.length), j₁ < j₂ → g.val[j₁] ≠ g.val[j₂]) := by
  sorry

/-- Whenever the function returns a result r, the sum over all groups g in r of len(g) equals n.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_9 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    (r.val.map (fun g => g.val.length)).sum = groupSizes.val.length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), (r.val.map (fun g => g.val.length)).sum = groupSizes.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k. Then the number of groups g in r with len(g) = k is exactly C_k / k.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_10 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r) :
    ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      (r.val.filter (fun g => g.val.length = k.toNat)).length
        = countEq groupSizes k / k.toNat := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k)
    (r : alloc.vec.Vec (alloc.vec.Vec I64))
    (hr : group_the_people groupSizes = ok r), ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      (r.val.filter (fun g => g.val.length = k.toNat)).length
        = countEq groupSizes k / k.toNat) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(groupSizes). The preconditions are: 1 <= n <= 500; for every i with 0 <= i < n, 1 <= groupSizes[i] <= n; and for every integer k with 1 <= k <= n, let C_k be the number of indices i with 0 <= i < n and groupSizes[i] = k; then C_k is a multiple of k. -/
theorem spec_11 (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k) :
    ∃ (r : alloc.vec.Vec (alloc.vec.Vec I64)), group_the_people groupSizes = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (groupSizes : Slice I64)
    (h_n_pos : 1 ≤ groupSizes.val.length)
    (h_n_le : groupSizes.val.length ≤ 500)
    (h_entry : ∀ (i : Nat) (hi : i < groupSizes.val.length),
      1 ≤ (groupSizes.val[i]).val ∧ (groupSizes.val[i]).val ≤ (groupSizes.val.length : Int))
    (h_count : ∀ (k : Int), 1 ≤ k → k ≤ (groupSizes.val.length : Int) →
      k.toNat ∣ countEq groupSizes k), ∃ (r : alloc.vec.Vec (alloc.vec.Vec I64)), group_the_people groupSizes = ok r) := by
  sorry

end AegisSpec.GroupThePeople
