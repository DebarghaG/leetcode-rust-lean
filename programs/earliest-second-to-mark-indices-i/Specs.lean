import Aegis.EarliestSecondToMarkIndices.Code.Funs

/-!
# Specifications of `Aegis.EarliestSecondToMarkIndices.earliest_second_to_mark_indices`

LeetCode problem `earliest-second-to-mark-indices-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EarliestSecondToMarkIndices

abbrev earliest (nums changeIndices : Slice I64) : Result I64 :=
  Aegis.EarliestSecondToMarkIndices.earliest_second_to_mark_indices nums changeIndices

def ValidInput (nums changeIndices : Slice I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 2000 ∧
  1 ≤ changeIndices.val.length ∧ changeIndices.val.length ≤ 2000 ∧
  (∀ (i : Nat) (x : I64), nums.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000) ∧
  (∀ (j : Nat) (x : I64),
      changeIndices.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ (nums.val.length : Int))

def Markable (nums changeIndices : Slice I64) (s : Nat) : Prop :=
  ∃ (t : Fin nums.val.length → Nat) (D : Fin nums.val.length → Finset Nat),
    (∀ i, 1 ≤ t i ∧ t i ≤ s) ∧
    (∀ i, ∃ x : I64, changeIndices.val[t i - 1]? = some x ∧ x.val = (i.val : Int) + 1) ∧
    (∀ i, D i ⊆ Finset.Icc 1 (t i - 1) ∧
      (D i).card = (nums.val.get ⟨i.val, i.isLt⟩).val.toNat) ∧
    (∀ i j, i ≠ j → Disjoint (D i) (D j)) ∧
    (∀ i j, t j ∉ D i) ∧
    (∀ i j, i ≠ j → t i ≠ t j)

def AllIndicesOccurBy (changeIndices : Slice I64) (n : Nat) (s : Nat) : Prop :=
  ∀ i : Nat, 1 ≤ i → i ≤ n →
    ∃ (j : Nat) (x : I64), j < s ∧ changeIndices.val[j]? = some x ∧ x.val = (i : Int)

def IsLastOccurrence (changeIndices : Slice I64) (r i p : Nat) : Prop :=
  1 ≤ p ∧ p ≤ r ∧
  (∃ x : I64, changeIndices.val[p - 1]? = some x ∧ x.val = (i : Int)) ∧
  (∀ p' : Nat, p < p' → p' ≤ r →
    ∀ x : I64, changeIndices.val[p' - 1]? = some x → x.val ≠ (i : Int))

/-- The function returns a result r (it does not fail), and r is the earliest second in the following sense. For s with 1 <= s <= m, call s markable if there exist pairwise distinct seconds t_1,...,t_n in {1,...,s} and, for each i in {1,...,n}, a set D_i of exactly nums[i-1] distinct seconds contained in {1,...,t_i-1}, such that change_indices[t_i-1] = i for every i, and the sets D_1,...,D_n together with the singleton sets {t_1},...,{t_n} are pairwise disjoint. If some s in {1,...,m} is markable, r is the least such s; otherwise r = -1.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_1 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∃ r : I64,
      earliest nums changeIndices = ok r ∧
      ((∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s) →
        (∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s ∧
          r.val = (s : Int) ∧
          (∀ s' : Nat, 1 ≤ s' → s' < s → ¬ Markable nums changeIndices s'))) ∧
      (¬ (∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s) →
        r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∃ r : I64,
      earliest nums changeIndices = ok r ∧
      ((∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s) →
        (∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s ∧
          r.val = (s : Int) ∧
          (∀ s' : Nat, 1 ≤ s' → s' < s → ¬ Markable nums changeIndices s'))) ∧
      (¬ (∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧ Markable nums changeIndices s) →
        r.val = -1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow occurs).
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_2 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∃ r : I64, earliest nums changeIndices = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∃ r : I64, earliest nums changeIndices = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= m.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_3 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (changeIndices.val.length : Int))) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      (r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (changeIndices.val.length : Int)))) := by
  sorry

/-- Let n = len(nums) and m = len(change_indices). For 1 <= s <= m, say s is markable iff there exist pairwise distinct seconds t_1,...,t_n in {1,...,s} and, for each i in {1,...,n}, a set D_i of exactly nums[i-1] distinct seconds contained in {1,...,t_i-1}, such that change_indices[t_i-1] = i for every i, and the sets D_1,...,D_n together with the singleton sets {t_1},...,{t_n} are pairwise disjoint. Whenever the function returns a result r with r != -1, r is markable.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_4 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      Markable nums changeIndices r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      Markable nums changeIndices r.val.toNat) := by
  sorry

/-- Using the definition of markable from spec_4, whenever the function returns a result r with r != -1, for every s with 1 <= s < r, s is not markable.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_5 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∀ s : Nat, 1 ≤ s → s < r.val.toNat → ¬ Markable nums changeIndices s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∀ s : Nat, 1 ≤ s → s < r.val.toNat → ¬ Markable nums changeIndices s) := by
  sorry

/-- Using the definition of markable from spec_4, whenever the function returns a result r, r = -1 iff for every s with 1 <= s <= m, s is not markable.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_6 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      (r.val = -1 ↔
        ∀ s : Nat, 1 ≤ s → s ≤ changeIndices.val.length → ¬ Markable nums changeIndices s) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      (r.val = -1 ↔
        ∀ s : Nat, 1 ≤ s → s ≤ changeIndices.val.length → ¬ Markable nums changeIndices s)) := by
  sorry

/-- Whenever the function returns a result r, if there is an index i with 1 <= i <= n such that for every j with 0 <= j < m, change_indices[j] != i, then r = -1.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_7 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      (∃ i : Nat, 1 ≤ i ∧ i ≤ nums.val.length ∧
        (∀ (j : Nat) (x : I64), changeIndices.val[j]? = some x → x.val ≠ (i : Int))) →
      r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      (∃ i : Nat, 1 ≤ i ∧ i ≤ nums.val.length ∧
        (∀ (j : Nat) (x : I64), changeIndices.val[j]? = some x → x.val ≠ (i : Int))) →
      r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] = 0 for every i with 0 <= i < n, then r is the least s in {1,...,m} such that every index i in {1,...,n} occurs among change_indices[0],...,change_indices[s-1]; if no such s exists, then r = -1.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_8 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      (∀ (i : Nat) (x : I64), nums.val[i]? = some x → x.val = 0) →
      ((∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧
          AllIndicesOccurBy changeIndices nums.val.length s ∧
          r.val = (s : Int) ∧
          (∀ s' : Nat, 1 ≤ s' → s' < s →
            ¬ AllIndicesOccurBy changeIndices nums.val.length s')) ∨
        (¬ (∃ s : Nat,
            1 ≤ s ∧ s ≤ changeIndices.val.length ∧
            AllIndicesOccurBy changeIndices nums.val.length s) ∧
          r.val = -1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      (∀ (i : Nat) (x : I64), nums.val[i]? = some x → x.val = 0) →
      ((∃ s : Nat,
          1 ≤ s ∧ s ≤ changeIndices.val.length ∧
          AllIndicesOccurBy changeIndices nums.val.length s ∧
          r.val = (s : Int) ∧
          (∀ s' : Nat, 1 ≤ s' → s' < s →
            ¬ AllIndicesOccurBy changeIndices nums.val.length s')) ∨
        (¬ (∃ s : Nat,
            1 ≤ s ∧ s ≤ changeIndices.val.length ∧
            AllIndicesOccurBy changeIndices nums.val.length s) ∧
          r.val = -1))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, n + sum_{i=0}^{n-1} nums[i] <= r.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_9 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      (nums.val.length : Int) + (nums.val.map (fun x => x.val)).sum ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      (nums.val.length : Int) + (nums.val.map (fun x => x.val)).sum ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every index i with 1 <= i <= n there exists j with 0 <= j < r and change_indices[j] = i.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_10 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∀ i : Nat, 1 ≤ i → i ≤ nums.val.length →
        ∃ (j : Nat) (x : I64), j < r.val.toNat ∧ changeIndices.val[j]? = some x ∧
          x.val = (i : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∀ i : Nat, 1 ≤ i → i ≤ nums.val.length →
        ∃ (j : Nat) (x : I64), j < r.val.toNat ∧ changeIndices.val[j]? = some x ∧
          x.val = (i : Int)) := by
  sorry

/-- Whenever the function returns a result r, if n + sum_{i=0}^{n-1} nums[i] > m, then r = -1.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_11 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      (nums.val.length : Int) + (nums.val.map (fun x => x.val)).sum >
        (changeIndices.val.length : Int) →
      r.val = -1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      (nums.val.length : Int) + (nums.val.map (fun x => x.val)).sum >
        (changeIndices.val.length : Int) →
      r.val = -1) := by
  sorry

/-- Whenever the function returns a result r, if m < n, then r = -1.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_12 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r →
      changeIndices.val.length < nums.val.length → r.val = -1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r →
      changeIndices.val.length < nums.val.length → r.val = -1) := by
  sorry

/-- Let ans(A) denote the value returned by the function on (A, change_indices), for any array A of length n with 0 <= A[i] <= 1000000000 for all i. For any two such arrays A and B, if A[i] <= B[i] for every i with 0 <= i < n, then ans(A) is no later than ans(B), treating -1 as +infinity: explicitly, if ans(B) != -1 then ans(A) != -1 and ans(A) <= ans(B), and if ans(B) = -1 there is no additional restriction.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_13 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices)
    (A B : Slice I64)
    (hA : A.val.length = nums.val.length) (hB : B.val.length = nums.val.length)
    (hAb : ∀ (i : Nat) (x : I64), A.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hBb : ∀ (i : Nat) (x : I64), B.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hle : ∀ (i : Nat) (x y : I64), A.val[i]? = some x → B.val[i]? = some y → x.val ≤ y.val) :
    ∀ rA rB : I64,
      earliest A changeIndices = ok rA →
      earliest B changeIndices = ok rB →
      (rB.val ≠ -1 → rA.val ≠ -1 ∧ rA.val ≤ rB.val) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices)
    (A B : Slice I64)
    (hA : A.val.length = nums.val.length) (hB : B.val.length = nums.val.length)
    (hAb : ∀ (i : Nat) (x : I64), A.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hBb : ∀ (i : Nat) (x : I64), B.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (hle : ∀ (i : Nat) (x y : I64), A.val[i]? = some x → B.val[i]? = some y → x.val ≤ y.val), ∀ rA rB : I64,
      earliest A changeIndices = ok rA →
      earliest B changeIndices = ok rB →
      (rB.val ≠ -1 → rA.val ≠ -1 ∧ rA.val ≤ rB.val)) := by
  sorry

/-- Fix any array A of length n with 0 <= A[i] <= 1000000000 for all i. Let ans(C) denote the value returned by the function on (A,C) for any nonempty list C of length at most 2000 whose entries lie in {1,...,n}. For any two such lists C and C' (both nonempty, length at most 2000, entries in {1,...,n}) such that C' extends C (len(C) <= len(C') and C'[j] = C[j] for every 0 <= j < len(C)), ans(C') is no later than ans(C) when -1 is treated as +infinity: explicitly, if ans(C) != -1 then ans(C') != -1 and ans(C') <= ans(C), and if ans(C) = -1 there is no additional restriction.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_14 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices)
    (A : Slice I64) (hA : A.val.length = nums.val.length)
    (hAb : ∀ (i : Nat) (x : I64), A.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (C C' : Slice I64)
    (hC : 1 ≤ C.val.length ∧ C.val.length ≤ 2000 ∧
      (∀ (j : Nat) (x : I64), C.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ (nums.val.length : Int)))
    (hC' : 1 ≤ C'.val.length ∧ C'.val.length ≤ 2000 ∧
      (∀ (j : Nat) (x : I64), C'.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ (nums.val.length : Int)))
    (hext : C.val.length ≤ C'.val.length ∧
      ∀ (j : Nat) (x : I64), C.val[j]? = some x → C'.val[j]? = some x) :
    ∀ r r' : I64,
      earliest A C = ok r →
      earliest A C' = ok r' →
      (r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices)
    (A : Slice I64) (hA : A.val.length = nums.val.length)
    (hAb : ∀ (i : Nat) (x : I64), A.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 1000000000)
    (C C' : Slice I64)
    (hC : 1 ≤ C.val.length ∧ C.val.length ≤ 2000 ∧
      (∀ (j : Nat) (x : I64), C.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ (nums.val.length : Int)))
    (hC' : 1 ≤ C'.val.length ∧ C'.val.length ≤ 2000 ∧
      (∀ (j : Nat) (x : I64), C'.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ (nums.val.length : Int)))
    (hext : C.val.length ≤ C'.val.length ∧
      ∀ (j : Nat) (x : I64), C.val[j]? = some x → C'.val[j]? = some x), ∀ r r' : I64,
      earliest A C = ok r →
      earliest A C' = ok r' →
      (r.val ≠ -1 → r'.val ≠ -1 ∧ r'.val ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for each index i in {1,...,n} let p_i be the last second in {1,...,r} with change_indices[p_i-1] = i. Order the indices as i_1,...,i_n so that p_{i_1} < p_{i_2} < ... < p_{i_n}. Then for every k with 1 <= k <= n, sum_{h=1}^{k} (nums[i_h-1] + 1) <= p_{i_k}.
  Preconditions: Let n = len(nums) and m = len(change_indices). Assume 1 <= n <= 2000, 1 <= m <= 2000, for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000, and for every j with 0 <= j < m, 1 <= change_indices[j] <= n. -/
theorem spec_15 (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices) :
    ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∃ p : Fin nums.val.length → Nat,
        (∀ i, IsLastOccurrence changeIndices r.val.toNat (i.val + 1) (p i)) ∧
        (∀ i : Fin nums.val.length,
          (∑ j ∈ Finset.univ.filter (fun j => p j < p i),
              ((nums.val.get j).val + 1)) +
            ((nums.val.get i).val + 1) ≤ (p i : Int)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums changeIndices : Slice I64) (hpre : ValidInput nums changeIndices), ∀ r : I64, earliest nums changeIndices = ok r → r.val ≠ -1 →
      ∃ p : Fin nums.val.length → Nat,
        (∀ i, IsLastOccurrence changeIndices r.val.toNat (i.val + 1) (p i)) ∧
        (∀ i : Fin nums.val.length,
          (∑ j ∈ Finset.univ.filter (fun j => p j < p i),
              ((nums.val.get j).val + 1)) +
            ((nums.val.get i).val + 1) ≤ (p i : Int))) := by
  sorry

end AegisSpec.EarliestSecondToMarkIndices
