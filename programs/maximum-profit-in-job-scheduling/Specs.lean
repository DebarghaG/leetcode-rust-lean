import Aegis.JobScheduling.Code.Funs

/-!
# Specifications of `Aegis.JobScheduling.job_scheduling`

LeetCode problem `maximum-profit-in-job-scheduling`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.JobScheduling

namespace AegisSpec.JobScheduling

def ints (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def entry (s : Slice Std.I64) (i : ℕ) : ℤ := (ints s).getD i 0

def profitSum (profit : Slice Std.I64) (S : Finset ℕ) : ℤ := ∑ i ∈ S, entry profit i

def totalProfit (profit : Slice Std.I64) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, entry profit i

def PairwiseCompatible (startTime endTime : Slice Std.I64) (S : Finset ℕ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → entry endTime i ≤ entry startTime j ∨ entry endTime j ≤ entry startTime i

/-- Whenever job_scheduling(startTime, endTime, profit) returns a result r, r is the maximum of the set of all sums sum_{i in S} profit[i] over subsets S of {0,...,n-1} such that for every two distinct indices i,j in S, endTime[i] <= startTime[j] or endTime[j] <= startTime[i]. The empty subset is allowed and contributes 0.
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_1
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    (∃ S : Finset ℕ, S ⊆ Finset.range n ∧ PairwiseCompatible startTime endTime S ∧
        profitSum profit S = r.val) ∧
      ∀ S : Finset ℕ, S ⊆ Finset.range n → PairwiseCompatible startTime endTime S →
        profitSum profit S ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), (∃ S : Finset ℕ, S ⊆ Finset.range n ∧ PairwiseCompatible startTime endTime S ∧
        profitSum profit S = r.val) ∧
      ∀ S : Finset ℕ, S ⊆ Finset.range n → PairwiseCompatible startTime endTime S →
        profitSum profit S ≤ r.val) := by
  sorry

/-- For every input satisfying the preconditions, job_scheduling(startTime, endTime, profit) returns a result r; it does not fail, overflow, or panic.
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_2
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4) :
    ∃ r : Std.I64, job_scheduling startTime endTime profit = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4), ∃ r : Std.I64, job_scheduling startTime endTime profit = ok r) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns a result r, r <= sum_{i=0}^{n-1} profit[i].
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_3
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    r.val ≤ totalProfit profit n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), r.val ≤ totalProfit profit n) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns a result r, for every i with 0 <= i < n we have r >= profit[i].
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_4
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    ∀ i, i < n → entry profit i ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), ∀ i, i < n → entry profit i ≤ r.val) := by
  sorry

/-- If for every two distinct indices i,j with 0 <= i,j < n we have startTime[i] < endTime[j] and startTime[j] < endTime[i] (every two jobs overlap in positive time), then whenever job_scheduling(startTime, endTime, profit) returns a result r, r = max_{0 <= i < n} profit[i].
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_5
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → i ≠ j →
      entry startTime i < entry endTime j ∧ entry startTime j < entry endTime i)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    ∃ i, i < n ∧ entry profit i = r.val ∧ ∀ j, j < n → entry profit j ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hoverlap : ∀ i, i < n → ∀ j, j < n → i ≠ j →
      entry startTime i < entry endTime j ∧ entry startTime j < entry endTime i)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), ∃ i, i < n ∧ entry profit i = r.val ∧ ∀ j, j < n → entry profit j ≤ r.val) := by
  sorry

/-- If for every two distinct indices i,j with 0 <= i,j < n we have endTime[i] <= startTime[j] or endTime[j] <= startTime[i] (all jobs are pairwise compatible), then whenever job_scheduling(startTime, endTime, profit) returns a result r, r = sum_{i=0}^{n-1} profit[i].
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_6
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hcompatible : ∀ i, i < n → ∀ j, j < n → i ≠ j →
      entry endTime i ≤ entry startTime j ∨ entry endTime j ≤ entry startTime i)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    r.val = totalProfit profit n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hcompatible : ∀ i, i < n → ∀ j, j < n → i ≠ j →
      entry endTime i ≤ entry startTime j ∨ entry endTime j ≤ entry startTime i)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), r.val = totalProfit profit n) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit1) returns r1 and job_scheduling(startTime, endTime, profit2) returns r2, we have r1 <= r2.
  Preconditions: Let n = len(startTime) = len(endTime) = len(profit1) = len(profit2). We require 1 <= n <= 50000. Both (startTime, endTime, profit1) and (startTime, endTime, profit2) satisfy the problem constraints: for every i with 0 <= i < n, 1 <= startTime[i] < endTime[i] <= 10^9, 1 <= profit1[i] <= 10^4, 1 <= profit2[i] <= 10^4, and profit1[i] <= profit2[i]. -/
theorem spec_7
    (startTime endTime profit1 profit2 : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf1_len : profit1.val.length = n)
    (hpf2_len : profit2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits1 : ∀ i, i < n → 1 ≤ entry profit1 i ∧ entry profit1 i ≤ (10 : ℤ) ^ 4)
    (hprofits2 : ∀ i, i < n → 1 ≤ entry profit2 i ∧ entry profit2 i ≤ (10 : ℤ) ^ 4)
    (hle : ∀ i, i < n → entry profit1 i ≤ entry profit2 i)
    (r1 r2 : Std.I64)
    (hr1 : job_scheduling startTime endTime profit1 = ok r1)
    (hr2 : job_scheduling startTime endTime profit2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (startTime endTime profit1 profit2 : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf1_len : profit1.val.length = n)
    (hpf2_len : profit2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits1 : ∀ i, i < n → 1 ≤ entry profit1 i ∧ entry profit1 i ≤ (10 : ℤ) ^ 4)
    (hprofits2 : ∀ i, i < n → 1 ≤ entry profit2 i ∧ entry profit2 i ≤ (10 : ℤ) ^ 4)
    (hle : ∀ i, i < n → entry profit1 i ≤ entry profit2 i)
    (r1 r2 : Std.I64)
    (hr1 : job_scheduling startTime endTime profit1 = ok r1)
    (hr2 : job_scheduling startTime endTime profit2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns r and job_scheduling(startTime', endTime', profit') returns r', we have r = r'.
  Preconditions: Let n = len(startTime) = len(endTime) = len(profit). We require 1 <= n <= 50000 and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. Let π be any permutation of {0,...,n-1}. Define startTime', endTime', profit' of length n by startTime'[k] = startTime[π(k)], endTime'[k] = endTime[π(k)], profit'[k] = profit[π(k)] for 0 <= k < n. -/
theorem spec_8
    (startTime endTime profit : Slice Std.I64) (n : ℕ) (π : Equiv.Perm (Fin n))
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (startTime' endTime' profit' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n)
    (het_len' : endTime'.val.length = n)
    (hpf_len' : profit'.val.length = n)
    (hst' : ∀ k : Fin n, entry startTime' k = entry startTime (π k))
    (het' : ∀ k : Fin n, entry endTime' k = entry endTime (π k))
    (hpf' : ∀ k : Fin n, entry profit' k = entry profit (π k))
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ) (π : Equiv.Perm (Fin n))
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (startTime' endTime' profit' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n)
    (het_len' : endTime'.val.length = n)
    (hpf_len' : profit'.val.length = n)
    (hst' : ∀ k : Fin n, entry startTime' k = entry startTime (π k))
    (het' : ∀ k : Fin n, entry endTime' k = entry endTime (π k))
    (hpf' : ∀ k : Fin n, entry profit' k = entry profit (π k))
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns r and job_scheduling(startTime', endTime', profit) returns r', we have r = r'.
  Preconditions: Let n = len(startTime) = len(endTime) = len(profit). We require 1 <= n <= 50000 and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. Let c be an integer such that for every i with 0 <= i < n, 1 <= startTime[i] + c and endTime[i] + c <= 10^9. Define startTime'[i] = startTime[i] + c and endTime'[i] = endTime[i] + c for 0 <= i < n. -/
theorem spec_9
    (startTime endTime profit : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hc_low : ∀ i, i < n → 1 ≤ entry startTime i + c)
    (hc_high : ∀ i, i < n → entry endTime i + c ≤ (10 : ℤ) ^ 9)
    (startTime' endTime' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n)
    (het_len' : endTime'.val.length = n)
    (hst' : ∀ i, i < n → entry startTime' i = entry startTime i + c)
    (het' : ∀ i, i < n → entry endTime' i = entry endTime i + c)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hc_low : ∀ i, i < n → 1 ≤ entry startTime i + c)
    (hc_high : ∀ i, i < n → entry endTime i + c ≤ (10 : ℤ) ^ 9)
    (startTime' endTime' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n)
    (het_len' : endTime'.val.length = n)
    (hst' : ∀ i, i < n → entry startTime' i = entry startTime i + c)
    (het' : ∀ i, i < n → entry endTime' i = entry endTime i + c)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns r and job_scheduling(startTime, endTime, profit') returns r', we have r' = k * r.
  Preconditions: Let n = len(startTime) = len(endTime) = len(profit). We require 1 <= n <= 50000 and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. Let k be a positive integer such that for every i with 0 <= i < n, 1 <= k * profit[i] <= 10^4. Define profit'[i] = k * profit[i] for 0 <= i < n. -/
theorem spec_10
    (startTime endTime profit : Slice Std.I64) (n : ℕ) (k : ℤ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hk_pos : 1 ≤ k)
    (hk_bounds : ∀ i, i < n → 1 ≤ k * entry profit i ∧ k * entry profit i ≤ (10 : ℤ) ^ 4)
    (profit' : Slice Std.I64)
    (hpf_len' : profit'.val.length = n)
    (hpf' : ∀ i, i < n → entry profit' i = k * entry profit i)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime endTime profit' = ok r') :
    r'.val = k * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ) (k : ℤ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (hk_pos : 1 ≤ k)
    (hk_bounds : ∀ i, i < n → 1 ≤ k * entry profit i ∧ k * entry profit i ≤ (10 : ℤ) ^ 4)
    (profit' : Slice Std.I64)
    (hpf_len' : profit'.val.length = n)
    (hpf' : ∀ i, i < n → entry profit' i = k * entry profit i)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime endTime profit' = ok r'), r'.val = k * r.val) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns r and job_scheduling(startTime', endTime', profit') returns r', we have r' >= r.
  Preconditions: Let n = len(startTime) = len(endTime) = len(profit). We require 1 <= n <= 49999 (so that n+1 <= 50000) and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. Let s,e,p be integers with 1 <= s < e <= 10^9 and 1 <= p <= 10^4. Define startTime', endTime', profit' of length n+1 by startTime'[i] = startTime[i], endTime'[i] = endTime[i], profit'[i] = profit[i] for 0 <= i < n, and startTime'[n] = s, endTime'[n] = e, profit'[n] = p. -/
theorem spec_11
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 49999)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (s e p : ℤ)
    (hs_pos : 1 ≤ s) (hse : s < e) (he_bound : e ≤ (10 : ℤ) ^ 9)
    (hp_pos : 1 ≤ p) (hp_bound : p ≤ (10 : ℤ) ^ 4)
    (startTime' endTime' profit' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n + 1)
    (het_len' : endTime'.val.length = n + 1)
    (hpf_len' : profit'.val.length = n + 1)
    (hst' : ∀ i, i < n → entry startTime' i = entry startTime i)
    (het' : ∀ i, i < n → entry endTime' i = entry endTime i)
    (hpf' : ∀ i, i < n → entry profit' i = entry profit i)
    (hst_last : entry startTime' n = s)
    (het_last : entry endTime' n = e)
    (hpf_last : entry profit' n = p)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 49999)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (s e p : ℤ)
    (hs_pos : 1 ≤ s) (hse : s < e) (he_bound : e ≤ (10 : ℤ) ^ 9)
    (hp_pos : 1 ≤ p) (hp_bound : p ≤ (10 : ℤ) ^ 4)
    (startTime' endTime' profit' : Slice Std.I64)
    (hst_len' : startTime'.val.length = n + 1)
    (het_len' : endTime'.val.length = n + 1)
    (hpf_len' : profit'.val.length = n + 1)
    (hst' : ∀ i, i < n → entry startTime' i = entry startTime i)
    (het' : ∀ i, i < n → entry endTime' i = entry endTime i)
    (hpf' : ∀ i, i < n → entry profit' i = entry profit i)
    (hst_last : entry startTime' n = s)
    (het_last : entry endTime' n = e)
    (hpf_last : entry profit' n = p)
    (r r' : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r)
    (hr' : job_scheduling startTime' endTime' profit' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever job_scheduling(startTime, endTime, profit) returns a result r, there exists a subset S of {0,...,n-1} such that (a) for every two distinct indices i,j in S, endTime[i] <= startTime[j] or endTime[j] <= startTime[i], and (b) sum_{i in S} profit[i] = r.
  Preconditions: Let n = len(startTime). We require len(startTime) = len(endTime) = len(profit) = n, 1 <= n <= 50000, and for every i with 0 <= i < n: 1 <= startTime[i] < endTime[i] <= 10^9 and 1 <= profit[i] <= 10^4. -/
theorem spec_12
    (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r) :
    ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ PairwiseCompatible startTime endTime S ∧
      profitSum profit S = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (startTime endTime profit : Slice Std.I64) (n : ℕ)
    (hst_len : startTime.val.length = n)
    (het_len : endTime.val.length = n)
    (hpf_len : profit.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 50000)
    (hjobs : ∀ i, i < n →
      1 ≤ entry startTime i ∧ entry startTime i < entry endTime i ∧
        entry endTime i ≤ (10 : ℤ) ^ 9)
    (hprofits : ∀ i, i < n → 1 ≤ entry profit i ∧ entry profit i ≤ (10 : ℤ) ^ 4)
    (r : Std.I64)
    (hr : job_scheduling startTime endTime profit = ok r), ∃ S : Finset ℕ, S ⊆ Finset.range n ∧ PairwiseCompatible startTime endTime S ∧
      profitSum profit S = r.val) := by
  sorry

end AegisSpec.JobScheduling
