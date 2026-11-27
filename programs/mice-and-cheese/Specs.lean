import Aegis.MiceAndCheese.Code.Funs

/-!
# Specifications of `Aegis.MiceAndCheese.mice_and_cheese`

LeetCode problem `mice-and-cheese`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MiceAndCheese
open scoped BigOperators

namespace AegisSpec.MiceAndCheese

def valAt (s : Slice Std.I64) (i : Nat) : Int := (s.val.getD i 0#i64).val

def total (reward1 reward2 : Slice Std.I64) (n : Nat) (S : Finset (Fin n)) : Int :=
  (∑ i ∈ S, valAt reward1 i.val) + (∑ i ∈ Sᶜ, valAt reward2 i.val)

def sumRange (reward : Slice Std.I64) (n : Nat) : Int :=
  ∑ i ∈ Finset.range n, valAt reward i

def sumMin (reward1 reward2 : Slice Std.I64) (n : Nat) : Int :=
  ∑ i ∈ Finset.range n, min (valAt reward1 i) (valAt reward2 i)

def sumMax (reward1 reward2 : Slice Std.I64) (n : Nat) : Int :=
  ∑ i ∈ Finset.range n, max (valAt reward1 i) (valAt reward2 i)

def diffList (reward1 reward2 : Slice Std.I64) : List Int :=
  reward1.val.zipWith (fun a b => a.val - b.val) reward2.val

def sumTop (k : Nat) (l : List Int) : Int :=
  List.sum (List.take k (List.mergeSort l (fun a b => decide (b ≤ a))))

/-- Whenever the function returns a result r, the following holds. For a subset S of indices {0,...,n-1}, define total(S) = sum_{i in S} reward1[i] + sum_{i notin S} reward2[i]. Then (a) there exists S with |S| = k and total(S) = r, and (b) for every T subset of {0,...,n-1} with |T| = k, total(T) <= r.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_1 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      (∃ S : Finset (Fin n),
          (S.card : Int) = k.val ∧ total reward1 reward2 n S = r.val) ∧
        (∀ T : Finset (Fin n),
          (T.card : Int) = k.val → total reward1 reward2 n T ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      (∃ S : Finset (Fin n),
          (S.card : Int) = k.val ∧ total reward1 reward2 n S = r.val) ∧
        (∀ T : Finset (Fin n),
          (T.card : Int) = k.val → total reward1 reward2 n T ≤ r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access an index out of bounds.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_2 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∃ r, mice_and_cheese reward1 reward2 k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∃ r, mice_and_cheese reward1 reward2 k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{n-1} min(reward1[i], reward2[i]).
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_3 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      sumMin reward1 reward2 n ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      sumMin reward1 reward2 n ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} max(reward1[i], reward2[i]).
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_4 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      r.val ≤ sumMax reward1 reward2 n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      r.val ≤ sumMax reward1 reward2 n) := by
  sorry

/-- Whenever the function returns a result r, if there exist integers c1 and c2 such that reward1[i] = c1 and reward2[i] = c2 for every i with 0 <= i < n, then r = k*c1 + (n-k)*c2.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_5 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      ∀ c1 c2 : Int,
        (∀ i, i < n → valAt reward1 i = c1 ∧ valAt reward2 i = c2) →
          r.val = k.val * c1 + ((n : Int) - k.val) * c2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      ∀ c1 c2 : Int,
        (∀ i, i < n → valAt reward1 i = c1 ∧ valAt reward2 i = c2) →
          r.val = k.val * c1 + ((n : Int) - k.val) * c2) := by
  sorry

/-- Whenever the function returns r on (reward1, reward2, k), and whenever it returns r' on (reward2, reward1, n - k), we have r = r'.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_6 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ (k' : Std.I64) (r r' : Std.I64), k'.val = (n : Int) - k.val →
      mice_and_cheese reward1 reward2 k = ok r →
        mice_and_cheese reward2 reward1 k' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ (k' : Std.I64) (r r' : Std.I64), k'.val = (n : Int) - k.val →
      mice_and_cheese reward1 reward2 k = ok r →
        mice_and_cheese reward2 reward1 k' = ok r' → r = r') := by
  sorry

/-- For every array a of length n with 1 <= a[i] <= 1000 and a[i] >= reward1[i] for every i with 0 <= i < n, if the function returns r on (reward1, reward2, k) and returns r_a on (a, reward2, k), then r_a >= r.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_7 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ (a : Slice Std.I64), a.val.length = n →
      (∀ i, i < n →
        1 ≤ valAt a i ∧ valAt a i ≤ 1000 ∧ valAt reward1 i ≤ valAt a i) →
        ∀ r ra : Std.I64, mice_and_cheese reward1 reward2 k = ok r →
          mice_and_cheese a reward2 k = ok ra → ra.val ≥ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ (a : Slice Std.I64), a.val.length = n →
      (∀ i, i < n →
        1 ≤ valAt a i ∧ valAt a i ≤ 1000 ∧ valAt reward1 i ≤ valAt a i) →
        ∀ r ra : Std.I64, mice_and_cheese reward1 reward2 k = ok r →
          mice_and_cheese a reward2 k = ok ra → ra.val ≥ r.val) := by
  sorry

/-- For every array b of length n with 1 <= b[i] <= 1000 and b[i] >= reward2[i] for every i with 0 <= i < n, if the function returns r on (reward1, reward2, k) and returns r_b on (reward1, b, k), then r_b >= r.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_8 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ (b : Slice Std.I64), b.val.length = n →
      (∀ i, i < n →
        1 ≤ valAt b i ∧ valAt b i ≤ 1000 ∧ valAt reward2 i ≤ valAt b i) →
        ∀ r rb : Std.I64, mice_and_cheese reward1 reward2 k = ok r →
          mice_and_cheese reward1 b k = ok rb → rb.val ≥ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ (b : Slice Std.I64), b.val.length = n →
      (∀ i, i < n →
        1 ≤ valAt b i ∧ valAt b i ≤ 1000 ∧ valAt reward2 i ≤ valAt b i) →
        ∀ r rb : Std.I64, mice_and_cheese reward1 reward2 k = ok r →
          mice_and_cheese reward1 b k = ok rb → rb.val ≥ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset S of {0,...,n-1} with |S| = k such that total(S) = r, where total(S) = sum_{i in S} reward1[i] + sum_{i notin S} reward2[i], and for every i in S and every j in {0,...,n-1} not in S, reward1[i] - reward2[i] >= reward1[j] - reward2[j].
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_9 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      ∃ S : Finset (Fin n),
        (S.card : Int) = k.val ∧ total reward1 reward2 n S = r.val ∧
          (∀ i ∈ S, ∀ j : Fin n, j ∉ S →
            valAt reward1 i.val - valAt reward2 i.val ≥
              valAt reward1 j.val - valAt reward2 j.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      ∃ S : Finset (Fin n),
        (S.card : Int) = k.val ∧ total reward1 reward2 n S = r.val ∧
          (∀ i ∈ S, ∀ j : Fin n, j ∉ S →
            valAt reward1 i.val - valAt reward2 i.val ≥
              valAt reward1 j.val - valAt reward2 j.val)) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{i=0}^{n-1} reward2[i] + the sum of the k largest values among {reward1[i] - reward2[i] | 0 <= i < n}, with the empty sum when k = 0.
  Preconditions: Let n = len(reward1). The preconditions are: len(reward1) = len(reward2) = n; 1 <= n <= 10^5; for every i with 0 <= i < n, 1 <= reward1[i] <= 1000 and 1 <= reward2[i] <= 1000; and 0 <= k <= n. -/
theorem spec_10 (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)) :
    ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      r.val = sumRange reward2 n + sumTop k.val.toNat (diffList reward1 reward2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (reward1 reward2 : Slice Std.I64) (k : Std.I64) (n : Nat)
    (hlen1 : reward1.val.length = n) (hlen2 : reward2.val.length = n)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hr1 : ∀ i, i < n → 1 ≤ valAt reward1 i ∧ valAt reward1 i ≤ 1000)
    (hr2 : ∀ i, i < n → 1 ≤ valAt reward2 i ∧ valAt reward2 i ≤ 1000)
    (hk_lb : 0 ≤ k.val) (hk_ub : k.val ≤ (n : Int)), ∀ r, mice_and_cheese reward1 reward2 k = ok r →
      r.val = sumRange reward2 n + sumTop k.val.toNat (diffList reward1 reward2)) := by
  sorry

end AegisSpec.MiceAndCheese
