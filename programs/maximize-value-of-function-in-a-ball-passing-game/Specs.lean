import Aegis.GetMaxFunctionValue.Code.Funs

/-!
# Specifications of `Aegis.GetMaxFunctionValue.get_max_function_value`

LeetCode problem `maximize-value-of-function-in-a-ball-passing-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetMaxFunctionValue

def len (receiver : Slice Std.I64) : ℕ := receiver.val.length

def rcv (receiver : Slice Std.I64) (i : ℕ) : ℤ :=
  match receiver.val[i]? with
  | some x => x.val
  | none => 0

def nxt (receiver : Slice Std.I64) (i : ℕ) : ℕ := (rcv receiver i).toNat

def fpow (receiver : Slice Std.I64) (t i : ℕ) : ℕ := (nxt receiver)^[t] i

def score (receiver : Slice Std.I64) (steps i : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (steps + 1), fpow receiver t i

def maxScore (receiver : Slice Std.I64) (steps : ℕ) : ℕ :=
  (Finset.range (len receiver)).sup (score receiver steps)

def pairScore (receiver : Slice Std.I64) (i : ℕ) : ℕ := i + nxt receiver i

def maxPairScore (receiver : Slice Std.I64) : ℕ :=
  (Finset.range (len receiver)).sup (pairScore receiver)

def minVal (receiver : Slice Std.I64) : ℤ :=
  match receiver.val with
  | [] => 0
  | x :: xs => xs.foldr (fun y acc => min y.val acc) x.val

def maxVal (receiver : Slice Std.I64) : ℤ :=
  match receiver.val with
  | [] => 0
  | x :: xs => xs.foldr (fun y acc => max y.val acc) x.val

def kSteps (k : Std.I64) : ℕ := k.val.toNat

/-- Define f(i) = receiver[i] for 0 <= i < n, with f^0(i) = i and f^(t+1)(i) = receiver[f^t(i)] for t >= 0. Define score(i) = sum_{t=0}^{k} f^t(i). The function returns a result r and r = max{ score(i) | 0 <= i < n }.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_1 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∃ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r ∧
        r.val = (maxScore receiver (kSteps k) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∃ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r ∧
        r.val = (maxScore receiver (kSteps k) : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, get_max_function_value returns Ok r for some 64-bit integer r; it does not panic, return Err, perform an out-of-bounds access, or overflow the returned result.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_2 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∃ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∃ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r) := by
  sorry

/-- Define f(i) = receiver[i], f^0(i) = i, f^(t+1)(i) = receiver[f^t(i)], and score(i) = sum_{t=0}^{k} f^t(i). Whenever the function returns r, for every starting player i with 0 <= i < n, score(i) <= r.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_3 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ∀ i : ℕ, i < len receiver → (score receiver (kSteps k) i : ℤ) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ∀ i : ℕ, i < len receiver → (score receiver (kSteps k) i : ℤ) ≤ r.val) := by
  sorry

/-- Define f(i) = receiver[i], f^0(i) = i, f^(t+1)(i) = receiver[f^t(i)], and score(i) = sum_{t=0}^{k} f^t(i). Whenever the function returns r, there exists a starting player i0 with 0 <= i0 < n such that score(i0) = r.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_4 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ∃ i0 : ℕ, i0 < len receiver ∧ (score receiver (kSteps k) i0 : ℤ) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ∃ i0 : ℕ, i0 < len receiver ∧ (score receiver (kSteps k) i0 : ℤ) = r.val) := by
  sorry

/-- Whenever the function returns r, r >= n - 1.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_5 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (len receiver : ℤ) - 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (len receiver : ℤ) - 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns r, r <= (n - 1) * (k + 1).
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_6 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val ≤ ((len receiver : ℤ) - 1) * (k.val + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val ≤ ((len receiver : ℤ) - 1) * (k.val + 1)) := by
  sorry

/-- If k = 1, then whenever the function returns r, r = max{ i + receiver[i] | 0 <= i < n }.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_7 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) (hk : k.val = 1) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val = (maxPairScore receiver : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) (hk : k.val = 1), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val = (maxPairScore receiver : ℤ)) := by
  sorry

/-- If receiver is constant, meaning receiver[i] = receiver[0] for every i with 0 <= i < n, then whenever the function returns r, r = (n - 1) + k * receiver[0].
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_8 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10)
    (hconst : ∀ i : ℕ, i < len receiver → rcv receiver i = rcv receiver 0) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val = ((len receiver : ℤ) - 1) + k.val * rcv receiver 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10)
    (hconst : ∀ i : ℕ, i < len receiver → rcv receiver i = rcv receiver 0), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val = ((len receiver : ℤ) - 1) + k.val * rcv receiver 0) := by
  sorry

/-- Whenever the function returns r, r = (n - 1) * (k + 1) if and only if receiver[n - 1] = n - 1.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_9 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (r.val = ((len receiver : ℤ) - 1) * (k.val + 1)
          ↔ rcv receiver (len receiver - 1) = (len receiver : ℤ) - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (r.val = ((len receiver : ℤ) - 1) * (k.val + 1)
          ↔ rcv receiver (len receiver - 1) = (len receiver : ℤ) - 1)) := by
  sorry

/-- Let r1 be the result of get_max_function_value(receiver, k1) and r2 the result of get_max_function_value(receiver, k2). Whenever both calls return results r1 and r2, r1 <= r2.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k1 <= k2 <= 10^10. -/
theorem spec_10 (receiver : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk11 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 10) :
    ∀ r1 r2 : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k1 = ok r1 →
        Aegis.GetMaxFunctionValue.get_max_function_value receiver k2 = ok r2 →
          r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk11 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ 10 ^ 10), ∀ r1 r2 : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k1 = ok r1 →
        Aegis.GetMaxFunctionValue.get_max_function_value receiver k2 = ok r2 →
          r1.val ≤ r2.val) := by
  sorry

/-- Let m = min{ receiver[j] | 0 <= j < n }. Whenever the function returns r, r >= (n - 1) + k * m.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_11 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ((len receiver : ℤ) - 1) + k.val * minVal receiver ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        ((len receiver : ℤ) - 1) + k.val * minVal receiver ≤ r.val) := by
  sorry

/-- Let M = max{ receiver[j] | 0 <= j < n }. Whenever the function returns r, r <= (n - 1) + k * M.
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_12 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val ≤ ((len receiver : ℤ) - 1) + k.val * maxVal receiver := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        r.val ≤ ((len receiver : ℤ) - 1) + k.val * maxVal receiver) := by
  sorry

/-- If receiver[j] = j for some j with 0 <= j < n, then whenever the function returns r, r >= j * (k + 1).
  Preconditions: Let n = len(receiver). The preconditions are: 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= receiver[i] <= n - 1; and 1 <= k <= 10^10. -/
theorem spec_13 (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10)
    (j : ℕ) (hj : j < len receiver) (hfix : rcv receiver j = (j : ℤ)) :
    ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (j : ℤ) * (k.val + 1) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (receiver : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ len receiver) (hn2 : len receiver ≤ 10 ^ 5)
    (hrange : ∀ i : ℕ, i < len receiver →
      0 ≤ rcv receiver i ∧ rcv receiver i ≤ (len receiver : ℤ) - 1)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 10 ^ 10)
    (j : ℕ) (hj : j < len receiver) (hfix : rcv receiver j = (j : ℤ)), ∀ r : Std.I64,
      Aegis.GetMaxFunctionValue.get_max_function_value receiver k = ok r →
        (j : ℤ) * (k.val + 1) ≤ r.val) := by
  sorry

end AegisSpec.GetMaxFunctionValue
