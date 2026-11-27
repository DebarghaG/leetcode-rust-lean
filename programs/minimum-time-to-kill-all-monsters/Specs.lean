import Aegis.MinimumTime.Code.Funs

/-!
# Specifications of `Aegis.MinimumTime.minimum_time`

LeetCode problem `minimum-time-to-kill-all-monsters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimumTime

  namespace AegisSpec.MinimumTime

  def ceilDiv (a b : Int) : Int := (a + b - 1) / b

  def entry (power : Slice Std.I64) (j : Nat) : Int := (power.val.getD j 0#i64).val

  def minEntry (power : Slice Std.I64) : Int :=
    match power.val.map (fun x => x.val) with
    | [] => 0
    | x :: xs => xs.foldl min x

  def sumDivUpTo (m : Int) (n : Nat) : Int :=
    ((List.range n).map (fun k => ceilDiv m ((k : Int) + 1))).sum

  def IsPermOfRange (n : Nat) (ms : List Nat) : Prop :=
    ms.length = n ∧ ms.Nodup ∧ ∀ x ∈ ms, x < n

  def permCost (power : Slice Std.I64) (ms : List Nat) : Int :=
    ((List.range ms.length).map
      (fun k => ceilDiv (entry power (ms.getD k 0)) ((k : Int) + 1))).sum

  def costOverN (power : Slice Std.I64) (n : Nat) : Int :=
    (power.val.map (fun x => ceilDiv x.val (n : Int))).sum

  /-- The function returns a result r and r = min { Σ_{i=1}^{n} ceil(power[m_i] / i) | (m_1,...,m_n) is a permutation of {0,...,n-1} }, where for positive integers a and b, ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a. Here the index i is the 1-based position in the kill order (the gain when attempting to kill the i-th monster is i).
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_1 (power : Slice Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int)) :
      ∃ r, minimum_time power = ok r ∧
        (∀ ms, IsPermOfRange power.val.length ms → r.val ≤ permCost power ms) ∧
        (∃ ms, IsPermOfRange power.val.length ms ∧ r.val = permCost power ms) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (power : Slice Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int)), ∃ r, minimum_time power = ok r ∧
          (∀ ms, IsPermOfRange power.val.length ms → r.val ≤ permCost power ms) ∧
          (∃ ms, IsPermOfRange power.val.length ms ∧ r.val = permCost power ms)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a permutation (m_1,...,m_n) of {0,...,n-1} such that r = Σ_{i=1}^{n} ceil(power[m_i] / i), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_2 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      ∃ ms, IsPermOfRange power.val.length ms ∧ r.val = permCost power ms := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), ∃ ms, IsPermOfRange power.val.length ms ∧ r.val = permCost power ms) := by
    sorry

  /-- Whenever the function returns a result r, for every permutation (m_1,...,m_n) of {0,...,n-1}, r ≤ Σ_{i=1}^{n} ceil(power[m_i] / i), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_3 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      ∀ ms, IsPermOfRange power.val.length ms → r.val ≤ permCost power ms := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), ∀ ms, IsPermOfRange power.val.length ms → r.val ≤ permCost power ms) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ n.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_4 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      (power.val.length : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), (power.val.length : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ Σ_{i=1}^{n} ceil(m / i), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. Let m = min_{0≤j<n} power[j]. -/
  theorem spec_5 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      sumDivUpTo (minEntry power) power.val.length ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), sumDivUpTo (minEntry power) power.val.length ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ Σ_{j=0}^{n-1} ceil(power[j] / n), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_6 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      costOverN power power.val.length ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), costOverN power power.val.length ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = power[0].
    Preconditions: Let n = len(power). Assume n = 1 and 1 ≤ power[0] ≤ 10^9. -/
  theorem spec_7 (power : Slice Std.I64) (x : Std.I64) (r : Std.I64)
      (hval : power.val = [x])
      (hx : 1 ≤ x.val ∧ x.val ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      r.val = x.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (power : Slice Std.I64) (x : Std.I64) (r : Std.I64)
        (hval : power.val = [x])
        (hx : 1 ≤ x.val ∧ x.val ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), r.val = x.val) := by
    sorry

  /-- Whenever the function returns a result r, r = Σ_{i=1}^{n} ceil(c / i), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and there exists an integer c with 1 ≤ c ≤ 10^9 such that power[j] = c for all 0 ≤ j < n. -/
  theorem spec_8 (power : Slice Std.I64) (c : Int) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hc : 1 ≤ c ∧ c ≤ (10 ^ 9 : Int))
      (hconst : ∀ j, j < power.val.length → entry power j = c)
      (h : minimum_time power = ok r) :
      r.val = sumDivUpTo c power.val.length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (power : Slice Std.I64) (c : Int) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hc : 1 ≤ c ∧ c ≤ (10 ^ 9 : Int))
        (hconst : ∀ j, j < power.val.length → entry power j = c)
        (h : minimum_time power = ok r), r.val = sumDivUpTo c power.val.length) := by
    sorry

  /-- Whenever minimum_time(power) returns r and minimum_time(power') returns r', we have r = r'.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. Let σ be any permutation of {0,...,n-1} and define power' of length n by power'[i] = power[σ(i)] for 0 ≤ i < n. -/
  theorem spec_9 (power power' : Slice Std.I64) (σ : Nat → Nat) (r r' : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (hσ_mem : ∀ i, i < power.val.length → σ i < power.val.length)
      (hσ_inj : ∀ i j, i < power.val.length → j < power.val.length → σ i = σ j → i = j)
      (hpow' : power'.val = (List.range power.val.length).map (fun i => power.val.getD (σ i) 0#i64))
      (h : minimum_time power = ok r)
      (h' : minimum_time power' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (power power' : Slice Std.I64) (σ : Nat → Nat) (r r' : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (hσ_mem : ∀ i, i < power.val.length → σ i < power.val.length)
        (hσ_inj : ∀ i j, i < power.val.length → j < power.val.length → σ i = σ j → i = j)
        (hpow' : power'.val = (List.range power.val.length).map (fun i => power.val.getD (σ i) 0#i64))
        (h : minimum_time power = ok r)
        (h' : minimum_time power' = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever minimum_time(power) returns r and minimum_time(q) returns r_q, we have r ≤ r_q.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. Let q be any array of length n such that 1 ≤ q[j] ≤ 10^9 and power[j] ≤ q[j] for all 0 ≤ j < n. -/
  theorem spec_10 (power q : Slice Std.I64) (r rq : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (hq_len : q.val.length = power.val.length)
      (hq_bound : ∀ j, j < q.val.length →
        1 ≤ entry q j ∧ entry q j ≤ (10 ^ 9 : Int))
      (hle : ∀ j, j < power.val.length → entry power j ≤ entry q j)
      (h : minimum_time power = ok r)
      (hq : minimum_time q = ok rq) :
      r.val ≤ rq.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (power q : Slice Std.I64) (r rq : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (hq_len : q.val.length = power.val.length)
        (hq_bound : ∀ j, j < q.val.length →
          1 ≤ entry q j ∧ entry q j ≤ (10 ^ 9 : Int))
        (hle : ∀ j, j < power.val.length → entry power j ≤ entry q j)
        (h : minimum_time power = ok r)
        (hq : minimum_time q = ok rq), r.val ≤ rq.val) := by
    sorry

  /-- The function returns a result r (it does not panic, overflow, or otherwise fail).
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_11 (power : Slice Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int)) :
      ∃ r, minimum_time power = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (power : Slice Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int)), ∃ r, minimum_time power = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists a permutation (m_1,...,m_n) of {0,...,n-1} such that power[m_1] ≤ power[j] for all 0 ≤ j < n, and r = Σ_{i=1}^{n} ceil(power[m_i] / i), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and 1 ≤ power[j] ≤ 10^9 for all 0 ≤ j < n. -/
  theorem spec_12 (power : Slice Std.I64) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hbound : ∀ j, j < power.val.length →
        1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
      (h : minimum_time power = ok r) :
      ∃ (m₁ : Nat) (rest : List Nat),
        IsPermOfRange power.val.length (m₁ :: rest) ∧
        (∀ j, j < power.val.length → entry power m₁ ≤ entry power j) ∧
        r.val = permCost power (m₁ :: rest) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (power : Slice Std.I64) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hbound : ∀ j, j < power.val.length →
          1 ≤ entry power j ∧ entry power j ≤ (10 ^ 9 : Int))
        (h : minimum_time power = ok r), ∃ (m₁ : Nat) (rest : List Nat),
          IsPermOfRange power.val.length (m₁ :: rest) ∧
          (∀ j, j < power.val.length → entry power m₁ ≤ entry power j) ∧
          r.val = permCost power (m₁ :: rest)) := by
    sorry

  /-- Whenever the function returns a result r, r = (n - 1) + ceil(P / n), where ceil(a/b) is the smallest integer d ≥ 0 such that d*b ≥ a.
    Preconditions: Let n = len(power). Assume 1 ≤ n ≤ 17 and there exists an index k and an integer P with 2 ≤ P ≤ 10^9 such that power[k] = P and power[j] = 1 for all j ≠ k. -/
  theorem spec_13 (power : Slice Std.I64) (k : Nat) (P : Int) (r : Std.I64)
      (hn_pos : 1 ≤ power.val.length)
      (hn_le : power.val.length ≤ 17)
      (hk : k < power.val.length)
      (hP : 2 ≤ P ∧ P ≤ (10 ^ 9 : Int))
      (hkP : entry power k = P)
      (hrest : ∀ j, j < power.val.length → j ≠ k → entry power j = 1)
      (h : minimum_time power = ok r) :
      r.val = ((power.val.length : Int) - 1) + ceilDiv P (power.val.length : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (power : Slice Std.I64) (k : Nat) (P : Int) (r : Std.I64)
        (hn_pos : 1 ≤ power.val.length)
        (hn_le : power.val.length ≤ 17)
        (hk : k < power.val.length)
        (hP : 2 ≤ P ∧ P ≤ (10 ^ 9 : Int))
        (hkP : entry power k = P)
        (hrest : ∀ j, j < power.val.length → j ≠ k → entry power j = 1)
        (h : minimum_time power = ok r), r.val = ((power.val.length : Int) - 1) + ceilDiv P (power.val.length : Int)) := by
    sorry

  end AegisSpec.MinimumTime
