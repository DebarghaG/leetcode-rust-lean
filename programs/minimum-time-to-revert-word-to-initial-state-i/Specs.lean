import Aegis.MinimumTimeToInitialState.Code.Funs

/-!
# Specifications of `Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state`

LeetCode problem `minimum-time-to-revert-word-to-initial-state-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTimeToInitialState

  def byteAt (word : Slice Std.U8) (i : ℤ) : Option Std.U8 :=
    if 0 ≤ i ∧ i < (word.length : ℤ) then word.val[i.toNat]? else none

  def ShiftEq (word : Slice Std.U8) (d : ℤ) : Prop :=
    ∀ i : ℤ, 0 ≤ i → i < (word.length : ℤ) - d → byteAt word i = byteAt word (i + d)

  def ShiftNe (word : Slice Std.U8) (d : ℤ) : Prop :=
    ∃ i : ℤ, 0 ≤ i ∧ i < (word.length : ℤ) - d ∧ byteAt word i ≠ byteAt word (i + d)

  def Feasible (word : Slice Std.U8) (k t : ℤ) : Prop :=
    (word.length : ℤ) ≤ t * k ∨ ((t * k) < (word.length : ℤ) ∧ ShiftEq word (t * k))

  def IsLeastFeasible (word : Slice Std.U8) (k r : ℤ) : Prop :=
    1 ≤ r ∧ Feasible word k r ∧ ∀ t : ℤ, 1 ≤ t → t < r → ¬ Feasible word k t

  def ceilDiv (n k : ℤ) : ℤ := (n + k - 1) / k

  /-- Let n = len(word). Call an integer t >= 1 feasible when either (a) t*k >= n, or (b) t*k < n and for every index i with 0 <= i < n - t*k, word[i] = word[i + t*k]. The function returns a result r and r is the least feasible positive integer: feasible(r) holds, and for every integer t with 1 <= t < r, feasible(t) does not hold. Products such as t*k are ordinary integer products; t is a mathematical integer, not a machine value.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_1
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∃ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r ∧
          IsLeastFeasible word k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∃ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r ∧
            IsLeastFeasible word k.val r.val) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or produce an arithmetic overflow for any input satisfying the preconditions.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_2
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∃ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∃ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r) := by
    sorry

  /-- Let n = len(word). Whenever the function returns a result r, r <= ceil(n/k), where ceil(n/k) is the integer (n + k - 1) div k.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_3
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          r.val ≤ ceilDiv (word.length : ℤ) k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            r.val ≤ ceilDiv (word.length : ℤ) k.val) := by
    sorry

  /-- Let n = len(word). Whenever the function returns a result r, either r*k >= n, or both r*k < n and for every i with 0 <= i < n - r*k, word[i] = word[i + r*k].
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_4
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          Feasible word k.val r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            Feasible word k.val r.val) := by
    sorry

  /-- Let n = len(word). Whenever the function returns a result r, for every integer t with 1 <= t < r, we have t*k < n and there exists an index i with 0 <= i < n - t*k such that word[i] != word[i + t*k].
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_5
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          ∀ t : ℤ, 1 ≤ t → t < r.val →
            t * k.val < (word.length : ℤ) ∧ ShiftNe word (t * k.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            ∀ t : ℤ, 1 ≤ t → t < r.val →
              t * k.val < (word.length : ℤ) ∧ ShiftNe word (t * k.val)) := by
    sorry

  /-- Let n = len(word). Whenever the function returns a result r, r = 1 if and only if either k = n or for every i with 0 <= i < n - k, word[i] = word[i + k].
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_6
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          (r.val = 1 ↔ k.val = (word.length : ℤ) ∨ ShiftEq word k.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            (r.val = 1 ↔ k.val = (word.length : ℤ) ∨ ShiftEq word k.val)) := by
    sorry

  /-- Let n = len(word). Whenever the function returns a result r, if r*k >= n then r = ceil(n/k) = (n + k - 1) div k.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_7
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          (word.length : ℤ) ≤ r.val * k.val →
            r.val = ceilDiv (word.length : ℤ) k.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            (word.length : ℤ) ≤ r.val * k.val →
              r.val = ceilDiv (word.length : ℤ) k.val) := by
    sorry

  /-- Whenever the function returns a result r, if k = 1 then r is the smallest integer p with 1 <= p <= len(word) such that for every i with 0 <= i < len(word) - p, word[i] = word[i + p]. For p = len(word) the condition is vacuous.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_8
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          k.val = 1 →
            1 ≤ r.val ∧ r.val ≤ (word.length : ℤ) ∧ ShiftEq word r.val ∧
              ∀ p : ℤ, 1 ≤ p → p ≤ (word.length : ℤ) → ShiftEq word p → r.val ≤ p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            k.val = 1 →
              1 ≤ r.val ∧ r.val ≤ (word.length : ℤ) ∧ ShiftEq word r.val ∧
                ∀ p : ℤ, 1 ≤ p → p ≤ (word.length : ℤ) → ShiftEq word p → r.val ≤ p) := by
    sorry

  /-- Let n = len(word) and let c = ceil(n/k) = (n + k - 1) div k. Whenever the function returns a result r, if for every integer t with 1 <= t < c there exists an index i with 0 <= i < n - t*k such that word[i] != word[i + t*k], then r = c.
    Preconditions: len(word) is between 1 and 50 inclusive; every byte word[i] with 0 <= i < len(word) satisfies 97 <= word[i] <= 122; k satisfies 1 <= k <= len(word). -/
  theorem spec_9
      (word : Slice Std.U8) (k : Std.I64)
      (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
      (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)) :
      ∀ r : Std.I64,
        Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
          (∀ t : ℤ, 1 ≤ t → t < ceilDiv (word.length : ℤ) k.val →
              ShiftNe word (t * k.val)) →
            r.val = ceilDiv (word.length : ℤ) k.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice Std.U8) (k : Std.I64)
        (hlen1 : 1 ≤ word.length) (hlen50 : word.length ≤ 50)
        (hbytes : ∀ b ∈ word.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hk1 : 1 ≤ k.val) (hklen : k.val ≤ (word.length : ℤ)), ∀ r : Std.I64,
          Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = Result.ok r →
            (∀ t : ℤ, 1 ≤ t → t < ceilDiv (word.length : ℤ) k.val →
                ShiftNe word (t * k.val)) →
              r.val = ceilDiv (word.length : ℤ) k.val) := by
    sorry

  end AegisSpec.MinimumTimeToInitialState
