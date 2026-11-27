import Aegis.MinimumTimeToInitialState.Code.Funs

/-!
# Specifications of `Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state`

LeetCode problem `minimum-time-to-revert-word-to-initial-state-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumTimeToInitialState

  def isAsciiLower (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def achievable (word : List U8) (k t : Int) : Prop :=
    (word.length : Int) ≤ t * k ∨
      (t * k < (word.length : Int) ∧
        ∀ i : Nat, (i : Int) < (word.length : Int) - t * k →
          word[i]? = word[i + (t * k).toNat]?)

  def leastAchievable (word : List U8) (k r : Int) : Prop :=
    1 ≤ r ∧ achievable word k r ∧ ∀ t : Int, 1 ≤ t → achievable word k t → r ≤ t

  /-- For every input satisfying the preconditions, the function returns a result r, and r is the least integer t with t ≥ 1 such that either (a) t*k ≥ n, or (b) t*k < n and for every i with 0 ≤ i < n - t*k, word[i] = word[i + t*k].
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n (with k regarded as its mathematical integer value). -/
  theorem spec_1 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int)) :
      ∃ r : I64, Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r ∧
        leastAchievable word.val k.val r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int)), ∃ r : I64, Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r ∧
          leastAchievable word.val k.val r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_2 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int)) :
      ∃ r : I64, Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int)), ∃ r : I64, Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ 1.
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_3 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let q be the least positive integer such that q*k ≥ n; then r ≤ q (equivalently, r ≤ ceil(n/k)).
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_4 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      (q : Int)
      (hq_pos : 1 ≤ q)
      (hq_ge : (word.val.length : Int) ≤ q * k.val)
      (hq_min : ∀ q' : Int, 1 ≤ q' → (word.val.length : Int) ≤ q' * k.val → q ≤ q')
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) :
      r.val ≤ q := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        (q : Int)
        (hq_pos : 1 ≤ q)
        (hq_ge : (word.val.length : Int) ≤ q * k.val)
        (hq_min : ∀ q' : Int, 1 ≤ q' → (word.val.length : Int) ≤ q' * k.val → q ≤ q')
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r), r.val ≤ q) := by
    sorry

  /-- Whenever the function returns a result r, r is an achievable reversion time: either r*k ≥ n, or r*k < n and for every i with 0 ≤ i < n - r*k, word[i] = word[i + r*k].
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_5 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) :
      achievable word.val k.val r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r), achievable word.val k.val r.val) := by
    sorry

  /-- Whenever the function returns a result r, no positive integer t < r is an achievable reversion time. That is, for every integer t with 1 ≤ t < r, we have t*k < n and there exists an index i with 0 ≤ i < n - t*k such that word[i] ≠ word[i + t*k].
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_6 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) :
      ∀ t : Int, 1 ≤ t → t < r.val →
        t * k.val < (word.val.length : Int) ∧
          ∃ i : Nat, (i : Int) < (word.val.length : Int) - t * k.val ∧
            word.val[i]? ≠ word.val[i + (t * k.val).toNat]? := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r), ∀ t : Int, 1 ≤ t → t < r.val →
          t * k.val < (word.val.length : Int) ∧
            ∃ i : Nat, (i : Int) < (word.val.length : Int) - t * k.val ∧
              word.val[i]? ≠ word.val[i + (t * k.val).toNat]?) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if for every i with 0 ≤ i < n - k, word[i] = word[i + k].
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_7 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r) :
      (r.val = 1 ↔
        ∀ i : Nat, (i : Int) < (word.val.length : Int) - k.val →
          word.val[i]? = word.val[i + k.val.toNat]?) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r), (r.val = 1 ↔
          ∀ i : Nat, (i : Int) < (word.val.length : Int) - k.val →
            word.val[i]? = word.val[i + k.val.toNat]?)) := by
    sorry

  /-- Whenever the function returns a result r and k = 1, r is the least positive integer p such that for every i with 0 ≤ i < n - p, word[i] = word[i + p].
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_8 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r)
      (hk_one : k.val = 1) :
      1 ≤ r.val ∧
        (∀ i : Nat, (i : Int) < (word.val.length : Int) - r.val →
          word.val[i]? = word.val[i + r.val.toNat]?) ∧
          ∀ p : Int, 1 ≤ p →
            (∀ i : Nat, (i : Int) < (word.val.length : Int) - p →
              word.val[i]? = word.val[i + p.toNat]?) →
            r.val ≤ p := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r)
        (hk_one : k.val = 1), 1 ≤ r.val ∧
          (∀ i : Nat, (i : Int) < (word.val.length : Int) - r.val →
            word.val[i]? = word.val[i + r.val.toNat]?) ∧
            ∀ p : Int, 1 ≤ p →
              (∀ i : Nat, (i : Int) < (word.val.length : Int) - p →
                word.val[i]? = word.val[i + p.toNat]?) →
              r.val ≤ p) := by
    sorry

  /-- Whenever the function returns a result r and all bytes of word are equal (there exists c such that word[i] = c for every i with 0 ≤ i < n), r = 1.
    Preconditions: Let n = len(word). The input satisfies 1 ≤ n ≤ 1,000,000, every byte word[j] for 0 ≤ j < n is an ASCII lowercase English letter, and 1 ≤ k ≤ n. -/
  theorem spec_9 (word : Slice U8) (k : I64)
      (hn_pos : 1 ≤ word.val.length)
      (hn_max : word.val.length ≤ 1000000)
      (hbytes : ∀ b ∈ word.val, isAsciiLower b)
      (hk_pos : 1 ≤ k.val)
      (hk_le : k.val ≤ (word.val.length : Int))
      {r : I64}
      (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r)
      (hconst : ∃ c : U8, ∀ b ∈ word.val, b = c) :
      r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (word : Slice U8) (k : I64)
        (hn_pos : 1 ≤ word.val.length)
        (hn_max : word.val.length ≤ 1000000)
        (hbytes : ∀ b ∈ word.val, isAsciiLower b)
        (hk_pos : 1 ≤ k.val)
        (hk_le : k.val ≤ (word.val.length : Int))
        {r : I64}
        (hr : Aegis.MinimumTimeToInitialState.minimum_time_to_initial_state word k = ok r)
        (hconst : ∃ c : U8, ∀ b ∈ word.val, b = c), r.val = 1) := by
    sorry

  end AegisSpec.MinimumTimeToInitialState
