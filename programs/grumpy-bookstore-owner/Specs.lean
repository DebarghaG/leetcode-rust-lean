import Aegis.MaxSatisfied.Code.Funs

/-!
# Specifications of `Aegis.MaxSatisfied.max_satisfied`

LeetCode problem `grumpy-bookstore-owner`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxSatisfied

  def cell (s : Slice Std.I64) (i : ℕ) : ℤ := (s.val.getD i 0#i64).val

  def kOf (minutes : Std.I64) : ℕ := minutes.val.toNat

  def starts (n k : ℕ) : Finset ℕ := Finset.Icc 0 (n - k)

  def value (customers grumpy : Slice Std.I64) (n k s : ℕ) : ℤ :=
    ∑ i ∈ Finset.range n,
      if cell grumpy i = 0 ∨ (s ≤ i ∧ i < s + k) then cell customers i else 0

  def baseSum (customers grumpy : Slice Std.I64) (n : ℕ) : ℤ :=
    ∑ i ∈ Finset.range n, if cell grumpy i = 0 then cell customers i else 0

  def totalSum (customers : Slice Std.I64) (n : ℕ) : ℤ :=
    ∑ i ∈ Finset.range n, cell customers i

  def gain (customers grumpy : Slice Std.I64) (n k s : ℕ) : ℤ :=
    ∑ i ∈ Finset.range n,
      if cell grumpy i = 1 ∧ s ≤ i ∧ i < s + k then cell customers i else 0

  def loss (customers grumpy : Slice Std.I64) (n k s : ℕ) : ℤ :=
    ∑ i ∈ Finset.range n,
      if cell grumpy i = 1 ∧ ¬ (s ≤ i ∧ i < s + k) then cell customers i else 0

  def maxValue (customers grumpy : Slice Std.I64) (n k : ℕ) : ℤ :=
    Finset.max' ((starts n k).image (fun s => value customers grumpy n k s))
      (Finset.image_nonempty.mpr
        ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩⟩)

  def maxGain (customers grumpy : Slice Std.I64) (n k : ℕ) : ℤ :=
    Finset.max' ((starts n k).image (fun s => gain customers grumpy n k s))
      (Finset.image_nonempty.mpr
        ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩⟩)

  def minLoss (customers grumpy : Slice Std.I64) (n k : ℕ) : ℤ :=
    Finset.min' ((starts n k).image (fun s => loss customers grumpy n k s))
      (Finset.image_nonempty.mpr
        ⟨0, Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.zero_le _⟩⟩)

  /-- The function returns a result r and, for every integer s with 0 <= s <= n - minutes, define value(s) = sum over i from 0 to n-1 of (customers[i] if grumpy[i] = 0 or s <= i < s + minutes, else 0). Then r = max{value(s) | s is an integer and 0 <= s <= n - minutes}.
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_1
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∃ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r ∧
        r.val = maxValue customers grumpy n (kOf minutes) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∃ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r ∧
          r.val = maxValue customers grumpy n (kOf minutes)) := by
    sorry

  /-- The function returns a result r; it does not overflow, access out of bounds, or panic.
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_2
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∃ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∃ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= sum over i from 0 to n-1 of customers[i].
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_3
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        0 ≤ r.val ∧ r.val ≤ totalSum customers n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          0 ≤ r.val ∧ r.val ≤ totalSum customers n) := by
    sorry

  /-- Whenever the function returns a result r, for every integer s with 0 <= s <= n - minutes, sum over i from 0 to n-1 of (customers[i] if grumpy[i] = 0 or s <= i < s + minutes, else 0) <= r.
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_4
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        ∀ s, s ≤ n - kOf minutes → value customers grumpy n (kOf minutes) s ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          ∀ s, s ≤ n - kOf minutes → value customers grumpy n (kOf minutes) s ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer s with 0 <= s <= n - minutes such that r = sum over i from 0 to n-1 of (customers[i] if grumpy[i] = 0 or s <= i < s + minutes, else 0).
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_5
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        ∃ s, s ≤ n - kOf minutes ∧
          r.val = value customers grumpy n (kOf minutes) s := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          ∃ s, s ≤ n - kOf minutes ∧
            r.val = value customers grumpy n (kOf minutes) s) := by
    sorry

  /-- Whenever the function returns a result r, r >= sum over i with 0 <= i < n and grumpy[i] = 0 of customers[i].
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_6
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        baseSum customers grumpy n ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          baseSum customers grumpy n ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = B + G, where B = sum over i with 0 <= i < n and grumpy[i] = 0 of customers[i], and G is the maximum, over integers s with 0 <= s <= n - minutes, of sum over i from s to s+minutes-1 of (customers[i] if grumpy[i] = 1, else 0).
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_7
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        r.val = baseSum customers grumpy n + maxGain customers grumpy n (kOf minutes) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          r.val = baseSum customers grumpy n + maxGain customers grumpy n (kOf minutes)) := by
    sorry

  /-- Whenever the function returns a result r, let T = sum over i from 0 to n-1 of customers[i], and for each integer s with 0 <= s <= n - minutes let U(s) = sum over i with 0 <= i < n, grumpy[i] = 1, and not (s <= i < s + minutes) of customers[i]. Then r = T - min{U(s) | s is an integer and 0 <= s <= n - minutes}.
    Preconditions: Let n = len(customers). The input satisfies n = len(grumpy), 1 <= minutes <= n <= 20000, for every i with 0 <= i < n, 0 <= customers[i] <= 1000, and for every i with 0 <= i < n, grumpy[i] is 0 or 1. -/
  theorem spec_8
      (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
      (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
      (hn_bound : n ≤ 20000)
      (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
      (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
      (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1) :
      ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
        r.val = totalSum customers n - minLoss customers grumpy n (kOf minutes) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (customers grumpy : Slice Std.I64) (minutes : Std.I64) (n : ℕ)
        (hc_len : customers.val.length = n) (hg_len : grumpy.val.length = n)
        (hn_bound : n ≤ 20000)
        (hminutes_pos : 1 ≤ minutes.val) (hminutes_le : minutes.val ≤ (n : ℤ))
        (hcustomers : ∀ i, i < n → 0 ≤ cell customers i ∧ cell customers i ≤ 1000)
        (hgrumpy : ∀ i, i < n → cell grumpy i = 0 ∨ cell grumpy i = 1), ∀ r, Aegis.MaxSatisfied.max_satisfied customers grumpy minutes = ok r →
          r.val = totalSum customers n - minLoss customers grumpy n (kOf minutes)) := by
    sorry

  end AegisSpec.MaxSatisfied
