import Aegis.DailyTemperatures.Code.Funs

/-!
# Specifications of `Aegis.DailyTemperatures.daily_temperatures`

LeetCode problem `daily-temperatures`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DailyTemperatures

  def elem (l : List Std.I64) (i : Nat) : Int :=
    if h : i < l.length then (l[i]'h).val else 0

  /-- Whenever daily_temperatures(temperatures) returns a result r, let n = len(temperatures). Then len(r) = n, and for every i with 0 <= i < n the following holds. If there exists j with i < j < n and temperatures[j] > temperatures[i], then r[i] is the smallest positive integer d such that i + d < n and temperatures[i + d] > temperatures[i]; equivalently r[i] = d, temperatures[i + d] > temperatures[i], and temperatures[i + k] <= temperatures[i] for every integer k with 0 < k < d. If no such j exists, then r[i] = 0.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_1 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      r.val.length = temperatures.val.length ∧
        ∀ i, i < temperatures.val.length →
          ((∃ j, i < j ∧ j < temperatures.val.length ∧
              elem temperatures.val i < elem temperatures.val j) →
            ∃ d : Nat, 0 < d ∧ elem r.val i = (d : Int) ∧
              i + d < temperatures.val.length ∧
              elem temperatures.val i < elem temperatures.val (i + d) ∧
              (∀ k : Nat, 0 < k → k < d →
                elem temperatures.val (i + k) ≤ elem temperatures.val i) ∧
              (∀ d' : Nat, 0 < d' → i + d' < temperatures.val.length →
                elem temperatures.val i < elem temperatures.val (i + d') → d ≤ d')) ∧
          ((¬ ∃ j, i < j ∧ j < temperatures.val.length ∧
              elem temperatures.val i < elem temperatures.val j) →
            elem r.val i = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), r.val.length = temperatures.val.length ∧
          ∀ i, i < temperatures.val.length →
            ((∃ j, i < j ∧ j < temperatures.val.length ∧
                elem temperatures.val i < elem temperatures.val j) →
              ∃ d : Nat, 0 < d ∧ elem r.val i = (d : Int) ∧
                i + d < temperatures.val.length ∧
                elem temperatures.val i < elem temperatures.val (i + d) ∧
                (∀ k : Nat, 0 < k → k < d →
                  elem temperatures.val (i + k) ≤ elem temperatures.val i) ∧
                (∀ d' : Nat, 0 < d' → i + d' < temperatures.val.length →
                  elem temperatures.val i < elem temperatures.val (i + d') → d ≤ d')) ∧
            ((¬ ∃ j, i < j ∧ j < temperatures.val.length ∧
                elem temperatures.val i < elem temperatures.val j) →
              elem r.val i = 0)) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, len(r) = len(temperatures).
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_2 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      r.val.length = temperatures.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), r.val.length = temperatures.val.length) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures), 0 <= r[i] <= len(temperatures) - 1 - i.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_3 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length →
        0 ≤ elem r.val i ∧ elem r.val i ≤ (temperatures.val.length : Int) - 1 - (i : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length →
          0 ≤ elem r.val i ∧ elem r.val i ≤ (temperatures.val.length : Int) - 1 - (i : Int)) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures), r[i] = 0 if and only if every j with i < j < len(temperatures) satisfies temperatures[j] <= temperatures[i].
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_4 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length →
        (elem r.val i = 0 ↔
          ∀ j, i < j → j < temperatures.val.length →
            elem temperatures.val j ≤ elem temperatures.val i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length →
          (elem r.val i = 0 ↔
            ∀ j, i < j → j < temperatures.val.length →
              elem temperatures.val j ≤ elem temperatures.val i)) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures), if r[i] > 0 then i + r[i] < len(temperatures) and temperatures[i + r[i]] > temperatures[i].
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_5 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length → 0 < elem r.val i →
        i + (elem r.val i).toNat < temperatures.val.length ∧
          elem temperatures.val i < elem temperatures.val (i + (elem r.val i).toNat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length → 0 < elem r.val i →
          i + (elem r.val i).toNat < temperatures.val.length ∧
            elem temperatures.val i < elem temperatures.val (i + (elem r.val i).toNat)) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i and every integer d with 0 <= i < len(temperatures) and 0 < d < r[i], i + d < len(temperatures) and temperatures[i + d] <= temperatures[i].
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_6 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ (i d : Nat), i < temperatures.val.length → 0 < d → (d : Int) < elem r.val i →
        i + d < temperatures.val.length ∧
          elem temperatures.val (i + d) ≤ elem temperatures.val i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ (i d : Nat), i < temperatures.val.length → 0 < d → (d : Int) < elem r.val i →
          i + d < temperatures.val.length ∧
            elem temperatures.val (i + d) ≤ elem temperatures.val i) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, r[len(temperatures) - 1] = 0.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_7 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      elem r.val (temperatures.val.length - 1) = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), elem r.val (temperatures.val.length - 1) = 0) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures) - 1, r[i] = 1 if and only if temperatures[i + 1] > temperatures[i].
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_8 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length - 1 →
        (elem r.val i = 1 ↔
          elem temperatures.val i < elem temperatures.val (i + 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length - 1 →
          (elem r.val i = 1 ↔
            elem temperatures.val i < elem temperatures.val (i + 1))) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures), if temperatures[i] = 100 then r[i] = 0.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_9 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length → elem temperatures.val i = 100 → elem r.val i = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length → elem temperatures.val i = 100 → elem r.val i = 0) := by
    sorry

  /-- Whenever daily_temperatures(temperatures) returns a result r, for every i with 0 <= i < len(temperatures) - 1, if temperatures[i] = temperatures[i + 1], then r[i] = 0 if and only if r[i + 1] = 0, and if r[i + 1] > 0 then r[i] = r[i + 1] + 1.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_10 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
      (r : alloc.vec.Vec Std.I64)
      (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) :
      ∀ i, i < temperatures.val.length - 1 →
        elem temperatures.val i = elem temperatures.val (i + 1) →
          (elem r.val i = 0 ↔ elem r.val (i + 1) = 0) ∧
            (0 < elem r.val (i + 1) → elem r.val i = elem r.val (i + 1) + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100)
        (r : alloc.vec.Vec Std.I64)
        (hres : Aegis.DailyTemperatures.daily_temperatures temperatures = ok r), ∀ i, i < temperatures.val.length - 1 →
          elem temperatures.val i = elem temperatures.val (i + 1) →
            (elem r.val i = 0 ↔ elem r.val (i + 1) = 0) ∧
              (0 < elem r.val (i + 1) → elem r.val i = elem r.val (i + 1) + 1)) := by
    sorry

  /-- For every integer c such that 30 <= temperatures[i] + c <= 100 for all i with 0 <= i < n, let t' be the slice of length n with t'[i] = temperatures[i] + c. Whenever daily_temperatures(temperatures) returns r and daily_temperatures(t') returns r', len(r) = len(r') and r[i] = r'[i] for every i with 0 <= i < n.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_11 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100) :
      ∀ c : Int,
        (∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i + c ∧ elem temperatures.val i + c ≤ 100) →
        ∀ t' : Slice Std.I64,
          t'.val.length = temperatures.val.length →
          (∀ i, i < temperatures.val.length →
            elem t'.val i = elem temperatures.val i + c) →
          ∀ r r' : alloc.vec.Vec Std.I64,
            Aegis.DailyTemperatures.daily_temperatures temperatures = ok r →
            Aegis.DailyTemperatures.daily_temperatures t' = ok r' →
            r.val.length = r'.val.length ∧
              ∀ i, i < temperatures.val.length → elem r.val i = elem r'.val i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100), ∀ c : Int,
          (∀ i, i < temperatures.val.length →
            30 ≤ elem temperatures.val i + c ∧ elem temperatures.val i + c ≤ 100) →
          ∀ t' : Slice Std.I64,
            t'.val.length = temperatures.val.length →
            (∀ i, i < temperatures.val.length →
              elem t'.val i = elem temperatures.val i + c) →
            ∀ r r' : alloc.vec.Vec Std.I64,
              Aegis.DailyTemperatures.daily_temperatures temperatures = ok r →
              Aegis.DailyTemperatures.daily_temperatures t' = ok r' →
              r.val.length = r'.val.length ∧
                ∀ i, i < temperatures.val.length → elem r.val i = elem r'.val i) := by
    sorry

  /-- For every index i with 0 <= i < n and every slice b of length n satisfying 30 <= b[k] <= 100 for all 0 <= k < n and b[k] = temperatures[k] for every k with i <= k < n, whenever daily_temperatures(temperatures) returns r and daily_temperatures(b) returns r_b, r[i] = r_b[i].
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_12 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100) :
      ∀ i, i < temperatures.val.length →
        ∀ b : Slice Std.I64,
          b.val.length = temperatures.val.length →
          (∀ k, k < temperatures.val.length →
            30 ≤ elem b.val k ∧ elem b.val k ≤ 100) →
          (∀ k, i ≤ k → k < temperatures.val.length →
            elem b.val k = elem temperatures.val k) →
          ∀ r r_b : alloc.vec.Vec Std.I64,
            Aegis.DailyTemperatures.daily_temperatures temperatures = ok r →
            Aegis.DailyTemperatures.daily_temperatures b = ok r_b →
            elem r.val i = elem r_b.val i := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100), ∀ i, i < temperatures.val.length →
          ∀ b : Slice Std.I64,
            b.val.length = temperatures.val.length →
            (∀ k, k < temperatures.val.length →
              30 ≤ elem b.val k ∧ elem b.val k ≤ 100) →
            (∀ k, i ≤ k → k < temperatures.val.length →
              elem b.val k = elem temperatures.val k) →
            ∀ r r_b : alloc.vec.Vec Std.I64,
              Aegis.DailyTemperatures.daily_temperatures temperatures = ok r →
              Aegis.DailyTemperatures.daily_temperatures b = ok r_b →
              elem r.val i = elem r_b.val i) := by
    sorry

  /-- For every slice temperatures of 64-bit integers satisfying the preconditions, daily_temperatures(temperatures) returns a result r; it does not overflow, go out of bounds, or panic.
    Preconditions: Let n = len(temperatures). 1 <= n <= 100000 and 30 <= temperatures[i] <= 100 for every i with 0 <= i < n. -/
  theorem spec_13 (temperatures : Slice Std.I64)
      (hlen : 1 ≤ temperatures.val.length)
      (hlen_le : temperatures.val.length ≤ 100000)
      (hrange : ∀ i, i < temperatures.val.length →
        30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.DailyTemperatures.daily_temperatures temperatures = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (temperatures : Slice Std.I64)
        (hlen : 1 ≤ temperatures.val.length)
        (hlen_le : temperatures.val.length ≤ 100000)
        (hrange : ∀ i, i < temperatures.val.length →
          30 ≤ elem temperatures.val i ∧ elem temperatures.val i ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.DailyTemperatures.daily_temperatures temperatures = ok r) := by
    sorry

  end AegisSpec.DailyTemperatures
