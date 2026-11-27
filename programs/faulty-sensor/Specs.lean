import Aegis.BadSensor.Code.Funs

/-!
# Specifications of `Aegis.BadSensor.bad_sensor`

LeetCode problem `faulty-sensor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Aeneas.Std.Result

namespace AegisSpec.BadSensor

abbrev I64Slice := Slice Std.I64

def valAt (s : I64Slice) (i : Nat) (h : i < s.val.length) : Int := (s.val[i]).val

def Returns (s1 s2 : I64Slice) (r : Int) : Prop :=
  ∃ v : Std.I64, Aegis.BadSensor.bad_sensor s1 s2 = Result.ok v ∧ v.val = r

def Succeeds (s1 s2 : I64Slice) : Prop :=
  ∃ v : Std.I64, Aegis.BadSensor.bad_sensor s1 s2 = Result.ok v

def E (s1 s2 : I64Slice) (n : Nat) (h1 : s1.val.length = n) (h2 : s2.val.length = n) : Prop :=
  ∀ (i : Nat) (hi : i < n - 1), valAt s1 i (by omega) = valAt s2 i (by omega)

def D1 (s1 s2 : I64Slice) (n : Nat) (h1 : s1.val.length = n) (h2 : s2.val.length = n) : Prop :=
  ∃ (d : Nat) (hdn : d < n),
    (∀ (i : Nat) (hi : i < d), valAt s1 i (by omega) = valAt s2 i (by omega)) ∧
    (∀ (i : Nat) (hdi : d ≤ i) (hin : i < n - 1),
      valAt s1 i (by omega) = valAt s2 (i + 1) (by omega))

def D2 (s1 s2 : I64Slice) (n : Nat) (h1 : s1.val.length = n) (h2 : s2.val.length = n) : Prop :=
  ∃ (d : Nat) (hdn : d < n),
    (∀ (i : Nat) (hi : i < d), valAt s2 i (by omega) = valAt s1 i (by omega)) ∧
    (∀ (i : Nat) (hdi : d ≤ i) (hin : i < n - 1),
      valAt s2 i (by omega) = valAt s1 (i + 1) (by omega))

/-- The function returns a result r (it does not fail). Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D1 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor1[i] = sensor2[i], and (b) for every i with d <= i < n-1, sensor1[i] = sensor2[i+1]. Let D2 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor2[i] = sensor1[i], and (b) for every i with d <= i < n-1, sensor2[i] = sensor1[i+1]. Then r = -1 if E holds; r = 2 if E does not hold and D2 holds and D1 does not hold; and r = 1 otherwise (i.e., if E does not hold and either D1 holds or D2 does not hold).
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_1 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ∃ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r ∧
      (E sensor1 sensor2 n h_len1 h_len2 → r.val = -1) ∧
      (¬ E sensor1 sensor2 n h_len1 h_len2 →
        D2 sensor1 sensor2 n h_len1 h_len2 →
        ¬ D1 sensor1 sensor2 n h_len1 h_len2 → r.val = 2) ∧
      (¬ E sensor1 sensor2 n h_len1 h_len2 →
        (D1 sensor1 sensor2 n h_len1 h_len2 ∨
          ¬ D2 sensor1 sensor2 n h_len1 h_len2) → r.val = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ∃ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r ∧
      (E sensor1 sensor2 n h_len1 h_len2 → r.val = -1) ∧
      (¬ E sensor1 sensor2 n h_len1 h_len2 →
        D2 sensor1 sensor2 n h_len1 h_len2 →
        ¬ D1 sensor1 sensor2 n h_len1 h_len2 → r.val = 2) ∧
      (¬ E sensor1 sensor2 n h_len1 h_len2 →
        (D1 sensor1 sensor2 n h_len1 h_len2 ∨
          ¬ D2 sensor1 sensor2 n h_len1 h_len2) → r.val = 1)) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_2 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    Succeeds sensor1 sensor2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), Succeeds sensor1 sensor2) := by
  sorry

/-- Whenever the function returns a result r, r is an integer and r is either -1, 1, or 2.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_3 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = -1 ∨ r.val = 1 ∨ r.val = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = -1 ∨ r.val = 1 ∨ r.val = 2) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. If E holds, then the function returns -1.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_4 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    E sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 (-1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), E sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 (-1)) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D1 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor1[i] = sensor2[i], and (b) for every i with d <= i < n-1, sensor1[i] = sensor2[i+1]. Let D2 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor2[i] = sensor1[i], and (b) for every i with d <= i < n-1, sensor2[i] = sensor1[i+1]. If E does not hold, D2 holds, and D1 does not hold, then the function returns 2.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_5 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ¬ E sensor1 sensor2 n h_len1 h_len2 →
      D2 sensor1 sensor2 n h_len1 h_len2 →
      ¬ D1 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ¬ E sensor1 sensor2 n h_len1 h_len2 →
      D2 sensor1 sensor2 n h_len1 h_len2 →
      ¬ D1 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 2) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D2 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor2[i] = sensor1[i], and (b) for every i with d <= i < n-1, sensor2[i] = sensor1[i+1]. If E does not hold and D2 does not hold, then the function returns 1.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_6 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ¬ E sensor1 sensor2 n h_len1 h_len2 →
      ¬ D2 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ¬ E sensor1 sensor2 n h_len1 h_len2 →
      ¬ D2 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 1) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D1 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor1[i] = sensor2[i], and (b) for every i with d <= i < n-1, sensor1[i] = sensor2[i+1]. If E does not hold and D1 holds, then the function returns 1.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_7 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ¬ E sensor1 sensor2 n h_len1 h_len2 →
      D1 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ¬ E sensor1 sensor2 n h_len1 h_len2 →
      D1 sensor1 sensor2 n h_len1 h_len2 → Returns sensor1 sensor2 1) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D1 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor1[i] = sensor2[i], and (b) for every i with d <= i < n-1, sensor1[i] = sensor2[i+1]. Let D2 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor2[i] = sensor1[i], and (b) for every i with d <= i < n-1, sensor2[i] = sensor1[i+1]. Whenever the function returns 2, E does not hold, D2 holds, and D1 does not hold.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_8 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = 2 →
        ¬ E sensor1 sensor2 n h_len1 h_len2 ∧
          D2 sensor1 sensor2 n h_len1 h_len2 ∧
          ¬ D1 sensor1 sensor2 n h_len1 h_len2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = 2 →
        ¬ E sensor1 sensor2 n h_len1 h_len2 ∧
          D2 sensor1 sensor2 n h_len1 h_len2 ∧
          ¬ D1 sensor1 sensor2 n h_len1 h_len2) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Whenever the function returns -1, E holds.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_9 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = -1 → E sensor1 sensor2 n h_len1 h_len2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = -1 → E sensor1 sensor2 n h_len1 h_len2) := by
  sorry

/-- Let E mean that for every i with 0 <= i < n-1, sensor1[i] = sensor2[i]. Let D1 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor1[i] = sensor2[i], and (b) for every i with d <= i < n-1, sensor1[i] = sensor2[i+1]. Let D2 mean that there exists an integer d with 0 <= d < n such that (a) for every i with 0 <= i < d, sensor2[i] = sensor1[i], and (b) for every i with d <= i < n-1, sensor2[i] = sensor1[i+1]. Whenever the function returns 1, E does not hold, and either D1 holds or D2 does not hold.
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_10 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = 1 →
        ¬ E sensor1 sensor2 n h_len1 h_len2 ∧
          (D1 sensor1 sensor2 n h_len1 h_len2 ∨
            ¬ D2 sensor1 sensor2 n h_len1 h_len2) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), ∀ r : Std.I64,
      Aegis.BadSensor.bad_sensor sensor1 sensor2 = Result.ok r →
      r.val = 1 →
        ¬ E sensor1 sensor2 n h_len1 h_len2 ∧
          (D1 sensor1 sensor2 n h_len1 h_len2 ∨
            ¬ D2 sensor1 sensor2 n h_len1 h_len2)) := by
  sorry

/-- For every pair of slices (sensor1, sensor2) satisfying the preconditions, the function returns -1 on (sensor1, sensor2) if and only if it returns -1 on (sensor2, sensor1).
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_11 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    (Returns sensor1 sensor2 (-1) ↔ Returns sensor2 sensor1 (-1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), (Returns sensor1 sensor2 (-1) ↔ Returns sensor2 sensor1 (-1))) := by
  sorry

/-- For every pair of slices (sensor1, sensor2) satisfying the preconditions, if the function returns 2 on (sensor1, sensor2), then it returns 1 on (sensor2, sensor1).
  Preconditions: n = len(sensor1) = len(sensor2); 1 <= n <= 100; for every i with 0 <= i < n, 1 <= sensor1[i] <= 100 and 1 <= sensor2[i] <= 100. -/
theorem spec_12 (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100) :
    Returns sensor1 sensor2 2 → Returns sensor2 sensor1 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (sensor1 sensor2 : I64Slice) (n : Nat)
    (h_len1 : sensor1.val.length = n) (h_len2 : sensor2.val.length = n)
    (h_lo : 1 ≤ n) (h_hi : n ≤ 100)
    (h_b1 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor1 i (by omega) ∧ valAt sensor1 i (by omega) ≤ 100)
    (h_b2 : ∀ (i : Nat) (hi : i < n),
      1 ≤ valAt sensor2 i (by omega) ∧ valAt sensor2 i (by omega) ≤ 100), Returns sensor1 sensor2 2 → Returns sensor2 sensor1 1) := by
  sorry

end AegisSpec.BadSensor
