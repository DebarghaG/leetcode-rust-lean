import Aegis.CountTestedDevices.Code.Funs

/-!
# Specifications of `Aegis.CountTestedDevices.count_tested_devices`

LeetCode problem `count-tested-devices-after-test-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountTestedDevices

  open Aegis.CountTestedDevices

  def testedPrefix (b : List Std.I64) : ℕ → ℕ
    | 0 => 0
    | i + 1 =>
      let t := testedPrefix b i
      match b[i]? with
      | some x => if x.val > (t : ℤ) then t + 1 else t
      | none => t

  def maxEntry (b : List Std.I64) : ℤ := b.foldr (fun x acc => max x.val acc) 0

  def countPos (b : List Std.I64) : ℕ := (b.filter (fun x => decide (0 < x.val))).length

  def sliceOfList (l : List Std.I64) (h : l.length ≤ Std.Usize.max) : Slice Std.I64 :=
    Slice.mk l.length (Aeneas.Data.ListN.ListN.fromList l) h

  theorem sliceOfList_val (l : List Std.I64) (h : l.length ≤ Std.Usize.max) :
      (sliceOfList l h).val = l :=
    Aeneas.Data.ListN.ListN.from_to_inverse

  def suffixSlice (b : Slice Std.I64) (k : ℕ) : Slice Std.I64 :=
    sliceOfList (b.val.drop k) (by
      have h := Slice.length_ineq b
      simp only [List.length_drop]
      omega)

  theorem suffixSlice_val (b : Slice Std.I64) (k : ℕ) :
      (suffixSlice b k).val = b.val.drop k :=
    sliceOfList_val (b.val.drop k) _

  def HasWitness (b : List Std.I64) (k : ℕ) : Prop :=
    ∃ is : ℕ → ℕ,
      (∀ (j : ℕ), j < k → is j < b.length) ∧
      (∀ (j j' : ℕ), j < j' → j' < k → is j < is j') ∧
      (∀ (j : ℕ), j < k → ∃ (h : is j < b.length), (b[is j]'h).val ≥ (j : ℤ) + 1)

  def IsMaxWitnessValue (b : List Std.I64) (r : ℤ) : Prop :=
    HasWitness b r.toNat ∧ ∀ (k : ℕ), HasWitness b k → (k : ℤ) ≤ r

  /-- The function returns a result r and r = T_n, where T_0 = 0 and, for each i with 0 <= i < n, T_{i+1} = T_i + 1 if batteryPercentages[i] > T_i, and T_{i+1} = T_i otherwise. Here T_i is the number of devices already tested when the process reaches device i, and device i is tested exactly when its battery after all decrements by earlier tested devices is positive.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_1 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧ r.val = (testedPrefix b.val b.val.length : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧ r.val = (testedPrefix b.val b.val.length : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_2 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n, where n = len(batteryPercentages).
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_3 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (b.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (b.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if batteryPercentages[i] = 0 for every i with 0 <= i < n.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_4 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧
        (r.val = 0 ↔ ∀ (i : ℕ) (hi : i < b.val.length), (b.val[i]'hi).val = 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧
          (r.val = 0 ↔ ∀ (i : ℕ) (hi : i < b.val.length), (b.val[i]'hi).val = 0)) := by
    sorry

  /-- The function returns a result r and r = n if and only if batteryPercentages[i] >= i + 1 for every i with 0 <= i < n (equivalently, batteryPercentages[i] > i for every such i).
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_5 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧
        (r.val = (b.val.length : ℤ) ↔
          ∀ (i : ℕ) (hi : i < b.val.length), (b.val[i]'hi).val ≥ (i : ℤ) + 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧
          (r.val = (b.val.length : ℤ) ↔
            ∀ (i : ℕ) (hi : i < b.val.length), (b.val[i]'hi).val ≥ (i : ℤ) + 1)) := by
    sorry

  /-- The function returns a result r and r <= max { batteryPercentages[i] | 0 <= i < n }.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_6 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧ r.val ≤ maxEntry b.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧ r.val ≤ maxEntry b.val) := by
    sorry

  /-- The function returns a result r and r <= P, where P is the number of indices i with 0 <= i < n and batteryPercentages[i] > 0.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_7 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧ r.val ≤ (countPos b.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧ r.val ≤ (countPos b.val : ℤ)) := by
    sorry

  /-- The function returns a result r and r equals the value returned by count_tested_devices on the suffix slice [batteryPercentages[k], ..., batteryPercentages[n-1]].
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100, all batteryPercentages[i] are in [0,100], and there is an integer k with 1 <= k < n such that batteryPercentages[i] = 0 for every i with 0 <= i < k. -/
  theorem spec_8 (b : Slice Std.I64) (k : ℕ)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
      (hk_lo : 1 ≤ k) (hk_hi : k < b.val.length)
      (hz : ∀ (i : ℕ) (hi : i < k), (b.val[i]'(Nat.lt_trans hi hk_hi)).val = 0) :
      ∃ r r', count_tested_devices b = ok r ∧
        count_tested_devices (suffixSlice b k) = ok r' ∧ r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (b : Slice Std.I64) (k : ℕ)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
        (hk_lo : 1 ≤ k) (hk_hi : k < b.val.length)
        (hz : ∀ (i : ℕ) (hi : i < k), (b.val[i]'(Nat.lt_trans hi hk_hi)).val = 0), ∃ r r', count_tested_devices b = ok r ∧
          count_tested_devices (suffixSlice b k) = ok r' ∧ r = r') := by
    sorry

  /-- Let c be the slice of length n defined by c[i] = min(batteryPercentages[i], n) for every i with 0 <= i < n. The function returns a result r and r equals the value returned by count_tested_devices on c.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_9 (b c : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
      (hc_len : c.val.length = b.val.length)
      (hc : ∀ (i : ℕ) (hi : i < b.val.length) (hj : i < c.val.length),
        (c.val[i]'hj).val = min (b.val[i]'hi).val (b.val.length : ℤ)) :
      ∃ r r', count_tested_devices b = ok r ∧ count_tested_devices c = ok r' ∧ r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (b c : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
        (hc_len : c.val.length = b.val.length)
        (hc : ∀ (i : ℕ) (hi : i < b.val.length) (hj : i < c.val.length),
          (c.val[i]'hj).val = min (b.val[i]'hi).val (b.val.length : ℤ)), ∃ r r', count_tested_devices b = ok r ∧ count_tested_devices c = ok r' ∧ r = r') := by
    sorry

  /-- Whenever count_tested_devices returns r on batteryPercentages and r_y on y, we have r <= r_y.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100, all batteryPercentages[i] are in [0,100], y is a slice with len(y) = n, all y[i] are in [0,100], and batteryPercentages[i] <= y[i] for every i with 0 <= i < n. -/
  theorem spec_10 (b y : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
      (hy_len : y.val.length = b.val.length)
      (hy : ∀ (i : ℕ) (hi : i < y.val.length),
        0 ≤ (y.val[i]'hi).val ∧ (y.val[i]'hi).val ≤ 100)
      (hle : ∀ (i : ℕ) (hi : i < b.val.length) (hj : i < y.val.length),
        (b.val[i]'hi).val ≤ (y.val[i]'hj).val) :
      ∀ (r ry : Std.I64), count_tested_devices b = ok r → count_tested_devices y = ok ry →
        r.val ≤ ry.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (b y : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
        (hy_len : y.val.length = b.val.length)
        (hy : ∀ (i : ℕ) (hi : i < y.val.length),
          0 ≤ (y.val[i]'hi).val ∧ (y.val[i]'hi).val ≤ 100)
        (hle : ∀ (i : ℕ) (hi : i < b.val.length) (hj : i < y.val.length),
          (b.val[i]'hi).val ≤ (y.val[i]'hj).val), ∀ (r ry : Std.I64), count_tested_devices b = ok r → count_tested_devices y = ok ry →
          r.val ≤ ry.val) := by
    sorry

  /-- Let r be the result returned by count_tested_devices on batteryPercentages, and let r_prime be the result returned on the slice batteryPercentages followed by the single value v (length n+1). Then r_prime = r + 1 if v > r, and r_prime = r otherwise.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 99, all batteryPercentages[i] are in [0,100], and v is an integer with 0 <= v <= 100. -/
  theorem spec_11 (b b' : Slice Std.I64) (v : Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 99)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
      (hv_lo : 0 ≤ v.val) (hv_hi : v.val ≤ 100)
      (hb'_len : b'.val.length = b.val.length + 1)
      (hb' : b'.val = b.val ++ [v]) :
      ∃ r r', count_tested_devices b = ok r ∧ count_tested_devices b' = ok r' ∧
        (r.val < v.val → r'.val = r.val + 1) ∧ (v.val ≤ r.val → r'.val = r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (b b' : Slice Std.I64) (v : Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 99)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100)
        (hv_lo : 0 ≤ v.val) (hv_hi : v.val ≤ 100)
        (hb'_len : b'.val.length = b.val.length + 1)
        (hb' : b'.val = b.val ++ [v]), ∃ r r', count_tested_devices b = ok r ∧ count_tested_devices b' = ok r' ∧
          (r.val < v.val → r'.val = r.val + 1) ∧ (v.val ≤ r.val → r'.val = r.val)) := by
    sorry

  /-- The function returns a result r, and r is the largest integer k with 0 <= k <= n for which there exist indices i_1 < i_2 < ... < i_k, all with 0 <= i_j < n, such that batteryPercentages[i_j] >= j for every j = 1, ..., k.
    Preconditions: Let n = len(batteryPercentages). Assume 1 <= n <= 100 and, for every i with 0 <= i < n, 0 <= batteryPercentages[i] <= 100. -/
  theorem spec_12 (b : Slice Std.I64)
      (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
      (hb : ∀ (i : ℕ) (hi : i < b.val.length),
        0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100) :
      ∃ r, count_tested_devices b = ok r ∧ IsMaxWitnessValue b.val r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (b : Slice Std.I64)
        (hn_lo : 1 ≤ b.val.length) (hn_hi : b.val.length ≤ 100)
        (hb : ∀ (i : ℕ) (hi : i < b.val.length),
          0 ≤ (b.val[i]'hi).val ∧ (b.val[i]'hi).val ≤ 100), ∃ r, count_tested_devices b = ok r ∧ IsMaxWitnessValue b.val r.val) := by
    sorry

  end AegisSpec.CountTestedDevices
