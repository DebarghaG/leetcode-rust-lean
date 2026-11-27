import Aegis.IdealArrays.Code.Funs

/-!
# Specifications of `Aegis.IdealArrays.ideal_arrays`

LeetCode problem `count-the-number-of-ideal-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IdealArrays

def MOD : ℤ := 1000000007

def IsIdealArray (n M : ℕ) (arr : Fin n → ℕ) : Prop :=
  (∀ i : Fin n, 1 ≤ arr i ∧ arr i ≤ M) ∧
    ∀ (i j : Fin n), i.val + 1 = j.val → arr i ∣ arr j

instance instDecidablePredIsIdealArray (n M : ℕ) : DecidablePred (IsIdealArray n M) :=
  fun arr => by
    unfold IsIdealArray
    infer_instance

def idealArrayFinset (n M : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 M)).filter
    (fun arr => ∀ (i j : Fin n), i.val + 1 = j.val → arr i ∣ arr j)

def idealArrayCount (n M : ℕ) : ℕ := (idealArrayFinset n M).card

def idealArrayFinsetContaining (n M : ℕ) : Finset (Fin n → ℕ) :=
  (idealArrayFinset n M).filter (fun arr => ∃ i : Fin n, arr i = M)

def idealArrayCountContaining (n M : ℕ) : ℕ := (idealArrayFinsetContaining n M).card

theorem mem_idealArrayFinset {n M : ℕ} {arr : Fin n → ℕ} :
    arr ∈ idealArrayFinset n M ↔ IsIdealArray n M arr := by
  simp only [idealArrayFinset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    IsIdealArray]

theorem mem_idealArrayFinsetContaining {n M : ℕ} {arr : Fin n → ℕ} :
    arr ∈ idealArrayFinsetContaining n M ↔ IsIdealArray n M arr ∧ ∃ i : Fin n, arr i = M := by
  simp only [idealArrayFinsetContaining, Finset.mem_filter, mem_idealArrayFinset]

def idealArraysPred (n maxValue : Std.I64) : Result Std.I64 := do
  let maxValuePred ← maxValue - 1#i64
  Aegis.IdealArrays.ideal_arrays n maxValuePred

/-- Let MOD = 1000000007. Let C(n, M) be the number of integer arrays arr of length n such that 1 <= arr[i] <= M for every 0 <= i < n and arr[i-1] divides arr[i] for every 0 < i < n. The function returns a result r, and r is the unique integer satisfying 0 <= r < MOD and r is congruent to C(n, maxValue) modulo MOD.
  Preconditions: 2 <= n <= 10^4 and 1 <= maxValue <= 10^4. -/
theorem spec_1 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4) :
    ∃ r : Std.I64,
      Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧
        0 ≤ r.val ∧ r.val < MOD ∧
          r.val ≡ ((idealArrayCount n.val.toNat maxValue.val.toNat : ℕ) : ℤ) [ZMOD MOD] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4), ∃ r : Std.I64,
      Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧
        0 ≤ r.val ∧ r.val < MOD ∧
          r.val ≡ ((idealArrayCount n.val.toNat maxValue.val.toNat : ℕ) : ℤ) [ZMOD MOD]) := by
  sorry

/-- For every n and maxValue satisfying the preconditions, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: 2 <= n <= 10^4 and 1 <= maxValue <= 10^4. -/
theorem spec_2 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4) :
    ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4), ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r) := by
  sorry

/-- For every n and maxValue satisfying the preconditions, whenever the function returns a result r, 0 <= r < 1000000007.
  Preconditions: 2 <= n <= 10^4 and 1 <= maxValue <= 10^4. -/
theorem spec_3 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4) :
    ∀ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r → 0 ≤ r.val ∧ r.val < MOD := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4), ∀ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r → 0 ≤ r.val ∧ r.val < MOD) := by
  sorry

/-- The function returns r = 1.
  Preconditions: 2 <= n <= 10^4 and maxValue = 1. -/
theorem spec_4 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 1) :
    ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 1), ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = 1) := by
  sorry

/-- Let MOD = 1000000007. The function returns r with r = (sum_{a=1}^{maxValue} floor(maxValue / a)) mod MOD, where floor(maxValue / a) is integer division.
  Preconditions: n = 2 and 1 <= maxValue <= 10^4. -/
theorem spec_5 (n maxValue : Std.I64)
    (hn : n.val = 2)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4) :
    ∃ r : Std.I64,
      Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧
        r.val = ((∑ a ∈ Finset.Icc 1 maxValue.val.toNat, maxValue.val.toNat / a : ℕ) : ℤ) %
          MOD := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : n.val = 2)
    (hm : 1 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4), ∃ r : Std.I64,
      Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧
        r.val = ((∑ a ∈ Finset.Icc 1 maxValue.val.toNat, maxValue.val.toNat / a : ℕ) : ℤ) %
          MOD) := by
  sorry

/-- The function returns r = n + 1.
  Preconditions: 2 <= n <= 10^4 and maxValue = 2. -/
theorem spec_6 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 2) :
    ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = n.val + 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 2), ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = n.val + 1) := by
  sorry

/-- The function returns r = 2*n + 1.
  Preconditions: 2 <= n <= 10^4 and maxValue = 3. -/
theorem spec_7 (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 3) :
    ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = 2 * n.val + 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n maxValue : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : maxValue.val = 3), ∃ r : Std.I64, Aegis.IdealArrays.ideal_arrays n maxValue = ok r ∧ r.val = 2 * n.val + 1) := by
  sorry

/-- Let MOD = 1000000007. An ideal array of length n with upper bound M is an integer array arr of length n with 1 <= arr[i] <= M for all 0 <= i < n and arr[i-1] divides arr[i] for all 0 < i < n. Whenever r = ideal_arrays(n, maxValue) and s = ideal_arrays(n, maxValue - 1) both return, (r - s) mod MOD equals the number, modulo MOD, of ideal arrays of length n with upper bound maxValue that contain the value maxValue at least once.
  Preconditions: 2 <= n <= 10^4 and 2 <= maxValue <= 10^4. -/
theorem spec_8 (n maxValue r s : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 2 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4)
    (hr : Aegis.IdealArrays.ideal_arrays n maxValue = ok r)
    (hs : idealArraysPred n maxValue = ok s) :
    (r.val - s.val) % MOD =
      (((idealArrayCountContaining n.val.toNat maxValue.val.toNat : ℕ)) : ℤ) % MOD := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n maxValue r s : Std.I64)
    (hn : 2 ≤ n.val) (hn' : n.val ≤ 10 ^ 4)
    (hm : 2 ≤ maxValue.val) (hm' : maxValue.val ≤ 10 ^ 4)
    (hr : Aegis.IdealArrays.ideal_arrays n maxValue = ok r)
    (hs : idealArraysPred n maxValue = ok s), (r.val - s.val) % MOD =
      (((idealArrayCountContaining n.val.toNat maxValue.val.toNat : ℕ)) : ℤ) % MOD) := by
  sorry

end AegisSpec.IdealArrays
