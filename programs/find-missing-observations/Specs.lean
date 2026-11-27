import Aegis.MissingRolls.Code.Funs

/-!
# Specifications of `Aegis.MissingRolls.missing_rolls`

LeetCode problem `find-missing-observations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.MissingRolls

  namespace AegisSpec.MissingRolls

  def vals (l : List Std.I64) : List ℤ := l.map (fun x => x.val)

  def sumZ (l : List Std.I64) : ℤ := (vals l).sum

  def sumFirst (l : List Std.I64) (k : ℕ) : ℤ := (vals (l.take k)).sum

  theorem sumFirst_length_eq_sumZ (l : List Std.I64) : sumFirst l l.length = sumZ l := by
    simp [sumFirst, sumZ, vals]

  def dieBounded (l : List Std.I64) : Prop := ∀ x ∈ l, 1 ≤ x.val ∧ x.val ≤ 6

  theorem dieBounded_iff_getElem (l : List Std.I64) :
      dieBounded l ↔ ∀ (j : ℕ) (hj : j < l.length), 1 ≤ (l[j]).val ∧ (l[j]).val ≤ 6 := by
    constructor
    · intro h j hj
      exact h _ (List.getElem_mem hj)
    · intro h x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      exact h j hj

  def neededSum (rolls : List Std.I64) (mean n : Std.I64) (m : ℕ) : ℤ :=
    mean.val * (n.val + (m : ℤ)) - sumZ rolls

  def NoCompletion (rolls : List Std.I64) (mean n : Std.I64) (m : ℕ) : Prop :=
    ¬ ∃ w : List ℤ, w.length = n.val.toNat ∧ (∀ x ∈ w, 1 ≤ x ∧ x ≤ 6) ∧
      sumZ rolls + w.sum = mean.val * (n.val + (m : ℤ))

  /-- Let S = sum_{i=0}^{m-1} rolls[i] and T = mean*(n+m) - S. The function returns a result r and the following two implications hold. (a) If n <= T <= 6*n, then len(r) = n, for every j with 0 <= j < n we have 1 <= r[j] <= 6, and S + sum_{j=0}^{n-1} r[j] = mean*(n+m). (b) If T < n or T > 6*n, then len(r) = 0.
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. -/
  theorem spec_1 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val) :
      ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r ∧
        ((n.val ≤ neededSum rolls.val mean n m ∧ neededSum rolls.val mean n m ≤ 6 * n.val) →
          r.val.length = n.val.toNat ∧ dieBounded (r.val.take n.val.toNat) ∧
            sumZ rolls.val + sumFirst r.val n.val.toNat = mean.val * (n.val + (m : ℤ))) ∧
        ((neededSum rolls.val mean n m < n.val ∨ 6 * n.val < neededSum rolls.val mean n m) →
          r.val.length = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val), ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r ∧
          ((n.val ≤ neededSum rolls.val mean n m ∧ neededSum rolls.val mean n m ≤ 6 * n.val) →
            r.val.length = n.val.toNat ∧ dieBounded (r.val.take n.val.toNat) ∧
              sumZ rolls.val + sumFirst r.val n.val.toNat = mean.val * (n.val + (m : ℤ))) ∧
          ((neededSum rolls.val mean n m < n.val ∨ 6 * n.val < neededSum rolls.val mean n m) →
            r.val.length = 0)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), 1 <= r[j] <= 6.
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. -/
  theorem spec_2 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val)
      (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r) :
      dieBounded r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val)
        (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r), dieBounded r.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, no overflow, out-of-bounds access, or panic occurs.
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. -/
  theorem spec_3 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val) :
      ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val), ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 0, there is no vector w of length n such that 1 <= w[k] <= 6 for every k with 0 <= k < n and S + sum_{k=0}^{n-1} w[k] = mean*(n+m).
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. Let S = sum_{i=0}^{m-1} rolls[i]. -/
  theorem spec_4 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val)
      (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r)
      (hlen : r.val.length = 0) :
      NoCompletion rolls.val mean n m := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val)
        (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r)
        (hlen : r.val.length = 0), NoCompletion rolls.val mean n m) := by
    sorry

  /-- Whenever the function returns a result r with len(r) > 0, r is a valid completion: len(r) = n, 1 <= r[k] <= 6 for every k with 0 <= k < n, and S + sum_{k=0}^{n-1} r[k] = mean*(n+m).
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. Let S = sum_{i=0}^{m-1} rolls[i]. -/
  theorem spec_5 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val)
      (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r)
      (hlen : 0 < r.val.length) :
      r.val.length = n.val.toNat ∧ dieBounded (r.val.take n.val.toNat) ∧
        sumZ rolls.val + sumFirst r.val n.val.toNat = mean.val * (n.val + (m : ℤ)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val)
        (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r)
        (hlen : 0 < r.val.length), r.val.length = n.val.toNat ∧ dieBounded (r.val.take n.val.toNat) ∧
          sumZ rolls.val + sumFirst r.val n.val.toNat = mean.val * (n.val + (m : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, either len(r) = 0 or len(r) = n.
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. -/
  theorem spec_6 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val)
      (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r) :
      r.val.length = 0 ∨ r.val.length = n.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val)
        (r : alloc.vec.Vec Std.I64) (hr : missing_rolls rolls mean n = ok r), r.val.length = 0 ∨ r.val.length = n.val.toNat) := by
    sorry

  /-- Let r1 and r2 be the results returned by the function on rolls1 and on rolls2 with the same mean and n. Whenever both calls return results, len(r1) = len(r2). If this common length is positive, then len(r1) = n and sum_{j=0}^{n-1} r1[j] = sum_{j=0}^{n-1} r2[j] = mean*(n+m) - sum_{i=0}^{m-1} rolls1[i]; if the common length is 0, then both calls return empty vectors.
    Preconditions: Let m = len(rolls1) = len(rolls2); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls1[i] <= 6 and 1 <= rolls2[i] <= 6; and sum_{i=0}^{m-1} rolls1[i] = sum_{i=0}^{m-1} rolls2[i]. -/
  theorem spec_7 (rolls1 rolls2 : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm1 : rolls1.val.length = m) (hm2 : rolls2.val.length = m)
      (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls1 : dieBounded rolls1.val) (hrolls2 : dieBounded rolls2.val)
      (hsum : sumZ rolls1.val = sumZ rolls2.val)
      (r1 r2 : alloc.vec.Vec Std.I64)
      (hr1 : missing_rolls rolls1 mean n = ok r1)
      (hr2 : missing_rolls rolls2 mean n = ok r2) :
      r1.val.length = r2.val.length ∧
        ((0 < r1.val.length) →
          r1.val.length = n.val.toNat ∧
            sumFirst r1.val n.val.toNat = mean.val * (n.val + (m : ℤ)) - sumZ rolls1.val ∧
            sumFirst r2.val n.val.toNat = mean.val * (n.val + (m : ℤ)) - sumZ rolls1.val) ∧
        (r1.val.length = 0 → r1.val = [] ∧ r2.val = []) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rolls1 rolls2 : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm1 : rolls1.val.length = m) (hm2 : rolls2.val.length = m)
        (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls1 : dieBounded rolls1.val) (hrolls2 : dieBounded rolls2.val)
        (hsum : sumZ rolls1.val = sumZ rolls2.val)
        (r1 r2 : alloc.vec.Vec Std.I64)
        (hr1 : missing_rolls rolls1 mean n = ok r1)
        (hr2 : missing_rolls rolls2 mean n = ok r2), r1.val.length = r2.val.length ∧
          ((0 < r1.val.length) →
            r1.val.length = n.val.toNat ∧
              sumFirst r1.val n.val.toNat = mean.val * (n.val + (m : ℤ)) - sumZ rolls1.val ∧
              sumFirst r2.val n.val.toNat = mean.val * (n.val + (m : ℤ)) - sumZ rolls1.val) ∧
          (r1.val.length = 0 → r1.val = [] ∧ r2.val = [])) := by
    sorry

  /-- Whenever the function returns a result r, len(r) > 0 if and only if n <= T <= 6*n.
    Preconditions: m = len(rolls); 1 <= m <= 100000; 1 <= n <= 100000; 1 <= mean <= 6; for every i with 0 <= i < m, 1 <= rolls[i] <= 6. Let S = sum_{i=0}^{m-1} rolls[i] and T = mean*(n+m) - S. -/
  theorem spec_8 (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
      (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
      (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
      (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
      (hrolls : dieBounded rolls.val) :
      ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r ∧
        (0 < r.val.length ↔
          n.val ≤ neededSum rolls.val mean n m ∧ neededSum rolls.val mean n m ≤ 6 * n.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rolls : Slice Std.I64) (mean n : Std.I64) (m : ℕ)
        (hm : rolls.val.length = m) (hm_lb : 1 ≤ m) (hm_ub : m ≤ 100000)
        (hn_lb : 1 ≤ n.val) (hn_ub : n.val ≤ 100000)
        (hmean_lb : 1 ≤ mean.val) (hmean_ub : mean.val ≤ 6)
        (hrolls : dieBounded rolls.val), ∃ r : alloc.vec.Vec Std.I64, missing_rolls rolls mean n = ok r ∧
          (0 < r.val.length ↔
            n.val ≤ neededSum rolls.val mean n m ∧ neededSum rolls.val mean n m ≤ 6 * n.val)) := by
    sorry

  end AegisSpec.MissingRolls
