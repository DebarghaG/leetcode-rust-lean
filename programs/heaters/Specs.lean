import Aegis.FindRadius.Code.Funs

/-!
# Specifications of `Aegis.FindRadius.find_radius`

LeetCode problem `heaters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindRadius

def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def AdmitsRadius (houses heaters : Slice Std.I64) (R : ℤ) : Prop :=
  ∀ (i : ℕ) (hi : i < houses.val.length),
    ∃ (j : ℕ) (hj : j < heaters.val.length),
      |(houses.val[i]'hi).val - (heaters.val[j]'hj).val| ≤ R

def IsMinDist (x : ℤ) (heaters : Slice Std.I64) (d : ℤ) : Prop :=
  (∀ (j : ℕ) (hj : j < heaters.val.length), d ≤ |x - (heaters.val[j]'hj).val|) ∧
  (∃ (j : ℕ) (hj : j < heaters.val.length), d = |x - (heaters.val[j]'hj).val|)

def IsMaxHouseDist (houses : Slice Std.I64) (y : ℤ) (d : ℤ) : Prop :=
  (∀ (i : ℕ) (hi : i < houses.val.length), |(houses.val[i]'hi).val - y| ≤ d) ∧
  (∃ (i : ℕ) (hi : i < houses.val.length), d = |(houses.val[i]'hi).val - y|)

def ShiftBy (s s' : Slice Std.I64) (t : ℤ) : Prop :=
  vals s' = (vals s).map (fun x => x + t)

def PermOf (s s' : Slice Std.I64) : Prop := (vals s').Perm (vals s)

def DedupOf (s s' : Slice Std.I64) : Prop :=
  (vals s').Nodup ∧ (∀ x : ℤ, x ∈ vals s' ↔ x ∈ vals s)

def ValidSuperset (s s' : Slice Std.I64) : Prop :=
  s'.val.length ≤ 30000 ∧
  (∀ x ∈ vals s', 1 ≤ x ∧ x ≤ 1000000000) ∧
  (∀ x ∈ vals s, x ∈ vals s')

/-- The function returns a result r, and r is the least nonnegative integer R such that for every i with 0 <= i < len(houses) there exists j with 0 <= j < len(heaters) and |houses[i] - heaters[j]| <= R. Equivalently, r = max over 0 <= i < len(houses) of min over 0 <= j < len(heaters) of |houses[i] - heaters[j]|.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_1 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000) :
    ∃ r : Std.I64,
      Aegis.FindRadius.find_radius houses heaters = ok r ∧
      0 ≤ r.val ∧
      AdmitsRadius houses heaters r.val ∧
      (∀ R : ℤ, 0 ≤ R → AdmitsRadius houses heaters R → r.val ≤ R) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000), ∃ r : Std.I64,
      Aegis.FindRadius.find_radius houses heaters = ok r ∧
      0 ≤ r.val ∧
      AdmitsRadius houses heaters r.val ∧
      (∀ R : ℤ, 0 ≤ R → AdmitsRadius houses heaters R → r.val ≤ R)) := by
  sorry

/-- For every input satisfying the preconditions, find_radius returns a result r; in particular it does not fail, panic, or overflow.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_2 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000) :
    ∃ r : Std.I64, Aegis.FindRadius.find_radius houses heaters = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000), ∃ r : Std.I64, Aegis.FindRadius.find_radius houses heaters = ok r) := by
  sorry

/-- Whenever find_radius returns a result r, we have 0 <= r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_3 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever find_radius returns a result r, for every j with 0 <= j < len(heaters), r <= max over 0 <= i < len(houses) of |houses[i] - heaters[j]|.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_4 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    ∀ (j : ℕ) (hj : j < heaters.val.length),
      ∀ d : ℤ, IsMaxHouseDist houses (heaters.val[j]'hj).val d → r.val ≤ d := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), ∀ (j : ℕ) (hj : j < heaters.val.length),
      ∀ d : ℤ, IsMaxHouseDist houses (heaters.val[j]'hj).val d → r.val ≤ d) := by
  sorry

/-- Whenever find_radius returns a result r, for every i with 0 <= i < len(houses) there exists j with 0 <= j < len(heaters) such that |houses[i] - heaters[j]| <= r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_5 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    AdmitsRadius houses heaters r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), AdmitsRadius houses heaters r.val) := by
  sorry

/-- Whenever find_radius returns a result r, for every integer R with 0 <= R < r there exists i with 0 <= i < len(houses) such that for every j with 0 <= j < len(heaters), |houses[i] - heaters[j]| > R.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_6 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    ∀ R : ℤ, 0 ≤ R → R < r.val →
      ∃ (i : ℕ) (hi : i < houses.val.length),
        ∀ (j : ℕ) (hj : j < heaters.val.length),
          R < |(houses.val[i]'hi).val - (heaters.val[j]'hj).val| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), ∀ R : ℤ, 0 ≤ R → R < r.val →
      ∃ (i : ℕ) (hi : i < houses.val.length),
        ∀ (j : ℕ) (hj : j < heaters.val.length),
          R < |(houses.val[i]'hi).val - (heaters.val[j]'hj).val|) := by
  sorry

/-- Whenever find_radius returns a result r, there exists i0 with 0 <= i0 < len(houses) such that r = min over 0 <= j < len(heaters) of |houses[i0] - heaters[j]|.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_7 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    ∃ (i0 : ℕ) (hi0 : i0 < houses.val.length),
      IsMinDist (houses.val[i0]'hi0).val heaters r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), ∃ (i0 : ℕ) (hi0 : i0 < houses.val.length),
      IsMinDist (houses.val[i0]'hi0).val heaters r.val) := by
  sorry

/-- Whenever find_radius returns a result r, r = 0 if and only if for every i with 0 <= i < len(houses) there exists j with 0 <= j < len(heaters) such that houses[i] = heaters[j].
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_8 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r) :
    r.val = 0 ↔
      ∀ (i : ℕ) (hi : i < houses.val.length),
        ∃ (j : ℕ) (hj : j < heaters.val.length),
          (houses.val[i]'hi).val = (heaters.val[j]'hj).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r), r.val = 0 ↔
      ∀ (i : ℕ) (hi : i < houses.val.length),
        ∃ (j : ℕ) (hj : j < heaters.val.length),
          (houses.val[i]'hi).val = (heaters.val[j]'hj).val) := by
  sorry

/-- Whenever find_radius returns a result r and len(heaters) = 1, r = max over 0 <= i < len(houses) of |houses[i] - heaters[0]|.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_9 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (hlen : heaters.val.length = 1) :
    IsMaxHouseDist houses (heaters.val[0]'(by omega)).val r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (hlen : heaters.val.length = 1), IsMaxHouseDist houses (heaters.val[0]'(by omega)).val r.val) := by
  sorry

/-- Whenever find_radius returns a result r and len(houses) = 1, r = min over 0 <= j < len(heaters) of |houses[0] - heaters[j]|.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_10 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (hlen : houses.val.length = 1) :
    IsMinDist (houses.val[0]'(by omega)).val heaters r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (hlen : houses.val.length = 1), IsMinDist (houses.val[0]'(by omega)).val heaters r.val) := by
  sorry

/-- Whenever find_radius returns a result r, for every integer t such that 1 <= houses[i] + t <= 1000000000 for all i with 0 <= i < len(houses) and 1 <= heaters[j] + t <= 1000000000 for all j with 0 <= j < len(heaters), if houses' and heaters' are the slices with houses'[i] = houses[i] + t and heaters'[j] = heaters[j] + t, then whenever find_radius(houses', heaters') returns r', we have r' = r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_11 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (t : ℤ)
    (hbt : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val + t ∧ (houses.val[i]'hi).val + t ≤ 1000000000)
    (hgt : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val + t ∧ (heaters.val[j]'hj).val + t ≤ 1000000000)
    (houses' heaters' : Slice Std.I64)
    (hs' : ShiftBy houses houses' t) (ht' : ShiftBy heaters heaters' t)
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (t : ℤ)
    (hbt : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val + t ∧ (houses.val[i]'hi).val + t ≤ 1000000000)
    (hgt : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val + t ∧ (heaters.val[j]'hj).val + t ≤ 1000000000)
    (houses' heaters' : Slice Std.I64)
    (hs' : ShiftBy houses houses' t) (ht' : ShiftBy heaters heaters' t)
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever find_radius returns a result r, if houses' is any permutation of houses and heaters' is any permutation of heaters (the same multisets of positions, with duplicate occurrences counted), then whenever find_radius(houses', heaters') returns r', we have r' = r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_12 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' heaters' : Slice Std.I64)
    (hp : PermOf houses houses') (hq : PermOf heaters heaters')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' heaters' : Slice Std.I64)
    (hp : PermOf houses houses') (hq : PermOf heaters heaters')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever find_radius returns a result r, if houses' is obtained from houses by deleting duplicate occurrences so that each distinct house position occurs once, and heaters' is obtained from heaters by deleting duplicate occurrences so that each distinct heater position occurs once, and houses' and heaters' are still nonempty, then whenever find_radius(houses', heaters') returns r', we have r' = r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_13 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' heaters' : Slice Std.I64)
    (hd : DedupOf houses houses') (he : DedupOf heaters heaters')
    (hn1 : 1 ≤ houses'.val.length) (hn2 : 1 ≤ heaters'.val.length)
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' heaters' : Slice Std.I64)
    (hd : DedupOf houses houses') (he : DedupOf heaters heaters')
    (hn1 : 1 ≤ houses'.val.length) (hn2 : 1 ≤ heaters'.val.length)
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters' = ok r'), r'.val = r.val) := by
  sorry

/-- Whenever find_radius returns a result r, if houses' is a valid slice (length at most 30000 and every entry in [1,1000000000]) whose set of positions contains every house position occurring in houses, and heaters is unchanged, then whenever find_radius(houses', heaters) returns r', we have r <= r'.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_14 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' : Slice Std.I64) (hv : ValidSuperset houses houses')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (houses' : Slice Std.I64) (hv : ValidSuperset houses houses')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses' heaters = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever find_radius returns a result r, if heaters' is a valid slice (length at most 30000 and every entry in [1,1000000000]) whose set of positions contains every heater position occurring in heaters, and houses is unchanged, then whenever find_radius(houses, heaters') returns r', we have r' <= r.
  Preconditions: All indices are 0-based. 1 <= len(houses) <= 30000 and 1 <= len(heaters) <= 30000. For every i with 0 <= i < len(houses), 1 <= houses[i] <= 1000000000. For every j with 0 <= j < len(heaters), 1 <= heaters[j] <= 1000000000. The values are Std.I64 and all mentioned bounds fit in Std.I64. -/
theorem spec_15 (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (heaters' : Slice Std.I64) (hv : ValidSuperset heaters heaters')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses heaters' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (houses heaters : Slice Std.I64)
    (hh1 : 1 ≤ houses.val.length) (hh2 : houses.val.length ≤ 30000)
    (ht1 : 1 ≤ heaters.val.length) (ht2 : heaters.val.length ≤ 30000)
    (hb : ∀ (i : ℕ) (hi : i < houses.val.length),
      1 ≤ (houses.val[i]'hi).val ∧ (houses.val[i]'hi).val ≤ 1000000000)
    (hg : ∀ (j : ℕ) (hj : j < heaters.val.length),
      1 ≤ (heaters.val[j]'hj).val ∧ (heaters.val[j]'hj).val ≤ 1000000000)
    (r : Std.I64) (hr : Aegis.FindRadius.find_radius houses heaters = ok r)
    (heaters' : Slice Std.I64) (hv : ValidSuperset heaters heaters')
    (r' : Std.I64) (hr' : Aegis.FindRadius.find_radius houses heaters' = ok r'), r'.val ≤ r.val) := by
  sorry

end AegisSpec.FindRadius
