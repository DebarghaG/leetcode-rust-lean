import Aegis.MinDays.Code.Funs

/-!
# Specifications of `Aegis.MinDays.min_days`

LeetCode problem `minimum-number-of-days-to-make-m-bouquets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinDays

def sliceLen (bloomDay : Slice Std.I64) : Nat := bloomDay.val.length

def vals (bloomDay : Slice Std.I64) : List Int := bloomDay.val.map (fun x => x.val)

def listMax (l : List Int) : Option Int :=
  l.foldr (fun x acc => some (match acc with | none => x | some a => max x a)) none

def listMin (l : List Int) : Option Int :=
  l.foldr (fun x acc => some (match acc with | none => x | some a => min x a)) none

def IsMaxOf (l : List Int) (x : Int) : Prop :=
  (∃ y ∈ l, y = x) ∧ ∀ y ∈ l, y ≤ x

def windowMax (l : List Int) (s k : Nat) : Option Int := listMax ((l.drop s).take k)

def windowMaxes (l : List Int) (k : Nat) : List Int :=
  (List.range (l.length + 1 - k)).filterMap (fun s => windowMax l s k)

def slidingMinWindowMax (l : List Int) (k : Nat) : Option Int := listMin (windowMaxes l k)

def cnt (bloomDay : Slice Std.I64) (d : Int) : Nat :=
  (vals bloomDay).countP (fun x => decide (x ≤ d))

def scanStep (k : Nat) (d : Int) (st : Nat × Nat) (x : Int) : Nat × Nat :=
  if x ≤ d then
    (if st.2 + 1 = k then (st.1 + 1, 0) else (st.1, st.2 + 1))
  else (st.1, 0)

def B (bloomDay : Slice Std.I64) (k : Int) (d : Int) : Nat :=
  ((vals bloomDay).foldl (scanStep k.toNat d) (0, 0)).1

/-- The function returns a result r (it does not fail). For an integer d, define B(d) to be the maximum number of pairwise disjoint intervals [s, s+k-1] of indices with 0 <= s and s+k-1 < n such that bloomDay[i] <= d for every i with s <= i <= s+k-1. Equivalently, B(d) is the sum, over all maximal contiguous runs of indices i for which bloomDay[i] <= d, of floor(run_length / k). If there exists a nonnegative integer d with B(d) >= m, then r is the least such d; otherwise r = -1.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_1 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      ((∃ d : Int, 0 ≤ d ∧ m.val ≤ ((B bloomDay k d : Nat) : Int)) →
        (0 ≤ r.val ∧ m.val ≤ ((B bloomDay k r.val : Nat) : Int) ∧
          ∀ d : Int, 0 ≤ d → m.val ≤ ((B bloomDay k d : Nat) : Int) → r.val ≤ d)) ∧
      ((¬ ∃ d : Int, 0 ≤ d ∧ m.val ≤ ((B bloomDay k d : Nat) : Int)) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      ((∃ d : Int, 0 ≤ d ∧ m.val ≤ ((B bloomDay k d : Nat) : Int)) →
        (0 ≤ r.val ∧ m.val ≤ ((B bloomDay k r.val : Nat) : Int) ∧
          ∀ d : Int, 0 ≤ d → m.val ≤ ((B bloomDay k d : Nat) : Int) → r.val ≤ d)) ∧
      ((¬ ∃ d : Int, 0 ≤ d ∧ m.val ≤ ((B bloomDay k d : Nat) : Int)) → r.val = -1)) := by
  sorry

/-- The function returns a result r and does not fail: no arithmetic overflow, no out-of-bounds slice access, and no panic occur.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_2 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r) := by
  sorry

/-- For an integer d, define B(d) as the maximum number of pairwise disjoint intervals [s, s+k-1] with 0 <= s and s+k-1 < n such that bloomDay[i] <= d for every i in the interval; equivalently, B(d) is the sum over maximal runs of available indices of floor(run_length/k), where available means bloomDay[i] <= d. Whenever the function returns a result r with r != -1, we have B(r) >= m.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_3 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      m.val ≤ ((B bloomDay k r.val : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      m.val ≤ ((B bloomDay k r.val : Nat) : Int)) := by
  sorry

/-- For an integer d, define B(d) as the maximum number of pairwise disjoint intervals [s, s+k-1] with 0 <= s and s+k-1 < n such that bloomDay[i] <= d for every i in the interval; equivalently, B(d) is the sum over maximal runs of available indices of floor(run_length/k), where available means bloomDay[i] <= d. Whenever the function returns a result r with r != -1, for every integer d with 0 <= d < r, we have B(d) < m.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_4 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∀ d : Int, 0 ≤ d → d < r.val → ((B bloomDay k d : Nat) : Int) < m.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∀ d : Int, 0 ≤ d → d < r.val → ((B bloomDay k d : Nat) : Int) < m.val) := by
  sorry

/-- The function returns r = -1 if and only if len(bloomDay) < m * k.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_5 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      (r.val = -1 ↔ (sliceLen bloomDay : Int) < m.val * k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      (r.val = -1 ↔ (sliceLen bloomDay : Int) < m.val * k.val)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r >= min_{0 <= i < n} bloomDay[i].
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_6 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, r <= max_{0 <= i < n} bloomDay[i].
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_7 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), r.val ≤ (bloomDay.val[i]'hi).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), r.val ≤ (bloomDay.val[i]'hi).val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < n such that r = bloomDay[i].
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_8 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)) :
    ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), r.val = (bloomDay.val[i]'hi).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int)), ∀ r, Aegis.MinDays.min_days bloomDay m k = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < bloomDay.val.length), r.val = (bloomDay.val[i]'hi).val) := by
  sorry

/-- If m = 1, then the function returns a result r and r = min_{0 <= s <= n-k} max_{s <= i < s+k} bloomDay[i].
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_9 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hm : m.val = 1) :
    ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      slidingMinWindowMax (vals bloomDay) k.val.toNat = some r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hm : m.val = 1), ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧
      slidingMinWindowMax (vals bloomDay) k.val.toNat = some r.val) := by
  sorry

/-- If k = 1, let cnt(d) be the number of indices i with 0 <= i < n and bloomDay[i] <= d. If m <= n, then the function returns a result r with r = min { d >= 0 | cnt(d) >= m }; if m > n, then the function returns r = -1.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_10 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hk : k.val = 1) :
    ((m.val ≤ (sliceLen bloomDay : Int)) →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ 0 ≤ r.val ∧
        m.val ≤ ((cnt bloomDay r.val : Nat) : Int) ∧
        ∀ d : Int, 0 ≤ d → m.val ≤ ((cnt bloomDay d : Nat) : Int) → r.val ≤ d) ∧
    ((sliceLen bloomDay : Int) < m.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hk : k.val = 1), ((m.val ≤ (sliceLen bloomDay : Int)) →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ 0 ≤ r.val ∧
        m.val ≤ ((cnt bloomDay r.val : Nat) : Int) ∧
        ∀ d : Int, 0 ≤ d → m.val ≤ ((cnt bloomDay d : Nat) : Int) → r.val ≤ d) ∧
    ((sliceLen bloomDay : Int) < m.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1)) := by
  sorry

/-- If there is an integer B such that bloomDay[i] = B for every i with 0 <= i < n, then the function returns r = B when n >= m * k, and returns r = -1 when n < m * k.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_11 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (Bday : Int)
    (hconst : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val = Bday) :
    ((m.val * k.val ≤ (sliceLen bloomDay : Int)) →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = Bday) ∧
    ((sliceLen bloomDay : Int) < m.val * k.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (Bday : Int)
    (hconst : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val = Bday), ((m.val * k.val ≤ (sliceLen bloomDay : Int)) →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = Bday) ∧
    ((sliceLen bloomDay : Int) < m.val * k.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1)) := by
  sorry

/-- If k = n, then the function returns r = max_{0 <= i < n} bloomDay[i] when m = 1, and returns r = -1 when m > 1.
  Preconditions: Let n = len(bloomDay). 1 <= n <= 100000; for every integer i with 0 <= i < n, 1 <= bloomDay[i] <= 1000000000; 1 <= m <= 1000000; 1 <= k <= n. -/
theorem spec_12 (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hk : k.val = (sliceLen bloomDay : Int)) :
    ((m.val = 1 →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ IsMaxOf (vals bloomDay) r.val)) ∧
    ((1 < m.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (bloomDay : Slice Std.I64) (m k : Std.I64)
    (hn_pos : 1 ≤ sliceLen bloomDay) (hn_le : sliceLen bloomDay ≤ 100000)
    (hday_lb : ∀ (i : Nat) (hi : i < bloomDay.val.length), 1 ≤ (bloomDay.val[i]'hi).val)
    (hday_ub : ∀ (i : Nat) (hi : i < bloomDay.val.length), (bloomDay.val[i]'hi).val ≤ 1000000000)
    (hm_pos : 1 ≤ m.val) (hm_le : m.val ≤ 1000000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (sliceLen bloomDay : Int))
    (hk : k.val = (sliceLen bloomDay : Int)), ((m.val = 1 →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ IsMaxOf (vals bloomDay) r.val)) ∧
    ((1 < m.val →
      ∃ r, Aegis.MinDays.min_days bloomDay m k = ok r ∧ r.val = -1))) := by
  sorry

end AegisSpec.MinDays
