import Aegis.CountCompleteDayPairs.Code.Funs

/-!
# Specifications of `Aegis.CountCompleteDayPairs.count_complete_day_pairs`

LeetCode problem `count-pairs-that-form-a-complete-day-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountCompleteDayPairs

  namespace AegisSpec.CountCompleteDayPairs

  def vals (hours : Slice Std.I64) : List ℤ := hours.val.map (fun x => x.val)

  @[reducible] def IsCompleteDayPair (a b : ℤ) : Prop := (a + b) % 24 = 0

  def completeDayPairFinset (l : List ℤ) : Finset (Fin l.length × Fin l.length) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ IsCompleteDayPair (l.get p.1) (l.get p.2))

  def completeDayPairs (l : List ℤ) : ℕ := (completeDayPairFinset l).card

  def residueCount (l : List ℤ) (t : ℕ) : ℕ :=
    (Finset.univ.filter (fun i : Fin l.length => l.get i % 24 = (t : ℤ))).card

  def residuePairCount (l : List ℤ) : ℕ :=
    Nat.choose (residueCount l 0) 2 + Nat.choose (residueCount l 12) 2 +
      (Finset.Icc 1 11).sum (fun a => residueCount l a * residueCount l (24 - a))

  def neighborCount (l : List ℤ) (i : Fin l.length) : ℕ :=
    (Finset.univ.filter (fun j : Fin l.length => j ≠ i ∧ IsCompleteDayPair (l.get i) (l.get j))).card

  def neighborTotal (l : List ℤ) : ℕ := Finset.univ.sum (fun i : Fin l.length => neighborCount l i)

  def IsPermOf (l l' : List ℤ) : Prop :=
    ∃ π : Fin l'.length → Fin l.length,
      Function.Bijective π ∧ ∀ i : Fin l'.length, l'.get i = l.get (π i)

  /-- The function returns a result r, and r equals the number of pairs (i,j) of indices such that 0 <= i < j < n and hours[i] + hours[j] is an exact multiple of 24 (equivalently, (hours[i] + hours[j]) mod 24 = 0; the sum is the exact integer sum, which does not overflow under these preconditions).
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_1 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        count_complete_day_pairs hours = ok r ∧ r.val = ↑(completeDayPairs (vals hours)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64,
          count_complete_day_pairs hours = ok r ∧ r.val = ↑(completeDayPairs (vals hours))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds on any input satisfying the preconditions.
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_2 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64, count_complete_day_pairs hours = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64, count_complete_day_pairs hours = ok r) := by
    sorry

  /-- The function returns a result r, and 0 <= r <= n*(n-1)/2.
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_3 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        count_complete_day_pairs hours = ok r ∧ 0 ≤ r.val ∧
          r.val ≤ ↑(hours.val.length * (hours.val.length - 1) / 2) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64,
          count_complete_day_pairs hours = ok r ∧ 0 ≤ r.val ∧
            r.val ≤ ↑(hours.val.length * (hours.val.length - 1) / 2)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if there do not exist indices i, j with 0 <= i < j < n and (hours[i] + hours[j]) mod 24 = 0.
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_4 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        count_complete_day_pairs hours = ok r ∧
          (r.val = 0 ↔
            ¬ ∃ (i j : Fin (vals hours).length),
              i < j ∧ IsCompleteDayPair ((vals hours).get i) ((vals hours).get j)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64,
          count_complete_day_pairs hours = ok r ∧
            (r.val = 0 ↔
              ¬ ∃ (i j : Fin (vals hours).length),
                i < j ∧ IsCompleteDayPair ((vals hours).get i) ((vals hours).get j))) := by
    sorry

  /-- For t = 0,1,...,23, let c_t be the number of indices i with 0 <= i < n and hours[i] mod 24 = t, where the remainder is taken in {0,...,23}. The function returns a result r, and r = C(c_0,2) + C(c_12,2) + sum_{a=1}^{11} c_a * c_{24-a}, where C(x,2) = x*(x-1)/2.
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_5 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        count_complete_day_pairs hours = ok r ∧ r.val = ↑(residuePairCount (vals hours)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64,
          count_complete_day_pairs hours = ok r ∧ r.val = ↑(residuePairCount (vals hours))) := by
    sorry

  /-- For each i with 0 <= i < n, let d_i be the number of indices j with 0 <= j < n, j != i, and (hours[i] + hours[j]) mod 24 = 0. The function returns a result r, and r = (1/2) * sum_{i=0}^{n-1} d_i.
    Preconditions: Let n = len(hours). The array satisfies 1 <= n <= 100 and 1 <= hours[i] <= 10^9 for every i with 0 <= i < n. -/
  theorem spec_6 (hours : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9) :
      ∃ r : Std.I64,
        count_complete_day_pairs hours = ok r ∧ r.val = ↑(neighborTotal (vals hours) / 2) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (hours : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9), ∃ r : Std.I64,
          count_complete_day_pairs hours = ok r ∧ r.val = ↑(neighborTotal (vals hours) / 2)) := by
    sorry

  /-- The function returns a result r for hours and a result r' for hours', and r = r'.
    Preconditions: Let hours and hours' be two arrays satisfying the input constraints, with n = len(hours) = len(hours'). Assume hours' is a permutation of hours: there exists a bijection pi from {0,...,n-1} to {0,...,n-1} such that hours'[i] = hours[pi(i)] for every i with 0 <= i < n. -/
  theorem spec_7 (hours hours' : Slice Std.I64)
      (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
      (hbounds : ∀ i : Fin hours.val.length,
        1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9)
      (hn'_pos : 1 ≤ hours'.val.length) (hn'_le : hours'.val.length ≤ 100)
      (hbounds' : ∀ i : Fin hours'.val.length,
        1 ≤ (hours'.val.get i).val ∧ (hours'.val.get i).val ≤ 10 ^ 9)
      (hperm : IsPermOf (vals hours) (vals hours')) :
      ∃ r r' : Std.I64,
        count_complete_day_pairs hours = ok r ∧ count_complete_day_pairs hours' = ok r' ∧
          r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (hours hours' : Slice Std.I64)
        (hn_pos : 1 ≤ hours.val.length) (hn_le : hours.val.length ≤ 100)
        (hbounds : ∀ i : Fin hours.val.length,
          1 ≤ (hours.val.get i).val ∧ (hours.val.get i).val ≤ 10 ^ 9)
        (hn'_pos : 1 ≤ hours'.val.length) (hn'_le : hours'.val.length ≤ 100)
        (hbounds' : ∀ i : Fin hours'.val.length,
          1 ≤ (hours'.val.get i).val ∧ (hours'.val.get i).val ≤ 10 ^ 9)
        (hperm : IsPermOf (vals hours) (vals hours')), ∃ r r' : Std.I64,
          count_complete_day_pairs hours = ok r ∧ count_complete_day_pairs hours' = ok r' ∧
            r.val = r'.val) := by
    sorry

  /-- Let r_old be the result returned for old and r_new the result returned for hours. Then r_new = r_old + d, where d is the number of indices i with 0 <= i < n and (old[i] + h) mod 24 = 0.
    Preconditions: Let old be an array satisfying the input constraints with len(old) = n, and let h be an integer with 1 <= h <= 10^9. Let hours be the array of length n+1 with hours[i] = old[i] for 0 <= i < n and hours[n] = h; assume n+1 <= 100, so hours also satisfies the input constraints. -/
  theorem spec_8 (old hours : Slice Std.I64) (h : ℤ)
      (hn_pos : 1 ≤ old.val.length) (hn_lt : old.val.length + 1 ≤ 100)
      (hbounds : ∀ i : Fin old.val.length,
        1 ≤ (old.val.get i).val ∧ (old.val.get i).val ≤ 10 ^ 9)
      (hh : 1 ≤ h ∧ h ≤ 10 ^ 9)
      (hhours : vals hours = vals old ++ [h]) :
      ∃ r_old r_new : Std.I64,
        count_complete_day_pairs old = ok r_old ∧
          count_complete_day_pairs hours = ok r_new ∧
            r_new.val = r_old.val +
              ↑((Finset.univ.filter
                  (fun i : Fin old.val.length =>
                    IsCompleteDayPair ((old.val.get i).val) h)).card) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (old hours : Slice Std.I64) (h : ℤ)
        (hn_pos : 1 ≤ old.val.length) (hn_lt : old.val.length + 1 ≤ 100)
        (hbounds : ∀ i : Fin old.val.length,
          1 ≤ (old.val.get i).val ∧ (old.val.get i).val ≤ 10 ^ 9)
        (hh : 1 ≤ h ∧ h ≤ 10 ^ 9)
        (hhours : vals hours = vals old ++ [h]), ∃ r_old r_new : Std.I64,
          count_complete_day_pairs old = ok r_old ∧
            count_complete_day_pairs hours = ok r_new ∧
              r_new.val = r_old.val +
                ↑((Finset.univ.filter
                    (fun i : Fin old.val.length =>
                      IsCompleteDayPair ((old.val.get i).val) h)).card)) := by
    sorry

  end AegisSpec.CountCompleteDayPairs
