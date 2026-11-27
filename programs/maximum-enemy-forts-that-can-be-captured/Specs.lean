import Aegis.CaptureForts.Code.Funs

/-!
# Specifications of `Aegis.CaptureForts.capture_forts`

LeetCode problem `maximum-enemy-forts-that-can-be-captured`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CaptureForts

open Aegis.CaptureForts (capture_forts)

def vlist (forts : Slice Std.I64) : List ℤ := forts.val.map (fun x => x.val)

def Pre (forts : Slice Std.I64) : Prop :=
  1 ≤ (vlist forts).length ∧ (vlist forts).length ≤ 1000 ∧
    ∀ x, x ∈ vlist forts → x = -1 ∨ x = 0 ∨ x = 1

def span (i j : ℕ) : ℤ := (max i j : ℤ) - (min i j : ℤ)

def gap (i j : ℕ) : ℤ := span i j - 1

def IsPair (l : List ℤ) (i j : ℕ) : Prop :=
  i < l.length ∧ j < l.length ∧ l[i]? = some 1 ∧ l[j]? = some (-1) ∧
    ∀ k, min i j < k → k < max i j → l[k]? = some 0

def HasPair (l : List ℤ) : Prop := ∃ i j, IsPair l i j

def IsMaxGap (l : List ℤ) (r : ℤ) : Prop :=
  (∃ i j, IsPair l i j ∧ gap i j = r) ∧ ∀ i j, IsPair l i j → gap i j ≤ r

abbrev zeroBlock (l : List ℤ) (s len : ℕ) : Prop :=
  s + len ≤ l.length ∧ (l.drop s).take len = List.replicate len 0

def longestZeroRun (l : List ℤ) : ℕ :=
  ((List.range (l.length + 1)).filter (fun len =>
      (List.range (l.length + 1)).any (fun s => decide (zeroBlock l s len)))).foldr max 0

def sliceOfList (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 where
  leng := l.length
  list := Aeneas.Data.ListN.ListN.fromList l
  bound := h

def negValue (x : Std.I64) : Std.I64 := ⟨-x.bv⟩

def negForts (forts : Slice Std.I64) : Slice Std.I64 :=
  sliceOfList (forts.val.map negValue) (by
    rw [List.length_map]
    have h : forts.val.length = forts.leng := Aeneas.Data.ListN.ListN_length forts.list
    rw [h]
    exact forts.bound)

def reverseForts (forts : Slice Std.I64) : Slice Std.I64 :=
  sliceOfList forts.val.reverse (by
    rw [List.length_reverse]
    have h : forts.val.length = forts.leng := Aeneas.Data.ListN.ListN_length forts.list
    rw [h]
    exact forts.bound)

/-- The function returns a result r and the following holds. If there is no pair (i,j) with 0 <= i,j < n such that forts[i] = 1, forts[j] = -1, and forts[k] = 0 for every k with min(i,j) < k < max(i,j), then r = 0. Otherwise r = max { max(i,j) - min(i,j) - 1 | 0 <= i,j < n, forts[i] = 1, forts[j] = -1, and forts[k] = 0 for every k with min(i,j) < k < max(i,j) }.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_1 (forts : Slice Std.I64) (hpre : Pre forts) :
    ∃ r : Std.I64, capture_forts forts = ok r ∧
      (¬ HasPair (vlist forts) → r.val = 0) ∧
      (HasPair (vlist forts) → IsMaxGap (vlist forts) r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts), ∃ r : Std.I64, capture_forts forts = ok r ∧
      (¬ HasPair (vlist forts) → r.val = 0) ∧
      (HasPair (vlist forts) → IsMaxGap (vlist forts) r.val)) := by
  sorry

/-- For every forts satisfying the preconditions, the function returns a result r; it does not fail, overflow, access out of bounds, or panic.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_2 (forts : Slice Std.I64) (hpre : Pre forts) :
    ∃ r : Std.I64, capture_forts forts = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts), ∃ r : Std.I64, capture_forts forts = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= max(0, len(forts) - 2).
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_3 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r) :
    0 ≤ r.val ∧ r.val ≤ max 0 (((vlist forts).length : ℤ) - 2) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r), 0 ≤ r.val ∧ r.val ≤ max 0 (((vlist forts).length : ℤ) - 2)) := by
  sorry

/-- Whenever the function returns a result r, if there is no index i with 0 <= i < len(forts) and forts[i] = 1, then r = 0.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_4 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ i, i < (vlist forts).length ∧ (vlist forts)[i]? = some 1) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ i, i < (vlist forts).length ∧ (vlist forts)[i]? = some 1), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if there is no index j with 0 <= j < len(forts) and forts[j] = -1, then r = 0.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_5 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ j, j < (vlist forts).length ∧ (vlist forts)[j]? = some (-1)) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ j, j < (vlist forts).length ∧ (vlist forts)[j]? = some (-1)), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, if there is no index k with 0 <= k < len(forts) and forts[k] = 0, then r = 0.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_6 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ k, k < (vlist forts).length ∧ (vlist forts)[k]? = some 0) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r)
    (hno : ¬ ∃ k, k < (vlist forts).length ∧ (vlist forts)[k]? = some 0), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i,j < len(forts), forts[i] = 1, forts[j] = -1, and forts[k] = 0 for every k with min(i,j) < k < max(i,j), we have max(i,j) - min(i,j) - 1 <= r.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_7 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r) :
    ∀ i j, IsPair (vlist forts) i j → gap i j ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r), ∀ i j, IsPair (vlist forts) i j → gap i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if there exists at least one pair (i,j) with 0 <= i,j < len(forts), forts[i] = 1, forts[j] = -1, and forts[k] = 0 for every k with min(i,j) < k < max(i,j), then there exist such i and j for which r = max(i,j) - min(i,j) - 1.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_8 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r) :
    HasPair (vlist forts) → ∃ i j, IsPair (vlist forts) i j ∧ r.val = gap i j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r), HasPair (vlist forts) → ∃ i j, IsPair (vlist forts) i j ∧ r.val = gap i j) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist i and j with 0 <= i,j < len(forts), forts[i] = 1, forts[j] = -1, forts[k] = 0 for every k with min(i,j) < k < max(i,j), and max(i,j) - min(i,j) >= 2.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_9 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r) :
    0 < r.val ↔ ∃ i j, IsPair (vlist forts) i j ∧ 2 ≤ span i j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r), 0 < r.val ↔ ∃ i j, IsPair (vlist forts) i j ∧ 2 ≤ span i j) := by
  sorry

/-- Whenever the function returns a result r, r is at most the largest L such that for some s with 0 <= s and s + L <= len(forts), forts[k] = 0 for every k with s <= k < s + L. This largest L is well-defined because L = 0 is always allowed.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_10 (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r) :
    r.val ≤ (longestZeroRun (vlist forts) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r : Std.I64)
    (hr : capture_forts forts = ok r), r.val ≤ (longestZeroRun (vlist forts) : ℤ)) := by
  sorry

/-- Let r be the result returned by capture_forts on forts, and let r' be the result returned by capture_forts on the reverse of forts, defined by reverse(forts)[i] = forts[len(forts)-1-i] for 0 <= i < len(forts). Then r = r'.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_11 (forts : Slice Std.I64) (hpre : Pre forts) (r r' : Std.I64)
    (hr : capture_forts forts = ok r)
    (hr' : capture_forts (reverseForts forts) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r r' : Std.I64)
    (hr : capture_forts forts = ok r)
    (hr' : capture_forts (reverseForts forts) = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = n - 2.
  Preconditions: Let n = len(forts). 2 <= n <= 1000, for every i with 0 <= i < n, forts[i] in {-1,0,1}, either (forts[0] = 1 and forts[n-1] = -1) or (forts[0] = -1 and forts[n-1] = 1), and for every k with 0 < k < n-1, forts[k] = 0. -/
theorem spec_12 (forts : Slice Std.I64) (hpre : Pre forts) (h2 : 2 ≤ (vlist forts).length)
    (hends :
      ((vlist forts)[0]? = some 1 ∧ (vlist forts)[(vlist forts).length - 1]? = some (-1)) ∨
      ((vlist forts)[0]? = some (-1) ∧ (vlist forts)[(vlist forts).length - 1]? = some 1))
    (hmid : ∀ k, 0 < k → k < (vlist forts).length - 1 → (vlist forts)[k]? = some 0)
    (r : Std.I64) (hr : capture_forts forts = ok r) :
    r.val = ((vlist forts).length : ℤ) - 2 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (h2 : 2 ≤ (vlist forts).length)
    (hends :
      ((vlist forts)[0]? = some 1 ∧ (vlist forts)[(vlist forts).length - 1]? = some (-1)) ∨
      ((vlist forts)[0]? = some (-1) ∧ (vlist forts)[(vlist forts).length - 1]? = some 1))
    (hmid : ∀ k, 0 < k → k < (vlist forts).length - 1 → (vlist forts)[k]? = some 0)
    (r : Std.I64) (hr : capture_forts forts = ok r), r.val = ((vlist forts).length : ℤ) - 2) := by
  sorry

/-- Let r be the result returned by capture_forts on forts, and let r' be the result returned by capture_forts on neg(forts), defined by neg(forts)[i] = -forts[i] for 0 <= i < len(forts). Then r = r'.
  Preconditions: Let n = len(forts). 1 <= n <= 1000 and for every i with 0 <= i < n, forts[i] in {-1,0,1}. -/
theorem spec_13 (forts : Slice Std.I64) (hpre : Pre forts) (r r' : Std.I64)
    (hr : capture_forts forts = ok r)
    (hr' : capture_forts (negForts forts) = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (forts : Slice Std.I64) (hpre : Pre forts) (r r' : Std.I64)
    (hr : capture_forts forts = ok r)
    (hr' : capture_forts (negForts forts) = ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.CaptureForts
