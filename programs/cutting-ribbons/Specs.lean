import Aegis.MaxLength.Code.Funs

/-!
# Specifications of `Aegis.MaxLength.max_length`

LeetCode problem `cutting-ribbons`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxLength

open Aegis.MaxLength

def pieces (ribbons : Slice I64) (x : ℤ) : ℤ :=
  (ribbons.val.map (fun r => Int.ediv r.val x)).sum

def totalLength (ribbons : Slice I64) : ℤ :=
  (ribbons.val.map (fun r => r.val)).sum

def maxRibbon (ribbons : Slice I64) : ℤ :=
  ribbons.val.foldl (fun acc x => max acc x.val) 0

def minRibbon (ribbons : Slice I64) : ℤ :=
  match ribbons.val with
  | [] => 0
  | x :: xs => xs.foldl (fun acc y => min acc y.val) x.val

def feasible (ribbons : Slice I64) (k : I64) (x : ℤ) : Prop :=
  0 < x ∧ k.val ≤ pieces ribbons x

def candidateSet (ribbons : Slice I64) (k : I64) : Set ℤ :=
  {0} ∪ {x : ℤ | feasible ribbons k x}

def PointwiseLe (l₁ l₂ : List I64) : Prop :=
  ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
    (l₁.get ⟨i, h₁⟩).val ≤ (l₂.get ⟨i, h₂⟩).val

/-- The function returns a result r, and r is the maximum of the set {0} union { x : x is an integer, x > 0, and sum_{i=0}^{len(ribbons)-1} floor(ribbons[i] / x) >= k }, where floor is integer division.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_1 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ r : I64, max_length ribbons k = ok r ∧ IsGreatest (candidateSet ribbons k) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∃ r : I64, max_length ribbons k = ok r ∧ IsGreatest (candidateSet ribbons k) r.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, the candidate length r is feasible: sum_{i=0}^{len(ribbons)-1} floor(ribbons[i] / r) >= k.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_2 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val) :
    k.val ≤ pieces ribbons r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val), k.val ≤ pieces ribbons r.val) := by
  sorry

/-- Whenever the function returns a result r with r > 0, every integer x with x > r is infeasible: sum_{i=0}^{len(ribbons)-1} floor(ribbons[i] / x) < k.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_3 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val)
    (x : ℤ) (hx : r.val < x) :
    pieces ribbons x < k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val)
    (x : ℤ) (hx : r.val < x), pieces ribbons x < k.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if sum_{i=0}^{len(ribbons)-1} ribbons[i] < k.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_4 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) :
    (r.val = 0 ↔ totalLength ribbons < k.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r), (r.val = 0 ↔ totalLength ribbons < k.val)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= max_{0 <= i < len(ribbons)} ribbons[i].
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_5 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) :
    0 ≤ r.val ∧ r.val ≤ maxRibbon ribbons := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r), 0 ≤ r.val ∧ r.val ≤ maxRibbon ribbons) := by
  sorry

/-- Whenever the function returns a result r, r * k <= sum_{i=0}^{len(ribbons)-1} ribbons[i].
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_6 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) :
    r.val * k.val ≤ totalLength ribbons := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r), r.val * k.val ≤ totalLength ribbons) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exists an index i with 0 <= i < len(ribbons) such that ribbons[i] >= r.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_7 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val) :
    ∃ x ∈ ribbons.val, r.val ≤ x.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) (hr_pos : 0 < r.val), ∃ x ∈ ribbons.val, r.val ≤ x.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer x with 1 <= x <= r, sum_{i=0}^{len(ribbons)-1} floor(ribbons[i] / x) >= k.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_8 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r)
    (x : ℤ) (hx_ge : 1 ≤ x) (hx_le : x ≤ r.val) :
    k.val ≤ pieces ribbons x := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r)
    (x : ℤ) (hx_ge : 1 ≤ x) (hx_le : x ≤ r.val), k.val ≤ pieces ribbons x) := by
  sorry

/-- For every ribbons and k satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_9 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000) :
    ∃ r : I64, max_length ribbons k = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000), ∃ r : I64, max_length ribbons k = ok r) := by
  sorry

/-- The result of max_length(ribbons', k) equals the result of max_length(ribbons, k).
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, 1 <= k <= 1000000000, and ribbons' is any slice of i64 obtained by permuting the entries of ribbons. -/
theorem spec_10 (ribbons ribbons' : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_perm : ribbons'.val.Perm ribbons.val) :
    max_length ribbons' k = max_length ribbons k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (ribbons ribbons' : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_perm : ribbons'.val.Perm ribbons.val), max_length ribbons' k = max_length ribbons k) := by
  sorry

/-- If max_length(ribbons, k) returns r and max_length(ribbons', k) returns r', then r <= r'.
  Preconditions: ribbons and ribbons' are slices of i64 of the same length, both satisfy len >= 1, len <= 100000, and all entries are between 1 and 100000; 1 <= k <= 1000000000; and for every i with 0 <= i < len(ribbons), ribbons[i] <= ribbons'[i]. -/
theorem spec_11 (ribbons ribbons' : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_len_ge' : 1 ≤ ribbons'.val.length) (h_len_le' : ribbons'.val.length ≤ 100000)
    (h_entries' : ∀ x ∈ ribbons'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_same_len : ribbons'.val.length = ribbons.val.length)
    (h_pointwise : PointwiseLe ribbons.val ribbons'.val)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r r' : I64) (hr : max_length ribbons k = ok r) (hr' : max_length ribbons' k = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (ribbons ribbons' : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_len_ge' : 1 ≤ ribbons'.val.length) (h_len_le' : ribbons'.val.length ≤ 100000)
    (h_entries' : ∀ x ∈ ribbons'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_same_len : ribbons'.val.length = ribbons.val.length)
    (h_pointwise : PointwiseLe ribbons.val ribbons'.val)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r r' : I64) (hr : max_length ribbons k = ok r) (hr' : max_length ribbons' k = ok r'), r.val ≤ r'.val) := by
  sorry

/-- If max_length(ribbons, k1) returns r1 and max_length(ribbons, k2) returns r2, then r2 <= r1.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k1 <= k2 <= 1000000000. -/
theorem spec_12 (ribbons : Slice I64) (k1 k2 : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k1 : 1 ≤ k1.val) (h_k_mono : k1.val ≤ k2.val) (h_k2 : k2.val ≤ 1000000000)
    (r1 r2 : I64) (hr1 : max_length ribbons k1 = ok r1) (hr2 : max_length ribbons k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (ribbons : Slice I64) (k1 k2 : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k1 : 1 ≤ k1.val) (h_k_mono : k1.val ≤ k2.val) (h_k2 : k2.val ≤ 1000000000)
    (r1 r2 : I64) (hr1 : max_length ribbons k1 = ok r1) (hr2 : max_length ribbons k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Let M = max_{0 <= i < len(ribbons)} ribbons[i]. Whenever the function returns a result r, r = M if and only if the number of indices i with ribbons[i] = M is at least k.
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, and 1 <= k <= 1000000000. -/
theorem spec_13 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r) :
    (r.val = maxRibbon ribbons ↔
      k.val ≤ ((ribbons.val.filter (fun x => x.val = maxRibbon ribbons)).length : ℤ)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (r : I64) (hr : max_length ribbons k = ok r), (r.val = maxRibbon ribbons ↔
      k.val ≤ ((ribbons.val.filter (fun x => x.val = maxRibbon ribbons)).length : ℤ))) := by
  sorry

/-- Whenever the function returns a result r, r >= min_{0 <= i < len(ribbons)} ribbons[i].
  Preconditions: len(ribbons) >= 1, len(ribbons) <= 100000, for every i with 0 <= i < len(ribbons), 1 <= ribbons[i] <= 100000, 1 <= k <= 1000000000, and k <= len(ribbons). -/
theorem spec_14 (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_k_len : k.val ≤ (ribbons.val.length : ℤ))
    (r : I64) (hr : max_length ribbons k = ok r) :
    minRibbon ribbons ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (ribbons : Slice I64) (k : I64)
    (h_len_ge : 1 ≤ ribbons.val.length) (h_len_le : ribbons.val.length ≤ 100000)
    (h_entries : ∀ x ∈ ribbons.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h_k : 1 ≤ k.val ∧ k.val ≤ 1000000000)
    (h_k_len : k.val ≤ (ribbons.val.length : ℤ))
    (r : I64) (hr : max_length ribbons k = ok r), minRibbon ribbons ≤ r.val) := by
  sorry

end AegisSpec.MaxLength
