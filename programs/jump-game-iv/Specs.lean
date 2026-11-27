import Aegis.MinJumps.Code.Funs

/-!
# Specifications of `Aegis.MinJumps.min_jumps`

LeetCode problem `jump-game-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinJumps

def value (arr : Slice Std.I64) (i : ℕ) : ℤ :=
  ((arr.val[i]?).map (fun x => x.val)).getD 0

def Step (arr : Slice Std.I64) (i j : ℕ) : Prop :=
  i + 1 = j ∨ j + 1 = i ∨ (i ≠ j ∧ value arr i = value arr j)

def Walk (arr : Slice Std.I64) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  x 0 = 0 ∧ x k = arr.val.length - 1 ∧
    (∀ t, t ≤ k → x t < arr.val.length) ∧
    (∀ t, 1 ≤ t → t ≤ k → Step arr (x (t - 1)) (x t))

/-- Whenever min_jumps(arr) returns a result r, r equals the least integer k >= 0 for which there is a sequence of indices x_0, x_1, ..., x_k such that 0 <= x_t < n for every t, x_0 = 0, x_k = n - 1, and for every t with 1 <= t <= k, either |x_t - x_{t-1}| = 1 or (x_t != x_{t-1} and arr[x_t] = arr[x_{t-1}]).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    (∃ (k : ℕ) (x : ℕ → ℕ), (k : ℤ) = r.val ∧ Walk arr k x) ∧
      (∀ (k : ℕ) (x : ℕ → ℕ), Walk arr k x → r.val ≤ (k : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), (∃ (k : ℕ) (x : ℕ → ℕ), (k : ℤ) = r.val ∧ Walk arr k x) ∧
      (∀ (k : ℕ) (x : ℕ → ℕ), Walk arr k x → r.val ≤ (k : ℤ))) := by
  sorry

/-- For every arr satisfying the preconditions, min_jumps(arr) returns a result; that is, it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8) :
    ∃ r : Std.I64, Aegis.MinJumps.min_jumps arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8), ∃ r : Std.I64, Aegis.MinJumps.min_jumps arr = ok r) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, 0 <= r <= n - 1.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    0 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), 0 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) - 1) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, r = 0 if and only if n = 1.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    r.val = 0 ↔ arr.val.length = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), r.val = 0 ↔ arr.val.length = 1) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, r = 1 if and only if (n = 2 or (n > 1 and arr[0] = arr[n - 1])).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    r.val = 1 ↔ (arr.val.length = 2 ∨
      (1 < arr.val.length ∧ value arr 0 = value arr (arr.val.length - 1))) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), r.val = 1 ↔ (arr.val.length = 2 ∨
      (1 < arr.val.length ∧ value arr 0 = value arr (arr.val.length - 1)))) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, if arr[i] != arr[j] for all 0 <= i < j < n, then r = n - 1.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hdistinct : ∀ (i j : ℕ), i < j → j < arr.val.length → value arr i ≠ value arr j) :
    r.val = (arr.val.length : ℤ) - 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hdistinct : ∀ (i j : ℕ), i < j → j < arr.val.length → value arr i ≠ value arr j), r.val = (arr.val.length : ℤ) - 1) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, if n > 1, then for every index k with 1 <= k < n and arr[k] = arr[0], we have r <= n - k.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_7 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hn : 1 < arr.val.length)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < arr.val.length)
    (hk_eq : value arr k = value arr 0) :
    r.val ≤ (arr.val.length : ℤ) - (k : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hn : 1 < arr.val.length)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_lt : k < arr.val.length)
    (hk_eq : value arr k = value arr 0), r.val ≤ (arr.val.length : ℤ) - (k : ℤ)) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, if n > 1, then for every index k with 0 <= k < n - 1 and arr[k] = arr[n - 1], we have r <= k + 1.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_8 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hn : 1 < arr.val.length)
    (k : ℕ) (hk_lt : k < arr.val.length - 1)
    (hk_eq : value arr k = value arr (arr.val.length - 1)) :
    r.val ≤ (k : ℤ) + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hn : 1 < arr.val.length)
    (k : ℕ) (hk_lt : k < arr.val.length - 1)
    (hk_eq : value arr k = value arr (arr.val.length - 1)), r.val ≤ (k : ℤ) + 1) := by
  sorry

/-- Let rev(arr) be the slice of length n with rev(arr)[i] = arr[n - 1 - i] for every 0 <= i < n. Whenever min_jumps(arr) returns a result r and min_jumps(rev(arr)) returns a result s, we have r = s.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_9 (arr rev : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (hrev : rev.val = arr.val.reverse)
    (r s : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hs : Aegis.MinJumps.min_jumps rev = ok s) :
    r = s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr rev : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (hrev : rev.val = arr.val.reverse)
    (r s : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hs : Aegis.MinJumps.min_jumps rev = ok s), r = s) := by
  sorry

/-- For any two slices arr and brr of the same length n satisfying the preconditions, if for all 0 <= i < n and 0 <= j < n, arr[i] = arr[j] if and only if brr[i] = brr[j], then whenever min_jumps(arr) returns a result r and min_jumps(brr) returns a result s, we have r = s.
  Preconditions: Let n = len(arr) = len(brr). Both arr and brr satisfy 1 <= n <= 50000 and -10^8 <= each entry <= 10^8. -/
theorem spec_10 (arr brr : Slice Std.I64)
    (hlen : arr.val.length = brr.val.length)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds_arr : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (hbounds_brr : ∀ (i : ℕ), i < brr.val.length →
      -(10 ^ 8 : ℤ) ≤ value brr i ∧ value brr i ≤ 10 ^ 8)
    (hpattern : ∀ (i j : ℕ), i < arr.val.length → j < arr.val.length →
      (value arr i = value arr j ↔ value brr i = value brr j))
    (r s : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hs : Aegis.MinJumps.min_jumps brr = ok s) :
    r = s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr brr : Slice Std.I64)
    (hlen : arr.val.length = brr.val.length)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds_arr : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (hbounds_brr : ∀ (i : ℕ), i < brr.val.length →
      -(10 ^ 8 : ℤ) ≤ value brr i ∧ value brr i ≤ 10 ^ 8)
    (hpattern : ∀ (i j : ℕ), i < arr.val.length → j < arr.val.length →
      (value arr i = value arr j ↔ value brr i = value brr j))
    (r s : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r)
    (hs : Aegis.MinJumps.min_jumps brr = ok s), r = s) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, there exists a sequence of indices x_0, x_1, ..., x_r such that 0 <= x_t < n for every t, x_0 = 0, x_r = n - 1, and for every t with 1 <= t <= r, either |x_t - x_{t-1}| = 1 or (x_t != x_{t-1} and arr[x_t] = arr[x_{t-1}]).
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_11 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    ∃ (k : ℕ) (x : ℕ → ℕ), (k : ℤ) = r.val ∧ Walk arr k x := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), ∃ (k : ℕ) (x : ℕ → ℕ), (k : ℤ) = r.val ∧ Walk arr k x) := by
  sorry

/-- Whenever min_jumps(arr) returns a result r, for every integer k >= 0 and every sequence of indices y_0, y_1, ..., y_k such that 0 <= y_t < n for every t, y_0 = 0, y_k = n - 1, and for every t with 1 <= t <= k, either |y_t - y_{t-1}| = 1 or (y_t != y_{t-1} and arr[y_t] = arr[y_{t-1}]), we have k >= r.
  Preconditions: Let n = len(arr). The input satisfies 1 <= n <= 50000 and -10^8 <= arr[i] <= 10^8 for every 0 <= i < n. -/
theorem spec_12 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r) :
    ∀ (k : ℕ) (y : ℕ → ℕ), Walk arr k y → r.val ≤ (k : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ), i < arr.val.length →
      -(10 ^ 8 : ℤ) ≤ value arr i ∧ value arr i ≤ 10 ^ 8)
    (r : Std.I64) (hr : Aegis.MinJumps.min_jumps arr = ok r), ∀ (k : ℕ) (y : ℕ → ℕ), Walk arr k y → r.val ≤ (k : ℤ)) := by
  sorry

end AegisSpec.MinJumps
