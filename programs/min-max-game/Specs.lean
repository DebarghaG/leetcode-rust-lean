import Aegis.MinMaxGame.Code.Funs

/-!
# Specifications of `Aegis.MinMaxGame.min_max_game`

LeetCode problem `min-max-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinMaxGame

namespace AegisSpec.MinMaxGame

def valueAt (l : List Std.I64) (i : ℕ) (hi : i < l.length) : ℤ := l[i].val

def Occurs {α : Type} (x : α) (l : List α) : Prop := ∃ j : ℕ, l[j]? = some x

def listMin : List ℤ → ℤ
  | [] => 0
  | a :: l => l.foldr min a

def listMax : List ℤ → ℤ
  | [] => 0
  | a :: l => l.foldr max a

def EntriesInRange (l : List Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), 1 ≤ valueAt l i hi ∧ valueAt l i hi ≤ 1000000000

def round (l : List ℤ) : List ℤ :=
  (List.range (l.length / 2)).map fun j =>
    if j % 2 = 0 then min (l.getD (2 * j) 0) (l.getD (2 * j + 1) 0)
    else max (l.getD (2 * j) 0) (l.getD (2 * j + 1) 0)

theorem round_length (l : List ℤ) : (round l).length = l.length / 2 := by
  simp [round]

def R : List ℤ → ℤ
  | [] => 0
  | [a] => a
  | a :: b :: rest => R (round (a :: b :: rest))
termination_by l => l.length
decreasing_by
  simp only [round_length, List.length_cons]
  omega

/-- The function returns a result r and r = R(nums), where R is defined for any nonempty slice A whose length m is a power of 2 by: if m = 1 then R(A) = A[0]; if m > 1 then let B be the slice of length m/2 such that B[j] = min(A[2*j], A[2*j+1]) for every even j with 0 <= j < m/2, and B[j] = max(A[2*j], A[2*j+1]) for every odd j with 0 <= j < m/2; then R(A) = R(B).
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; there is an integer k >= 0 with n = 2^k; and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val) :
    ∃ r : Std.I64, min_max_game nums = ok r ∧ r.val = R (nums.val.map fun x => x.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val), ∃ r : Std.I64, min_max_game nums = ok r ∧ r.val = R (nums.val.map fun x => x.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns Ok r; in particular, it never fails with an i64 overflow, an out-of-bounds access, or a panic.
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; n is a power of 2; and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val) :
    ∃ r : Std.I64, min_max_game nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val), ∃ r : Std.I64, min_max_game nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists an index j with 0 <= j < len(nums) such that r = nums[j].
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; n is a power of 2; and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (r : Std.I64) (hr : min_max_game nums = ok r) :
    Occurs r nums.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (r : Std.I64) (hr : min_max_game nums = ok r), Occurs r nums.val) := by
  sorry

/-- Whenever the function returns a result r, min_{0 <= i < len(nums)} nums[i] <= r <= max_{0 <= i < len(nums)} nums[i]. Consequently, since all entries satisfy 1 <= nums[i] <= 1000000000, also 1 <= r <= 1000000000.
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; n is a power of 2; and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (r : Std.I64) (hr : min_max_game nums = ok r) :
    listMin (nums.val.map fun x => x.val) ≤ r.val ∧
      r.val ≤ listMax (nums.val.map fun x => x.val) ∧
      1 ≤ r.val ∧ r.val ≤ 1000000000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (r : Std.I64) (hr : min_max_game nums = ok r), listMin (nums.val.map fun x => x.val) ≤ r.val ∧
      r.val ≤ listMax (nums.val.map fun x => x.val) ∧
      1 ≤ r.val ∧ r.val ≤ 1000000000) := by
  sorry

/-- Whenever the function returns a result r, r <= min(nums[0], nums[1]).
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; n is a power of 2; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; and n >= 2. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hn_two : 2 ≤ nums.val.length)
    (r : Std.I64) (hr : min_max_game nums = ok r) :
    r.val ≤ min (valueAt nums.val 0 (by omega)) (valueAt nums.val 1 (by omega)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hn_two : 2 ≤ nums.val.length)
    (r : Std.I64) (hr : min_max_game nums = ok r), r.val ≤ min (valueAt nums.val 0 (by omega)) (valueAt nums.val 1 (by omega))) := by
  sorry

/-- The function returns v.
  Preconditions: Let n = len(nums). All slice indices are 0-based. Preconditions: 1 <= n <= 1024; n is a power of 2; for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000; and there exists an integer v such that nums[i] = v for every i with 0 <= i < n. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (v : ℤ) (hv : ∀ (i : ℕ) (hi : i < nums.val.length), valueAt nums.val i hi = v) :
    ∃ r : Std.I64, min_max_game nums = ok r ∧ r.val = v := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (v : ℤ) (hv : ∀ (i : ℕ) (hi : i < nums.val.length), valueAt nums.val i hi = v), ∃ r : Std.I64, min_max_game nums = ok r ∧ r.val = v) := by
  sorry

/-- Let r1 be the result returned by min_max_game(nums) and let r2 be the result returned by min_max_game(other). Both calls return results, and r1 <= r2.
  Preconditions: Let n = len(nums). All slice indices are 0-based. Both nums and other are slices of length n. Preconditions for each: 1 <= n <= 1024; n is a power of 2; all entries of both slices lie in [1, 1000000000]. Additionally, for every i with 0 <= i < n, nums[i] <= other[i]. -/
theorem spec_7 (nums other : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hlen : other.val.length = nums.val.length)
    (hother_range : EntriesInRange other.val)
    (hpoint : ∀ (i : ℕ) (hi : i < nums.val.length),
      valueAt nums.val i hi ≤ valueAt other.val i (by omega)) :
    ∃ r1 r2 : Std.I64,
      min_max_game nums = ok r1 ∧ min_max_game other = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums other : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hlen : other.val.length = nums.val.length)
    (hother_range : EntriesInRange other.val)
    (hpoint : ∀ (i : ℕ) (hi : i < nums.val.length),
      valueAt nums.val i hi ≤ valueAt other.val i (by omega)), ∃ r1 r2 : Std.I64,
      min_max_game nums = ok r1 ∧ min_max_game other = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Let r be the result returned by min_max_game(nums) and let r' be the result returned by min_max_game(shifted). Both calls return results, and r' = r + c.
  Preconditions: Let n = len(nums). All slice indices are 0-based. The slice nums satisfies 1 <= n <= 1024, n is a power of 2, and 1 <= nums[i] <= 1000000000 for all i. Let c be an integer and let shifted be a slice of length n such that shifted[i] = nums[i] + c for every i with 0 <= i < n, and shifted also satisfies 1 <= n <= 1024, n is a power of 2, and 1 <= shifted[i] <= 1000000000 for all i. -/
theorem spec_8 (nums shifted : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hlen : shifted.val.length = nums.val.length)
    (hshifted_range : EntriesInRange shifted.val)
    (hshift : ∀ (i : ℕ) (hi : i < nums.val.length),
      valueAt shifted.val i (by omega) = valueAt nums.val i hi + c) :
    ∃ r r' : Std.I64,
      min_max_game nums = ok r ∧ min_max_game shifted = ok r' ∧ r'.val = r.val + c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums shifted : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hlen : shifted.val.length = nums.val.length)
    (hshifted_range : EntriesInRange shifted.val)
    (hshift : ∀ (i : ℕ) (hi : i < nums.val.length),
      valueAt shifted.val i (by omega) = valueAt nums.val i hi + c), ∃ r r' : Std.I64,
      min_max_game nums = ok r ∧ min_max_game shifted = ok r' ∧ r'.val = r.val + c) := by
  sorry

/-- Let r be the result returned by min_max_game(nums) and let r' be the result returned by min_max_game(swapped). Both calls return results, and r' = r.
  Preconditions: Let n = len(nums). All slice indices are 0-based. The slice nums satisfies 1 <= n <= 1024, n is a power of 2, and 1 <= nums[i] <= 1000000000 for all i. Let j be an integer with 0 <= j < n/2, and let swapped be the slice of length n defined by swapped[2*j] = nums[2*j+1], swapped[2*j+1] = nums[2*j], and swapped[i] = nums[i] for all other indices i. -/
theorem spec_9 (nums swapped : Slice Std.I64) (j : ℕ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hj : j < nums.val.length / 2)
    (hlen : swapped.val.length = nums.val.length)
    (hswap_even : valueAt swapped.val (2 * j) (by omega) =
      valueAt nums.val (2 * j + 1) (by omega))
    (hswap_odd : valueAt swapped.val (2 * j + 1) (by omega) =
      valueAt nums.val (2 * j) (by omega))
    (hother : ∀ (i : ℕ) (hi : i < nums.val.length), i ≠ 2 * j → i ≠ 2 * j + 1 →
      valueAt swapped.val i (by omega) = valueAt nums.val i hi) :
    ∃ r r' : Std.I64,
      min_max_game nums = ok r ∧ min_max_game swapped = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums swapped : Slice Std.I64) (j : ℕ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1024)
    (k : ℕ) (hn_pow : nums.val.length = 2 ^ k)
    (hn_range : EntriesInRange nums.val)
    (hj : j < nums.val.length / 2)
    (hlen : swapped.val.length = nums.val.length)
    (hswap_even : valueAt swapped.val (2 * j) (by omega) =
      valueAt nums.val (2 * j + 1) (by omega))
    (hswap_odd : valueAt swapped.val (2 * j + 1) (by omega) =
      valueAt nums.val (2 * j) (by omega))
    (hother : ∀ (i : ℕ) (hi : i < nums.val.length), i ≠ 2 * j → i ≠ 2 * j + 1 →
      valueAt swapped.val i (by omega) = valueAt nums.val i hi), ∃ r r' : Std.I64,
      min_max_game nums = ok r ∧ min_max_game swapped = ok r' ∧ r'.val = r.val) := by
  sorry

end AegisSpec.MinMaxGame
