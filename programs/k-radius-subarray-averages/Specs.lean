import Aegis.GetAverages.Code.Funs

/-!
# Specifications of `Aegis.GetAverages.get_averages`

LeetCode problem `k-radius-subarray-averages`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetAverages

open Aegis.GetAverages

def intAt (xs : List Std.I64) (i : Nat) : Option Int := (xs[i]?).map (fun x => x.val)

def winValues (nums : Slice Std.I64) (lo d : Nat) : List Int :=
  (List.range d).map (fun t => (intAt nums.val (lo + t)).getD 0)

def winSum (nums : Slice Std.I64) (lo d : Nat) : Int :=
  (winValues nums lo d).foldr (· + ·) 0

def winMin (nums : Slice Std.I64) (lo d : Nat) : Int :=
  match winValues nums lo d with
  | [] => 0
  | x :: xs => xs.foldl min x

def winMax (nums : Slice Std.I64) (lo d : Nat) : Int :=
  match winValues nums lo d with
  | [] => 0
  | x :: xs => xs.foldl max x

def winStart (k : Std.I64) (i : Nat) : Nat := i - k.val.toNat

def winWidth (k : Std.I64) : Nat := 2 * k.val.toNat + 1

/-- The function returns a result r and len(r) = n. For every i with 0 <= i < n: if i < k or i + k >= n, then r[i] = -1; otherwise r[i] = (sum_{j=i-k}^{i+k} nums[j]) / (2*k+1), where / denotes integer division truncating toward zero.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ (i : Nat) (hi : i < nums.val.length),
        ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int) →
            intAt r.val i = some (-1)) ∧
        (¬ ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            intAt r.val i =
              some (Int.tdiv (winSum nums (winStart k i) (winWidth k))
                ((winWidth k : Nat) : Int)))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ (i : Nat) (hi : i < nums.val.length),
        ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int) →
            intAt r.val i = some (-1)) ∧
        (¬ ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            intAt r.val i =
              some (Int.tdiv (winSum nums (winStart k i) (winWidth k))
                ((winWidth k : Nat) : Int))))) := by
  sorry

/-- The call get_averages nums k returns a result r; it does not fail, overflow, panic, or go out of bounds.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64, get_averages nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, get_averages nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, every element x of r satisfies -1 <= x <= 100000.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → ∀ x, x ∈ r.val → -1 ≤ x.val ∧ x.val ≤ 100000 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → ∀ x, x ∈ r.val → -1 ≤ x.val ∧ x.val ≤ 100000) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, for every i with 0 <= i < n, r[i] = -1 if and only if i < k or i + k >= n.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat) (hi : i < nums.val.length),
        (intAt r.val i = some (-1) ↔
          ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int))) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat) (hi : i < nums.val.length),
        (intAt r.val i = some (-1) ↔
          ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, for every i with k <= i and i + k < n, min { nums[j] | i-k <= j <= i+k } <= r[i] <= max { nums[j] | i-k <= j <= i+k }.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat), k.val ≤ (i : Int) → (i : Int) + k.val < (nums.val.length : Int) →
        (∀ v, intAt r.val i = some v →
          winMin nums (winStart k i) (winWidth k) ≤ v ∧
            v ≤ winMax nums (winStart k i) (winWidth k)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat), k.val ≤ (i : Int) → (i : Int) + k.val < (nums.val.length : Int) →
        (∀ v, intAt r.val i = some v →
          winMin nums (winStart k i) (winWidth k) ≤ v ∧
            v ≤ winMax nums (winStart k i) (winWidth k))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, for every i with k <= i and i + k < n, let S = sum_{j=i-k}^{i+k} nums[j] and d = 2*k+1. Then r[i] * d <= S < (r[i] + 1) * d.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat), k.val ≤ (i : Int) → (i : Int) + k.val < (nums.val.length : Int) →
        ∀ v, intAt r.val i = some v →
          v * ((winWidth k : Nat) : Int) ≤ winSum nums (winStart k i) (winWidth k) ∧
            winSum nums (winStart k i) (winWidth k) <
              (v + 1) * ((winWidth k : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ∀ (i : Nat), k.val ≤ (i : Int) → (i : Int) + k.val < (nums.val.length : Int) →
        ∀ v, intAt r.val i = some v →
          v * ((winWidth k : Nat) : Int) ≤ winSum nums (winStart k i) (winWidth k) ∧
            winSum nums (winStart k i) (winWidth k) <
              (v + 1) * ((winWidth k : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n and k = 0, for every i with 0 <= i < n, r[i] = nums[i].
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length → k.val = 0 →
      ∀ (i : Nat) (hi : i < nums.val.length),
        intAt r.val i = intAt nums.val i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length → k.val = 0 →
      ∀ (i : Nat) (hi : i < nums.val.length),
        intAt r.val i = intAt nums.val i) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n and k >= n, for every i with 0 <= i < n, r[i] = -1.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (nums.val.length : Int) ≤ k.val →
      ∀ (i : Nat) (hi : i < nums.val.length), intAt r.val i = some (-1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (nums.val.length : Int) ≤ k.val →
      ∀ (i : Nat) (hi : i < nums.val.length), intAt r.val i = some (-1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, if there is a value c such that for every j with 0 <= j < n, nums[j] = c, then for every i with 0 <= i < n: if i < k or i + k >= n then r[i] = -1, otherwise r[i] = c.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (∃ c : Int, ∀ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val = c) →
      ∀ (i : Nat) (hi : i < nums.val.length),
        (((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            intAt r.val i = some (-1)) ∧
        (¬ ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            ∃ c : Int, (∀ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val = c) ∧
              intAt r.val i = some c) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (∃ c : Int, ∀ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val = c) →
      ∀ (i : Nat) (hi : i < nums.val.length),
        (((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            intAt r.val i = some (-1)) ∧
        (¬ ((i : Int) < k.val ∨ (i : Int) + k.val ≥ (nums.val.length : Int)) →
            ∃ c : Int, (∀ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val = c) ∧
              intAt r.val i = some c)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, the number of indices i with 0 <= i < n and r[i] != -1 is max(0, n - 2*k).
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ((r.val.countP (fun x => x.val != -1) : Int) =
        max 0 ((nums.val.length : Int) - 2 * k.val)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      ((r.val.countP (fun x => x.val != -1) : Int) =
        max 0 ((nums.val.length : Int) - 2 * k.val))) := by
  sorry

/-- Whenever the function returns a result r with len(r) = n, if n >= 2*k + 1 then there exists an index i with 0 <= i < n such that r[i] != -1.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000, 0 <= k <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 100000. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (nums.val.length : Int) ≥ 2 * k.val + 1 →
      ∃ i, i < nums.val.length ∧ intAt r.val i ≠ some (-1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_ub : nums.val.length ≤ 100000)
    (hk_pos : 0 ≤ k.val) (hk_ub : k.val ≤ 100000)
    (hnums : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64,
      get_averages nums k = ok r → r.val.length = nums.val.length →
      (nums.val.length : Int) ≥ 2 * k.val + 1 →
      ∃ i, i < nums.val.length ∧ intAt r.val i ≠ some (-1)) := by
  sorry

end AegisSpec.GetAverages
