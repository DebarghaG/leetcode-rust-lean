import Aegis.CircularArrayLoop.Code.Funs

/-!
# Specifications of `Aegis.CircularArrayLoop.circular_array_loop`

LeetCode problem `circular-array-loop`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CircularArrayLoop

  def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun (x : Std.I64) => x.val)

  def entry (nums : Slice Std.I64) (i : ℕ) : ℤ := (contents nums).getD i 0

  def ValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.length ∧ nums.length ≤ 5000 ∧
      ∀ i, i < nums.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000 ∧ entry nums i ≠ 0

  def step (nums : Slice Std.I64) (x : ℕ) : ℤ := (x : ℤ) + entry nums x

  def nextIdx (nums : Slice Std.I64) (x : ℕ) : ℕ := (step nums x % (nums.length : ℤ)).toNat

  def IsCycle (nums : Slice Std.I64) (k : ℕ) (ix : ℕ → ℕ) : Prop :=
    2 ≤ k ∧ k ≤ nums.length ∧
      (∀ j, j < k → ix j < nums.length) ∧
      (∀ j₁, j₁ < k → ∀ j₂, j₂ < k → ix j₁ = ix j₂ → j₁ = j₂) ∧
      (∀ j, j < k - 1 → nextIdx nums (ix j) = ix (j + 1)) ∧
      nextIdx nums (ix (k - 1)) = ix 0 ∧
      ((∀ j, j < k → 0 < entry nums (ix j)) ∨ (∀ j, j < k → entry nums (ix j) < 0))

  def SameSign (a b : ℤ) : Prop := (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)

  def OddInt (v : ℤ) : Prop := v % 2 = 1

  /-- The function returns a result r (it does not fail), and r = true if and only if there exist an integer k and indices i_0, ..., i_{k-1} such that: 2 <= k <= n; i_0, ..., i_{k-1} are pairwise distinct and each lies in [0, n-1]; for every j with 0 <= j < k-1, next(i_j) = i_{j+1}, and next(i_{k-1}) = i_0, where next(x) is the unique index y with 0 <= y < n and y is congruent to x + nums[x] modulo n; and either nums[i_j] > 0 for every j with 0 <= j < k, or nums[i_j] < 0 for every j with 0 <= j < k. If no such k and indices exist, then r = false.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
  theorem spec_1 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∃ r : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          (r = true ↔ ∃ (k : ℕ) (ix : ℕ → ℕ), IsCycle nums k ix) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            (r = true ↔ ∃ (k : ℕ) (ix : ℕ → ℕ), IsCycle nums k ix)) := by
    sorry

  /-- The function returns a result r; equivalently, the call does not fail (no panic, out-of-bounds, or arithmetic failure) for any input satisfying the preconditions.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
  theorem spec_2 (nums : Slice Std.I64) (h : ValidInput nums) :
      ∃ r : Bool, Aegis.CircularArrayLoop.circular_array_loop nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums), ∃ r : Bool, Aegis.CircularArrayLoop.circular_array_loop nums = ok r) := by
    sorry

  /-- The function returns a result r with r = false.
    Preconditions: Let n = len(nums). n = 1. Also -1000 <= nums[0] <= 1000 and nums[0] != 0. -/
  theorem spec_3 (nums : Slice Std.I64) (hlen : nums.length = 1)
      (hb : -1000 ≤ entry nums 0 ∧ entry nums 0 ≤ 1000 ∧ entry nums 0 ≠ 0) :
      ∃ r : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧ r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.length = 1)
        (hb : -1000 ≤ entry nums 0 ∧ entry nums 0 ≤ 1000 ∧ entry nums 0 ≠ 0), ∃ r : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧ r = false) := by
    sorry

  /-- The function returns a result r. r = true if and only if nums[0] and nums[1] have the same sign (both positive or both negative) and both nums[0] and nums[1] are odd (equivalently, each is congruent to 1 modulo 2). In all other cases r = false.
    Preconditions: Let n = len(nums). n = 2. For i = 0 and i = 1, -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
  theorem spec_4 (nums : Slice Std.I64) (hlen : nums.length = 2)
      (hb : ∀ i, i < 2 →
        -1000 ≤ entry nums i ∧ entry nums i ≤ 1000 ∧ entry nums i ≠ 0) :
      ∃ r : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          (r = true ↔
            SameSign (entry nums 0) (entry nums 1) ∧
              OddInt (entry nums 0) ∧ OddInt (entry nums 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen : nums.length = 2)
        (hb : ∀ i, i < 2 →
          -1000 ≤ entry nums i ∧ entry nums i ≤ 1000 ∧ entry nums i ≠ 0), ∃ r : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            (r = true ↔
              SameSign (entry nums 0) (entry nums 1) ∧
                OddInt (entry nums 0) ∧ OddInt (entry nums 1))) := by
    sorry

  /-- The function returns a result r with r = true.
    Preconditions: Let n = len(nums). 2 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. Either nums[i] > 0 for every i with 0 <= i < n, or nums[i] < 0 for every i with 0 <= i < n. For every i with 0 <= i < n, n does not divide nums[i]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : 2 ≤ nums.length ∧ nums.length ≤ 5000)
      (hb : ∀ i, i < nums.length →
        -1000 ≤ entry nums i ∧ entry nums i ≤ 1000 ∧ entry nums i ≠ 0)
      (hsame : (∀ i, i < nums.length → 0 < entry nums i) ∨
        (∀ i, i < nums.length → entry nums i < 0))
      (hndvd : ∀ i, i < nums.length → ¬ (nums.length : ℤ) ∣ entry nums i) :
      ∃ r : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧ r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : 2 ≤ nums.length ∧ nums.length ≤ 5000)
        (hb : ∀ i, i < nums.length →
          -1000 ≤ entry nums i ∧ entry nums i ≤ 1000 ∧ entry nums i ≠ 0)
        (hsame : (∀ i, i < nums.length → 0 < entry nums i) ∨
          (∀ i, i < nums.length → entry nums i < 0))
        (hndvd : ∀ i, i < nums.length → ¬ (nums.length : ℤ) ∣ entry nums i), ∃ r : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧ r = true) := by
    sorry

  /-- Let r be the result on nums and r_rot be the result on rot. Both calls return results, and r_rot = r.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. Let t be an integer with 0 <= t < n, and define rot by rot[i] = nums[(i + t) mod n] for 0 <= i < n. -/
  theorem spec_6 (nums rot : Slice Std.I64) (t : ℕ)
      (h : ValidInput nums) (ht : t < nums.length)
      (hrot : contents rot = (contents nums).rotate t) :
      ∃ r r' : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          Aegis.CircularArrayLoop.circular_array_loop rot = ok r' ∧ r' = r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums rot : Slice Std.I64) (t : ℕ)
        (h : ValidInput nums) (ht : t < nums.length)
        (hrot : contents rot = (contents nums).rotate t), ∃ r r' : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            Aegis.CircularArrayLoop.circular_array_loop rot = ok r' ∧ r' = r) := by
    sorry

  /-- Let r be the result on nums and r_mirror be the result on mirror. Both calls return results, and r_mirror = r.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. Define mirror by mirror[i] = -nums[n - 1 - i] for 0 <= i < n. -/
  theorem spec_7 (nums mirror : Slice Std.I64)
      (h : ValidInput nums)
      (hmirror : contents mirror = (contents nums).reverse.map (fun v => -v)) :
      ∃ r r' : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          Aegis.CircularArrayLoop.circular_array_loop mirror = ok r' ∧ r' = r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums mirror : Slice Std.I64)
        (h : ValidInput nums)
        (hmirror : contents mirror = (contents nums).reverse.map (fun v => -v)), ∃ r r' : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            Aegis.CircularArrayLoop.circular_array_loop mirror = ok r' ∧ r' = r) := by
    sorry

  /-- Let r be the result on nums and r' be the result on nums'. Both calls return results, and r' = r.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. Let nums' be another array of length n satisfying the same bounds and nonzero conditions, and such that for every i with 0 <= i < n, nums'[i] is congruent to nums[i] modulo n and nums'[i] has the same sign as nums[i] (both positive or both negative). -/
  theorem spec_8 (nums nums' : Slice Std.I64)
      (h : ValidInput nums)
      (hlen : nums'.length = nums.length)
      (hb : ∀ i, i < nums'.length →
        -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000 ∧ entry nums' i ≠ 0)
      (hcong : ∀ i, i < nums.length →
        Int.ModEq (nums.length : ℤ) (entry nums' i) (entry nums i))
      (hsign : ∀ i, i < nums.length → (0 < entry nums' i ↔ 0 < entry nums i)) :
      ∃ r r' : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          Aegis.CircularArrayLoop.circular_array_loop nums' = ok r' ∧ r' = r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h : ValidInput nums)
        (hlen : nums'.length = nums.length)
        (hb : ∀ i, i < nums'.length →
          -1000 ≤ entry nums' i ∧ entry nums' i ≤ 1000 ∧ entry nums' i ≠ 0)
        (hcong : ∀ i, i < nums.length →
          Int.ModEq (nums.length : ℤ) (entry nums' i) (entry nums i))
        (hsign : ∀ i, i < nums.length → (0 < entry nums' i ↔ 0 < entry nums i)), ∃ r r' : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            Aegis.CircularArrayLoop.circular_array_loop nums' = ok r' ∧ r' = r) := by
    sorry

  /-- Whenever the function returns true, for any valid witness cycle (i_0, ..., i_{k-1}) as in the main specification, every index i_j in it satisfies: n does not divide nums[i_j].
    Preconditions: Let n = len(nums). 1 <= n <= 5000. For every i with 0 <= i < n, -1000 <= nums[i] <= 1000 and nums[i] != 0. -/
  theorem spec_9 (nums : Slice Std.I64) (h : ValidInput nums)
      (hr : Aegis.CircularArrayLoop.circular_array_loop nums = ok true)
      (k : ℕ) (ix : ℕ → ℕ) (hw : IsCycle nums k ix) :
      ∀ j, j < k → ¬ (nums.length : ℤ) ∣ entry nums (ix j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : ValidInput nums)
        (hr : Aegis.CircularArrayLoop.circular_array_loop nums = ok true)
        (k : ℕ) (ix : ℕ → ℕ) (hw : IsCycle nums k ix), ∀ j, j < k → ¬ (nums.length : ℤ) ∣ entry nums (ix j)) := by
    sorry

  /-- The function returns a result r. r = true if and only if n does not divide c. Equivalently, r = false exactly when c is congruent to 0 modulo n.
    Preconditions: Let n = len(nums). 1 <= n <= 5000. There is a nonzero integer c with -1000 <= c <= 1000 such that nums[i] = c for every i with 0 <= i < n. -/
  theorem spec_10 (nums : Slice Std.I64) (c : ℤ)
      (hlen : 1 ≤ nums.length ∧ nums.length ≤ 5000)
      (hc0 : c ≠ 0) (hlo : -1000 ≤ c) (hhi : c ≤ 1000)
      (hconst : ∀ i, i < nums.length → entry nums i = c) :
      ∃ r : Bool,
        Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
          (r = true ↔ ¬ (nums.length : ℤ) ∣ c) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (c : ℤ)
        (hlen : 1 ≤ nums.length ∧ nums.length ≤ 5000)
        (hc0 : c ≠ 0) (hlo : -1000 ≤ c) (hhi : c ≤ 1000)
        (hconst : ∀ i, i < nums.length → entry nums i = c), ∃ r : Bool,
          Aegis.CircularArrayLoop.circular_array_loop nums = ok r ∧
            (r = true ↔ ¬ (nums.length : ℤ) ∣ c)) := by
    sorry

  end AegisSpec.CircularArrayLoop
