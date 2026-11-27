import Aegis.MaxSlidingWindow.Code.Funs

/-!
# Specifications of `Aegis.MaxSlidingWindow.max_sliding_window`

LeetCode problem `sliding-window-maximum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxSlidingWindow

  namespace AegisSpec.MaxSlidingWindow

  def entry (a : List Std.I64) (j : Nat) : Int :=
    match a[j]? with
    | some x => x.val
    | none => 0

  def vals (a : List Std.I64) : List Int := a.map (fun x => x.val)

  def window (a : List Std.I64) (lo len : Nat) : List Int := ((vals a).drop lo).take len

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def maxAll (a : List Std.I64) : Int := listMax (vals a)

  def minAll (a : List Std.I64) : Int := listMin (vals a)

  def windowMax (a : List Std.I64) (i k : Nat) : Int := listMax (window a i k)

  def outLen (n : Nat) (k : Int) : Nat := n - k.toNat + 1

  def winLast (i : Nat) (k : Int) : Nat := i + k.toNat - 1

  /-- The function returns a result r and len(r) = n - k + 1. For every i with 0 <= i < n - k + 1, r[i] = max { nums[j] | 0 <= j < n and i <= j <= i + k - 1 }, i.e. r[i] is the maximum of the contiguous window of length k starting at index i.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∃ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r ∧
        r.val.length = outLen nums.val.length k.val ∧
        ∀ i, i < outLen nums.val.length k.val →
          entry r.val i = windowMax nums.val i k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r ∧
          r.val.length = outLen nums.val.length k.val ∧
          ∀ i, i < outLen nums.val.length k.val →
            entry r.val i = windowMax nums.val i k.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∃ r : alloc.vec.Vec Std.I64, max_sliding_window nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∃ r : alloc.vec.Vec Std.I64, max_sliding_window nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = n - k + 1.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r → r.val.length = outLen nums.val.length k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r → r.val.length = outLen nums.val.length k.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n - k + 1 and every j with i <= j <= i + k - 1, we have r[i] >= nums[j].
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r →
        ∀ i, i < outLen nums.val.length k.val →
          ∀ j, i ≤ j → j ≤ winLast i k.val → entry r.val i ≥ entry nums.val j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r →
          ∀ i, i < outLen nums.val.length k.val →
            ∀ j, i ≤ j → j ≤ winLast i k.val → entry r.val i ≥ entry nums.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n - k + 1 there exists j with i <= j <= i + k - 1 such that r[i] = nums[j].
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r →
        ∀ i, i < outLen nums.val.length k.val →
          ∃ j, i ≤ j ∧ j ≤ winLast i k.val ∧ entry r.val i = entry nums.val j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r →
          ∀ i, i < outLen nums.val.length k.val →
            ∃ j, i ≤ j ∧ j ≤ winLast i k.val ∧ entry r.val i = entry nums.val j) := by
    sorry

  /-- Whenever the function returns a result r, the maximum of all entries of r equals the maximum of all entries of nums: max(r[0], ..., r[len(r)-1]) = max(nums[0], ..., nums[n-1]).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r → maxAll r.val = maxAll nums.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r → maxAll r.val = maxAll nums.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), min(nums[0], ..., nums[n-1]) <= r[i] <= max(nums[0], ..., nums[n-1]).
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r →
        ∀ i, i < r.val.length → minAll nums.val ≤ entry r.val i ∧ entry r.val i ≤ maxAll nums.val
    := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r →
          ∀ i, i < r.val.length → minAll nums.val ≤ entry r.val i ∧ entry r.val i ≤ maxAll nums.val) := by
    sorry

  /-- Let m = n - k + 1. Whenever the function returns a result r, there exist indices t_0, ..., t_{m-1} such that for every i with 0 <= i < m, i <= t_i <= i + k - 1 and r[i] = nums[t_i], and moreover t_0 <= t_1 <= ... <= t_{m-1}.
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r →
        ∃ t : Nat → Nat,
          (∀ i, i < outLen nums.val.length k.val →
            i ≤ t i ∧ t i ≤ winLast i k.val ∧ entry r.val i = entry nums.val (t i)) ∧
          (∀ i, i + 1 < outLen nums.val.length k.val → t i ≤ t (i + 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r →
          ∃ t : Nat → Nat,
            (∀ i, i < outLen nums.val.length k.val →
              i ≤ t i ∧ t i ≤ winLast i k.val ∧ entry r.val i = entry nums.val (t i)) ∧
            (∀ i, i + 1 < outLen nums.val.length k.val → t i ≤ t (i + 1))) := by
    sorry

  /-- Let m = n - k + 1. Whenever the function returns a result r, for every i with 0 <= i < m - 1: (a) if r[i+1] < r[i] then r[i] = nums[i]; and (b) if r[i+1] > r[i] then r[i+1] = nums[i+k].
    Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, every nums[j] for 0 <= j < n lies in [-10000, 10000], and k is an i64 with 1 <= k <= n. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
      (hb : ∀ j, j < nums.val.length →
        -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)) :
      ∀ r : alloc.vec.Vec Std.I64,
        max_sliding_window nums k = ok r →
        ∀ i, i + 1 < outLen nums.val.length k.val →
          (entry r.val (i + 1) < entry r.val i → entry r.val i = entry nums.val i) ∧
          (entry r.val (i + 1) > entry r.val i →
            entry r.val (i + 1) = entry nums.val (i + k.val.toNat)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
        (hb : ∀ j, j < nums.val.length →
          -10000 ≤ entry nums.val j ∧ entry nums.val j ≤ 10000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ (nums.val.length : Int)), ∀ r : alloc.vec.Vec Std.I64,
          max_sliding_window nums k = ok r →
          ∀ i, i + 1 < outLen nums.val.length k.val →
            (entry r.val (i + 1) < entry r.val i → entry r.val i = entry nums.val i) ∧
            (entry r.val (i + 1) > entry r.val i →
              entry r.val (i + 1) = entry nums.val (i + k.val.toNat))) := by
    sorry

  end AegisSpec.MaxSlidingWindow
