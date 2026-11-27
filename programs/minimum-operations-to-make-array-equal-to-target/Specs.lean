import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-operations-to-make-array-equal-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperations

  open Aegis.MinimumOperations

  def vals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def InRange (l : List ℤ) : Prop := ∀ (i : ℕ) (h : i < l.length), 1 ≤ l[i] ∧ l[i] ≤ 100000000

  def diffs (nums target : Slice Std.I64) : List ℤ :=
    List.zipWith (fun a b => b - a) (vals nums) (vals target)

  def rises (prev : ℤ) : List ℤ → ℤ
    | [] => 0
    | x :: xs => max 0 (x - prev) + rises x xs

  def totalRises (nums target : Slice Std.I64) : ℤ := rises 0 (diffs nums target ++ [0])

  def absMax (l : List ℤ) : ℤ := l.foldl (fun acc x => max acc |x|) 0

  def absSum (l : List ℤ) : ℤ := l.foldl (fun acc x => acc + |x|) 0

  structure Op where

    l : ℕ

    u : ℕ

    s : ℤ

    s_mem : s = 1 ∨ s = -1

  def Op.apply (op : Op) (a : List ℤ) : List ℤ :=
    a.zipIdx.map (fun p => if op.l ≤ p.2 ∧ p.2 ≤ op.u then p.1 + op.s else p.1)

  def ValidOps (n : ℕ) (ops : List Op) : Prop := ∀ op ∈ ops, op.l ≤ op.u ∧ op.u < n

  def applyOps (ops : List Op) (a : List ℤ) : List ℤ :=
    ops.foldl (fun acc op => op.apply acc) a

  /-- Whenever the function returns a result r: let d(i) = target[i] - nums[i] for 0 <= i < n, and extend it by d(-1) = 0 and d(n) = 0; then r = sum over i = 0..n of max(0, d(i) - d(i-1)).
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_1 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      r.val = totalRises nums target := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), r.val = totalRises nums target) := by
    sorry

  /-- The function returns a result r (it does not fail: no arithmetic overflow, panic, or out-of-bounds access) for every input satisfying the preconditions.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_2 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target)) :
      ∃ r : Std.I64, minimum_operations nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target)), ∃ r : Std.I64, minimum_operations nums target = ok r) := by
    sorry

  /-- Whenever the function returns a result r: there exists a sequence of exactly r operations whose in-order application to nums yields target, where an operation is a triple (l, u, s) with 0 <= l <= u < n and s in {+1, -1}, and applying it to an array a produces a' with a'[i] = a[i] + s for every l <= i <= u and a'[i] = a[i] for every other i.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_3 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      ∃ ops : List Op,
        ValidOps n ops ∧ applyOps ops (vals nums) = vals target ∧ (ops.length : ℤ) = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), ∃ ops : List Op,
          ValidOps n ops ∧ applyOps ops (vals nums) = vals target ∧ (ops.length : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r: for every integer k >= 0 and every sequence of k operations (an operation being a triple (l, u, s) with 0 <= l <= u < n and s in {+1, -1}, adding s to every position in [l, u]) whose in-order application to nums yields target, it holds that k >= r.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_4 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      ∀ (k : ℕ) (ops : List Op),
        ValidOps n ops → ops.length = k → applyOps ops (vals nums) = vals target →
        r.val ≤ (k : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), ∀ (k : ℕ) (ops : List Op),
          ValidOps n ops → ops.length = k → applyOps ops (vals nums) = vals target →
          r.val ≤ (k : ℤ)) := by
    sorry

  /-- Whenever the function returns r on inputs (nums, target) and returns r' on inputs (target, nums), it holds that r = r'.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_5 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r r' : Std.I64)
      (hr : minimum_operations nums target = ok r)
      (hr' : minimum_operations target nums = ok r') :
      r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r r' : Std.I64)
        (hr : minimum_operations nums target = ok r)
        (hr' : minimum_operations target nums = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns a result r: r = 0 if and only if nums[i] = target[i] for every i with 0 <= i < n.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_6 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      r.val = 0 ↔ ∀ i, i < n → (vals nums)[i]? = (vals target)[i]? := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), r.val = 0 ↔ ∀ i, i < n → (vals nums)[i]? = (vals target)[i]?) := by
    sorry

  /-- Whenever the function returns a result r and there exists an integer c such that target[i] - nums[i] = c for every i with 0 <= i < n: r = |c|.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_7 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r)
      (c : ℤ) (hc : ∀ z ∈ diffs nums target, z = c) :
      r.val = |c| := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r)
        (c : ℤ) (hc : ∀ z ∈ diffs nums target, z = c), r.val = |c|) := by
    sorry

  /-- Whenever the function returns a result r: r >= max over 0 <= i < n of |target[i] - nums[i]|.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_8 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      absMax (diffs nums target) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), absMax (diffs nums target) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r: r <= sum over i = 0..n-1 of |target[i] - nums[i]|.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_9 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (r : Std.I64) (hr : minimum_operations nums target = ok r) :
      r.val ≤ absSum (diffs nums target) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (r : Std.I64) (hr : minimum_operations nums target = ok r), r.val ≤ absSum (diffs nums target)) := by
    sorry

  /-- For every integer c such that 1 <= nums[i] + c <= 100000000 and 1 <= target[i] + c <= 100000000 for all 0 <= i < n: whenever the function returns r on (nums, target) and returns r_c on (nums', target') with nums'[i] = nums[i] + c and target'[i] = target[i] + c, it holds that r_c = r.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_10 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (c : ℤ)
      (hnums_shift_range : InRange ((vals nums).map (fun x => x + c)))
      (htarget_shift_range : InRange ((vals target).map (fun x => x + c)))
      (nums' target' : Slice Std.I64)
      (hnums' : vals nums' = (vals nums).map (fun x => x + c))
      (htarget' : vals target' = (vals target).map (fun x => x + c))
      (r r_c : Std.I64)
      (hr : minimum_operations nums target = ok r)
      (hr_c : minimum_operations nums' target' = ok r_c) :
      r_c = r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (c : ℤ)
        (hnums_shift_range : InRange ((vals nums).map (fun x => x + c)))
        (htarget_shift_range : InRange ((vals target).map (fun x => x + c)))
        (nums' target' : Slice Std.I64)
        (hnums' : vals nums' = (vals nums).map (fun x => x + c))
        (htarget' : vals target' = (vals target).map (fun x => x + c))
        (r r_c : Std.I64)
        (hr : minimum_operations nums target = ok r)
        (hr_c : minimum_operations nums' target' = ok r_c), r_c = r) := by
    sorry

  /-- For every integer k >= 0 such that 1 <= nums[i] + k * (target[i] - nums[i]) <= 100000000 for all 0 <= i < n: whenever the function returns r on (nums, target) and returns r_k on (nums, target') with target'[i] = nums[i] + k * (target[i] - nums[i]), it holds that r_k = k * r.
    Preconditions: len(nums) = len(target) = n with 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000000 and 1 <= target[i] <= 100000000. -/
  theorem spec_11 (nums target : Slice Std.I64) (n : ℕ)
      (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
      (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
      (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
      (k : ℕ)
      (hnums_scaled_range :
        InRange (List.zipWith (fun x y => x + (k : ℤ) * (y - x)) (vals nums) (vals target)))
      (target' : Slice Std.I64)
      (htarget' :
        vals target' = List.zipWith (fun x y => x + (k : ℤ) * (y - x)) (vals nums) (vals target))
      (r r_k : Std.I64)
      (hr : minimum_operations nums target = ok r)
      (hr_k : minimum_operations nums target' = ok r_k) :
      r_k.val = (k : ℤ) * r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums target : Slice Std.I64) (n : ℕ)
        (hnums_len : nums.val.length = n) (htarget_len : target.val.length = n)
        (hn_lb : 1 ≤ n) (hn_ub : n ≤ 100000)
        (hnums_range : InRange (vals nums)) (htarget_range : InRange (vals target))
        (k : ℕ)
        (hnums_scaled_range :
          InRange (List.zipWith (fun x y => x + (k : ℤ) * (y - x)) (vals nums) (vals target)))
        (target' : Slice Std.I64)
        (htarget' :
          vals target' = List.zipWith (fun x y => x + (k : ℤ) * (y - x)) (vals nums) (vals target))
        (r r_k : Std.I64)
        (hr : minimum_operations nums target = ok r)
        (hr_k : minimum_operations nums target' = ok r_k), r_k.val = (k : ℤ) * r.val) := by
    sorry

  end AegisSpec.MinimumOperations
