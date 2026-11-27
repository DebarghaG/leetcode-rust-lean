import Aegis.MaximumJumps.Code.Funs

/-!
# Specifications of `Aegis.MaximumJumps.maximum_jumps`

LeetCode problem `maximum-number-of-jumps-to-reach-the-last-index`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumJumps

  open Aegis.MaximumJumps

  def get (nums : Slice Std.I64) (i : Nat) : ℤ :=
    match (nums.val[i]? : Option Std.I64) with
    | some x => x.val
    | none => 0

  theorem get_eq (nums : Slice Std.I64) (i : Nat) (h : i < nums.val.length) :
      get nums i = (nums.val[i]'h).val := by
    simp [get, List.getElem?_eq_getElem h]

  def entries (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def maxVal (nums : Slice Std.I64) : ℤ :=
    match entries nums with
    | [] => 0
    | x :: xs => List.foldl (fun acc y => max acc y) x xs

  def minVal (nums : Slice Std.I64) : ℤ :=
    match entries nums with
    | [] => 0
    | x :: xs => List.foldl (fun acc y => min acc y) x xs

  def countEqFirst (nums : Slice Std.I64) : Nat :=
    List.countP (fun i => decide (get nums i = get nums 0)) (List.range nums.val.length)

  structure IsJumpSeq (nums : Slice Std.I64) (target : ℤ) (L : List Nat) : Prop where

    head_eq : L.head? = some 0

    last_eq : L.getLast? = some (nums.val.length - 1)

    strictMono : L.Pairwise (· < ·)

    inBounds : ∀ i, i ∈ L → i < nums.val.length

    step : ∀ t : Nat, t + 1 < L.length →
      -target ≤ get nums L[t + 1]! - get nums L[t]! ∧
        get nums L[t + 1]! - get nums L[t]! ≤ target

  def HasJumpSeq (nums : Slice Std.I64) (target : ℤ) (k : Nat) : Prop :=
    ∃ L : List Nat, IsJumpSeq nums target L ∧ L.length = k + 1

  theorem IsJumpSeq.length_pos {nums : Slice Std.I64} {target : ℤ} {L : List Nat}
      (h : IsJumpSeq nums target L) : 0 < L.length := by
    cases L with
    | nil =>
      have hh := h.head_eq
      simp at hh
    | cons x xs => simp

  /-- The function returns a result r (it does not fail). A jump sequence is a sequence of indices i_0, i_1, ..., i_k such that i_0 = 0, i_k = n-1, 0 <= i_0 < i_1 < ... < i_k < n, and for every t with 0 <= t < k, -target <= nums[i_{t+1}] - nums[i_t] <= target. The integer r satisfies: if there exists at least one jump sequence, then r is the maximum k over all jump sequences (so r >= 0, there exists a jump sequence of length r, and no jump sequence has length greater than r); if no jump sequence exists, then r = -1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∃ r : Std.I64,
        maximum_jumps nums target = ok r ∧
          (((∃ k : Nat, (k : ℤ) = r.val ∧ HasJumpSeq nums target.val k) ∧
              (∀ k : Nat, HasJumpSeq nums target.val k → (k : ℤ) ≤ r.val)) ∨
            (r.val = -1 ∧ ∀ k : Nat, ¬ HasJumpSeq nums target.val k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∃ r : Std.I64,
          maximum_jumps nums target = ok r ∧
            (((∃ k : Nat, (k : ℤ) = r.val ∧ HasJumpSeq nums target.val k) ∧
                (∀ k : Nat, HasJumpSeq nums target.val k → (k : ℤ) ≤ r.val)) ∨
              (r.val = -1 ∧ ∀ k : Nat, ¬ HasJumpSeq nums target.val k))) := by
    sorry

  /-- Whenever the function returns a result r, we have -1 <= r <= n-1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∀ r : Std.I64, maximum_jumps nums target = ok r → -1 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∀ r : Std.I64, maximum_jumps nums target = ok r → -1 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, there exists a jump sequence from index 0 to index n-1 of length r. Here a jump sequence of length r is a sequence of indices i_0, i_1, ..., i_r such that i_0 = 0, i_r = n-1, 0 <= i_0 < i_1 < ... < i_r < n, and for every t with 0 <= t < r, -target <= nums[i_{t+1}] - nums[i_t] <= target.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∀ r : Std.I64, maximum_jumps nums target = ok r → 0 ≤ r.val →
        ∃ k : Nat, (k : ℤ) = r.val ∧ HasJumpSeq nums target.val k := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∀ r : Std.I64, maximum_jumps nums target = ok r → 0 ≤ r.val →
          ∃ k : Nat, (k : ℤ) = r.val ∧ HasJumpSeq nums target.val k) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every jump sequence from index 0 to index n-1 of length k (defined as in spec_3: i_0 = 0, i_k = n-1, 0 <= i_0 < ... < i_k < n, and for every t < k, -target <= nums[i_{t+1}] - nums[i_t] <= target), we have k <= r.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_4 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∀ r : Std.I64, maximum_jumps nums target = ok r → 0 ≤ r.val →
        ∀ k : Nat, HasJumpSeq nums target.val k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∀ r : Std.I64, maximum_jumps nums target = ok r → 0 ≤ r.val →
          ∀ k : Nat, HasJumpSeq nums target.val k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns -1, there does not exist any jump sequence from index 0 to index n-1 (defined as in spec_3: a sequence of indices i_0, ..., i_k with i_0 = 0, i_k = n-1, 0 <= i_0 < ... < i_k < n, and for every t < k, -target <= nums[i_{t+1}] - nums[i_t] <= target).
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_5 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∀ r : Std.I64, maximum_jumps nums target = ok r → r.val = -1 →
        ¬ (∃ k : Nat, HasJumpSeq nums target.val k) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∀ r : Std.I64, maximum_jumps nums target = ok r → r.val = -1 →
          ¬ (∃ k : Nat, HasJumpSeq nums target.val k)) := by
    sorry

  /-- Whenever the function returns a result r and there exists at least one jump sequence from index 0 to index n-1 (defined as in spec_3), we have r >= 1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∀ r : Std.I64, maximum_jumps nums target = ok r →
        (∃ k : Nat, HasJumpSeq nums target.val k) → 1 ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∀ r : Std.I64, maximum_jumps nums target = ok r →
          (∃ k : Nat, HasJumpSeq nums target.val k) → 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r = 1 if |nums[1] - nums[0]| <= target, and r = -1 otherwise.
    Preconditions: len(nums) = n, n = 2, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn : n = 2)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∃ r : Std.I64,
        maximum_jumps nums target = ok r ∧
          ((|get nums 1 - get nums 0| ≤ target.val ∧ r.val = 1) ∨
            (target.val < |get nums 1 - get nums 0| ∧ r.val = -1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn : n = 2)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∃ r : Std.I64,
          maximum_jumps nums target = ok r ∧
            ((|get nums 1 - get nums 0| ≤ target.val ∧ r.val = 1) ∨
              (target.val < |get nums 1 - get nums 0| ∧ r.val = -1))) := by
    sorry

  /-- Let c be the number of indices i with 0 <= i < n and nums[i] = nums[0]. If nums[n-1] = nums[0], the function returns r = c - 1; otherwise it returns r = -1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and target = 0. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht : target.val = 0) :
      ∃ r : Std.I64,
        maximum_jumps nums target = ok r ∧
          r.val = (if get nums (n - 1) = get nums 0 then (countEqFirst nums : ℤ) - 1
                   else -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht : target.val = 0), ∃ r : Std.I64,
          maximum_jumps nums target = ok r ∧
            r.val = (if get nums (n - 1) = get nums 0 then (countEqFirst nums : ℤ) - 1
                     else -1)) := by
    sorry

  /-- The function returns r = n - 1 if and only if for every i with 0 <= i < n-1, -target <= nums[i+1] - nums[i] <= target.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_9 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∃ r : Std.I64,
        maximum_jumps nums target = ok r ∧
          (r.val = (n : ℤ) - 1 ↔
            ∀ i, i < n - 1 →
              -target.val ≤ get nums (i + 1) - get nums i ∧
                get nums (i + 1) - get nums i ≤ target.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∃ r : Std.I64,
          maximum_jumps nums target = ok r ∧
            (r.val = (n : ℤ) - 1 ↔
              ∀ i, i < n - 1 →
                -target.val ≤ get nums (i + 1) - get nums i ∧
                  get nums (i + 1) - get nums i ≤ target.val)) := by
    sorry

  /-- The function returns r = n - 1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. Let max_val = max_{0 <= i < n} nums[i] and min_val = min_{0 <= i < n} nums[i]. Assume target >= max_val - min_val. -/
  theorem spec_10 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hspan : maxVal nums - minVal nums ≤ target.val) :
      ∃ r : Std.I64, maximum_jumps nums target = ok r ∧ r.val = (n : ℤ) - 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hspan : maxVal nums - minVal nums ≤ target.val), ∃ r : Std.I64, maximum_jumps nums target = ok r ∧ r.val = (n : ℤ) - 1) := by
    sorry

  /-- Let r1 be the result of maximum_jumps(nums, t1) and r2 be the result of maximum_jumps(nums, t2). If r1 != -1, then r2 != -1 and r2 >= r1.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= t1 <= t2 <= 2*10^9. -/
  theorem spec_11 (nums : Slice Std.I64) (t1 t2 : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (h10 : 0 ≤ t1.val) (h12 : t1.val ≤ t2.val) (h2 : t2.val ≤ 2000000000) :
      ∀ r1 r2 : Std.I64,
        maximum_jumps nums t1 = ok r1 → maximum_jumps nums t2 = ok r2 →
          r1.val ≠ -1 → r2.val ≠ -1 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (t1 t2 : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (h10 : 0 ≤ t1.val) (h12 : t1.val ≤ t2.val) (h2 : t2.val ≤ 2000000000), ∀ r1 r2 : Std.I64,
          maximum_jumps nums t1 = ok r1 → maximum_jumps nums t2 = ok r2 →
            r1.val ≠ -1 → r2.val ≠ -1 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- Let nums' be the array of length n with nums'[i] = nums[i] + c for all i. Then maximum_jumps(nums, target) = maximum_jumps(nums', target).
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, 0 <= target <= 2*10^9, and c is an integer such that for all i, nums[i] + c is representable as i64 (i.e., -2^63 <= nums[i] + c <= 2^63 - 1). -/
  theorem spec_12 (nums : Slice Std.I64) (target : Std.I64) (n : Nat) (c : ℤ)
      (nums' : Slice Std.I64)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hc : ∀ i, i < n → -((2 : ℤ) ^ 63) ≤ get nums i + c ∧
        get nums i + c ≤ (2 : ℤ) ^ 63 - 1)
      (hlen' : nums'.val.length = n)
      (hval : ∀ i, i < n → get nums' i = get nums i + c) :
      maximum_jumps nums target = maximum_jumps nums' target := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat) (c : ℤ)
        (nums' : Slice Std.I64)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hc : ∀ i, i < n → -((2 : ℤ) ^ 63) ≤ get nums i + c ∧
          get nums i + c ≤ (2 : ℤ) ^ 63 - 1)
        (hlen' : nums'.val.length = n)
        (hval : ∀ i, i < n → get nums' i = get nums i + c), maximum_jumps nums target = maximum_jumps nums' target) := by
    sorry

  /-- Let nums' be the array of length n with nums'[i] = -nums[i] for all i. Then maximum_jumps(nums, target) = maximum_jumps(nums', target).
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_13 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (nums' : Slice Std.I64)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hlen' : nums'.val.length = n)
      (hval : ∀ i, i < n → get nums' i = -get nums i) :
      maximum_jumps nums target = maximum_jumps nums' target := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (nums' : Slice Std.I64)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hlen' : nums'.val.length = n)
        (hval : ∀ i, i < n → get nums' i = -get nums i), maximum_jumps nums target = maximum_jumps nums' target) := by
    sorry

  /-- Let rev be the array of length n with rev[i] = nums[n-1-i] for all i. Then maximum_jumps(nums, target) = maximum_jumps(rev, target).
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_14 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (rev : Slice Std.I64)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hlen' : rev.val.length = n)
      (hval : ∀ i, i < n → get rev i = get nums (n - 1 - i)) :
      maximum_jumps nums target = maximum_jumps rev target := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (rev : Slice Std.I64)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hlen' : rev.val.length = n)
        (hval : ∀ i, i < n → get rev i = get nums (n - 1 - i)), maximum_jumps nums target = maximum_jumps rev target) := by
    sorry

  /-- Let nums' be the array of length n with nums'[i] = k * nums[i] for all i, and let target' = k * target. Then maximum_jumps(nums, target) = maximum_jumps(nums', target').
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. Let k be an integer with k > 0. Assume: for every i, k * nums[i] is representable as i64; k * target is representable as i64; and for every i,j with 0 <= i,j < n, the integer k * (nums[j] - nums[i]) is representable as i64 and its absolute value is at most 2^63 - 1 (so subtraction and absolute value in the comparison cannot overflow). -/
  theorem spec_15 (nums : Slice Std.I64) (target : Std.I64) (n : Nat) (k : ℤ)
      (nums' : Slice Std.I64) (target' : Std.I64)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hk : 0 < k)
      (hknums : ∀ i, i < n → -((2 : ℤ) ^ 63) ≤ k * get nums i ∧
        k * get nums i ≤ (2 : ℤ) ^ 63 - 1)
      (hktarget : -((2 : ℤ) ^ 63) ≤ k * target.val ∧
        k * target.val ≤ (2 : ℤ) ^ 63 - 1)
      (hkdiff : ∀ i j, i < n → j < n →
        |k * (get nums j - get nums i)| ≤ (2 : ℤ) ^ 63 - 1)
      (hlen' : nums'.val.length = n)
      (hval : ∀ i, i < n → get nums' i = k * get nums i)
      (htarget' : target'.val = k * target.val) :
      maximum_jumps nums target = maximum_jumps nums' target' := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat) (k : ℤ)
        (nums' : Slice Std.I64) (target' : Std.I64)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hk : 0 < k)
        (hknums : ∀ i, i < n → -((2 : ℤ) ^ 63) ≤ k * get nums i ∧
          k * get nums i ≤ (2 : ℤ) ^ 63 - 1)
        (hktarget : -((2 : ℤ) ^ 63) ≤ k * target.val ∧
          k * target.val ≤ (2 : ℤ) ^ 63 - 1)
        (hkdiff : ∀ i j, i < n → j < n →
          |k * (get nums j - get nums i)| ≤ (2 : ℤ) ^ 63 - 1)
        (hlen' : nums'.val.length = n)
        (hval : ∀ i, i < n → get nums' i = k * get nums i)
        (htarget' : target'.val = k * target.val), maximum_jumps nums target = maximum_jumps nums' target') := by
    sorry

  /-- The function returns a result r with r >= 1 (i.e., r is not -1).
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, 0 <= target <= 2*10^9, and |nums[n-1] - nums[0]| <= target. -/
  theorem spec_16 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
      (hclose : |get nums (n - 1) - get nums 0| ≤ target.val) :
      ∃ r : Std.I64, maximum_jumps nums target = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000)
        (hclose : |get nums (n - 1) - get nums 0| ≤ target.val), ∃ r : Std.I64, maximum_jumps nums target = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- The function returns a result r (it does not fail due to integer overflow, out-of-bounds access, or any other panic) for every input satisfying the constraints.
    Preconditions: len(nums) = n, 2 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and 0 <= target <= 2*10^9. -/
  theorem spec_17 (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
      (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
      (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
      (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000) :
      ∃ r : Std.I64, maximum_jumps nums target = ok r := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64) (n : Nat)
        (hlen : nums.val.length = n) (hn2 : 2 ≤ n) (hn1000 : n ≤ 1000)
        (hbound : ∀ i, i < n → -1000000000 ≤ get nums i ∧ get nums i ≤ 1000000000)
        (ht0 : 0 ≤ target.val) (ht2000 : target.val ≤ 2000000000), ∃ r : Std.I64, maximum_jumps nums target = ok r) := by
    sorry

  end AegisSpec.MaximumJumps
