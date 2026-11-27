import Aegis.CanJump.Code.Funs

/-!
# Specifications of `Aegis.CanJump.can_jump`

LeetCode problem `jump-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanJump

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def PathTo (nums : Slice Std.I64) (k j : Nat) (idx : Nat → Nat) : Prop :=
    idx 0 = 0 ∧ idx k = j ∧
      (∀ t, t ≤ k → idx t < nums.val.length) ∧
      (∀ t, t < k →
        idx t < idx (t + 1) ∧
          ((idx (t + 1) : Int) - (idx t : Int)) ≤ elem nums (idx t))

  def Reach (nums : Slice Std.I64) (j : Nat) : Prop :=
    ∃ (k : Nat) (idx : Nat → Nat), PathTo nums k j idx

  /-- Whenever can_jump nums returns a result r, r is true if and only if there exist a natural number k >= 0 and indices i_0, ..., i_k such that i_0 = 0, i_k = n-1, every i_t satisfies 0 <= i_t < n, and for every t with 0 <= t < k, i_t < i_{t+1} and i_{t+1} - i_t <= nums[i_t]. Equivalently, r is false exactly when no such sequence exists. For n=1 the empty sequence with k=0 and i_0=0 is such a sequence, so the condition is true.
    Preconditions: Let n = len(nums). 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_1
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      (r = true ↔ Reach nums (n - 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), (r = true ↔ Reach nums (n - 1))) := by
    sorry

  /-- For every input satisfying the preconditions, the call can_jump nums returns a Boolean result r; it does not fail by panic, arithmetic overflow, or out-of-bounds slice access.
    Preconditions: Let n = len(nums). 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_2
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000) :
      ∃ r : Bool, Aegis.CanJump.can_jump nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000), ∃ r : Bool, Aegis.CanJump.can_jump nums = ok r) := by
    sorry

  /-- Whenever can_jump nums returns a result r, r = false.
    Preconditions: Let n = len(nums). 2 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. nums[0] = 0. -/
  theorem spec_3
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (h0 : elem nums 0 = 0)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (h0 : elem nums 0 = 0)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = false) := by
    sorry

  /-- Whenever can_jump nums returns a result r, r = true.
    Preconditions: Let n = len(nums). 2 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. nums[0] >= n-1. -/
  theorem spec_4
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (h0 : (n : Int) - 1 ≤ elem nums 0)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (h0 : (n : Int) - 1 ≤ elem nums 0)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = true) := by
    sorry

  /-- Whenever can_jump nums returns r and can_jump nums2 returns r2, r = r2.
    Preconditions: Let n = len(nums). Let nums2 be any slice with len(nums2) = n. 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000 and 0 <= nums2[i] <= 100000. For every i with 0 <= i < n-1, nums[i] = nums2[i]. -/
  theorem spec_5
      (nums nums2 : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn2len : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (helem2 : ∀ i : Nat, i < n → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
      (hagree : ∀ i : Nat, i < n - 1 → elem nums i = elem nums2 i)
      (r r2 : Bool)
      (hr : Aegis.CanJump.can_jump nums = ok r)
      (hr2 : Aegis.CanJump.can_jump nums2 = ok r2) :
      r = r2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn2len : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (helem2 : ∀ i : Nat, i < n → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
        (hagree : ∀ i : Nat, i < n - 1 → elem nums i = elem nums2 i)
        (r r2 : Bool)
        (hr : Aegis.CanJump.can_jump nums = ok r)
        (hr2 : Aegis.CanJump.can_jump nums2 = ok r2), r = r2) := by
    sorry

  /-- Whenever can_jump nums returns r and can_jump nums2 returns r2, if r = true then r2 = true.
    Preconditions: Let n = len(nums). Let nums2 be any slice with len(nums2) = n. 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000 and 0 <= nums2[i] <= 100000. For every i with 0 <= i < n, nums[i] <= nums2[i]. -/
  theorem spec_6
      (nums nums2 : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn2len : nums2.val.length = n)
      (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (helem2 : ∀ i : Nat, i < n → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
      (hle : ∀ i : Nat, i < n → elem nums i ≤ elem nums2 i)
      (r r2 : Bool)
      (hr : Aegis.CanJump.can_jump nums = ok r)
      (hr2 : Aegis.CanJump.can_jump nums2 = ok r2) :
      r = true → r2 = true := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn2len : nums2.val.length = n)
        (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (helem2 : ∀ i : Nat, i < n → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
        (hle : ∀ i : Nat, i < n → elem nums i ≤ elem nums2 i)
        (r r2 : Bool)
        (hr : Aegis.CanJump.can_jump nums = ok r)
        (hr2 : Aegis.CanJump.can_jump nums2 = ok r2), r = true → r2 = true) := by
    sorry

  /-- Whenever can_jump nums returns r and r = true, then for every p with 0 <= p < n there exist k >= 0 and indices i_0, ..., i_k such that i_0 = 0, i_k = p, every i_t satisfies 0 <= i_t < n, for every t with 0 <= t < k we have i_t < i_{t+1} and i_{t+1} - i_t <= nums[i_t].
    Preconditions: Let n = len(nums). 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_7
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = true → ∀ p : Nat, p < n → Reach nums p := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = true → ∀ p : Nat, p < n → Reach nums p) := by
    sorry

  /-- Whenever can_jump nums returns r and r = false, there exists an index b with 0 <= b < n-1 such that b is reachable from 0 (meaning there exist k >= 0 and indices i_0, ..., i_k with i_0 = 0, i_k = b, every i_t in [0,n), i_t < i_{t+1} for all t < k, and i_{t+1} - i_t <= nums[i_t] for all t < k), and for every j with 0 <= j <= b we have j + nums[j] <= b. In particular nums[b] = 0.
    Preconditions: Let n = len(nums). 2 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_8
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = false →
        ∃ b : Nat, b < n - 1 ∧ Reach nums b ∧
          (∀ j : Nat, j ≤ b → (j : Int) + elem nums j ≤ (b : Int)) ∧
          elem nums b = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = false →
          ∃ b : Nat, b < n - 1 ∧ Reach nums b ∧
            (∀ j : Nat, j ≤ b → (j : Int) + elem nums j ≤ (b : Int)) ∧
            elem nums b = 0) := by
    sorry

  /-- Whenever can_jump nums returns r and r = true, then for every index i with 1 <= i < n-1 and nums[i] = 0, there exists an index j with 0 <= j < i such that j + nums[j] >= i+1.
    Preconditions: Let n = len(nums). 2 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_9
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = true →
        ∀ i : Nat, 1 ≤ i → i < n - 1 → elem nums i = 0 →
          ∃ j : Nat, j < i ∧ (i : Int) + 1 ≤ (j : Int) + elem nums j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = true →
          ∀ i : Nat, 1 ≤ i → i < n - 1 → elem nums i = 0 →
            ∃ j : Nat, j < i ∧ (i : Int) + 1 ≤ (j : Int) + elem nums j) := by
    sorry

  /-- Whenever can_jump nums returns r and r = true, there exists an index j with 0 <= j < n-1 such that j is reachable from 0 (meaning there exist k >= 0 and indices i_0, ..., i_k with i_0 = 0, i_k = j, every i_t in [0,n), i_t < i_{t+1} for all t < k, and i_{t+1} - i_t <= nums[i_t] for all t < k) and j + nums[j] >= n-1.
    Preconditions: Let n = len(nums). 2 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_10
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = true →
        ∃ j : Nat, j < n - 1 ∧ Reach nums j ∧
          (n : Int) - 1 ≤ (j : Int) + elem nums j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 2 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = true →
          ∃ j : Nat, j < n - 1 ∧ Reach nums j ∧
            (n : Int) - 1 ≤ (j : Int) + elem nums j) := by
    sorry

  /-- Whenever can_jump nums returns r and r = true, there exist k >= 0 and indices i_0, ..., i_k such that i_0 = 0, i_k = n-1, every i_t satisfies 0 <= i_t < n, for every t with 0 <= t < k we have i_t < i_{t+1} and i_{t+1} - i_t <= nums[i_t], and k <= n-1. Moreover, if n > 1 then k >= 1.
    Preconditions: Let n = len(nums). 1 <= n <= 10000. For every i with 0 <= i < n, as an integer, 0 <= nums[i] <= 100000. -/
  theorem spec_11
      (nums : Slice Std.I64) (n : Nat)
      (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
      (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
      (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r) :
      r = true →
        ∃ (k : Nat) (idx : Nat → Nat),
          PathTo nums k (n - 1) idx ∧ k ≤ n - 1 ∧ (1 < n → 1 ≤ k) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat)
        (hn : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 10000)
        (helem : ∀ i : Nat, i < n → 0 ≤ elem nums i ∧ elem nums i ≤ 100000)
        (r : Bool) (hr : Aegis.CanJump.can_jump nums = ok r), r = true →
          ∃ (k : Nat) (idx : Nat → Nat),
            PathTo nums k (n - 1) idx ∧ k ≤ n - 1 ∧ (1 < n → 1 ≤ k)) := by
    sorry

  end AegisSpec.CanJump
