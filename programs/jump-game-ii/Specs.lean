import Aegis.Jump.Code.Funs

/-!
# Specifications of `Aegis.Jump.jump`

LeetCode problem `jump-game-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Jump

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elem (a : List Int) (i : Nat) : Int := a.getD i 0

def Path (a : List Int) (js : List Nat) : Prop :=
  js.head? = some 0 ∧
    js.getLast? = some (a.length - 1) ∧
    ∀ (t j j' : Nat), js[t]? = some j → js[t + 1]? = some j' →
      (j : Int) < (j' : Int) ∧ (j' : Int) ≤ (j : Int) + elem a j

def Reachable (a : List Int) (k : Nat) : Prop :=
  ∃ js : List Nat, Path a js ∧ js.length = k + 1

/-- Whenever the function returns a result r, r is the least nonnegative integer k for which there exist indices i_0, ..., i_k with i_0 = 0, i_k = n - 1, and i_t < i_{t+1} <= i_t + nums[i_t] for every t with 0 <= t < k. In other words, r is the minimum number of forward jumps needed to get from index 0 to index n - 1, where a jump from index i can go to any index j with i < j < n and j <= i + nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and there exist a nonnegative integer k and indices i_0, ..., i_k such that i_0 = 0, i_k = n - 1, and for every t with 0 <= t < k, i_t < i_{t+1} <= i_t + nums[i_t]. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    0 ≤ r.val ∧ Reachable (vals nums) r.val.toNat ∧
      (∀ k, Reachable (vals nums) k → r.val.toNat ≤ k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), 0 ≤ r.val ∧ Reachable (vals nums) r.val.toNat ∧
      (∀ k, Reachable (vals nums) k → r.val.toNat ≤ k)) := by
  sorry

/-- The function returns a result r for every nums satisfying the preconditions; it does not fail, overflow, panic, or access an index outside 0 .. n - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and there exist a nonnegative integer k and indices i_0, ..., i_k such that i_0 = 0, i_k = n - 1, and for every t with 0 <= t < k, i_t < i_{t+1} <= i_t + nums[i_t]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k) :
    ∃ r : Std.I64, Aegis.Jump.jump nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k), ∃ r : Std.I64, Aegis.Jump.jump nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and there exist a nonnegative integer k and indices i_0, ..., i_k such that i_0 = 0, i_k = n - 1, and for every t with 0 <= t < k, i_t < i_{t+1} <= i_t + nums[i_t]. -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((Slice.len nums).val : Int) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), 0 ≤ r.val ∧ r.val ≤ ((Slice.len nums).val : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: Let n = len(nums). Assume n = 1 and 0 <= nums[0] <= 1000. -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 1)
    (h0_lo : 0 ≤ elem (vals nums) 0)
    (h0_hi : elem (vals nums) 0 ≤ 1000)
    (hres : Aegis.Jump.jump nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn : (Slice.len nums).val = 1)
    (h0_lo : 0 ≤ elem (vals nums) 0)
    (h0_hi : elem (vals nums) 0 ≤ 1000)
    (hres : Aegis.Jump.jump nums = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if nums[0] >= n - 1.
  Preconditions: Let n = len(nums). Assume n >= 2, n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and the last index is reachable from 0 by valid jumps (there is a strictly increasing index sequence from 0 to n - 1 with each step at most the array value at its start). -/
theorem spec_5 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    (r.val = 1) ↔ (((Slice.len nums).val : Int) - 1 ≤ elem (vals nums) 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), (r.val = 1) ↔ (((Slice.len nums).val : Int) - 1 ≤ elem (vals nums) 0)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let n = len(nums). Assume n >= 2, n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and the last index is reachable from 0 by valid jumps. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 2 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= 0 and there exist indices i_0, ..., i_r such that i_0 = 0, i_r = n - 1, and i_t < i_{t+1} <= i_t + nums[i_t] for every t with 0 <= t < r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and there exist a nonnegative integer k and indices i_0, ..., i_k such that i_0 = 0, i_k = n - 1, and for every t with 0 <= t < k, i_t < i_{t+1} <= i_t + nums[i_t]. -/
theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    0 ≤ r.val ∧ Reachable (vals nums) r.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), 0 ≤ r.val ∧ Reachable (vals nums) r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every nonnegative integer k and every list of indices i_0, ..., i_k satisfying i_0 = 0, i_k = n - 1, and i_t < i_{t+1} <= i_t + nums[i_t] for every t with 0 <= t < k, we have r <= k.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and there exist a nonnegative integer k and indices i_0, ..., i_k such that i_0 = 0, i_k = n - 1, and for every t with 0 <= t < k, i_t < i_{t+1} <= i_t + nums[i_t]. -/
theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r) :
    ∀ k, Reachable (vals nums) k → r.val ≤ (k : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hres : Aegis.Jump.jump nums = ok r), ∀ k, Reachable (vals nums) k → r.val ≤ (k : Int)) := by
  sorry

/-- If jump(nums) returns r and jump(nums') returns r', then r' <= r.
  Preconditions: Let n = len(nums) = len(nums'). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000 and 0 <= nums'[i] <= 1000, nums[i] <= nums'[i] for every i, and both nums and nums' allow reaching the last index from 0 by valid jumps. -/
theorem spec_9 (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen : (Slice.len nums).val = (Slice.len nums').val)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hbound' : ∀ i, i < (Slice.len nums').val →
      0 ≤ elem (vals nums') i ∧ elem (vals nums') i ≤ 1000)
    (hmono : ∀ i, i < (Slice.len nums).val → elem (vals nums) i ≤ elem (vals nums') i)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hreach' : ∃ k, Reachable (vals nums') k)
    (hres : Aegis.Jump.jump nums = ok r)
    (hres' : Aegis.Jump.jump nums' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen : (Slice.len nums).val = (Slice.len nums').val)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hbound' : ∀ i, i < (Slice.len nums').val →
      0 ≤ elem (vals nums') i ∧ elem (vals nums') i ≤ 1000)
    (hmono : ∀ i, i < (Slice.len nums).val → elem (vals nums) i ≤ elem (vals nums') i)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hreach' : ∃ k, Reachable (vals nums') k)
    (hres : Aegis.Jump.jump nums = ok r)
    (hres' : Aegis.Jump.jump nums' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- If jump(nums) returns r and jump(nums') returns r', then r' = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 10000, for every i with 0 <= i < n we have 0 <= nums[i] <= 1000, and the last index is reachable from 0 by valid jumps. Let nums' be the array of length n defined by nums'[i] = min(nums[i], n - 1 - i) for every 0 <= i < n; then nums' also has values in 0 .. 1000 and is reachable. -/
theorem spec_10 (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen : (Slice.len nums).val = (Slice.len nums').val)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hdef : ∀ i, i < (Slice.len nums).val →
      elem (vals nums') i =
        min (elem (vals nums) i) (((Slice.len nums).val : Int) - 1 - (i : Int)))
    (hres : Aegis.Jump.jump nums = ok r)
    (hres' : Aegis.Jump.jump nums' = ok r') :
    r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen : (Slice.len nums).val = (Slice.len nums').val)
    (hn_lo : 1 ≤ (Slice.len nums).val)
    (hn_hi : (Slice.len nums).val ≤ 10000)
    (hbound : ∀ i, i < (Slice.len nums).val →
      0 ≤ elem (vals nums) i ∧ elem (vals nums) i ≤ 1000)
    (hreach : ∃ k, Reachable (vals nums) k)
    (hdef : ∀ i, i < (Slice.len nums).val →
      elem (vals nums') i =
        min (elem (vals nums) i) (((Slice.len nums).val : Int) - 1 - (i : Int)))
    (hres : Aegis.Jump.jump nums = ok r)
    (hres' : Aegis.Jump.jump nums' = ok r'), r'.val = r.val) := by
  sorry

end AegisSpec.Jump
