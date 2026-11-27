import Aegis.DestroyTargets.Code.Funs

/-!
# Specifications of `Aegis.DestroyTargets.destroy_targets`

LeetCode problem `destroy-sequential-targets`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.DestroyTargets

def IsMultipleOf (space d : ℤ) : Prop := ∃ k : ℤ, d = k * space

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

noncomputable def cnt (nums : Slice Std.I64) (space : Std.I64) (s : ℤ) : ℕ :=
  (nums.val.filter (fun x => ∃ c : ℕ, x.val = s + (c : ℤ) * space.val)).length

noncomputable def cls (nums : Slice Std.I64) (space : Std.I64) (v : ℤ) : ℕ :=
  (nums.val.filter (fun x => IsMultipleOf space.val (x.val - v))).length

def numsMax (nums : Slice Std.I64) : ℤ := (vals nums).max?.getD 0

def numsMin (nums : Slice Std.I64) : ℤ := (vals nums).min?.getD 0

/-- Define cnt(s) = the number of indices i with 0 <= i < len(nums) for which there exists a non-negative integer c such that nums[i] = s + c * space. The function returns a result r and: (a) there is an index i with 0 <= i < len(nums) such that nums[i] = r; (b) for every i with 0 <= i < len(nums), cnt(r) >= cnt(nums[i]); (c) for every i with 0 <= i < len(nums), if cnt(nums[i]) = cnt(r) then r <= nums[i].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_1
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∃ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = r.val) ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val ≤ cnt nums space r.val) ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val = cnt nums space r.val →
        r.val ≤ (nums.val[i]'hi).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∃ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = r.val) ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val ≤ cnt nums space r.val) ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val = cnt nums space r.val →
        r.val ≤ (nums.val[i]'hi).val)) := by
  sorry

/-- The function returns a result r, and there is an index i with 0 <= i < len(nums) such that nums[i] = r.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_2
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∃ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = r.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∃ (i : ℕ) (hi : i < nums.length), (nums.val[i]'hi).val = r.val)) := by
  sorry

/-- Define cnt(s) = the number of indices i with 0 <= i < len(nums) for which there exists a non-negative integer c such that nums[i] = s + c * space. The function returns a result r, and for every i with 0 <= i < len(nums), cnt(r) >= cnt(nums[i]).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_3
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val ≤ cnt nums space r.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val ≤ cnt nums space r.val)) := by
  sorry

/-- Define cnt(s) = the number of indices i with 0 <= i < len(nums) for which there exists a non-negative integer c such that nums[i] = s + c * space. The function returns a result r, and for every i with 0 <= i < len(nums), if cnt(nums[i]) = cnt(r) then r <= nums[i].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_4
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val = cnt nums space r.val →
        r.val ≤ (nums.val[i]'hi).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        cnt nums space (nums.val[i]'hi).val = cnt nums space r.val →
        r.val ≤ (nums.val[i]'hi).val)) := by
  sorry

/-- Define cnt(s) = the number of indices i with 0 <= i < len(nums) for which there exists a non-negative integer c such that nums[i] = s + c * space. The function returns a result r, and 1 <= cnt(r) <= len(nums).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_5
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      1 ≤ cnt nums space r.val ∧ cnt nums space r.val ≤ nums.length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      1 ≤ cnt nums space r.val ∧ cnt nums space r.val ≤ nums.length) := by
  sorry

/-- The function returns a result r, and for every i with 0 <= i < len(nums), if nums[i] - r is an integer multiple of space (equivalently nums[i] and r have the same remainder modulo space), then r <= nums[i].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_6
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        IsMultipleOf space.val ((nums.val[i]'hi).val - r.val) →
        r.val ≤ (nums.val[i]'hi).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        IsMultipleOf space.val ((nums.val[i]'hi).val - r.val) →
        r.val ≤ (nums.val[i]'hi).val)) := by
  sorry

/-- Define cls(v) = the number of indices i with 0 <= i < len(nums) such that nums[i] - v is an integer multiple of space (the size of the residue class of v). The function returns a result r, and for every j with 0 <= j < len(nums), cls(nums[j]) <= cls(r).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_7
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ j (hj : j < nums.length),
        cls nums space (nums.val[j]'hj).val ≤ cls nums space r.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ j (hj : j < nums.length),
        cls nums space (nums.val[j]'hj).val ≤ cls nums space r.val)) := by
  sorry

/-- Define Mx = the maximum of the values nums[i] over 0 <= i < len(nums) (which exists since len(nums) >= 1). The function returns a result r, and 1 <= r <= Mx.
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_8
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      1 ≤ r.val ∧ r.val ≤ numsMax nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      1 ≤ r.val ∧ r.val ≤ numsMax nums) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_9
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r) := by
  sorry

/-- The function returns a result r, and r equals the minimum of the values nums[i] over 0 <= i < len(nums).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; space = 1. -/
theorem spec_10
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : space.val = 1) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      r.val = numsMin nums := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : space.val = 1), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      r.val = numsMin nums) := by
  sorry

/-- The function returns a result r, and r = nums[0].
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000; for every i with 0 <= i < len(nums), nums[i] = nums[0]. -/
theorem spec_11
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000)
    (hall : ∀ i (hi : i < nums.length),
      (nums.val[i]'hi).val =
        (nums.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen)).val) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      r.val = (nums.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen)).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000)
    (hall : ∀ i (hi : i < nums.length),
      (nums.val[i]'hi).val =
        (nums.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen)).val), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      r.val = (nums.val[0]'(Nat.lt_of_lt_of_le Nat.zero_lt_one hlen)).val) := by
  sorry

/-- Define cnt(s) = the number of indices i with 0 <= i < len(nums) for which there exists a non-negative integer c such that nums[i] = s + c * space. The function returns a result r, and for every i with 0 <= i < len(nums), if nums[i] < r then cnt(nums[i]) < cnt(r).
  Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; 1 <= space <= 1000000000. -/
theorem spec_12
    (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000) :
    ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        (nums.val[i]'hi).val < r.val →
        cnt nums space (nums.val[i]'hi).val < cnt nums space r.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (space : Std.I64)
    (hlen : 1 ≤ nums.length) (hlen_le : nums.length ≤ 100000)
    (hlo : ∀ i (hi : i < nums.length), 1 ≤ (nums.val[i]'hi).val)
    (hhi : ∀ i (hi : i < nums.length), (nums.val[i]'hi).val ≤ 1000000000)
    (hspace : 1 ≤ space.val) (hspace_le : space.val ≤ 1000000000), ∃ r, Aegis.DestroyTargets.destroy_targets nums space = ok r ∧
      (∀ i (hi : i < nums.length),
        (nums.val[i]'hi).val < r.val →
        cnt nums space (nums.val[i]'hi).val < cnt nums space r.val)) := by
  sorry

end AegisSpec.DestroyTargets
