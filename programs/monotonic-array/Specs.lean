import Aegis.IsMonotonic.Code.Funs

/-!
# Specifications of `Aegis.IsMonotonic.is_monotonic`

LeetCode problem `monotonic-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsMonotonic

def len (s : Slice Std.I64) : Nat := s.val.length

def nth (s : Slice Std.I64) (i : Nat) : Int := (s.val.getD i 0#i64).val

def Nondecreasing (s : Slice Std.I64) : Prop :=
  ∀ i j : Nat, i ≤ j → j < len s → nth s i ≤ nth s j

def Nonincreasing (s : Slice Std.I64) : Prop :=
  ∀ i j : Nat, i ≤ j → j < len s → nth s i ≥ nth s j

def HasPeakOrValley (s : Slice Std.I64) : Prop :=
  ∃ i j k : Nat, i < j ∧ j < k ∧ k < len s ∧
    ((nth s i < nth s j ∧ nth s j > nth s k) ∨
     (nth s i > nth s j ∧ nth s j < nth s k))

def IsReverse (s t : Slice Std.I64) : Prop :=
  len t = len s ∧ ∀ i : Nat, i < len s → nth t i = nth s (len s - 1 - i)

def IsNegation (s t : Slice Std.I64) : Prop :=
  len t = len s ∧ ∀ i : Nat, i < len s → nth t i = - nth s i

def IsShift (s : Slice Std.I64) (c : Int) (t : Slice Std.I64) : Prop :=
  len t = len s ∧ ∀ i : Nat, i < len s → nth t i = nth s i + c

def IsScale (s : Slice Std.I64) (k : Nat) (t : Slice Std.I64) : Prop :=
  len t = len s ∧ ∀ i : Nat, i < len s → nth t i = (k : Int) * nth s i

/-- The function returns a result r, and r = true if and only if either (for every i and j with 0 <= i <= j < len(nums), nums[i] <= nums[j]) or (for every i and j with 0 <= i <= j < len(nums), nums[i] >= nums[j]).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∃ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      (r = true ↔ Nondecreasing nums ∨ Nonincreasing nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∃ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      (r = true ↔ Nondecreasing nums ∨ Nonincreasing nums)) := by
  sorry

/-- The function returns a Boolean result r; for every input satisfying the preconditions it does not fail (no overflow, panic, out-of-bounds access, or other runtime error).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∃ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∃ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r) := by
  sorry

/-- Whenever the call returns a result r, if r = false then there exist indices i, j, k with 0 <= i < j < k < len(nums) such that either (nums[i] < nums[j] and nums[j] > nums[k]) or (nums[i] > nums[j] and nums[j] < nums[k]).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = false →
      HasPeakOrValley nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = false →
      HasPeakOrValley nums) := by
  sorry

/-- Whenever the call returns a result r, if r = true then there do not exist indices i, j, k with 0 <= i < j < k < len(nums) such that either (nums[i] < nums[j] and nums[j] > nums[k]) or (nums[i] > nums[j] and nums[j] < nums[k]).
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      ¬ HasPeakOrValley nums := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      ¬ HasPeakOrValley nums) := by
  sorry

/-- Whenever the call returns a result r, if r = true and nums[0] < nums[len(nums)-1], then for every i and j with 0 <= i <= j < len(nums), nums[i] <= nums[j].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 < nth nums (len nums - 1) → Nondecreasing nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 < nth nums (len nums - 1) → Nondecreasing nums) := by
  sorry

/-- Whenever the call returns a result r, if r = true and nums[0] > nums[len(nums)-1], then for every i and j with 0 <= i <= j < len(nums), nums[i] >= nums[j].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 > nth nums (len nums - 1) → Nonincreasing nums := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 > nth nums (len nums - 1) → Nonincreasing nums) := by
  sorry

/-- Whenever the call returns a result r, if r = true and nums[0] = nums[len(nums)-1], then for every i with 0 <= i < len(nums), nums[i] = nums[0].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 = nth nums (len nums - 1) →
      ∀ i : Nat, i < len nums → nth nums i = nth nums 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 = nth nums (len nums - 1) →
      ∀ i : Nat, i < len nums → nth nums i = nth nums 0) := by
  sorry

/-- Whenever the call returns a result r, if for every i and j with 0 <= i <= j < len(nums), nums[i] <= nums[j], then r = true.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → Nondecreasing nums → r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → Nondecreasing nums → r = true) := by
  sorry

/-- Whenever the call returns a result r, if for every i and j with 0 <= i <= j < len(nums), nums[i] >= nums[j], then r = true.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → Nonincreasing nums → r = true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → Nonincreasing nums → r = true) := by
  sorry

/-- Whenever the call returns a result r, if len(nums) <= 2, then r = true.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → len nums ≤ 2 → r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → len nums ≤ 2 → r = true) := by
  sorry

/-- For every nums satisfying the preconditions, let rev be the slice with len(rev) = len(nums) and rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). The call on nums returns r, the call on rev returns r_rev, and r = r_rev.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_11 (nums rev : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hrev : IsReverse nums rev) :
    ∃ r r_rev : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic rev = ok r_rev ∧ r = r_rev := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hrev : IsReverse nums rev), ∃ r r_rev : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic rev = ok r_rev ∧ r = r_rev) := by
  sorry

/-- For every nums satisfying the preconditions, let neg be the slice with len(neg) = len(nums) and neg[i] = -nums[i] for every i with 0 <= i < len(nums). The call on nums returns r, the call on neg returns r_neg, and r = r_neg.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_12 (nums neg : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hneg : IsNegation nums neg) :
    ∃ r r_neg : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic neg = ok r_neg ∧ r = r_neg := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums neg : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hneg : IsNegation nums neg), ∃ r r_neg : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic neg = ok r_neg ∧ r = r_neg) := by
  sorry

/-- For every nums satisfying the preconditions and every integer c such that -100000 <= nums[i] + c <= 100000 for all i with 0 <= i < len(nums), let shifted be the slice with len(shifted) = len(nums) and shifted[i] = nums[i] + c for every i. The call on nums returns r, the call on shifted returns r_shifted, and r = r_shifted.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_13 (nums shifted : Slice Std.I64) (c : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hshift_bounds : ∀ i : Nat, i < len nums →
      -100000 ≤ nth nums i + c ∧ nth nums i + c ≤ 100000)
    (hshift : IsShift nums c shifted) :
    ∃ r r_shifted : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic shifted = ok r_shifted ∧ r = r_shifted := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums shifted : Slice Std.I64) (c : Int)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hshift_bounds : ∀ i : Nat, i < len nums →
      -100000 ≤ nth nums i + c ∧ nth nums i + c ≤ 100000)
    (hshift : IsShift nums c shifted), ∃ r r_shifted : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic shifted = ok r_shifted ∧ r = r_shifted) := by
  sorry

/-- For every nums satisfying the preconditions and every positive integer k such that -100000 <= k * nums[i] <= 100000 for all i with 0 <= i < len(nums), let scaled be the slice with len(scaled) = len(nums) and scaled[i] = k * nums[i] for every i. The call on nums returns r, the call on scaled returns r_scaled, and r = r_scaled.
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_14 (nums scaled : Slice Std.I64) (k : Nat)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hk_pos : 0 < k)
    (hscale_bounds : ∀ i : Nat, i < len nums →
      -100000 ≤ (k : Int) * nth nums i ∧ (k : Int) * nth nums i ≤ 100000)
    (hscale : IsScale nums k scaled) :
    ∃ r r_scaled : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic scaled = ok r_scaled ∧ r = r_scaled := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums scaled : Slice Std.I64) (k : Nat)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000)
    (hk_pos : 0 < k)
    (hscale_bounds : ∀ i : Nat, i < len nums →
      -100000 ≤ (k : Int) * nth nums i ∧ (k : Int) * nth nums i ≤ 100000)
    (hscale : IsScale nums k scaled), ∃ r r_scaled : Bool,
      Aegis.IsMonotonic.is_monotonic nums = ok r ∧
      Aegis.IsMonotonic.is_monotonic scaled = ok r_scaled ∧ r = r_scaled) := by
  sorry

/-- Whenever the call returns a result r, if r = true and nums[0] < nums[len(nums)-1], then for every i with 0 <= i < len(nums), nums[0] <= nums[i] and nums[i] <= nums[len(nums)-1].
  Preconditions: 1 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_15 (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000) :
    ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 < nth nums (len nums - 1) →
      ∀ i : Nat, i < len nums →
        nth nums 0 ≤ nth nums i ∧ nth nums i ≤ nth nums (len nums - 1) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lo : 1 ≤ len nums) (hlen_hi : len nums ≤ 100000)
    (hbounds : ∀ i : Nat, i < len nums → -100000 ≤ nth nums i ∧ nth nums i ≤ 100000), ∀ r : Bool, Aegis.IsMonotonic.is_monotonic nums = ok r → r = true →
      nth nums 0 < nth nums (len nums - 1) →
      ∀ i : Nat, i < len nums →
        nth nums 0 ≤ nth nums i ∧ nth nums i ≤ nth nums (len nums - 1)) := by
  sorry

end AegisSpec.IsMonotonic
