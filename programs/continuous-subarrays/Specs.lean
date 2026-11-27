import Aegis.ContinuousSubarrays.Code.Funs

/-!
# Specifications of `Aegis.ContinuousSubarrays.continuous_subarrays`

LeetCode problem `continuous-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ContinuousSubarrays

set_option autoImplicit false

  namespace AegisSpec.ContinuousSubarrays

  def elt (l : List Std.I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def windowContinuous (l : List Std.I64) (a b : Nat) : Prop :=
    ∀ i j, a ≤ i → i ≤ b → a ≤ j → j ≤ b → |elt l i - elt l j| ≤ 2

  theorem windowContinuous_self (l : List Std.I64) (a : Nat) : windowContinuous l a a := by
    intro i j hi hib hj hjb
    have h1 : i = a := by omega
    have h2 : j = a := by omega
    rw [h1, h2]
    simp

  noncomputable def pairCount (l : List Std.I64) (P : Nat → Nat → Prop) : Nat :=
    by
      classical
      exact (((Finset.range l.length).product (Finset.range l.length)).filter
        (fun p => p.1 ≤ p.2 ∧ P p.1 p.2)).card

  noncomputable def rightEnd (l : List Std.I64) (a : Nat) : Nat :=
    by
      classical
      exact Nat.findGreatest (fun b => a ≤ b ∧ b < l.length ∧ windowContinuous l a b)
        (l.length - 1)

  noncomputable def leftStart (l : List Std.I64) (b : Nat) : Nat :=
    by
      classical
      exact Nat.find (p := fun a => a ≤ b ∧ windowContinuous l a b)
        ⟨b, Nat.le_refl b, windowContinuous_self l b⟩

  def intMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def intMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def maxElt (l : List Std.I64) : Int := intMax (l.map (fun x => x.val))

  def minElt (l : List Std.I64) : Int := intMin (l.map (fun x => x.val))

  /-- Let n = len(nums). The function returns a result r, and r is exactly the number of pairs (a,b) such that 0 <= a <= b < n and for every i,j with a <= i <= b and a <= j <= b, |nums[i] - nums[j]| <= 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        r.val = ↑(pairCount nums.val (fun a b => windowContinuous nums.val a b)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          r.val = ↑(pairCount nums.val (fun a b => windowContinuous nums.val a b))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, access out of bounds, or overflow in 64-bit arithmetic.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r) := by
    sorry

  /-- The function returns r and r >= len(nums).
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧ ↑nums.val.length ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧ ↑nums.val.length ≤ r.val) := by
    sorry

  /-- The function returns r and r <= len(nums) * (len(nums) + 1) / 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        r.val ≤ ↑(nums.val.length * (nums.val.length + 1) / 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          r.val ≤ ↑(nums.val.length * (nums.val.length + 1) / 2)) := by
    sorry

  /-- The function returns r and r = len(nums) * (len(nums) + 1) / 2 if and only if (max over 0 <= i < len(nums) of nums[i]) - (min over 0 <= i < len(nums) of nums[i]) <= 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        (r.val = ↑(nums.val.length * (nums.val.length + 1) / 2) ↔
          maxElt nums.val - minElt nums.val ≤ 2) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          (r.val = ↑(nums.val.length * (nums.val.length + 1) / 2) ↔
            maxElt nums.val - minElt nums.val ≤ 2)) := by
    sorry

  /-- The function returns r and r = len(nums) if and only if for every i with 0 <= i < len(nums)-1, |nums[i+1] - nums[i]| > 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        (r.val = ↑nums.val.length ↔
          ∀ i, i + 1 < nums.val.length →
            2 < |elt nums.val (i + 1) - elt nums.val i|) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          (r.val = ↑nums.val.length ↔
            ∀ i, i + 1 < nums.val.length →
              2 < |elt nums.val (i + 1) - elt nums.val i|)) := by
    sorry

  /-- The function returns r and, for every a,b with 0 <= a <= b < len(nums), if nums[a..b] is continuous (meaning for all i,j with a <= i <= b and a <= j <= b, |nums[i] - nums[j]| <= 2), then r >= (b-a+1) * (b-a+2) / 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        ∀ a b, a ≤ b → b < nums.val.length → windowContinuous nums.val a b →
          ↑((b - a + 1) * (b - a + 2) / 2) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          ∀ a b, a ≤ b → b < nums.val.length → windowContinuous nums.val a b →
            ↑((b - a + 1) * (b - a + 2) / 2) ≤ r.val) := by
    sorry

  /-- Let n = len(nums). For each a with 0 <= a < n, let e(a) be the largest b with a <= b < n such that nums[a..b] is continuous (where nums[a..b] is continuous iff for all i,j with a <= i <= b and a <= j <= b, |nums[i] - nums[j]| <= 2). Such e(a) exists because b = a always works. The function returns r, and for every a,b with 0 <= a <= b < n, nums[a..b] is continuous if and only if b <= e(a). Equivalently, for each a the continuous subarrays starting at a are exactly nums[a..b] for a <= b <= e(a). Moreover, r = sum over a = 0 to n-1 of (e(a) - a + 1).
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        (∀ a b, a ≤ b → b < nums.val.length →
          (windowContinuous nums.val a b ↔ b ≤ rightEnd nums.val a)) ∧
        r.val = ↑(∑ a ∈ Finset.range nums.val.length,
          (rightEnd nums.val a - a + 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          (∀ a b, a ≤ b → b < nums.val.length →
            (windowContinuous nums.val a b ↔ b ≤ rightEnd nums.val a)) ∧
          r.val = ↑(∑ a ∈ Finset.range nums.val.length,
            (rightEnd nums.val a - a + 1))) := by
    sorry

  /-- Let rev be the slice with len(rev) = len(nums) and rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums). The function returns the same result on nums and on rev.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
      (rev : Slice Std.I64) (hrev : rev.val = nums.val.reverse) :
      ∃ r, continuous_subarrays nums = ok r ∧ continuous_subarrays rev = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
        (rev : Slice Std.I64) (hrev : rev.val = nums.val.reverse), ∃ r, continuous_subarrays nums = ok r ∧ continuous_subarrays rev = ok r) := by
    sorry

  /-- Let shifted be the slice with len(shifted) = len(nums) and shifted[i] = nums[i] + c for every 0 <= i < len(nums). The function returns the same result on nums and on shifted.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; c is an integer such that for every i with 0 <= i < len(nums), 1 <= nums[i] + c <= 1000000000. -/
  theorem spec_10 (nums shifted : Slice Std.I64) (c : Int)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
      (hshifted_len : shifted.val.length = nums.val.length)
      (hshifted : ∀ i, i < nums.val.length → elt shifted.val i = elt nums.val i + c)
      (hshifted_bound : ∀ i, i < nums.val.length →
        1 ≤ elt nums.val i + c ∧ elt nums.val i + c ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧ continuous_subarrays shifted = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums shifted : Slice Std.I64) (c : Int)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
        (hshifted_len : shifted.val.length = nums.val.length)
        (hshifted : ∀ i, i < nums.val.length → elt shifted.val i = elt nums.val i + c)
        (hshifted_bound : ∀ i, i < nums.val.length →
          1 ≤ elt nums.val i + c ∧ elt nums.val i + c ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧ continuous_subarrays shifted = ok r) := by
    sorry

  /-- The function returns r and r is exactly the number of pairs (a,b) with 0 <= a <= b < len(nums) and nums[b] - nums[a] <= 2.
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; nums is nondecreasing, i.e. for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
      (hnondecr : ∀ i, i + 1 < nums.val.length → elt nums.val i ≤ elt nums.val (i + 1)) :
      ∃ r, continuous_subarrays nums = ok r ∧
        r.val = ↑(pairCount nums.val (fun a b => elt nums.val b - elt nums.val a ≤ 2)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000)
        (hnondecr : ∀ i, i + 1 < nums.val.length → elt nums.val i ≤ elt nums.val (i + 1)), ∃ r, continuous_subarrays nums = ok r ∧
          r.val = ↑(pairCount nums.val (fun a b => elt nums.val b - elt nums.val a ≤ 2))) := by
    sorry

  /-- Let n = len(nums). For each b with 0 <= b < n, let s(b) be the smallest a with 0 <= a <= b such that nums[a..b] is continuous (where nums[a..b] is continuous iff for all i,j with a <= i <= b and a <= j <= b, |nums[i] - nums[j]| <= 2). Such s(b) exists because a = b always works. Then for every a,b with 0 <= a <= b < n, nums[a..b] is continuous if and only if a >= s(b), and the function returns r with r = sum over b = 0 to n-1 of (b - s(b) + 1).
    Preconditions: len(nums) >= 1; len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000) :
      ∃ r, continuous_subarrays nums = ok r ∧
        (∀ a b, a ≤ b → b < nums.val.length →
          (windowContinuous nums.val a b ↔ leftStart nums.val b ≤ a)) ∧
        r.val = ↑(∑ b ∈ Finset.range nums.val.length,
          (b - leftStart nums.val b + 1)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hbound : ∀ i, i < nums.val.length → 1 ≤ elt nums.val i ∧ elt nums.val i ≤ 1000000000), ∃ r, continuous_subarrays nums = ok r ∧
          (∀ a b, a ≤ b → b < nums.val.length →
            (windowContinuous nums.val a b ↔ leftStart nums.val b ≤ a)) ∧
          r.val = ↑(∑ b ∈ Finset.range nums.val.length,
            (b - leftStart nums.val b + 1))) := by
    sorry

  end AegisSpec.ContinuousSubarrays
