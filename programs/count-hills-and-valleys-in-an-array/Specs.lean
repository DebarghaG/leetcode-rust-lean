import Aegis.CountHillValley.Code.Funs

/-!
# Specifications of `Aegis.CountHillValley.count_hill_valley`

LeetCode problem `count-hills-and-valleys-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountHillValley

  open Aeneas.Std Aeneas.Std.Result

  def nthVal (l : List I64) (i : ℕ) : ℤ :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def IsPlateau (l : List I64) (a b : ℕ) : Prop :=
    a ≤ b ∧ b < l.length ∧
    (∀ k, a ≤ k → k ≤ b → nthVal l k = nthVal l a) ∧
    (a = 0 ∨ nthVal l (a - 1) ≠ nthVal l a) ∧
    (b = l.length - 1 ∨ nthVal l (b + 1) ≠ nthVal l b)

  def IsHill (l : List I64) (a b : ℕ) : Prop :=
    IsPlateau l a b ∧ 0 < a ∧ b < l.length - 1 ∧
    nthVal l (a - 1) < nthVal l a ∧ nthVal l (b + 1) < nthVal l a

  def IsValley (l : List I64) (a b : ℕ) : Prop :=
    IsPlateau l a b ∧ 0 < a ∧ b < l.length - 1 ∧
    nthVal l (a - 1) > nthVal l a ∧ nthVal l (b + 1) > nthVal l a

  noncomputable def countHillsValleys (l : List I64) : ℕ := by
    classical
    exact (((Finset.range l.length).product (Finset.range l.length)).filter
      (fun p => IsHill l p.1 p.2 ∨ IsValley l p.1 p.2)).card

  /-- The function returns a result res. Let a plateau be a pair (a,b) such that 0 <= a <= b < len(nums), nums[a] = nums[a+1] = ... = nums[b], (a = 0 or nums[a-1] != nums[a]), and (b = len(nums)-1 or nums[b+1] != nums[b]). A plateau (a,b) is a hill if a > 0, b < len(nums)-1, nums[a-1] < nums[a], and nums[b+1] < nums[a]. It is a valley if a > 0, b < len(nums)-1, nums[a-1] > nums[a], and nums[b+1] > nums[a]. Then res is equal to the number of plateaus that are either a hill or a valley.
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧
        res.val = (countHillsValleys nums.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧
          res.val = (countHillsValleys nums.val : ℤ)) := by
    sorry

  /-- The function returns a result res and does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res) := by
    sorry

  /-- The function returns a result res and 0 <= res.
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧ 0 ≤ res.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧ 0 ≤ res.val) := by
    sorry

  /-- The function returns a result res and res <= len(nums) - 2.
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧
        res.val ≤ (nums.val.length : ℤ) - 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧
          res.val ≤ (nums.val.length : ℤ) - 2) := by
    sorry

  /-- The function returns a result res and res = 0.
    Preconditions: len(nums) is between 3 and 100 inclusive, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and for every i with 1 <= i < len(nums), nums[i-1] <= nums[i]. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hsorted : ∀ i (hi1 : 1 ≤ i) (hi2 : i < nums.val.length),
        (nums.val[i - 1]'(by omega)).val ≤ (nums.val[i]'hi2).val) :
      ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧ res.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hsorted : ∀ i (hi1 : 1 ≤ i) (hi2 : i < nums.val.length),
          (nums.val[i - 1]'(by omega)).val ≤ (nums.val[i]'hi2).val), ∃ res, Aegis.CountHillValley.count_hill_valley nums = ok res ∧ res.val = 0) := by
    sorry

  /-- The function returns a result res on nums and a result res' on rev, and res = res'.
    Preconditions: len(nums) is between 3 and 100 inclusive, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, and rev is a slice with len(rev) = len(nums) and for every i with 0 <= i < len(nums), rev[i] = nums[len(nums)-1-i]. -/
  theorem spec_6 (nums rev : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (hrev_len : rev.val.length = nums.val.length)
      (hrev : ∀ i (h : i < nums.val.length),
        (rev.val[i]'(by omega)).val = (nums.val[nums.val.length - 1 - i]'(by omega)).val) :
      ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
        Aegis.CountHillValley.count_hill_valley rev = ok res' ∧ res.val = res'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums rev : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (hrev_len : rev.val.length = nums.val.length)
        (hrev : ∀ i (h : i < nums.val.length),
          (rev.val[i]'(by omega)).val = (nums.val[nums.val.length - 1 - i]'(by omega)).val), ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
          Aegis.CountHillValley.count_hill_valley rev = ok res' ∧ res.val = res'.val) := by
    sorry

  /-- The function returns a result res on nums and a result res' on alt, and res = res'.
    Preconditions: len(nums) is between 3 and 100 inclusive, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, C is an integer, alt is a slice with len(alt) = len(nums), for every i with 0 <= i < len(nums), alt[i] = C - nums[i], and 1 <= alt[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums alt : Slice I64) (C : ℤ)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
      (halt_len : alt.val.length = nums.val.length)
      (halt : ∀ i (h : i < nums.val.length),
        (alt.val[i]'(by omega)).val = C - (nums.val[i]'h).val)
      (halt_range : ∀ i (h : i < alt.val.length),
        1 ≤ (alt.val[i]'h).val ∧ (alt.val[i]'h).val ≤ 100) :
      ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
        Aegis.CountHillValley.count_hill_valley alt = ok res' ∧ res.val = res'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums alt : Slice I64) (C : ℤ)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100)
        (halt_len : alt.val.length = nums.val.length)
        (halt : ∀ i (h : i < nums.val.length),
          (alt.val[i]'(by omega)).val = C - (nums.val[i]'h).val)
        (halt_range : ∀ i (h : i < alt.val.length),
          1 ≤ (alt.val[i]'h).val ∧ (alt.val[i]'h).val ≤ 100), ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
          Aegis.CountHillValley.count_hill_valley alt = ok res' ∧ res.val = res'.val) := by
    sorry

  /-- The function returns a result res on nums and a result res' on reduced, and res = res'.
    Preconditions: len(nums) is between 3 and 100 inclusive, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100, len(nums) >= 4, i is an index with 0 <= i < len(nums)-1, nums[i] = nums[i+1], and reduced is a slice with len(reduced) = len(nums)-1, reduced[j] = nums[j] for 0 <= j <= i, and reduced[j] = nums[j+1] for i < j < len(reduced). -/
  theorem spec_8 (nums reduced : Slice I64) (i : ℕ)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ k (h : k < nums.val.length),
        1 ≤ (nums.val[k]'h).val ∧ (nums.val[k]'h).val ≤ 100)
      (hlen4 : 4 ≤ nums.val.length)
      (hi : i < nums.val.length - 1)
      (hdup : (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val)
      (hred_len : reduced.val.length = nums.val.length - 1)
      (hred_left : ∀ j (hj : j ≤ i),
        (reduced.val[j]'(by omega)).val = (nums.val[j]'(by omega)).val)
      (hred_right : ∀ j (hj : j < reduced.val.length), i < j →
        (reduced.val[j]'hj).val = (nums.val[j + 1]'(by omega)).val) :
      ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
        Aegis.CountHillValley.count_hill_valley reduced = ok res' ∧ res.val = res'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums reduced : Slice I64) (i : ℕ)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ k (h : k < nums.val.length),
          1 ≤ (nums.val[k]'h).val ∧ (nums.val[k]'h).val ≤ 100)
        (hlen4 : 4 ≤ nums.val.length)
        (hi : i < nums.val.length - 1)
        (hdup : (nums.val[i]'(by omega)).val = (nums.val[i + 1]'(by omega)).val)
        (hred_len : reduced.val.length = nums.val.length - 1)
        (hred_left : ∀ j (hj : j ≤ i),
          (reduced.val[j]'(by omega)).val = (nums.val[j]'(by omega)).val)
        (hred_right : ∀ j (hj : j < reduced.val.length), i < j →
          (reduced.val[j]'hj).val = (nums.val[j + 1]'(by omega)).val), ∃ res res', Aegis.CountHillValley.count_hill_valley nums = ok res ∧
          Aegis.CountHillValley.count_hill_valley reduced = ok res' ∧ res.val = res'.val) := by
    sorry

  /-- Whenever the function returns a result res with res > 0, there exists a pair (a,b) such that 0 <= a <= b < len(nums), nums[a] = nums[a+1] = ... = nums[b], (a = 0 or nums[a-1] != nums[a]), (b = len(nums)-1 or nums[b+1] != nums[b]), a > 0, b < len(nums)-1, and either (nums[a-1] < nums[a] and nums[b+1] < nums[a]) or (nums[a-1] > nums[a] and nums[b+1] > nums[a]).
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∀ res, Aegis.CountHillValley.count_hill_valley nums = ok res → 0 < res.val →
        ∃ a b, IsHill nums.val a b ∨ IsValley nums.val a b := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∀ res, Aegis.CountHillValley.count_hill_valley nums = ok res → 0 < res.val →
          ∃ a b, IsHill nums.val a b ∨ IsValley nums.val a b) := by
    sorry

  /-- Whenever the function returns a result res with res = 0, for every pair (a,b) such that 0 <= a <= b < len(nums), nums[a] = nums[a+1] = ... = nums[b], (a = 0 or nums[a-1] != nums[a]), and (b = len(nums)-1 or nums[b+1] != nums[b]), if a > 0 and b < len(nums)-1 then neither (nums[a-1] < nums[a] and nums[b+1] < nums[a]) nor (nums[a-1] > nums[a] and nums[b+1] > nums[a]).
    Preconditions: len(nums) is between 3 and 100 inclusive, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice I64)
      (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hrange : ∀ i (h : i < nums.val.length),
        1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100) :
      ∀ res, Aegis.CountHillValley.count_hill_valley nums = ok res → res.val = 0 →
        ∀ a b, IsPlateau nums.val a b → 0 < a → b < nums.val.length - 1 →
          ¬ (nthVal nums.val (a - 1) < nthVal nums.val a ∧
              nthVal nums.val (b + 1) < nthVal nums.val a) ∧
          ¬ (nthVal nums.val (a - 1) > nthVal nums.val a ∧
              nthVal nums.val (b + 1) > nthVal nums.val a) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 3 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hrange : ∀ i (h : i < nums.val.length),
          1 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 100), ∀ res, Aegis.CountHillValley.count_hill_valley nums = ok res → res.val = 0 →
          ∀ a b, IsPlateau nums.val a b → 0 < a → b < nums.val.length - 1 →
            ¬ (nthVal nums.val (a - 1) < nthVal nums.val a ∧
                nthVal nums.val (b + 1) < nthVal nums.val a) ∧
            ¬ (nthVal nums.val (a - 1) > nthVal nums.val a ∧
                nthVal nums.val (b + 1) > nthVal nums.val a)) := by
    sorry

  end AegisSpec.CountHillValley
