import Aegis.FindMissingRanges.Code.Funs

/-!
# Specifications of `Aegis.FindMissingRanges.find_missing_ranges`

LeetCode problem `missing-ranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMissingRanges

def sliceVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def rangeVals (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
  r.val.map (fun v => v.val.map (fun x => x.val))

def rangeAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (j : ℕ) : Option (List ℤ) :=
  (rangeVals r)[j]?

abbrev OccursIn (nums : Slice Std.I64) (x : ℤ) : Prop := x ∈ sliceVals nums

abbrev Missing (nums : Slice Std.I64) (lower upper x : ℤ) : Prop :=
  lower ≤ x ∧ x ≤ upper ∧ ¬ OccursIn nums x

abbrev Starts (nums : Slice Std.I64) (lower upper x : ℤ) : Prop :=
  Missing nums lower upper x ∧ (x = lower ∨ ¬ Missing nums lower upper (x - 1))

def intRange (lo hi : ℤ) : List ℤ :=
  (List.range (Int.toNat (hi - lo + 1))).map (fun k => lo + (k : ℤ))

def countStarts (nums : Slice Std.I64) (lower upper : ℤ) : ℕ :=
  ((intRange lower upper).filter (fun x => decide (Starts nums lower upper x))).length

/-- Let M = { x : lower <= x <= upper and x is not an element of nums }. The function returns a result r such that: (1) for every j with 0 <= j < len(r), len(r[j]) = 2; writing r[j] = [a,b], we have a <= b, a is in M, b is in M, and every integer x with a <= x <= b is in M; (2) for every x in M there is exactly one j with 0 <= j < len(r) such that r[j][0] <= x <= r[j][1]; (3) for every j with 0 <= j < len(r), writing r[j] = [a,b], either a = lower or a - 1 is an element of nums, and either b = upper or b + 1 is an element of nums; (4) for every i,j with 0 <= i < j < len(r), r[i][1] < r[j][0].
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1] (so nums is strictly increasing and has no duplicates). -/
theorem spec_1 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧

      (∀ j (hj : j < (rangeVals r).length), ∃ a b : ℤ,
        rangeAt r j = some [a, b] ∧ a ≤ b ∧
          Missing nums lower.val upper.val a ∧ Missing nums lower.val upper.val b ∧
          (∀ x : ℤ, a ≤ x → x ≤ b → Missing nums lower.val upper.val x)) ∧

      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃! j : ℕ, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b) ∧

      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] →
        (a = lower.val ∨ OccursIn nums (a - 1)) ∧
          (b = upper.val ∨ OccursIn nums (b + 1))) ∧

      (∀ i j (hij : i < j) (hj : j < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r i = some [a, b] → rangeAt r j = some [c, d] → b < c) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧

      (∀ j (hj : j < (rangeVals r).length), ∃ a b : ℤ,
        rangeAt r j = some [a, b] ∧ a ≤ b ∧
          Missing nums lower.val upper.val a ∧ Missing nums lower.val upper.val b ∧
          (∀ x : ℤ, a ≤ x → x ≤ b → Missing nums lower.val upper.val x)) ∧

      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃! j : ℕ, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b) ∧

      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] →
        (a = lower.val ∨ OccursIn nums (a - 1)) ∧
          (b = upper.val ∨ OccursIn nums (b + 1))) ∧

      (∀ i j (hij : i < j) (hj : j < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r i = some [a, b] → rangeAt r j = some [c, d] → b < c)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), the inner vector r[j] has length exactly 2; writing r[j] = [a,b], we have a <= b.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_2 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r) and every integer x that occurs as an entry of r[j], lower <= x <= upper.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_3 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (x : ℤ),
        x ∈ (rangeVals r)[j] → lower.val ≤ x ∧ x ≤ upper.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (x : ℤ),
        x ∈ (rangeVals r)[j] → lower.val ≤ x ∧ x ≤ upper.val)) := by
  sorry

/-- The function returns a result r and for every integer x with lower <= x <= upper and x not an element of nums, there exists j with 0 <= j < len(r) such that len(r[j]) = 2 and r[j][0] <= x <= r[j][1].
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_4 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃ j, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃ j, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), if len(r[j]) = 2 and r[j] = [a,b] with a <= b, then for every integer x with a <= x <= b, x is not an element of nums (that is, for every i with 0 <= i < len(nums), nums[i] != x).
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_5 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        ∀ x : ℤ, a ≤ x → x ≤ b → ¬ OccursIn nums x) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        ∀ x : ℤ, a ≤ x → x ≤ b → ¬ OccursIn nums x)) := by
  sorry

/-- The function returns a result r and for every i,j with 0 <= i < j < len(r), if r[i] = [a,b] and r[j] = [c,d] with len(r[i]) = len(r[j]) = 2, a <= b, and c <= d, then b < c.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_6 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ i j (hij : i < j) (hj : j < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r i = some [a, b] → rangeAt r j = some [c, d] →
        a ≤ b → c ≤ d → b < c) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ i j (hij : i < j) (hj : j < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r i = some [a, b] → rangeAt r j = some [c, d] →
        a ≤ b → c ≤ d → b < c)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), if r[j] = [a,b] with len(r[j]) = 2 and a <= b, then either a = lower or a - 1 is an element of nums (there exists i with 0 <= i < len(nums) and nums[i] = a - 1).
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_7 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        a = lower.val ∨ OccursIn nums (a - 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        a = lower.val ∨ OccursIn nums (a - 1))) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), if r[j] = [a,b] with len(r[j]) = 2 and a <= b, then either b = upper or b + 1 is an element of nums (there exists i with 0 <= i < len(nums) and nums[i] = b + 1).
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_8 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        b = upper.val ∨ OccursIn nums (b + 1)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        b = upper.val ∨ OccursIn nums (b + 1))) := by
  sorry

/-- The function returns a result r and for every integer x with lower <= x <= upper and x not an element of nums, there is exactly one j with 0 <= j < len(r) such that len(r[j]) = 2 and r[j][0] <= x <= r[j][1].
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_9 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃! j : ℕ, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ x : ℤ, Missing nums lower.val upper.val x →
        ∃! j : ℕ, j < (rangeVals r).length ∧
          ∃ a b : ℤ, rangeAt r j = some [a, b] ∧ a ≤ x ∧ x ≤ b)) := by
  sorry

/-- The function returns a result r and len(r) = 0 if and only if for every integer x with lower <= x <= upper, x is an element of nums (there exists i with 0 <= i < len(nums) and nums[i] = x).
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_10 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((rangeVals r).length = 0 ↔
        ∀ x : ℤ, lower.val ≤ x → x ≤ upper.val → OccursIn nums x) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((rangeVals r).length = 0 ↔
        ∀ x : ℤ, lower.val ≤ x → x ≤ upper.val → OccursIn nums x)) := by
  sorry

/-- The function returns a result r. Let M = { x : lower <= x <= upper and x is not an element of nums }, and let S = { x in M : x = lower or x - 1 is not in M }. Then len(r) equals the number of elements of S.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_11 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (rangeVals r).length = countStarts nums lower.val upper.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (rangeVals r).length = countStarts nums lower.val upper.val) := by
  sorry

/-- The function returns a result r and: if there exists an integer x with lower <= x <= upper and x not an element of nums, then len(r) > 0, len(r[0]) = 2, r[0][0] is not an element of nums, lower <= r[0][0] <= upper, and for every missing number x (with lower <= x <= upper and x not in nums) we have r[0][0] <= x. If there is no missing number, then len(r) = 0.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_12 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((∃ x : ℤ, Missing nums lower.val upper.val x) →
        0 < (rangeVals r).length ∧
        ∃ a b : ℤ, rangeAt r 0 = some [a, b] ∧ ¬ OccursIn nums a ∧
          lower.val ≤ a ∧ a ≤ upper.val ∧
          (∀ x : ℤ, Missing nums lower.val upper.val x → a ≤ x)) ∧
      ((∀ x : ℤ, ¬ Missing nums lower.val upper.val x) → (rangeVals r).length = 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((∃ x : ℤ, Missing nums lower.val upper.val x) →
        0 < (rangeVals r).length ∧
        ∃ a b : ℤ, rangeAt r 0 = some [a, b] ∧ ¬ OccursIn nums a ∧
          lower.val ≤ a ∧ a ≤ upper.val ∧
          (∀ x : ℤ, Missing nums lower.val upper.val x → a ≤ x)) ∧
      ((∀ x : ℤ, ¬ Missing nums lower.val upper.val x) → (rangeVals r).length = 0)) := by
  sorry

/-- The function returns a result r and: if there exists an integer x with lower <= x <= upper and x not an element of nums, then len(r) > 0, len(r[len(r)-1]) = 2, r[len(r)-1][1] is not an element of nums, lower <= r[len(r)-1][1] <= upper, and for every missing number x (with lower <= x <= upper and x not in nums) we have x <= r[len(r)-1][1]. If there is no missing number, then len(r) = 0.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_13 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((∃ x : ℤ, Missing nums lower.val upper.val x) →
        0 < (rangeVals r).length ∧
        ∃ a b : ℤ, rangeAt r ((rangeVals r).length - 1) = some [a, b] ∧
          ¬ OccursIn nums b ∧ lower.val ≤ b ∧ b ≤ upper.val ∧
          (∀ x : ℤ, Missing nums lower.val upper.val x → x ≤ b)) ∧
      ((∀ x : ℤ, ¬ Missing nums lower.val upper.val x) → (rangeVals r).length = 0) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      ((∃ x : ℤ, Missing nums lower.val upper.val x) →
        0 < (rangeVals r).length ∧
        ∃ a b : ℤ, rangeAt r ((rangeVals r).length - 1) = some [a, b] ∧
          ¬ OccursIn nums b ∧ lower.val ≤ b ∧ b ≤ upper.val ∧
          (∀ x : ℤ, Missing nums lower.val upper.val x → x ≤ b)) ∧
      ((∀ x : ℤ, ¬ Missing nums lower.val upper.val x) → (rangeVals r).length = 0)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r)-1, if r[j] = [a,b] and r[j+1] = [c,d] with len(r[j]) = len(r[j+1]) = 2, a <= b, and c <= d, then b + 1 < c.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_14 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j + 1 < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r j = some [a, b] → rangeAt r (j + 1) = some [c, d] →
        a ≤ b → c ≤ d → b + 1 < c) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j + 1 < (rangeVals r).length) (a b c d : ℤ),
        rangeAt r j = some [a, b] → rangeAt r (j + 1) = some [c, d] →
        a ≤ b → c ≤ d → b + 1 < c)) := by
  sorry

/-- The function returns a result r and for every j with 0 <= j < len(r), if r[j] = [a,b] with len(r[j]) = 2 and a <= b, then a and b are missing numbers: lower <= a <= upper, lower <= b <= upper, a is not an element of nums, and b is not an element of nums.
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_15 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        lower.val ≤ a ∧ a ≤ upper.val ∧ lower.val ≤ b ∧ b ≤ upper.val ∧
          ¬ OccursIn nums a ∧ ¬ OccursIn nums b) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r ∧
      (∀ j (hj : j < (rangeVals r).length) (a b : ℤ),
        rangeAt r j = some [a, b] → a ≤ b →
        lower.val ≤ a ∧ a ≤ upper.val ∧ lower.val ≤ b ∧ b ≤ upper.val ∧
          ¬ OccursIn nums a ∧ ¬ OccursIn nums b)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: lower <= upper; -10^9 <= lower and upper <= 10^9; 0 <= len(nums) <= 100; for every i with 0 <= i < len(nums), lower <= nums[i] <= upper; and for every i with 0 <= i < len(nums)-1, nums[i] < nums[i+1]. -/
theorem spec_16 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]) :
    ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hle : lower.val ≤ upper.val)
    (hlow : -1000000000 ≤ lower.val)
    (hup : upper.val ≤ 1000000000)
    (hlen : (sliceVals nums).length ≤ 100)
    (hbounds : ∀ i (hi : i < (sliceVals nums).length),
      lower.val ≤ (sliceVals nums)[i] ∧ (sliceVals nums)[i] ≤ upper.val)
    (hsorted : ∀ i (hi : i + 1 < (sliceVals nums).length),
      (sliceVals nums)[i] < (sliceVals nums)[i + 1]), ∃ r, Aegis.FindMissingRanges.find_missing_ranges nums lower upper = ok r) := by
  sorry

end AegisSpec.FindMissingRanges
