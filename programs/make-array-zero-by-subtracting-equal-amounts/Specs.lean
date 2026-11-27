import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `make-array-zero-by-subtracting-equal-amounts`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumOperations

open Aegis.MinimumOperations

def positiveValues (nums : Slice Std.I64) : Finset Int :=
  ((nums.val.map (fun x => x.val)).toFinset).filter (fun v => 0 < v)

def distinctPositiveCount (nums : Slice Std.I64) : Nat :=
  (positiveValues nums).card

def hasMDistinctPositiveValues (nums : Slice Std.I64) (m : Nat) : Prop :=
  ∃ (is : List Nat) (vs : List Int),
    is.length = m ∧ vs.length = m ∧ is.Nodup ∧ vs.Nodup ∧
      List.Forall₂
        (fun i v => i < nums.val.length ∧ 0 < v ∧ (nums.val[i]?).map (fun x => x.val) = some v)
        is vs

/-- Let D(nums) be the number of distinct integers v such that v > 0 and there exists an index i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r and r = D(nums).
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every index i with 0 <= i < len(nums), nums[i] is an integer with 0 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ r, minimum_operations nums = ok r ∧ r.val = (distinctPositiveCount nums : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ r, minimum_operations nums = ok r ∧ r.val = (distinctPositiveCount nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ r, minimum_operations nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ r, minimum_operations nums = ok r → 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ r, minimum_operations nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ r, minimum_operations nums = ok r) := by
  sorry

/-- If every positive value occurring in nums also occurs in ws, that is, for every i with 0 <= i < len(nums) and nums[i] > 0 there exists j with 0 <= j < len(ws) and ws[j] = nums[i], then whenever minimum_operations(nums) returns r and minimum_operations(ws) returns s, r <= s.
  Preconditions: nums and ws both satisfy the constraints: each length is between 1 and 100 inclusive and each entry is between 0 and 100 inclusive. -/
theorem spec_4 (nums ws : Slice Std.I64)
    (hnums_low : 1 ≤ nums.val.length) (hnums_high : nums.val.length ≤ 100)
    (hws_low : 1 ≤ ws.val.length) (hws_high : ws.val.length ≤ 100)
    (hnums_entries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hws_entries : ∀ j (hj : j < ws.val.length),
      0 ≤ (ws.val[j]).val ∧ (ws.val[j]).val ≤ 100)
    (hcover : ∀ i (hi : i < nums.val.length),
      0 < (nums.val[i]).val →
        ∃ j, ∃ (hj : j < ws.val.length), (ws.val[j]).val = (nums.val[i]).val) :
    ∀ r s, minimum_operations nums = ok r → minimum_operations ws = ok s → r.val ≤ s.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums ws : Slice Std.I64)
    (hnums_low : 1 ≤ nums.val.length) (hnums_high : nums.val.length ≤ 100)
    (hws_low : 1 ≤ ws.val.length) (hws_high : ws.val.length ≤ 100)
    (hnums_entries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hws_entries : ∀ j (hj : j < ws.val.length),
      0 ≤ (ws.val[j]).val ∧ (ws.val[j]).val ≤ 100)
    (hcover : ∀ i (hi : i < nums.val.length),
      0 < (nums.val[i]).val →
        ∃ j, ∃ (hj : j < ws.val.length), (ws.val[j]).val = (nums.val[i]).val), ∀ r s, minimum_operations nums = ok r → minimum_operations ws = ok s → r.val ≤ s.val) := by
  sorry

/-- If nums and ws have exactly the same set of positive values, meaning that for every integer v > 0, v occurs among the entries of nums if and only if v occurs among the entries of ws, then whenever minimum_operations(nums) returns r and minimum_operations(ws) returns s, r = s.
  Preconditions: nums and ws both satisfy the constraints: each length is between 1 and 100 inclusive and each entry is between 0 and 100 inclusive. -/
theorem spec_5 (nums ws : Slice Std.I64)
    (hnums_low : 1 ≤ nums.val.length) (hnums_high : nums.val.length ≤ 100)
    (hws_low : 1 ≤ ws.val.length) (hws_high : ws.val.length ≤ 100)
    (hnums_entries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hws_entries : ∀ j (hj : j < ws.val.length),
      0 ≤ (ws.val[j]).val ∧ (ws.val[j]).val ≤ 100)
    (hsame : ∀ v : Int, 0 < v →
      (v ∈ nums.val.map (fun x => x.val) ↔ v ∈ ws.val.map (fun x => x.val))) :
    ∀ r s, minimum_operations nums = ok r → minimum_operations ws = ok s → r.val = s.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums ws : Slice Std.I64)
    (hnums_low : 1 ≤ nums.val.length) (hnums_high : nums.val.length ≤ 100)
    (hws_low : 1 ≤ ws.val.length) (hws_high : ws.val.length ≤ 100)
    (hnums_entries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
    (hws_entries : ∀ j (hj : j < ws.val.length),
      0 ≤ (ws.val[j]).val ∧ (ws.val[j]).val ≤ 100)
    (hsame : ∀ v : Int, 0 < v →
      (v ∈ nums.val.map (fun x => x.val) ↔ v ∈ ws.val.map (fun x => x.val))), ∀ r s, minimum_operations nums = ok r → minimum_operations ws = ok s → r.val = s.val) := by
  sorry

/-- For every integer m with 0 <= m <= 100, whenever the function returns a result r, the inequality r >= m holds if and only if nums contains at least m pairwise distinct positive values, that is, there are m distinct indices i1, ..., im and m pairwise distinct integers v1, ..., vm such that 0 <= ik < len(nums), vk > 0, and nums[ik] = vk for every k = 1, ..., m. For m = 0 the condition is vacuously true.
  Preconditions: len(nums) is between 1 and 100 inclusive, and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ m : Nat, m ≤ 100 →
      ∀ r, minimum_operations nums = ok r →
        ((m : Int) ≤ r.val ↔ hasMDistinctPositiveValues nums m) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_low : 1 ≤ nums.val.length) (hlen_high : nums.val.length ≤ 100)
    (hentries : ∀ i (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ m : Nat, m ≤ 100 →
      ∀ r, minimum_operations nums = ok r →
        ((m : Int) ≤ r.val ↔ hasMDistinctPositiveValues nums m)) := by
  sorry

end AegisSpec.MinimumOperations
