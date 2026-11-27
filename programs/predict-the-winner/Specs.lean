import Aegis.PredictTheWinner.Code.Funs

/-!
# Specifications of `Aegis.PredictTheWinner.predict_the_winner`

LeetCode problem `predict-the-winner`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PredictTheWinner

open Aegis.PredictTheWinner

def vals (s : Slice I64) : List Int := s.val.map (fun x => x.val)

def AllEntries (p : Int → Prop) (s : Slice I64) : Prop :=
  ∀ (i : Nat), (h : i < s.val.length) → p (s.val[i]'h).val

def InBounds (s : Slice I64) : Prop := AllEntries (fun v => 0 ≤ v ∧ v ≤ 10 ^ 7) s

def V : List Int → Int
  | [] => 0
  | x :: rest =>
      max (x - V rest) ((x :: rest).getLast (by simp) - V (x :: rest).dropLast)
termination_by xs => xs.length
decreasing_by
  · simp
  · simp only [List.length_cons, List.length_dropLast]
    omega

def playValue (p q : List Int → Bool) (turn : Bool) (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | x :: rest =>
      if turn then
        if p (x :: rest) then x - playValue p q false rest
        else (x :: rest).getLast (by simp) -
          playValue p q false (x :: rest).dropLast
      else
        if q (x :: rest) then x - playValue p q true rest
        else (x :: rest).getLast (by simp) -
          playValue p q true (x :: rest).dropLast
termination_by xs.length
decreasing_by
  all_goals
    simp only [List.length_cons, List.length_dropLast]
    omega

/-- Let V be the minimax final score difference for this game: V([]) = 0, and for a nonempty sequence xs of length n, V(xs) = max(xs[0] - V(xs[1..n-1]), xs[n-1] - V(xs[0..n-2])), where xs[1..n-1] is xs with its first element removed and xs[0..n-2] is xs with its last element removed. This V(xs) is Player 1's total score minus Player 2's total score when both play optimally from position xs with Player 1 to move. Whenever predict_the_winner(nums) returns a result r, r = true if and only if V(nums) >= 0.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. -/
theorem spec_1 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) :
    ∀ r, predict_the_winner nums = ok r → (r = true ↔ V (vals nums) ≥ 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums), ∀ r, predict_the_winner nums = ok r → (r = true ↔ V (vals nums) ≥ 0)) := by
  sorry

/-- The function returns a result r; it does not fail by panicking, overflowing, or indexing out of bounds.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. -/
theorem spec_2 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) :
    ∃ r, predict_the_winner nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums), ∃ r, predict_the_winner nums = ok r) := by
  sorry

/-- Whenever predict_the_winner(nums) returns a result r, r = true.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, and len(nums) is even. -/
theorem spec_3 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (heven : nums.val.length % 2 = 0) :
    ∀ r, predict_the_winner nums = ok r → r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (heven : nums.val.length % 2 = 0), ∀ r, predict_the_winner nums = ok r → r = true) := by
  sorry

/-- Let rev be the sequence of length len(nums) defined by rev[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). Whenever predict_the_winner(nums) returns r and predict_the_winner(rev) returns r_rev, r = r_rev.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. -/
theorem spec_4 (nums rev : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hrev : vals rev = (vals nums).reverse) :
    ∀ r r_rev, predict_the_winner nums = ok r →
      predict_the_winner rev = ok r_rev → r = r_rev := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums rev : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hrev : vals rev = (vals nums).reverse), ∀ r r_rev, predict_the_winner nums = ok r →
      predict_the_winner rev = ok r_rev → r = r_rev) := by
  sorry

/-- Whenever predict_the_winner(nums) returns r and predict_the_winner(scaled) returns r_scaled, r = r_scaled.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, and c is an integer with c >= 1 such that 0 <= c * nums[i] <= 10^7 for every i. Let scaled be the sequence of length len(nums) with scaled[i] = c * nums[i]. -/
theorem spec_5 (nums scaled : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hc : 1 ≤ c)
    (hcscaled : AllEntries (fun v => 0 ≤ c * v ∧ c * v ≤ 10 ^ 7) nums)
    (hscaled : vals scaled = (vals nums).map (fun v => c * v)) :
    ∀ r r_scaled, predict_the_winner nums = ok r →
      predict_the_winner scaled = ok r_scaled → r = r_scaled := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums scaled : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hc : 1 ≤ c)
    (hcscaled : AllEntries (fun v => 0 ≤ c * v ∧ c * v ≤ 10 ^ 7) nums)
    (hscaled : vals scaled = (vals nums).map (fun v => c * v)), ∀ r r_scaled, predict_the_winner nums = ok r →
      predict_the_winner scaled = ok r_scaled → r = r_scaled) := by
  sorry

/-- Whenever predict_the_winner(nums) returns r and predict_the_winner(shifted) returns r_shifted, r = r_shifted.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, len(nums) is even, and k is an integer such that 0 <= nums[i] + k <= 10^7 for every i. Let shifted be the sequence of length len(nums) with shifted[i] = nums[i] + k. -/
theorem spec_6 (nums shifted : Slice I64) (k : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (heven : nums.val.length % 2 = 0)
    (hkshifted : AllEntries (fun v => 0 ≤ v + k ∧ v + k ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + k)) :
    ∀ r r_shifted, predict_the_winner nums = ok r →
      predict_the_winner shifted = ok r_shifted → r = r_shifted := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums shifted : Slice I64) (k : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (heven : nums.val.length % 2 = 0)
    (hkshifted : AllEntries (fun v => 0 ≤ v + k ∧ v + k ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + k)), ∀ r r_shifted, predict_the_winner nums = ok r →
      predict_the_winner shifted = ok r_shifted → r = r_shifted) := by
  sorry

/-- Whenever predict_the_winner(nums) returns r, predict_the_winner(shifted) returns r_shifted, and r = true, we have r_shifted = true.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, and c is an integer with c >= 0 such that 0 <= nums[i] + c <= 10^7 for every i. Let shifted be the sequence of length len(nums) with shifted[i] = nums[i] + c. -/
theorem spec_7 (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hc : 0 ≤ c)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)) :
    ∀ r r_shifted, predict_the_winner nums = ok r →
      predict_the_winner shifted = ok r_shifted → r = true → r_shifted = true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hc : 0 ≤ c)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)), ∀ r r_shifted, predict_the_winner nums = ok r →
      predict_the_winner shifted = ok r_shifted → r = true → r_shifted = true) := by
  sorry

/-- If either nums[0] >= sum_{i=1}^{len(nums)-1} nums[i] or nums[len(nums)-1] >= sum_{i=0}^{len(nums)-2} nums[i], then whenever predict_the_winner(nums) returns a result r, r = true.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. Empty sums are 0. -/
theorem spec_8 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums)
    (hdominates :
      (∃ x : Int, (vals nums).head? = some x ∧ x ≥ (vals nums).tail.sum) ∨
      (∃ y : Int, (vals nums).getLast? = some y ∧ y ≥ (vals nums).dropLast.sum)) :
    ∀ r, predict_the_winner nums = ok r → r = true := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums)
    (hdominates :
      (∃ x : Int, (vals nums).head? = some x ∧ x ≥ (vals nums).tail.sum) ∨
      (∃ y : Int, (vals nums).getLast? = some y ∧ y ≥ (vals nums).dropLast.sum)), ∀ r, predict_the_winner nums = ok r → r = true) := by
  sorry

/-- Using the minimax value V defined by V([]) = 0 and V(xs) = max(xs[0] - V(xs without first), xs[len(xs)-1] - V(xs without last)) for nonempty xs, whenever predict_the_winner(nums) returns r and r = true, there exists j in {0, len(nums)-1} such that nums[j] - V(nums with index j removed) >= 0.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. -/
theorem spec_9 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) :
    ∀ r, predict_the_winner nums = ok r → r = true →
      ∃ j : Nat, j < (vals nums).length ∧
        (j = 0 ∨ j = (vals nums).length - 1) ∧
        ∃ v : Int, (vals nums)[j]? = some v ∧ v - V ((vals nums).eraseIdx j) ≥ 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums), ∀ r, predict_the_winner nums = ok r → r = true →
      ∃ j : Nat, j < (vals nums).length ∧
        (j = 0 ∨ j = (vals nums).length - 1) ∧
        ∃ v : Int, (vals nums)[j]? = some v ∧ v - V ((vals nums).eraseIdx j) ≥ 0) := by
  sorry

/-- Whenever predict_the_winner(shifted) returns a result r, r = true.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, len(nums) is odd, and c is an integer with c >= sum_{i=0}^{len(nums)-1} nums[i] such that 0 <= nums[i] + c <= 10^7 for every i. Let shifted be the sequence of length len(nums) with shifted[i] = nums[i] + c. -/
theorem spec_10 (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hodd : nums.val.length % 2 = 1)
    (hc : c ≥ (vals nums).sum)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)) :
    ∀ r, predict_the_winner shifted = ok r → r = true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hodd : nums.val.length % 2 = 1)
    (hc : c ≥ (vals nums).sum)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)), ∀ r, predict_the_winner shifted = ok r → r = true) := by
  sorry

/-- Whenever predict_the_winner(nums) returns a result r and r = false, Player 2 has a strategy such that, no matter how Player 1 plays, Player 2's final score is strictly greater than Player 1's final score.
  Preconditions: 1 <= len(nums) <= 20 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 10^7. -/
theorem spec_11 (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) :
    ∀ r, predict_the_winner nums = ok r → r = false →
      ∃ σ : List Int → Bool, ∀ π : List Int → Bool,
        playValue π σ true (vals nums) < 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums), ∀ r, predict_the_winner nums = ok r → r = false →
      ∃ σ : List Int → Bool, ∀ π : List Int → Bool,
        playValue π σ true (vals nums) < 0) := by
  sorry

/-- Let V be as defined in spec_1. Then V(shifted) = V(nums) + c. Consequently, whenever predict_the_winner(shifted) returns a result r, r = true if and only if V(nums) + c >= 0.
  Preconditions: 1 <= len(nums) <= 20, for every i with 0 <= i < len(nums) we have 0 <= nums[i] <= 10^7, len(nums) is odd, and c is an integer such that 0 <= nums[i] + c <= 10^7 for every i. Let shifted be the sequence of length len(nums) with shifted[i] = nums[i] + c. -/
theorem spec_12 (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hodd : nums.val.length % 2 = 1)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)) :
    V (vals shifted) = V (vals nums) + c ∧
      (∀ r, predict_the_winner shifted = ok r →
        (r = true ↔ V (vals nums) + c ≥ 0)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums shifted : Slice I64) (c : Int)
    (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 20)
    (hbounds : InBounds nums) (hodd : nums.val.length % 2 = 1)
    (hcshifted : AllEntries (fun v => 0 ≤ v + c ∧ v + c ≤ 10 ^ 7) nums)
    (hshifted : vals shifted = (vals nums).map (fun v => v + c)), V (vals shifted) = V (vals nums) + c ∧
      (∀ r, predict_the_winner shifted = ok r →
        (r = true ↔ V (vals nums) + c ≥ 0))) := by
  sorry

end AegisSpec.PredictTheWinner
