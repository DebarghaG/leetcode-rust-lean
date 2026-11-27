import Aegis.LengthOfLis.Code.Funs

/-!
# Specifications of `Aegis.LengthOfLis.length_of_lis`

LeetCode problem `longest-increasing-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LengthOfLis

def i64OfInt (x : Int) : I64 := ⟨BitVec.ofInt 64 x⟩

def selected (l : List I64) (idx : List Nat) : List I64 :=
  idx.filterMap (fun i => l[i]?)

def ValuesIncr : List I64 → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.val < b.val ∧ ValuesIncr (b :: rest)

def ValuesNonDecr : List I64 → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a.val ≤ b.val ∧ ValuesNonDecr (b :: rest)

def IncrIdx (l : List I64) (idx : List Nat) : Prop :=
  idx.Pairwise (fun i j => i < j) ∧
    (∀ i ∈ idx, i < l.length) ∧
    ValuesIncr (selected l idx)

def HasIncrLen (l : List I64) (k : Nat) : Prop :=
  ∃ idx : List Nat, idx.length = k ∧ IncrIdx l idx

def MaxIncrLen (l : List I64) (L : Nat) : Prop :=
  HasIncrLen l L ∧ ∀ k, HasIncrLen l k → k ≤ L

def distinctCount (l : List I64) : Nat :=
  (l.map (fun x => x.val)).dedup.length

def NonIncreasing (l : List I64) : Prop := l.Pairwise (fun a b => b.val ≤ a.val)

def EmbedsAt (l xs : List I64) (js : List Nat) : Prop :=
  js.length = l.length ∧
    js.Pairwise (fun i j => i < j) ∧
    (∀ j ∈ js, j < xs.length) ∧
    (∀ (i : Nat) (hi : i < js.length) (hi' : i < l.length),
      (xs[js[i]'hi]?).map (fun v => v.val) = some (l[i]'hi').val)

/-- The function returns a result r and r = L, where L is the maximum k such that there exist indices i_0, i_1, ..., i_{k-1} with 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) and nums[i_0] < nums[i_1] < ... < nums[i_{k-1}].
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ (r : I64) (L : Nat),
      Aegis.LengthOfLis.length_of_lis nums = ok r ∧ MaxIncrLen nums.val L ∧ r.val = (L : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ (r : I64) (L : Nat),
      Aegis.LengthOfLis.length_of_lis nums = ok r ∧ MaxIncrLen nums.val L ∧ r.val = (L : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r → (1 : Int) ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r → (1 : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      r.val ≤ ((nums.val.length : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      r.val ≤ ((nums.val.length : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i_0 < i_1 < ... < i_{r-1} with 0 <= i_j < len(nums) for all j and nums[i_0] < nums[i_1] < ... < nums[i_{r-1}].
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r → HasIncrLen nums.val r.val.toNat := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r → HasIncrLen nums.val r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every k and every sequence of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) for all j and nums[i_0] < nums[i_1] < ... < nums[i_{k-1}], we have k <= r.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ k, HasIncrLen nums.val k → (k : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ k, HasIncrLen nums.val k → (k : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if for every i, j with 0 <= i < j < len(nums), nums[i] >= nums[j].
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      (r.val = 1 ↔ NonIncreasing nums.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      (r.val = 1 ↔ NonIncreasing nums.val)) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) if and only if for every i with 0 <= i < len(nums) - 1, nums[i] < nums[i+1].
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      (r.val = ((nums.val.length : Nat) : Int) ↔ ValuesIncr nums.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      (r.val = ((nums.val.length : Nat) : Int) ↔ ValuesIncr nums.val)) := by
  sorry

/-- Whenever the function returns a result r, r <= D, where D is the number of distinct integers appearing in nums, i.e., D = |{ nums[i] : 0 <= i < len(nums) }|.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_8 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      r.val ≤ ((distinctCount nums.val : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      r.val ≤ ((distinctCount nums.val : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every slice xs of i64 with len(xs) = len(nums) such that for all i, j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] < nums[j] if and only if xs[i] < xs[j], r equals the maximum k such that there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) and xs[i_0] < xs[i_1] < ... < xs[i_{k-1}].
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_9 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ (xs : Slice I64) (hlen : xs.val.length = nums.val.length),
        (∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
          ((nums.val[i]).val < (nums.val[j]).val ↔
            (xs.val[i]'(by omega)).val < (xs.val[j]'(by omega)).val)) →
        MaxIncrLen xs.val r.val.toNat := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ (xs : Slice I64) (hlen : xs.val.length = nums.val.length),
        (∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
          ((nums.val[i]).val < (nums.val[j]).val ↔
            (xs.val[i]'(by omega)).val < (xs.val[j]'(by omega)).val)) →
        MaxIncrLen xs.val r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every integer x with -10000 <= x <= 10000, let nums' be the slice of length len(nums)+1 with nums'[i] = nums[i] for 0 <= i < len(nums) and nums'[len(nums)] = x; then the maximum k such that there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums)+1 and nums'[i_0] < nums'[i_1] < ... < nums'[i_{k-1}] is either r or r+1.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ x : Int, -10000 ≤ x → x ≤ 10000 →
        ∃ K : Nat,
          MaxIncrLen (nums.val ++ [i64OfInt x]) K ∧
            (K = r.val.toNat ∨ K = r.val.toNat + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ x : Int, -10000 ≤ x → x ≤ 10000 →
        ∃ K : Nat,
          MaxIncrLen (nums.val ++ [i64OfInt x]) K ∧
            (K = r.val.toNat ∨ K = r.val.toNat + 1)) := by
  sorry

/-- Whenever the function returns a result r, if for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1], then r = D, where D = |{ nums[i] : 0 <= i < len(nums) }|.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_11 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ValuesNonDecr nums.val →
        r.val = ((distinctCount nums.val : Nat) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ValuesNonDecr nums.val →
        r.val = ((distinctCount nums.val : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every slice xs of i64 and every sequence of indices j_0 < j_1 < ... < j_{m-1} with m = len(nums), 0 <= j_t < len(xs) for all t with 0 <= t < m, and nums[i] = xs[j_i] for all i with 0 <= i < len(nums), the maximum nonnegative integer K such that there exist indices i_0 < i_1 < ... < i_{K-1} with 0 <= i_s < len(xs) for all s with 0 <= s < K and xs[i_0] < xs[i_1] < ... < xs[i_{K-1}] is at least r.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_12 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ (xs : Slice I64) (js : List Nat), EmbedsAt nums.val xs.val js →
        ∃ K : Nat, MaxIncrLen xs.val K ∧ r.val.toNat ≤ K := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∀ r, Aegis.LengthOfLis.length_of_lis nums = ok r →
      ∀ (xs : Slice I64) (js : List Nat), EmbedsAt nums.val xs.val js →
        ∃ K : Nat, MaxIncrLen xs.val K ∧ r.val.toNat ≤ K) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: len(nums) >= 1 and len(nums) <= 2500 and for every i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. -/
theorem spec_13 (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r, Aegis.LengthOfLis.length_of_lis nums = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 2500)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r, Aegis.LengthOfLis.length_of_lis nums = ok r) := by
  sorry

end AegisSpec.LengthOfLis
