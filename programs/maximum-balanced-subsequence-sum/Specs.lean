import Aegis.MaxBalancedSubsequenceSum.Code.Funs

/-!
# Specifications of `Aegis.MaxBalancedSubsequenceSum.max_balanced_subsequence_sum`

LeetCode problem `maximum-balanced-subsequence-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxBalancedSubsequenceSum

  abbrev f : Slice I64 → Result I64 := Aegis.MaxBalancedSubsequenceSum.max_balanced_subsequence_sum

  def valAt (nums : Slice I64) (i : ℕ) : ℤ :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def ChainRel {α : Type} (r : α → α → Prop) : List α → Prop
    | [] => True
    | [_] => True
    | a :: b :: l => r a b ∧ ChainRel r (b :: l)

  def IdxSubseq (nums : Slice I64) (idx : List ℕ) : Prop :=
    ChainRel (· < ·) idx ∧ ∀ i ∈ idx, i < nums.val.length

  def Slope (nums : Slice I64) (a b : ℕ) : Prop :=
    (b : ℤ) - (a : ℤ) ≤ valAt nums b - valAt nums a

  def BalancedSubseq (nums : Slice I64) (idx : List ℕ) : Prop :=
    idx ≠ [] ∧ IdxSubseq nums idx ∧ ChainRel (Slope nums) idx

  def selSum (nums : Slice I64) (idx : List ℕ) : ℤ :=
    (idx.map (valAt nums)).sum

  def total (nums : Slice I64) : ℤ :=
    ((List.range nums.val.length).map (valAt nums)).sum

  def posSum (nums : Slice I64) : ℤ :=
    ((List.range nums.val.length).map (fun i => max (valAt nums i) 0)).sum

  def maxOver (n : ℕ) (f : ℕ → ℤ) : ℤ :=
    (List.range n).foldl (fun acc i => max acc (f i)) (f 0)

  def t (nums : Slice I64) (i : ℕ) : ℤ :=
    valAt nums i - (i : ℤ)

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r is the maximum sum of a non-empty balanced subsequence: every balanced index subsequence has element sum at most r, and there exists at least one balanced index subsequence whose element sum is exactly r.
    Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. A subsequence i0 < i1 < ... < ik-1 with k >= 1 is balanced when nums[i_j] - nums[i_{j-1}] >= i_j - i_{j-1} for every j with 1 <= j <= k-1. -/
  theorem spec_1 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000) :
      ∀ r : I64, f nums = ok r →
        (∀ idx : List ℕ, BalancedSubseq nums idx → selSum nums idx ≤ r.val) ∧
        ∃ idx : List ℕ, BalancedSubseq nums idx ∧ selSum nums idx = r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000), ∀ r : I64, f nums = ok r →
          (∀ idx : List ℕ, BalancedSubseq nums idx → selSum nums idx ≤ r.val) ∧
          ∃ idx : List ℕ, BalancedSubseq nums idx ∧ selSum nums idx = r.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, access out of bounds, or overflow i64 arithmetic.
    Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_2 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000) :
      ∃ r : I64, f nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000), ∃ r : I64, f nums = ok r) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, for every index i with 0 <= i < len(nums), r >= nums[i].
    Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_3 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000) :
      ∀ r : I64, f nums = ok r → ∀ i, i < nums.val.length → valAt nums i ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000), ∀ r : I64, f nums = ok r → ∀ i, i < nums.val.length → valAt nums i ≤ r.val) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r <= sum_{i=0}^{len(nums)-1} max(nums[i], 0), where max(nums[i], 0) is nums[i] when nums[i] > 0 and 0 otherwise.
    Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_4 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000) :
      ∀ r : I64, f nums = ok r → r.val ≤ posSum nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000), ∀ r : I64, f nums = ok r → r.val ≤ posSum nums) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, -(len(nums) * 10^9) <= r <= len(nums) * 10^9.
    Preconditions: nums satisfies the problem constraints: 1 <= len(nums) <= 10^5, and for every i with 0 <= i < len(nums), -10^9 <= nums[i] <= 10^9. -/
  theorem spec_5 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000) :
      ∀ r : I64, f nums = ok r →
        -((nums.val.length : ℤ) * 1000000000) ≤ r.val ∧
          r.val ≤ (nums.val.length : ℤ) * 1000000000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000), ∀ r : I64, f nums = ok r →
          -((nums.val.length : ℤ) * 1000000000) ≤ r.val ∧
            r.val ≤ (nums.val.length : ℤ) * 1000000000) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r = nums[0].
    Preconditions: nums satisfies the problem constraints, and len(nums) = 1. -/
  theorem spec_6 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (hone : nums.val.length = 1) :
      ∀ r : I64, f nums = ok r → r.val = valAt nums 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (hone : nums.val.length = 1), ∀ r : I64, f nums = ok r → r.val = valAt nums 0) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, if nums[1] - nums[0] >= 1 then r = max(nums[0], nums[1], nums[0] + nums[1]), and otherwise r = max(nums[0], nums[1]).
    Preconditions: nums satisfies the problem constraints, and len(nums) = 2. -/
  theorem spec_7 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (htwo : nums.val.length = 2) :
      ∀ r : I64, f nums = ok r →
        (if 1 ≤ valAt nums 1 - valAt nums 0
          then r.val = max (valAt nums 0) (max (valAt nums 1) (valAt nums 0 + valAt nums 1))
          else r.val = max (valAt nums 0) (valAt nums 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (htwo : nums.val.length = 2), ∀ r : I64, f nums = ok r →
          (if 1 ≤ valAt nums 1 - valAt nums 0
            then r.val = max (valAt nums 0) (max (valAt nums 1) (valAt nums 0 + valAt nums 1))
            else r.val = max (valAt nums 0) (valAt nums 1))) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r = max_{0 <= i < len(nums)} nums[i].
    Preconditions: nums satisfies the problem constraints, and nums[i] <= 0 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (hneg : ∀ i, i < nums.val.length → valAt nums i ≤ 0) :
      ∀ r : I64, f nums = ok r → r.val = maxOver nums.val.length (valAt nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (hneg : ∀ i, i < nums.val.length → valAt nums i ≤ 0), ∀ r : I64, f nums = ok r → r.val = maxOver nums.val.length (valAt nums)) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r = c.
    Preconditions: nums satisfies the problem constraints, and there exists an integer c such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (c : ℤ) (hconst : ∀ i, i < nums.val.length → valAt nums i = c) :
      ∀ r : I64, f nums = ok r → r.val = c := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (c : ℤ) (hconst : ∀ i, i < nums.val.length → valAt nums i = c), ∀ r : I64, f nums = ok r → r.val = c) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r = len(nums) * (len(nums) - 1) / 2.
    Preconditions: nums satisfies the problem constraints, and nums[i] = i for every i with 0 <= i < len(nums). -/
  theorem spec_10 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (hid : ∀ i, i < nums.val.length → valAt nums i = (i : ℤ)) :
      ∀ r : I64, f nums = ok r →
        r.val = (nums.val.length : ℤ) * ((nums.val.length : ℤ) - 1) / 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (hid : ∀ i, i < nums.val.length → valAt nums i = (i : ℤ)), ∀ r : I64, f nums = ok r →
          r.val = (nums.val.length : ℤ) * ((nums.val.length : ℤ) - 1) / 2) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, there exists a balanced index subsequence i0 < i1 < ... < ik-1 whose element sum is r and such that nums[i_j] >= 0 for every j with 0 <= j <= k-1.
    Preconditions: nums satisfies the problem constraints, and there exists an index i with 0 <= i < len(nums) such that nums[i] >= 0. A subsequence is balanced when nums[i_j] - nums[i_{j-1}] >= i_j - i_{j-1} for every j with 1 <= j <= k-1. -/
  theorem spec_11 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (hex : ∃ i, i < nums.val.length ∧ 0 ≤ valAt nums i) :
      ∀ r : I64, f nums = ok r →
        ∃ idx : List ℕ, BalancedSubseq nums idx ∧ selSum nums idx = r.val ∧
          ∀ i ∈ idx, 0 ≤ valAt nums i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (hex : ∃ i, i < nums.val.length ∧ 0 ≤ valAt nums i), ∀ r : I64, f nums = ok r →
          ∃ idx : List ℕ, BalancedSubseq nums idx ∧ selSum nums idx = r.val ∧
            ∀ i ∈ idx, 0 ≤ valAt nums i) := by
    sorry

  /-- Whenever max_balanced_subsequence_sum(nums) returns a result r, r = sum_{i=0}^{len(nums)-1} nums[i].
    Preconditions: nums satisfies the problem constraints, nums[i] >= 0 for every i with 0 <= i < len(nums), and nums[i+1] - nums[i] >= 1 for every i with 0 <= i < len(nums)-1. -/
  theorem spec_12 (nums : Slice I64)
      (hpos : 1 ≤ nums.val.length)
      (hlen : nums.val.length ≤ 100000)
      (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
        valAt nums i ≤ 1000000000)
      (hnonneg : ∀ i, i < nums.val.length → 0 ≤ valAt nums i)
      (hslope : ∀ i, i + 1 < nums.val.length → 1 ≤ valAt nums (i + 1) - valAt nums i) :
      ∀ r : I64, f nums = ok r → r.val = total nums := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64)
        (hpos : 1 ≤ nums.val.length)
        (hlen : nums.val.length ≤ 100000)
        (hbounds : ∀ i, i < nums.val.length → -(1000000000 : ℤ) ≤ valAt nums i ∧
          valAt nums i ≤ 1000000000)
        (hnonneg : ∀ i, i < nums.val.length → 0 ≤ valAt nums i)
        (hslope : ∀ i, i + 1 < nums.val.length → 1 ≤ valAt nums (i + 1) - valAt nums i), ∀ r : I64, f nums = ok r → r.val = total nums) := by
    sorry

  end AegisSpec.MaxBalancedSubsequenceSum
