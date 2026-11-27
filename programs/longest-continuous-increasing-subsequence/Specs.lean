import Aegis.FindLengthOfLcis.Code.Funs

/-!
# Specifications of `Aegis.FindLengthOfLcis.find_length_of_lcis`

LeetCode problem `longest-continuous-increasing-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindLengthOfLcis

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def block (l : List Int) (i j : Nat) : List Int := (l.drop i).take (j + 1 - i)

  def StepChain (R : Int → Int → Prop) : List Int → Prop
    | [] => True
    | [_] => True
    | a :: b :: rest => R a b ∧ StepChain R (b :: rest)

  instance instDecidableStepChain (R : Int → Int → Prop) [DecidableRel R] :
      DecidablePred (StepChain R) := by
    intro l
    induction l with
    | nil => exact isTrue trivial
    | cons a t ih =>
      cases t with
      | nil => exact isTrue trivial
      | cons b rest =>
        by_cases h : R a b
        · by_cases ht : StepChain R (b :: rest)
          · exact isTrue ⟨h, ht⟩
          · exact isFalse fun hc => ht hc.2
        · exact isFalse fun hc => h hc.1

  @[reducible] def IncBlock (l : List Int) (i j : Nat) : Prop :=
    StepChain (fun a b => a < b) (block l i j)

  @[reducible] def NonIncBlock (l : List Int) (i j : Nat) : Prop :=
    StepChain (fun a b => b ≤ a) (block l i j)

  def lcisLengths (l : List Int) : Set Nat :=
    { n | ∃ i j : Nat, i ≤ j ∧ j < l.length ∧ j - i + 1 = n ∧ IncBlock l i j }

  noncomputable def maxLcisLen (l : List Int) : Nat := sSup (lcisLengths l)

  def stepBlockLengths (l : List Int) : Set Nat :=
    { n | ∃ a b : Nat, a ≤ b ∧ b + 1 < l.length ∧ b - a + 1 = n ∧ IncBlock l a (b + 1) }

  noncomputable def maxStepBlockLen (l : List Int) : Nat := sSup (stepBlockLengths l)

  def stepCount (l : List Int) : Nat :=
    ((List.range (l.length - 1)).filter (fun k => decide (IncBlock l k (k + 1)))).length

  /-- The function returns a result out and: if len(nums) = 0 then out = 1; if len(nums) > 0 then out = max { j - i + 1 | 0 <= i <= j < len(nums) and for every k with i <= k < j, nums[k] < nums[k+1] }.
    Preconditions: len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        (nums.val.length = 0 → out.val = 1) ∧
        (0 < nums.val.length → out.val = (maxLcisLen (contents nums) : Int)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          (nums.val.length = 0 → out.val = 1) ∧
          (0 < nums.val.length → out.val = (maxLcisLen (contents nums) : Int))) := by
    sorry

  /-- The function returns a result out; in particular, it does not fail, panic, or overflow on any input satisfying the preconditions.
    Preconditions: len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out) := by
    sorry

  /-- The function returns a result out and 1 <= out <= len(nums).
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        1 ≤ out.val ∧ out.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          1 ≤ out.val ∧ out.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- The function returns a result out and there exist indices i and j with 0 <= i <= j < len(nums) such that j - i + 1 = out and for every k with i <= k < j, nums[k] < nums[k+1].
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        ∃ i j : Nat, i ≤ j ∧ j < nums.val.length ∧ ((j - i + 1 : Nat) : Int) = out.val ∧
          IncBlock (contents nums) i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          ∃ i j : Nat, i ≤ j ∧ j < nums.val.length ∧ ((j - i + 1 : Nat) : Int) = out.val ∧
            IncBlock (contents nums) i j) := by
    sorry

  /-- The function returns a result out and for every i and j with 0 <= i <= j < len(nums), if for every k with i <= k < j, nums[k] < nums[k+1], then j - i + 1 <= out.
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        ∀ (i j : Nat), i ≤ j → j < nums.val.length → IncBlock (contents nums) i j →
          ((j - i + 1 : Nat) : Int) ≤ out.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          ∀ (i j : Nat), i ≤ j → j < nums.val.length → IncBlock (contents nums) i j →
            ((j - i + 1 : Nat) : Int) ≤ out.val) := by
    sorry

  /-- The function returns a result out and out = 1 if and only if for every k with 0 <= k < len(nums)-1, nums[k] >= nums[k+1].
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        (out.val = 1 ↔
          NonIncBlock (contents nums) 0 (nums.val.length - 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          (out.val = 1 ↔
            NonIncBlock (contents nums) 0 (nums.val.length - 1))) := by
    sorry

  /-- The function returns a result out and out = 1 + M, where M is the maximum of all lengths b - a + 1 of contiguous blocks of indices a, a+1, ..., b with 0 <= a <= b < len(nums)-1 for which nums[k] < nums[k+1] for every k with a <= k <= b; if there is no such index block (in particular, when len(nums) = 1), then M = 0.
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        out.val = 1 + (maxStepBlockLen (contents nums) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          out.val = 1 + (maxStepBlockLen (contents nums) : Int)) := by
    sorry

  /-- The function returns a result out and out <= 1 + C, where C is the number of indices k with 0 <= k < len(nums)-1 and nums[k] < nums[k+1].
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        out.val ≤ 1 + (stepCount (contents nums) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          out.val ≤ 1 + (stepCount (contents nums) : Int)) := by
    sorry

  /-- The function returns a result out and, for every slice ys of 64-bit integers with len(ys) = len(nums) and for every t with 0 <= t < len(nums)-1, nums[t] < nums[t+1] if and only if ys[t] < ys[t+1], we have out = max { q - p + 1 | 0 <= p <= q < len(ys) and for every k with p <= k < q, ys[k] < ys[k+1] }.
    Preconditions: 1 <= len(nums) <= 10000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : nums.val.length ≤ 10000)
      (hval : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hpos : 1 ≤ nums.val.length) :
      ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
        ∀ (ys : Slice Std.I64), ys.val.length = nums.val.length →
          (∀ (t : Nat), t < nums.val.length - 1 →
            (IncBlock (contents nums) t (t + 1) ↔ IncBlock (contents ys) t (t + 1))) →
          out.val = (maxLcisLen (contents ys) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : nums.val.length ≤ 10000)
        (hval : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hpos : 1 ≤ nums.val.length), ∃ out : Std.I64, Aegis.FindLengthOfLcis.find_length_of_lcis nums = ok out ∧
          ∀ (ys : Slice Std.I64), ys.val.length = nums.val.length →
            (∀ (t : Nat), t < nums.val.length - 1 →
              (IncBlock (contents nums) t (t + 1) ↔ IncBlock (contents ys) t (t + 1))) →
            out.val = (maxLcisLen (contents ys) : Int)) := by
    sorry

  end AegisSpec.FindLengthOfLcis
