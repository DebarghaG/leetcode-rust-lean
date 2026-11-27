import Aegis.MinSumOfLengths.Code.Funs

/-!
# Specifications of `Aegis.MinSumOfLengths.min_sum_of_lengths`

LeetCode problem `find-two-non-overlapping-sub-arrays-each-with-target-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSumOfLengths

  def elemVal (arr : Slice I64) (i : Nat) : Int :=
    (arr.val[i]?).map (fun x => x.val) |>.getD 0

  def rangeSum (arr : Slice I64) (l u : Nat) : Int :=
    ((arr.val.drop l).take (u + 1 - l)).foldr (fun x acc => x.val + acc) 0

  def totalSum (arr : Slice I64) : Int := rangeSum arr 0 (arr.val.length - 1)

  def pairLenN (l1 u1 l2 u2 : Nat) : Nat := (u1 - l1 + 1) + (u2 - l2 + 1)

  def pairLen (l1 u1 l2 u2 : Nat) : Int := (pairLenN l1 u1 l2 u2 : Nat)

  def IsTwoSumPair (arr : Slice I64) (target : I64) (l1 u1 l2 u2 : Nat) : Prop :=
    l1 ≤ u1 ∧ u1 < arr.val.length ∧
    l2 ≤ u2 ∧ u2 < arr.val.length ∧
    (u1 < l2 ∨ u2 < l1) ∧
    rangeSum arr l1 u1 = target.val ∧
    rangeSum arr l2 u2 = target.val

  def HasValidPair (arr : Slice I64) (target : I64) : Prop :=
    ∃ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2

  def IsMinPairLen (arr : Slice I64) (target : I64) (m : Int) : Prop :=
    (∃ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 ∧ pairLen l1 u1 l2 u2 = m) ∧
    (∀ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 → m ≤ pairLen l1 u1 l2 u2)

  noncomputable def minPairLen (arr : Slice I64) (target : I64) : Int := by
    classical
    exact if h : HasValidPair arr target then
      ((Nat.find
        (p := fun n => ∃ l1 u1 l2 u2 : Nat,
          IsTwoSumPair arr target l1 u1 l2 u2 ∧ pairLenN l1 u1 l2 u2 = n)
        (by obtain ⟨l1, u1, l2, u2, hp⟩ := h
            exact ⟨_, l1, u1, l2, u2, hp, rfl⟩)) : Int)
    else 0

  def countVal (arr : Slice I64) (v : Int) : Nat :=
    List.countP (fun x => decide (x.val = v)) arr.val

  def ceilDiv1000 (t : Int) : Int := (t + 999) / 1000

  def revSlice (arr : Slice I64) : Slice I64 where
    leng := arr.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList arr.val.reverse
    bound := by
      simp only [List.length_reverse]
      simpa [Slice.val, Aeneas.Data.ListN.ListN_length] using arr.bound

  /-- A valid pair is a quadruple (l1,u1,l2,u2) such that 0 <= l1 <= u1 < len(arr), 0 <= l2 <= u2 < len(arr), either u1 < l2 or u2 < l1, sum from k=l1 to u1 of arr[k] equals target, and sum from k=l2 to u2 of arr[k] equals target. If at least one valid pair exists, let M be the minimum of (u1-l1+1)+(u2-l2+1) over all valid pairs. The function returns a result r and: if a valid pair exists then r = M; if no valid pair exists then r = -1.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_1 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧
        (HasValidPair arr target → r.val = minPairLen arr target) ∧
        (¬ HasValidPair arr target → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧
          (HasValidPair arr target → r.val = minPairLen arr target) ∧
          (¬ HasValidPair arr target → r.val = -1)) := by
    sorry

  /-- The function returns a result r; it does not fail, meaning there is no overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_2 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 2 <= r <= len(arr).
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_3 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
        r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (arr.val.length : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
          r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ (arr.val.length : Int))) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist indices l1,u1,l2,u2 such that 0 <= l1 <= u1 < len(arr), 0 <= l2 <= u2 < len(arr), either u1 < l2 or u2 < l1, sum from k=l1 to u1 of arr[k] equals target, sum from k=l2 to u2 of arr[k] equals target, and r = (u1-l1+1)+(u2-l2+1).
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_4 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
        ∃ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 ∧
          r.val = pairLen l1 u1 l2 u2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
          ∃ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 ∧
            r.val = pairLen l1 u1 l2 u2) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every quadruple l1,u1,l2,u2 with 0 <= l1 <= u1 < len(arr), 0 <= l2 <= u2 < len(arr), either u1 < l2 or u2 < l1, and both subarray sums equal target, we have r <= (u1-l1+1)+(u2-l2+1).
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_5 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
        ∀ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 →
          r.val ≤ pairLen l1 u1 l2 u2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
          ∀ l1 u1 l2 u2 : Nat, IsTwoSumPair arr target l1 u1 l2 u2 →
            r.val ≤ pairLen l1 u1 l2 u2) := by
    sorry

  /-- Whenever the function returns r = -1, there do not exist indices l1,u1,l2,u2 with 0 <= l1 <= u1 < len(arr), 0 <= l2 <= u2 < len(arr), either u1 < l2 or u2 < l1, and both subarray sums equal target.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_6 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val = -1 →
        ¬ HasValidPair arr target := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val = -1 →
          ¬ HasValidPair arr target) := by
    sorry

  /-- Whenever the function returns a result r, if there do not exist indices l1,u1,l2,u2 with 0 <= l1 <= u1 < len(arr), 0 <= l2 <= u2 < len(arr), either u1 < l2 or u2 < l1, and both subarray sums equal target, then r = -1.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_7 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
        ¬ HasValidPair arr target → r.val = -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
          ¬ HasValidPair arr target → r.val = -1) := by
    sorry

  /-- If len(arr) = 1, then the function returns r = -1.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_8 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
      (hlen_one : arr.val.length = 1) :
      ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
        (hlen_one : arr.val.length = 1), ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = -1) := by
    sorry

  /-- If sum from i=0 to len(arr)-1 of arr[i] is less than 2*target, then the function returns r = -1.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_9 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
      (hsum : totalSum arr < 2 * target.val) :
      ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
        (hsum : totalSum arr < 2 * target.val), ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = -1) := by
    sorry

  /-- If there exist indices i and j with 0 <= i < j < len(arr), arr[i] = target, and arr[j] = target, then the function returns r = 2.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_10 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
      (htwo : ∃ i j : Nat, i < j ∧ j < arr.val.length ∧
        elemVal arr i = target.val ∧ elemVal arr j = target.val) :
      ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
        (htwo : ∃ i j : Nat, i < j ∧ j < arr.val.length ∧
          elemVal arr i = target.val ∧ elemVal arr j = target.val), ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = 2) := by
    sorry

  /-- If target = 1, then the function returns r = 2 if there are at least two indices i with 0 <= i < len(arr) and arr[i] = 1, and returns r = -1 otherwise.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_11 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
      (htgt_one : target.val = 1) :
      ((2 ≤ countVal arr 1 →
          ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = 2) ∧
        (¬ 2 ≤ countVal arr 1 →
          ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧
            r.val = -1)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000)
        (htgt_one : target.val = 1), ((2 ≤ countVal arr 1 →
            ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧ r.val = 2) ∧
          (¬ 2 ≤ countVal arr 1 →
            ∃ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r ∧
              r.val = -1))) := by
    sorry

  /-- Whenever the function returns r = 2, there exist indices i and j with 0 <= i < j < len(arr), arr[i] = target, and arr[j] = target.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_12 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val = 2 →
        ∃ i j : Nat, i < j ∧ j < arr.val.length ∧
          elemVal arr i = target.val ∧ elemVal arr j = target.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val = 2 →
          ∃ i j : Nat, i < j ∧ j < arr.val.length ∧
            elemVal arr i = target.val ∧ elemVal arr j = target.val) := by
    sorry

  /-- Let rev(arr) be the array defined by rev(arr)[i] = arr[len(arr)-1-i] for 0 <= i < len(arr). If the function returns r on input (arr,target) and returns r' on input (rev(arr),target), then r = r'.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_13 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r r' : I64,
        Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
        Aegis.MinSumOfLengths.min_sum_of_lengths (revSlice arr) target = ok r' →
        r = r' := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r r' : I64,
          Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r →
          Aegis.MinSumOfLengths.min_sum_of_lengths (revSlice arr) target = ok r' →
          r = r') := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r >= 2 * ceil(target / 1000), where ceil(target / 1000) is the least integer c such that 1000*c >= target.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_14 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
        2 * ceilDiv1000 target.val ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
          2 * ceilDiv1000 target.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, r <= 2 * target.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_15 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
        r.val ≤ 2 * target.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ r : I64, Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
          r.val ≤ 2 * target.val) := by
    sorry

  /-- For every array arr2 of 64-bit integers satisfying 1 <= len(arr2) <= 100000, 1 <= arr2[i] <= 1000 for every i with 0 <= i < len(arr2), and len(arr2) >= len(arr) with arr2[i] = arr[i] for every 0 <= i < len(arr), if the function returns r on input (arr,target) with r != -1 and returns r2 on input (arr2,target), then r2 != -1 and r2 <= r.
    Preconditions: 1 <= len(arr) <= 100000; 1 <= target <= 100000000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000; arr[i] and target are interpreted as mathematical integers. -/
  theorem spec_16 (arr : Slice I64) (target : I64)
      (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
      (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
      (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000) :
      ∀ arr2 : Slice I64,
        (1 ≤ arr2.val.length) → (arr2.val.length ≤ 100000) →
        (∀ i : Nat, i < arr2.val.length → 1 ≤ elemVal arr2 i ∧ elemVal arr2 i ≤ 1000) →
        (arr.val.length ≤ arr2.val.length) →
        (∀ i : Nat, i < arr.val.length → elemVal arr2 i = elemVal arr i) →
        ∀ r r2 : I64,
          Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
          Aegis.MinSumOfLengths.min_sum_of_lengths arr2 target = ok r2 →
          r2.val ≠ -1 ∧ r2.val ≤ r.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (arr : Slice I64) (target : I64)
        (hlen_lb : 1 ≤ arr.val.length) (hlen_ub : arr.val.length ≤ 100000)
        (htgt_lb : 1 ≤ target.val) (htgt_ub : target.val ≤ 100000000)
        (hval : ∀ i : Nat, i < arr.val.length → 1 ≤ elemVal arr i ∧ elemVal arr i ≤ 1000), ∀ arr2 : Slice I64,
          (1 ≤ arr2.val.length) → (arr2.val.length ≤ 100000) →
          (∀ i : Nat, i < arr2.val.length → 1 ≤ elemVal arr2 i ∧ elemVal arr2 i ≤ 1000) →
          (arr.val.length ≤ arr2.val.length) →
          (∀ i : Nat, i < arr.val.length → elemVal arr2 i = elemVal arr i) →
          ∀ r r2 : I64,
            Aegis.MinSumOfLengths.min_sum_of_lengths arr target = ok r → r.val ≠ -1 →
            Aegis.MinSumOfLengths.min_sum_of_lengths arr2 target = ok r2 →
            r2.val ≠ -1 ∧ r2.val ≤ r.val) := by
    sorry

  end AegisSpec.MinSumOfLengths
