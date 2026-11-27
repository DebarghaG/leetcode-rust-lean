import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-operations-to-make-array-continuous`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinOperations

  namespace AegisSpec.MinOperations

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def IsValidInput (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧
      nums.val.length ≤ 100000 ∧
      ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000

  def Occurs (v : ℤ) (nums : Slice Std.I64) : Prop := v ∈ vals nums

  def distinctVals (nums : Slice Std.I64) : Finset ℤ := (vals nums).toFinset

  def numDistinct (nums : Slice Std.I64) : ℕ := (distinctVals nums).card

  def PairwiseDistinct (nums : Slice Std.I64) : Prop := (vals nums).Nodup

  def listMax : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldr max a

  def listMin : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldr min a

  def windowCount (D : Finset ℤ) (n L : ℤ) : ℕ :=
    (D.filter (fun v => L ≤ v ∧ v ≤ L + n - 1)).card

  def IsMaxWindowCount (D : Finset ℤ) (n M : ℤ) : Prop :=
    (∀ L : ℤ, (windowCount D n L : ℤ) ≤ M) ∧ ∃ L : ℤ, (windowCount D n L : ℤ) = M

  def diffCount : List ℤ → List ℤ → ℕ
    | [], _ => 0
    | _ :: _, [] => 0
    | a :: a', b :: b' => (if a = b then 0 else 1) + diffCount a' b'

  def IsContinuousArray (t : List ℤ) : Prop :=
    t.Nodup ∧ listMax t - listMin t = (t.length : ℤ) - 1

  /-- Let n = len(nums) and let D be the set of distinct integers occurring in nums, i.e. D = {v : there exists an index i with 0 <= i < n and nums[i] = v}. For an integer L let W(L) be the number of values v in D satisfying L <= v <= L + n - 1. Let M = max { W(L) : L is an integer }. Whenever the function returns a result r, it holds that r = n - M.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        ∃ M : ℤ, IsMaxWindowCount (distinctVals nums) (nums.val.length : ℤ) M ∧
          r.val = (nums.val.length : ℤ) - M := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          ∃ M : ℤ, IsMaxWindowCount (distinctVals nums) (nums.val.length : ℤ) M ∧
            r.val = (nums.val.length : ℤ) - M) := by
    sorry

  /-- For every nums satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∃ r : Std.I64, min_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∃ r : Std.I64, min_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns r, with n = len(nums), we have 0 <= r <= n - 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          0 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns r, with n = len(nums), we have r = 0 if and only if the entries of nums are pairwise distinct (nums[i] != nums[j] for all i, j with 0 <= i < j < n) and max(nums) - min(nums) = n - 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_4 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        (r.val = 0 ↔
          PairwiseDistinct nums ∧
            listMax (vals nums) - listMin (vals nums) = (nums.val.length : ℤ) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          (r.val = 0 ↔
            PairwiseDistinct nums ∧
              listMax (vals nums) - listMin (vals nums) = (nums.val.length : ℤ) - 1)) := by
    sorry

  /-- Whenever the function returns r, with n = len(nums) and D the set of distinct values occurring in nums, we have r = n - 1 if and only if for every two distinct values u, v in D, |u - v| >= n.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        (r.val = (nums.val.length : ℤ) - 1 ↔
          ∀ u ∈ distinctVals nums, ∀ v ∈ distinctVals nums, u ≠ v →
            (nums.val.length : ℤ) ≤ |u - v|) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          (r.val = (nums.val.length : ℤ) - 1 ↔
            ∀ u ∈ distinctVals nums, ∀ v ∈ distinctVals nums, u ≠ v →
              (nums.val.length : ℤ) ≤ |u - v|)) := by
    sorry

  /-- Let n = len(nums) and D the set of distinct values occurring in nums. Whenever the function returns r, r = n - |D| if and only if max(D) - min(D) <= n - 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        (r.val = (nums.val.length : ℤ) - (numDistinct nums : ℤ) ↔
          listMax (vals nums) - listMin (vals nums) ≤ (nums.val.length : ℤ) - 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          (r.val = (nums.val.length : ℤ) - (numDistinct nums : ℤ) ↔
            listMax (vals nums) - listMin (vals nums) ≤ (nums.val.length : ℤ) - 1)) := by
    sorry

  /-- Let n = len(nums) and D the set of distinct values occurring in nums. Whenever the function returns r, r >= n - |D|.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        (nums.val.length : ℤ) - (numDistinct nums : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          (nums.val.length : ℤ) - (numDistinct nums : ℤ) ≤ r.val) := by
    sorry

  /-- Let nums' be any sequence satisfying the same preconditions with len(nums') = len(nums) and with the same set of distinct values occurring (for every integer v, v occurs in nums' if and only if v occurs in nums). Then whenever the function returns r from nums and r' from nums', r = r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_8 (nums nums' : Slice Std.I64) (h : IsValidInput nums) (h' : IsValidInput nums')
      (hlen : nums'.val.length = nums.val.length)
      (hD : ∀ v : ℤ, Occurs v nums' ↔ Occurs v nums) :
      ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (h : IsValidInput nums) (h' : IsValidInput nums')
        (hlen : nums'.val.length = nums.val.length)
        (hD : ∀ v : ℤ, Occurs v nums' ↔ Occurs v nums), ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r = r') := by
    sorry

  /-- Let c be an integer such that 1 <= nums[i] + c <= 1000000000 for every i with 0 <= i < len(nums), and let nums' be defined by nums'[i] = nums[i] + c. Then whenever the function returns r from nums and r' from nums', r = r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64) (c : ℤ) (h : IsValidInput nums)
      (hc : ∀ v ∈ vals nums, 1 ≤ v + c ∧ v + c ≤ 1000000000)
      (hshift : vals nums' = (vals nums).map (fun v => v + c)) :
      ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ) (h : IsValidInput nums)
        (hc : ∀ v ∈ vals nums, 1 ≤ v + c ∧ v + c ≤ 1000000000)
        (hshift : vals nums' = (vals nums).map (fun v => v + c)), ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r = r') := by
    sorry

  /-- Let nums' be another sequence satisfying the preconditions with len(nums') = len(nums), whose set D' of distinct values contains the set D of distinct values of nums (D is a subset of D'). Then whenever nums yields r and nums' yields r', r >= r'.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_10 (nums nums' : Slice Std.I64) (h : IsValidInput nums) (h' : IsValidInput nums')
      (hlen : nums'.val.length = nums.val.length)
      (hsub : ∀ v : ℤ, Occurs v nums → Occurs v nums') :
      ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r ≥ r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (h : IsValidInput nums) (h' : IsValidInput nums')
        (hlen : nums'.val.length = nums.val.length)
        (hsub : ∀ v : ℤ, Occurs v nums → Occurs v nums'), ∀ r r' : Std.I64, min_operations nums = ok r → min_operations nums' = ok r' → r ≥ r') := by
    sorry

  /-- Whenever the function returns r, there exists a sequence t of length n = len(nums) such that (i) the entries of t are pairwise distinct and max(t) - min(t) = n - 1, and (ii) exactly r indices i with 0 <= i < n satisfy t[i] != nums[i].
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_11 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        ∃ t : List ℤ, t.length = nums.val.length ∧ IsContinuousArray t ∧
          (diffCount t (vals nums) : ℤ) = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          ∃ t : List ℤ, t.length = nums.val.length ∧ IsContinuousArray t ∧
            (diffCount t (vals nums) : ℤ) = r.val) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns r, for every sequence t of n integers whose entries are pairwise distinct and satisfy max(t) - min(t) = n - 1, the number of indices i with 0 <= i < n and t[i] != nums[i] is at least r. Together with spec_11 this states that r is exactly the minimum Hamming distance from nums to a continuous array.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and 1 <= nums[i] <= 1000000000 for every i with 0 <= i < len(nums). -/
  theorem spec_12 (nums : Slice Std.I64) (h : IsValidInput nums) :
      ∀ r : Std.I64, min_operations nums = ok r →
        ∀ t : List ℤ, t.length = nums.val.length → IsContinuousArray t →
          r.val ≤ (diffCount t (vals nums) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (h : IsValidInput nums), ∀ r : Std.I64, min_operations nums = ok r →
          ∀ t : List ℤ, t.length = nums.val.length → IsContinuousArray t →
            r.val ≤ (diffCount t (vals nums) : ℤ)) := by
    sorry

  end AegisSpec.MinOperations
