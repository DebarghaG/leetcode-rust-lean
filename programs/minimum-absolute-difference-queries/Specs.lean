import Aegis.MinDifference.Code.Funs

/-!
# Specifications of `Aegis.MinDifference.min_difference`

LeetCode problem `minimum-absolute-difference-queries`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinDifference

  namespace AegisSpec.MinDifference

  def vecInts (v : alloc.vec.Vec Std.I64) : List Int := v.val.map (fun x => x.val)

  def numsInts (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def numsAt (nums : Slice Std.I64) (k : Nat) : Int := (numsInts nums).getD k 0

  def vecAt (v : alloc.vec.Vec Std.I64) (k : Nat) : Int := (vecInts v).getD k 0

  def queryRow (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : alloc.vec.Vec Std.I64 :=
    queries.val.getD i (alloc.vec.Vec.new Std.I64)

  def queryL (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
    (vecAt (queryRow queries i) 0).toNat

  def queryR (queries : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
    (vecAt (queryRow queries i) 1).toNat

  def AllEqOn (nums : Slice Std.I64) (l r : Nat) : Prop :=
    ∀ k, l ≤ k → k ≤ r → numsAt nums k = numsAt nums l

  def HasDistinctPair (nums : Slice Std.I64) (l r : Nat) : Prop :=
    ∃ a b, l ≤ a ∧ a < b ∧ b ≤ r ∧ numsAt nums a ≠ numsAt nums b

  def IsMinPairDiff (nums : Slice Std.I64) (l r : Nat) (d : Int) : Prop :=
    (∃ a b, l ≤ a ∧ a < b ∧ b ≤ r ∧ numsAt nums a ≠ numsAt nums b ∧
        |numsAt nums a - numsAt nums b| = d) ∧
      (∀ a b, l ≤ a → a < b → b ≤ r → numsAt nums a ≠ numsAt nums b →
        |numsAt nums a - numsAt nums b| ≥ d)

  def ValidInput (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    2 ≤ nums.val.length ∧
      (∀ k, k < nums.val.length → 1 ≤ numsAt nums k ∧ numsAt nums k ≤ 100) ∧
      1 ≤ queries.val.length ∧
      (∀ i, i < queries.val.length →
        (queryRow queries i).val.length = 2 ∧
          0 ≤ vecAt (queryRow queries i) 0 ∧
          vecAt (queryRow queries i) 0 < vecAt (queryRow queries i) 1 ∧
          vecAt (queryRow queries i) 1 < (nums.val.length : Int))

  /-- The function returns a result ans with len(ans) = len(queries), and for every i with 0 <= i < len(queries), writing l = queries[i][0] and r = queries[i][1]: (a) if for every k with l <= k <= r, nums[k] = nums[l] (all elements of the contiguous subarray nums[l..r] are equal), then ans[i] = -1; (b) otherwise ans[i] is the minimum of the set { |nums[a] - nums[b]| : l <= a < b <= r and nums[a] != nums[b] }, that is, there exist a, b with l <= a < b <= r and nums[a] != nums[b] and |nums[a] - nums[b]| = ans[i], and for every a, b with l <= a < b <= r and nums[a] != nums[b], |nums[a] - nums[b]| >= ans[i].
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_1 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) :
      ∃ ans, min_difference nums queries = ok ans ∧ ans.val.length = queries.val.length ∧
        (∀ i, i < queries.val.length →
          (AllEqOn nums (queryL queries i) (queryR queries i) → vecAt ans i = -1) ∧
            (¬ AllEqOn nums (queryL queries i) (queryR queries i) →
              IsMinPairDiff nums (queryL queries i) (queryR queries i) (vecAt ans i))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries), ∃ ans, min_difference nums queries = ok ans ∧ ans.val.length = queries.val.length ∧
          (∀ i, i < queries.val.length →
            (AllEqOn nums (queryL queries i) (queryR queries i) → vecAt ans i = -1) ∧
              (¬ AllEqOn nums (queryL queries i) (queryR queries i) →
                IsMinPairDiff nums (queryL queries i) (queryR queries i) (vecAt ans i)))) := by
    sorry

  /-- The function returns a result ans (it does not fail, overflow, or panic) for every input satisfying the preconditions.
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_2 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) :
      ∃ ans, min_difference nums queries = ok ans := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries), ∃ ans, min_difference nums queries = ok ans) := by
    sorry

  /-- Whenever the function returns Ok ans, len(ans) = len(queries).
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_3 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ans.val.length = queries.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ans.val.length = queries.val.length) := by
    sorry

  /-- Whenever the function returns a result ans, for every i with 0 <= i < len(queries), ans[i] = -1 or 1 <= ans[i] <= 99.
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_4 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ∀ i, i < queries.val.length →
        vecAt ans i = -1 ∨ (1 ≤ vecAt ans i ∧ vecAt ans i ≤ 99) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ∀ i, i < queries.val.length →
          vecAt ans i = -1 ∨ (1 ≤ vecAt ans i ∧ vecAt ans i ≤ 99)) := by
    sorry

  /-- Whenever the function returns a result ans, for every i with 0 <= i < len(queries), writing l = queries[i][0] and r = queries[i][1], if there exist a, b with l <= a < b <= r and nums[a] != nums[b], then ans[i] >= 1.
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_5 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ∀ i, i < queries.val.length →
        HasDistinctPair nums (queryL queries i) (queryR queries i) → 1 ≤ vecAt ans i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ∀ i, i < queries.val.length →
          HasDistinctPair nums (queryL queries i) (queryR queries i) → 1 ≤ vecAt ans i) := by
    sorry

  /-- Whenever the function returns a result ans, for every i with 0 <= i < len(queries), writing l = queries[i][0] and r = queries[i][1], if ans[i] >= 1 then for every a, b with l <= a < b <= r and nums[a] != nums[b], |nums[a] - nums[b]| >= ans[i].
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_6 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ∀ i, i < queries.val.length → 1 ≤ vecAt ans i →
        ∀ a b, queryL queries i ≤ a → a < b → b ≤ queryR queries i →
          numsAt nums a ≠ numsAt nums b →
            |numsAt nums a - numsAt nums b| ≥ vecAt ans i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ∀ i, i < queries.val.length → 1 ≤ vecAt ans i →
          ∀ a b, queryL queries i ≤ a → a < b → b ≤ queryR queries i →
            numsAt nums a ≠ numsAt nums b →
              |numsAt nums a - numsAt nums b| ≥ vecAt ans i) := by
    sorry

  /-- Whenever the function returns a result ans, for every i with 0 <= i < len(queries), writing l = queries[i][0] and r = queries[i][1], if ans[i] >= 1 then there exist a, b with l <= a < b <= r and nums[a] != nums[b] and |nums[a] - nums[b]| = ans[i].
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_7 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ∀ i, i < queries.val.length → 1 ≤ vecAt ans i →
        ∃ a b, queryL queries i ≤ a ∧ a < b ∧ b ≤ queryR queries i ∧
          numsAt nums a ≠ numsAt nums b ∧
            |numsAt nums a - numsAt nums b| = vecAt ans i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ∀ i, i < queries.val.length → 1 ≤ vecAt ans i →
          ∃ a b, queryL queries i ≤ a ∧ a < b ∧ b ≤ queryR queries i ∧
            numsAt nums a ≠ numsAt nums b ∧
              |numsAt nums a - numsAt nums b| = vecAt ans i) := by
    sorry

  /-- Whenever the function returns a result ans, for every i, j with 0 <= i, j < len(queries), writing l_i = queries[i][0], r_i = queries[i][1], l_j = queries[j][0], r_j = queries[j][1], if l_i <= l_j and r_j <= r_i and ans[i] >= 1, then ans[j] = -1 or ans[j] >= ans[i].
    Preconditions: len(nums) >= 2; for every k with 0 <= k < len(nums), 1 <= nums[k] <= 100; len(queries) >= 1; for every i with 0 <= i < len(queries), len(queries[i]) = 2, and writing l = queries[i][0], r = queries[i][1], we have 0 <= l < r < len(nums). -/
  theorem spec_8 (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
      (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
      (h : min_difference nums queries = ok ans) :
      ∀ i j, i < queries.val.length → j < queries.val.length →
        queryL queries i ≤ queryL queries j → queryR queries j ≤ queryR queries i →
          1 ≤ vecAt ans i → vecAt ans j = -1 ∨ vecAt ans j ≥ vecAt ans i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (queries : Slice (alloc.vec.Vec Std.I64))
        (hp : ValidInput nums queries) (ans : alloc.vec.Vec Std.I64)
        (h : min_difference nums queries = ok ans), ∀ i j, i < queries.val.length → j < queries.val.length →
          queryL queries i ≤ queryL queries j → queryR queries j ≤ queryR queries i →
            1 ≤ vecAt ans i → vecAt ans j = -1 ∨ vecAt ans j ≥ vecAt ans i) := by
    sorry

  end AegisSpec.MinDifference
