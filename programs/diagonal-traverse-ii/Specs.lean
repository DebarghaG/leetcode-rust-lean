import Aegis.FindDiagonalOrder.Code.Funs

/-!
# Specifications of `Aegis.FindDiagonalOrder.find_diagonal_order`

LeetCode problem `diagonal-traverse-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.FindDiagonalOrder

  namespace AegisSpec.FindDiagonalOrder

  def mat (nums : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    nums.val.map (fun row => row.val.map (fun x => x.val))

  def rowCount (nums : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    (mat nums).length

  def rowLen (nums : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
    ((mat nums).getD i []).length

  def cellVal (nums : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option ℤ :=
    ((mat nums)[i]?).bind (fun row => row[j]?)

  def isCell (nums : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Prop :=
    (cellVal nums i j).isSome

  def cells (nums : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) :=
    (List.range (rowCount nums)).flatMap (fun i =>
      (List.range (rowLen nums i)).map (fun j => (i, j)))

  def outVals (r : alloc.vec.Vec Std.I64) : List ℤ :=
    r.val.map (fun x => x.val)

  def outAt (r : alloc.vec.Vec Std.I64) (k : Nat) : Option ℤ :=
    (r.val[k]?).map (fun x => x.val)

  def cellCount (nums : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : Nat :=
    ((cells nums).filter (fun c => decide (cellVal nums c.1 c.2 = some v))).length

  def outCount (r : alloc.vec.Vec Std.I64) (v : ℤ) : Nat :=
    ((outVals r).filter (fun x => decide (x = v))).length

  def rank (nums : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Nat :=
    ((cells nums).filter (fun c =>
      decide (c.1 + c.2 < i + j ∨ (c.1 + c.2 = i + j ∧ c.1 > i)))).length

  def maxDiagSum (nums : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((cells nums).map (fun c => c.1 + c.2)).foldr max 0

  /-- Whenever the function returns a result r, let C be the set of valid cells. There exists a sequence ((i_k,j_k))_{k=0}^{len(r)-1} of cells in C such that: (1) every cell of C occurs exactly once in the sequence; (2) for every k with 0 <= k < len(r), r[k] = nums[i_k][j_k]; and (3) for all k,l with 0 <= k < l < len(r), either i_k+j_k < i_l+j_l, or i_k+j_k = i_l+j_l and i_k > i_l. Equivalently, r lists all entries nums[i][j] in increasing order of i+j, breaking ties by decreasing i.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_1 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∃ f : Nat → Nat × Nat,

        (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧

        (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧

        (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧

        (∀ k l, k < l → l < r.val.length →
          (f k).1 + (f k).2 < (f l).1 + (f l).2 ∨
            ((f k).1 + (f k).2 = (f l).1 + (f l).2 ∧ (f k).1 > (f l).1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∃ f : Nat → Nat × Nat,

          (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧

          (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧

          (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧

          (∀ k l, k < l → l < r.val.length →
            (f k).1 + (f k).2 < (f l).1 + (f l).2 ∨
              ((f k).1 + (f k).2 = (f l).1 + (f l).2 ∧ (f k).1 > (f l).1))) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or access an index out of bounds) for every input satisfying the preconditions.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_2 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000) :
      ∃ r : alloc.vec.Vec Std.I64, find_diagonal_order nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, find_diagonal_order nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = sum_{i=0}^{len(nums)-1} len(nums[i]).
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_3 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      r.val.length = ((mat nums).map List.length).sum := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), r.val.length = ((mat nums).map List.length).sum) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices k with 0 <= k < len(r) and r[k] = v equals the number of valid cells (i,j) with nums[i][j] = v.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_4 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∀ v : ℤ, outCount r v = cellCount nums v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∀ v : ℤ, outCount r v = cellCount nums v) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k] <= 100000.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_5 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∀ k, k < r.val.length → ∃ v : ℤ, outAt r k = some v ∧ 1 ≤ v ∧ v ≤ 100000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∀ k, k < r.val.length → ∃ v : ℤ, outAt r k = some v ∧ 1 ≤ v ∧ v ≤ 100000) := by
    sorry

  /-- Whenever the function returns a result r, len(r) > 0 and r[0] = nums[0][0].
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_6 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      0 < r.val.length ∧ outAt r 0 = cellVal nums 0 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), 0 < r.val.length ∧ outAt r 0 = cellVal nums 0 0) := by
    sorry

  /-- Whenever the function returns a result r, for every valid cell (i,j), let p(i,j) be the number of valid cells (i',j') such that either i'+j' < i+j, or (i'+j' = i+j and i' > i). Then 0 <= p(i,j) < len(r) and r[p(i,j)] = nums[i][j].
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_7 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∀ i j, isCell nums i j →
        rank nums i j < r.val.length ∧ outAt r (rank nums i j) = cellVal nums i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∀ i j, isCell nums i j →
          rank nums i j < r.val.length ∧ outAt r (rank nums i j) = cellVal nums i j) := by
    sorry

  /-- Whenever the function returns a result r, there exists a sequence ((i_k,j_k))_{k=0}^{len(r)-1} of valid cells such that every valid cell occurs exactly once in the sequence, r[k] = nums[i_k][j_k] for every 0 <= k < len(r), and for all k,l with 0 <= k < l < len(r), i_k+j_k <= i_l+j_l.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_8 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∃ f : Nat → Nat × Nat,
        (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧
        (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧
        (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧
        (∀ k l, k < l → l < r.val.length →
          (f k).1 + (f k).2 ≤ (f l).1 + (f l).2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∃ f : Nat → Nat × Nat,
          (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧
          (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧
          (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧
          (∀ k l, k < l → l < r.val.length →
            (f k).1 + (f k).2 ≤ (f l).1 + (f l).2)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a sequence ((i_k,j_k))_{k=0}^{len(r)-1} of valid cells such that every valid cell occurs exactly once in the sequence, r[k] = nums[i_k][j_k] for every 0 <= k < len(r), and for all k,l with 0 <= k < l < len(r), if i_k+j_k = i_l+j_l then i_k > i_l.
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_9 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      ∃ f : Nat → Nat × Nat,
        (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧
        (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧
        (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧
        (∀ k l, k < l → l < r.val.length →
          ((f k).1 + (f k).2 = (f l).1 + (f l).2 → (f k).1 > (f l).1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), ∃ f : Nat → Nat × Nat,
          (∀ k, k < r.val.length → isCell nums (f k).1 (f k).2) ∧
          (∀ i j, isCell nums i j → ∃! k, k < r.val.length ∧ f k = (i, j)) ∧
          (∀ k, k < r.val.length → outAt r k = cellVal nums (f k).1 (f k).2) ∧
          (∀ k l, k < l → l < r.val.length →
            ((f k).1 + (f k).2 = (f l).1 + (f l).2 → (f k).1 > (f l).1))) := by
    sorry

  /-- Whenever the function returns a result r, let D = max {i+j | (i,j) is a valid cell}; let i* = min {i | (i,D-i) is a valid cell}; and let j* = D - i*. Then len(r) > 0 and r[len(r)-1] = nums[i*][j*].
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). -/
  theorem spec_10 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      0 < r.val.length ∧
        ∃ i : Nat, isCell nums i (maxDiagSum nums - i) ∧
          (∀ i', isCell nums i' (maxDiagSum nums - i') → i ≤ i') ∧
          outAt r (r.val.length - 1) = cellVal nums i (maxDiagSum nums - i) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), 0 < r.val.length ∧
          ∃ i : Nat, isCell nums i (maxDiagSum nums - i) ∧
            (∀ i', isCell nums i' (maxDiagSum nums - i') → i ≤ i') ∧
            outAt r (r.val.length - 1) = cellVal nums i (maxDiagSum nums - i)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums[0]) and for every j with 0 <= j < len(nums[0]), r[j] = nums[0][j].
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). In addition, len(nums)=1. -/
  theorem spec_11 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (hR_one : rowCount nums = 1)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      r.val.length = rowLen nums 0 ∧ ∀ j, j < rowLen nums 0 → outAt r j = cellVal nums 0 j := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (hR_one : rowCount nums = 1)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), r.val.length = rowLen nums 0 ∧ ∀ j, j < rowLen nums 0 → outAt r j = cellVal nums 0 j) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums) and for every i with 0 <= i < len(nums), r[i] = nums[i][0].
    Preconditions: Let R = len(nums). The input satisfies: 1 <= R <= 100000; for every i with 0 <= i < R, 1 <= len(nums[i]) <= 100000; sum_{i=0}^{R-1} len(nums[i]) <= 100000; and for every i,j with 0 <= i < R and 0 <= j < len(nums[i]), 1 <= nums[i][j] <= 100000. A valid cell is a pair (i,j) with 0 <= i < R and 0 <= j < len(nums[i]). In addition, for every i with 0 <= i < len(nums), len(nums[i]) = 1. -/
  theorem spec_12 (nums : Slice (alloc.vec.Vec Std.I64))
      (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
      (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
      (hsum : ((mat nums).map List.length).sum ≤ 100000)
      (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
      (hrow_one : ∀ i, i < rowCount nums → rowLen nums i = 1)
      (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r) :
      r.val.length = rowCount nums ∧ ∀ i, i < rowCount nums → outAt r i = cellVal nums i 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.I64))
        (hR_pos : 1 ≤ rowCount nums) (hR_le : rowCount nums ≤ 100000)
        (hrow_len : ∀ i, i < rowCount nums → 1 ≤ rowLen nums i ∧ rowLen nums i ≤ 100000)
        (hsum : ((mat nums).map List.length).sum ≤ 100000)
        (hval : ∀ i j v, cellVal nums i j = some v → 1 ≤ v ∧ v ≤ 100000)
        (hrow_one : ∀ i, i < rowCount nums → rowLen nums i = 1)
        (r : alloc.vec.Vec Std.I64) (hr : find_diagonal_order nums = ok r), r.val.length = rowCount nums ∧ ∀ i, i < rowCount nums → outAt r i = cellVal nums i 0) := by
    sorry

  end AegisSpec.FindDiagonalOrder
