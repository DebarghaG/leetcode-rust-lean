import Aegis.FindIndices.Code.Funs

/-!
# Specifications of `Aegis.FindIndices.find_indices`

LeetCode problem `find-indices-with-index-and-value-difference-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindIndices

  open Aegis.FindIndices (find_indices)

  def absDiff (a b : Int) : Int := max (a - b) (b - a)

  def sliceContent (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

  def vecContent (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

  def numAt (nums : Slice Std.I64) (i : Int) : Int :=
    (sliceContent nums)[i.toNat]?.getD 0

  def HasPair (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64) : Prop :=
    ∃ i j : Fin nums.val.length,
      absDiff ((i : Nat) : Int) ((j : Nat) : Int) ≥ indexDifference.val ∧
      absDiff (nums.val[i]).val (nums.val[j]).val ≥ valueDifference.val

  /-- The function returns a result r (it does not fail), len(r) = 2, and exactly one of the following holds: (a) r[0] = -1, r[1] = -1, and for every i and j with 0 <= i < n and 0 <= j < n, it is not the case that both |i - j| >= indexDifference and |nums[i] - nums[j]| >= valueDifference; (b) 0 <= r[0] < n, 0 <= r[1] < n, |r[0] - r[1]| >= indexDifference, and |nums[r[0]] - nums[r[1]]| >= valueDifference.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_1
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r ∧
        r.val.length = 2 ∧
        ((vecContent r = [-1, -1] ∧
            ¬ HasPair nums indexDifference valueDifference)
          ∨
          (∃ r0 r1 : Int,
            vecContent r = [r0, r1] ∧
            0 ≤ r0 ∧ r0 < (nums.val.length : Int) ∧
            0 ≤ r1 ∧ r1 < (nums.val.length : Int) ∧
            absDiff r0 r1 ≥ indexDifference.val ∧
            absDiff (numAt nums r0) (numAt nums r1) ≥ valueDifference.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r ∧
          r.val.length = 2 ∧
          ((vecContent r = [-1, -1] ∧
              ¬ HasPair nums indexDifference valueDifference)
            ∨
            (∃ r0 r1 : Int,
              vecContent r = [r0, r1] ∧
              0 ≤ r0 ∧ r0 < (nums.val.length : Int) ∧
              0 ≤ r1 ∧ r1 < (nums.val.length : Int) ∧
              absDiff r0 r1 ≥ indexDifference.val ∧
              absDiff (numAt nums r0) (numAt nums r1) ≥ valueDifference.val))) := by
    sorry

  /-- The function returns a result r; in particular, for every input satisfying the preconditions it does not fail (no panic, overflow, or out-of-bounds).
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_2
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_3
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, for each k in {0,1}, either r[k] = -1 or 0 <= r[k] < n; moreover, r[0] = -1 if and only if r[1] = -1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_4
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
        ∀ r0 r1 : Int, vecContent r = [r0, r1] →
          (r0 = -1 ∨ (0 ≤ r0 ∧ r0 < (nums.val.length : Int))) ∧
          (r1 = -1 ∨ (0 ≤ r1 ∧ r1 < (nums.val.length : Int))) ∧
          (r0 = -1 ↔ r1 = -1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
          ∀ r0 r1 : Int, vecContent r = [r0, r1] →
            (r0 = -1 ∨ (0 ≤ r0 ∧ r0 < (nums.val.length : Int))) ∧
            (r1 = -1 ∨ (0 ≤ r1 ∧ r1 < (nums.val.length : Int))) ∧
            (r0 = -1 ↔ r1 = -1)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, (r[0] = -1 and r[1] = -1) if and only if there do not exist indices i and j with 0 <= i < n, 0 <= j < n, |i - j| >= indexDifference, and |nums[i] - nums[j]| >= valueDifference.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_5
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
        ∀ r0 r1 : Int, vecContent r = [r0, r1] →
          ((r0 = -1 ∧ r1 = -1) ↔
            ¬ HasPair nums indexDifference valueDifference) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
          ∀ r0 r1 : Int, vecContent r = [r0, r1] →
            ((r0 = -1 ∧ r1 = -1) ↔
              ¬ HasPair nums indexDifference valueDifference)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and r[0] != -1, then 0 <= r[0] < n, 0 <= r[1] < n, |r[0] - r[1]| >= indexDifference, and |nums[r[0]] - nums[r[1]]| >= valueDifference.
    Preconditions: Let n = len(nums). 1 <= n <= 100000; for every k with 0 <= k < n, 0 <= nums[k] <= 1000000000; 0 <= indexDifference <= 100000; 0 <= valueDifference <= 1000000000. -/
  theorem spec_6
      (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
      (hnums : ∀ i : Fin nums.val.length,
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
      (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
      (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
        ∀ r0 r1 : Int, vecContent r = [r0, r1] → r0 ≠ -1 →
          0 ≤ r0 ∧ r0 < (nums.val.length : Int) ∧
          0 ≤ r1 ∧ r1 < (nums.val.length : Int) ∧
          absDiff r0 r1 ≥ indexDifference.val ∧
          absDiff (numAt nums r0) (numAt nums r1) ≥ valueDifference.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (indexDifference valueDifference : Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
        (hnums : ∀ i : Fin nums.val.length,
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
        (hidx_lo : 0 ≤ indexDifference.val) (hidx_hi : indexDifference.val ≤ 100000)
        (hval_lo : 0 ≤ valueDifference.val) (hval_hi : valueDifference.val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          find_indices nums indexDifference valueDifference = ok r → r.val.length = 2 →
          ∀ r0 r1 : Int, vecContent r = [r0, r1] → r0 ≠ -1 →
            0 ≤ r0 ∧ r0 < (nums.val.length : Int) ∧
            0 ≤ r1 ∧ r1 < (nums.val.length : Int) ∧
            absDiff r0 r1 ≥ indexDifference.val ∧
            absDiff (numAt nums r0) (numAt nums r1) ≥ valueDifference.val) := by
    sorry

  end AegisSpec.FindIndices
