import Aegis.FourSum.Code.Funs

/-!
# Specifications of `Aegis.FourSum.four_sum`

LeetCode problem `4sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FourSum

def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def vecVals (q : alloc.vec.Vec Std.I64) : List Int := q.val.map (fun x => x.val)

def idxVal (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def quadVal (q : alloc.vec.Vec Std.I64) (k : Nat) : Int :=
  match q.val[k]? with
  | some x => x.val
  | none => 0

def quadOfIdx (nums : Slice Std.I64) (a b c d : Nat) : List Int :=
  [idxVal nums a, idxVal nums b, idxVal nums c, idxVal nums d]

def pairwiseDistinct4 (a b c d : Nat) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def inRange4 (nums : Slice Std.I64) (a b c d : Nat) : Prop :=
  a < nums.val.length ∧ b < nums.val.length ∧
    c < nums.val.length ∧ d < nums.val.length

def permAt (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Nat) (l : List Int) : Prop :=
  ∃ q, r.val[i]? = some q ∧ (vecVals q).Perm l

def quadSumIs (q : alloc.vec.Vec Std.I64) (target : Std.I64) : Prop :=
  quadVal q 0 + quadVal q 1 + quadVal q 2 + quadVal q 3 = target.val

/-- The function returns a result r (a Vec of Vec of i64) and r is exactly the set of all unique quadruplets from nums that sum to target, in the following sense: (1) for every element q of r, len(q) = 4; (2) for every element q of r, q[0] + q[1] + q[2] + q[3] = target; (3) for every element q of r, there exist four pairwise distinct indices a,b,c,d with 0 <= a,b,c,d < len(nums) such that the sequence (q[0],q[1],q[2],q[3]) is a permutation of (nums[a],nums[b],nums[c],nums[d]); (4) for every two distinct indices i and j of r, the sequence (r[i][0],r[i][1],r[i][2],r[i][3]) is not a permutation of (r[j][0],r[j][1],r[j][2],r[j][3]); (5) for every four pairwise distinct indices a,b,c,d with 0 <= a,b,c,d < len(nums) and nums[a] + nums[b] + nums[c] + nums[d] = target, there exists exactly one index i of r such that (r[i][0],r[i][1],r[i][2],r[i][3]) is a permutation of (nums[a],nums[b],nums[c],nums[d]).
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧

      (∀ q ∈ r.val, q.val.length = 4) ∧

      (∀ q ∈ r.val, quadSumIs q target) ∧

      (∀ q ∈ r.val, ∃ a b c d : Nat,
        inRange4 nums a b c d ∧ pairwiseDistinct4 a b c d ∧
          (vecVals q).Perm (quadOfIdx nums a b c d)) ∧

      (∀ (i j : Nat), i ≠ j → ∀ q₁ q₂,
        r.val[i]? = some q₁ → r.val[j]? = some q₂ →
          ¬ (vecVals q₁).Perm (vecVals q₂)) ∧

      (∀ a b c d : Nat,
        inRange4 nums a b c d → pairwiseDistinct4 a b c d →
          idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d = target.val →
            ∃! i : Nat, permAt r i (quadOfIdx nums a b c d)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧

      (∀ q ∈ r.val, q.val.length = 4) ∧

      (∀ q ∈ r.val, quadSumIs q target) ∧

      (∀ q ∈ r.val, ∃ a b c d : Nat,
        inRange4 nums a b c d ∧ pairwiseDistinct4 a b c d ∧
          (vecVals q).Perm (quadOfIdx nums a b c d)) ∧

      (∀ (i j : Nat), i ≠ j → ∀ q₁ q₂,
        r.val[i]? = some q₁ → r.val[j]? = some q₂ →
          ¬ (vecVals q₁).Perm (vecVals q₂)) ∧

      (∀ a b c d : Nat,
        inRange4 nums a b c d → pairwiseDistinct4 a b c d →
          idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d = target.val →
            ∃! i : Nat, permAt r i (quadOfIdx nums a b c d))) := by
  sorry

/-- For every element q of the returned result r, len(q) = 4.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, q.val.length = 4 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, q.val.length = 4) := by
  sorry

/-- For every element q of the returned result r and for every k with 0 <= k < 4, -1000000000 <= q[k] <= 1000000000.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, ∀ k : Nat, k < 4 →
        -1000000000 ≤ quadVal q k ∧ quadVal q k ≤ 1000000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, ∀ k : Nat, k < 4 →
        -1000000000 ≤ quadVal q k ∧ quadVal q k ≤ 1000000000) := by
  sorry

/-- For every element q of the returned result r, q[0] + q[1] + q[2] + q[3] = target.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, quadSumIs q target := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, quadSumIs q target) := by
  sorry

/-- For every element q of the returned result r, there exist four pairwise distinct indices a,b,c,d with 0 <= a,b,c,d < len(nums) such that the sequence (q[0],q[1],q[2],q[3]) is a permutation of (nums[a],nums[b],nums[c],nums[d]).
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, ∃ a b c d : Nat,
        inRange4 nums a b c d ∧ pairwiseDistinct4 a b c d ∧
          (vecVals q).Perm (quadOfIdx nums a b c d) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ q ∈ r.val, ∃ a b c d : Nat,
        inRange4 nums a b c d ∧ pairwiseDistinct4 a b c d ∧
          (vecVals q).Perm (quadOfIdx nums a b c d)) := by
  sorry

/-- For every two distinct indices i and j with 0 <= i < len(r) and 0 <= j < len(r) and i != j, the sequence (r[i][0],r[i][1],r[i][2],r[i][3]) is not a permutation of (r[j][0],r[j][1],r[j][2],r[j][3]).
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ (i j : Nat), i < r.val.length → j < r.val.length → i ≠ j →
        ∀ q₁ q₂, r.val[i]? = some q₁ → r.val[j]? = some q₂ →
          ¬ (vecVals q₁).Perm (vecVals q₂) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ (i j : Nat), i < r.val.length → j < r.val.length → i ≠ j →
        ∀ q₁ q₂, r.val[i]? = some q₁ → r.val[j]? = some q₂ →
          ¬ (vecVals q₁).Perm (vecVals q₂)) := by
  sorry

/-- For every four pairwise distinct indices a,b,c,d with 0 <= a,b,c,d < len(nums) and nums[a] + nums[b] + nums[c] + nums[d] = target, there exists an index i with 0 <= i < len(r) such that the sequence (r[i][0],r[i][1],r[i][2],r[i][3]) is a permutation of (nums[a],nums[b],nums[c],nums[d]).
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ a b c d : Nat,
        inRange4 nums a b c d → pairwiseDistinct4 a b c d →
          idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d = target.val →
            ∃ i : Nat, permAt r i (quadOfIdx nums a b c d) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      ∀ a b c d : Nat,
        inRange4 nums a b c d → pairwiseDistinct4 a b c d →
          idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d = target.val →
            ∃ i : Nat, permAt r i (quadOfIdx nums a b c d)) := by
  sorry

/-- If nums[0] + nums[1] + nums[2] + nums[3] = target, then len(r) = 1 and (r[0][0],r[0][1],r[0][2],r[0][3]) is a permutation of (nums[0],nums[1],nums[2],nums[3]); otherwise len(r) = 0.
  Preconditions: len(nums) = 4; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
    (h_len : nums.val.length = 4)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      (idxVal nums 0 + idxVal nums 1 + idxVal nums 2 + idxVal nums 3 = target.val →
        r.val.length = 1 ∧ permAt r 0 (quadOfIdx nums 0 1 2 3)) ∧
      (idxVal nums 0 + idxVal nums 1 + idxVal nums 2 + idxVal nums 3 ≠ target.val →
        r.val.length = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len : nums.val.length = 4)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      (idxVal nums 0 + idxVal nums 1 + idxVal nums 2 + idxVal nums 3 = target.val →
        r.val.length = 1 ∧ permAt r 0 (quadOfIdx nums 0 1 2 3)) ∧
      (idxVal nums 0 + idxVal nums 1 + idxVal nums 2 + idxVal nums 3 ≠ target.val →
        r.val.length = 0)) := by
  sorry

/-- The returned result r is empty, i.e., len(r) = 0.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000; for every four pairwise distinct indices a,b,c,d with 0 <= a,b,c,d < len(nums), nums[a] + nums[b] + nums[c] + nums[d] != target. -/
theorem spec_9 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000)
    (h_no_quad : ∀ a b c d : Nat,
      inRange4 nums a b c d → pairwiseDistinct4 a b c d →
        idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d ≠ target.val) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧ r.val.length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000)
    (h_no_quad : ∀ a b c d : Nat,
      inRange4 nums a b c d → pairwiseDistinct4 a b c d →
        idxVal nums a + idxVal nums b + idxVal nums c + idxVal nums d ≠ target.val), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧ r.val.length = 0) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r) := by
  sorry

/-- The length of the returned result r is at most the number of 4-element subsets of the index set {0, 1, ..., len(nums)-1}, i.e., len(r) <= len(nums)*(len(nums)-1)*(len(nums)-2)*(len(nums)-3)/24 when len(nums) >= 4, and len(r) = 0 when len(nums) < 4.
  Preconditions: 1 <= len(nums) <= 200; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= target <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      (4 ≤ nums.val.length →
        r.val.length ≤
          nums.val.length * (nums.val.length - 1) * (nums.val.length - 2) *
            (nums.val.length - 3) / 24) ∧
      (nums.val.length < 4 → r.val.length = 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 200)
    (h_elems : ∀ i, i < nums.val.length →
      -1000000000 ≤ idxVal nums i ∧ idxVal nums i ≤ 1000000000)
    (h_target : -1000000000 ≤ target.val ∧ target.val ≤ 1000000000), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FourSum.four_sum nums target = ok r ∧
      (4 ≤ nums.val.length →
        r.val.length ≤
          nums.val.length * (nums.val.length - 1) * (nums.val.length - 2) *
            (nums.val.length - 3) / 24) ∧
      (nums.val.length < 4 → r.val.length = 0)) := by
  sorry

end AegisSpec.FourSum
