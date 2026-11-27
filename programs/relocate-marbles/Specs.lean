import Aegis.RelocateMarbles.Code.Funs

/-!
# Specifications of `Aegis.RelocateMarbles.relocate_marbles`

LeetCode problem `relocate-marbles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RelocateMarbles

open Aegis.RelocateMarbles

def valsOf (l : List Std.I64) : List ℤ := l.map fun x => x.val

def vals (s : Slice Std.I64) : List ℤ := valsOf s.val

def resVals (v : alloc.vec.Vec Std.I64) : List ℤ := valsOf v.val

def applyMoves : List ℤ → List ℤ → ℤ → ℤ
  | [], _, y => y
  | _ :: _, [], y => y
  | f :: fs, t :: ts, y => applyMoves fs ts (if y = f then t else y)

def final (moveFrom moveTo : Slice Std.I64) (x : ℤ) : ℤ :=
  applyMoves (vals moveFrom) (vals moveTo) x

def finalAfter (moveFrom moveTo : Slice Std.I64) (i : Nat) (x : ℤ) : ℤ :=
  applyMoves ((vals moveFrom).take i) ((vals moveTo).take i) x

def promise (nums moveFrom moveTo : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (hi : i < (vals moveFrom).length),
    ∃ (j : Nat) (hj : j < (vals nums).length),
      finalAfter moveFrom moveTo i (vals nums)[j] = (vals moveFrom)[i]

def distinctCount (l : List ℤ) : Nat := l.dedup.length

def finalPositions (nums moveFrom moveTo : Slice Std.I64) : List ℤ :=
  (vals nums).map (final moveFrom moveTo)

def StrictInc : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => a < b ∧ StrictInc (b :: rest)

def AllSelfMoves (moveFrom moveTo : Slice Std.I64) : Prop :=
  ∀ (i : Nat) (hi : i < (vals moveFrom).length) (hi' : i < (vals moveTo).length),
    (vals moveFrom)[i] = (vals moveTo)[i]

/-- Whenever the function returns a result r, r is exactly the sorted list of occupied final positions. Define final(x) for an initial position x by starting with y = x and, for i = 0, 1, ..., len(moveFrom)-1 in that order, setting y := moveTo[i] if y = moveFrom[i] and leaving y unchanged otherwise; set final(x) to the final y. Then (a) for every k with 0 <= k < len(r), there exists j with 0 <= j < len(nums) and r[k] = final(nums[j]); (b) for every j with 0 <= j < len(nums), there exists k with 0 <= k < len(r) and r[k] = final(nums[j]); and (c) for every k with 0 <= k+1 < len(r), r[k] < r[k+1].
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_1 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    (∀ (k : Nat) (hk : k < (resVals r).length),
      ∃ (j : Nat) (hj : j < (vals nums).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j])) ∧
    (∀ (j : Nat) (hj : j < (vals nums).length),
      ∃ (k : Nat) (hk : k < (resVals r).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j])) ∧
    (∀ (k : Nat) (hk : k + 1 < (resVals r).length), (resVals r)[k] < (resVals r)[k + 1]) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), (∀ (k : Nat) (hk : k < (resVals r).length),
      ∃ (j : Nat) (hj : j < (vals nums).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j])) ∧
    (∀ (j : Nat) (hj : j < (vals nums).length),
      ∃ (k : Nat) (hk : k < (resVals r).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j])) ∧
    (∀ (k : Nat) (hk : k + 1 < (resVals r).length), (resVals r)[k] < (resVals r)[k + 1])) := by
  sorry

/-- Whenever the preconditions hold, the function returns a result r (the call evaluates to Result.ok r); it does not fail, panic, overflow, or go out of bounds.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_2 (nums moveFrom moveTo : Slice I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo) :
    ∃ r : alloc.vec.Vec I64, relocate_marbles nums moveFrom moveTo = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo), ∃ r : alloc.vec.Vec I64, relocate_marbles nums moveFrom moveTo = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k] <= 1000000000.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_3 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    ∀ (k : Nat) (hk : k < (resVals r).length),
      1 ≤ (resVals r)[k] ∧ (resVals r)[k] ≤ 1000000000 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), ∀ (k : Nat) (hk : k < (resVals r).length),
      1 ≤ (resVals r)[k] ∧ (resVals r)[k] ≤ 1000000000) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= the number of distinct values occurring in nums, i.e. len(r) <= |{ nums[j] | 0 <= j < len(nums) }|.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_4 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    (resVals r).length ≤ distinctCount (vals nums) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), (resVals r).length ≤ distinctCount (vals nums)) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_5 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    1 ≤ (resVals r).length := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), 1 ≤ (resVals r).length) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of distinct values in the set { final(nums[j]) | 0 <= j < len(nums) }, where final(x) is obtained by applying the moves in order to a marble initially at x: at step i, replace the current position y by moveTo[i] if y = moveFrom[i], and otherwise leave y unchanged.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_6 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    (resVals r).length = distinctCount (finalPositions nums moveFrom moveTo) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), (resVals r).length = distinctCount (finalPositions nums moveFrom moveTo)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < len(nums), there exists k with 0 <= k < len(r) such that r[k] = final(nums[j]), where final(x) is obtained by applying the moves in order to a marble initially at x: at step i, replace the current position y by moveTo[i] if y = moveFrom[i], and otherwise leave y unchanged.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_7 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    ∀ (j : Nat) (hj : j < (vals nums).length),
      ∃ (k : Nat) (hk : k < (resVals r).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j]) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), ∀ (j : Nat) (hj : j < (vals nums).length),
      ∃ (k : Nat) (hk : k < (resVals r).length),
        (resVals r)[k] = final moveFrom moveTo ((vals nums)[j])) := by
  sorry

/-- Let r be the result returned for nums, moveFrom, moveTo and r' the result returned for nums', moveFrom, moveTo. Whenever both calls return results, if the set of values in nums equals the set of values in nums', then r = r'.
  Preconditions: For nums, moveFrom, moveTo: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds. For nums' the same constraints hold with nums' in place of nums. Also { nums[j] | 0 <= j < len(nums) } = { nums'[j] | 0 <= j < len(nums') }. -/
theorem spec_8 (nums nums' moveFrom moveTo : Slice I64)
    (r r' : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hnum'_pos : 1 ≤ (vals nums').length)
    (hnum'_le : (vals nums').length ≤ 100000)
    (hnum'_bounds : ∀ (j : Nat) (hj : j < (vals nums').length),
      1 ≤ (vals nums')[j] ∧ (vals nums')[j] ≤ 1000000000)
    (hpromise' : promise nums' moveFrom moveTo)
    (hset : ∀ (x : ℤ), x ∈ vals nums ↔ x ∈ vals nums')
    (hres : relocate_marbles nums moveFrom moveTo = ok r)
    (hres' : relocate_marbles nums' moveFrom moveTo = ok r') :
    resVals r = resVals r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' moveFrom moveTo : Slice I64)
    (r r' : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hnum'_pos : 1 ≤ (vals nums').length)
    (hnum'_le : (vals nums').length ≤ 100000)
    (hnum'_bounds : ∀ (j : Nat) (hj : j < (vals nums').length),
      1 ≤ (vals nums')[j] ∧ (vals nums')[j] ≤ 1000000000)
    (hpromise' : promise nums' moveFrom moveTo)
    (hset : ∀ (x : ℤ), x ∈ vals nums ↔ x ∈ vals nums')
    (hres : relocate_marbles nums moveFrom moveTo = ok r)
    (hres' : relocate_marbles nums' moveFrom moveTo = ok r'), resVals r = resVals r') := by
  sorry

/-- For every i with 0 <= i < len(moveFrom) and moveFrom[i] = moveTo[i], let final(x) be the final position of a marble initially at x under the full sequence, and let final'(x) be its final position under the sequence obtained by deleting step i. Then for every initial position x, final(x) = final'(x); consequently the set of occupied final positions, and hence the returned r, is the same for the two sequences.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_9 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    ∀ (i : Nat) (hi : i < (vals moveFrom).length) (hi' : i < (vals moveTo).length)
      (hsame : (vals moveFrom)[i] = (vals moveTo)[i])
      (moveFrom' moveTo' : Slice I64) (r' : alloc.vec.Vec I64)
      (hmf' : vals moveFrom' = (vals moveFrom).eraseIdx i)
      (hmt' : vals moveTo' = (vals moveTo).eraseIdx i)
      (hres' : relocate_marbles nums moveFrom' moveTo' = ok r'),
      (∀ (x : ℤ), final moveFrom moveTo x = final moveFrom' moveTo' x) ∧
        resVals r' = resVals r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), ∀ (i : Nat) (hi : i < (vals moveFrom).length) (hi' : i < (vals moveTo).length)
      (hsame : (vals moveFrom)[i] = (vals moveTo)[i])
      (moveFrom' moveTo' : Slice I64) (r' : alloc.vec.Vec I64)
      (hmf' : vals moveFrom' = (vals moveFrom).eraseIdx i)
      (hmt' : vals moveTo' = (vals moveTo).eraseIdx i)
      (hres' : relocate_marbles nums moveFrom' moveTo' = ok r'),
      (∀ (x : ℤ), final moveFrom moveTo x = final moveFrom' moveTo' x) ∧
        resVals r' = resVals r) := by
  sorry

/-- Whenever the function returns a result r, if all entries of nums are equal to p, then len(r) = 1 and r[0] = final(p), where final(p) is obtained by applying the moves in order to a marble initially at p: at step i, replace the current position y by moveTo[i] if y = moveFrom[i], and otherwise leave y unchanged.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; the problem's promise holds; and there exists p such that nums[j] = p for every j with 0 <= j < len(nums). -/
theorem spec_10 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64) (p : ℤ)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hall : ∀ (j : Nat) (hj : j < (vals nums).length), (vals nums)[j] = p)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    (resVals r).length = 1 ∧ (resVals r).head? = some (final moveFrom moveTo p) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64) (p : ℤ)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hall : ∀ (j : Nat) (hj : j < (vals nums).length), (vals nums)[j] = p)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), (resVals r).length = 1 ∧ (resVals r).head? = some (final moveFrom moveTo p)) := by
  sorry

/-- Whenever the function returns a result r, if every move is a self-move, then r is the strictly increasing list of the distinct values occurring in nums.
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; the problem's promise holds; and for every i with 0 <= i < len(moveFrom), moveFrom[i] = moveTo[i]. -/
theorem spec_11 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hself : AllSelfMoves moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    StrictInc (resVals r) ∧ ∀ (x : ℤ), (x ∈ resVals r ↔ x ∈ vals nums) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hself : AllSelfMoves moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), StrictInc (resVals r) ∧ ∀ (x : ℤ), (x ∈ resVals r ↔ x ∈ vals nums)) := by
  sorry

/-- Whenever the function returns a result r, for every position p with 1 <= p <= 1000000000, if p occurs in nums (there is j with 0 <= j < len(nums) and nums[j] = p) and p is not equal to moveFrom[i] for any i with 0 <= i < len(moveFrom), then p occurs in r (there is k with 0 <= k < len(r) and r[k] = p).
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_12 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    ∀ (p : ℤ) (hp1 : 1 ≤ p) (hp2 : p ≤ 1000000000)
      (hocc : ∃ (j : Nat) (hj : j < (vals nums).length), (vals nums)[j] = p)
      (hnotfrom : ∀ (i : Nat) (hi : i < (vals moveFrom).length), (vals moveFrom)[i] ≠ p),
      ∃ (k : Nat) (hk : k < (resVals r).length), (resVals r)[k] = p := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), ∀ (p : ℤ) (hp1 : 1 ≤ p) (hp2 : p ≤ 1000000000)
      (hocc : ∃ (j : Nat) (hj : j < (vals nums).length), (vals nums)[j] = p)
      (hnotfrom : ∀ (i : Nat) (hi : i < (vals moveFrom).length), (vals moveFrom)[i] ≠ p),
      ∃ (k : Nat) (hk : k < (resVals r).length), (resVals r)[k] = p) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), either there exists j with 0 <= j < len(nums) and r[k] = nums[j], or there exists i with 0 <= i < len(moveFrom) and r[k] = moveTo[i].
  Preconditions: len(nums) >= 1; len(moveFrom) >= 1; len(moveFrom) = len(moveTo); len(nums) <= 100000; len(moveFrom) <= 100000; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 1000000000; for every i with 0 <= i < len(moveFrom), 1 <= moveFrom[i] <= 1000000000 and 1 <= moveTo[i] <= 1000000000; and the problem's promise holds: just before each step i with 0 <= i < len(moveFrom), at least one marble is at moveFrom[i]. -/
theorem spec_13 (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r) :
    ∀ (k : Nat) (hk : k < (resVals r).length),
      (∃ (j : Nat) (hj : j < (vals nums).length),
        (resVals r)[k] = (vals nums)[j]) ∨
      (∃ (i : Nat) (hi : i < (vals moveTo).length),
        (resVals r)[k] = (vals moveTo)[i]) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums moveFrom moveTo : Slice I64) (r : alloc.vec.Vec I64)
    (hnum_pos : 1 ≤ (vals nums).length)
    (hmf_pos : 1 ≤ (vals moveFrom).length)
    (hlen : (vals moveFrom).length = (vals moveTo).length)
    (hnum_le : (vals nums).length ≤ 100000)
    (hmf_le : (vals moveFrom).length ≤ 100000)
    (hnum_bounds : ∀ (j : Nat) (hj : j < (vals nums).length),
      1 ≤ (vals nums)[j] ∧ (vals nums)[j] ≤ 1000000000)
    (hmf_bounds : ∀ (i : Nat) (hi : i < (vals moveFrom).length),
      1 ≤ (vals moveFrom)[i] ∧ (vals moveFrom)[i] ≤ 1000000000)
    (hmt_bounds : ∀ (i : Nat) (hi : i < (vals moveTo).length),
      1 ≤ (vals moveTo)[i] ∧ (vals moveTo)[i] ≤ 1000000000)
    (hpromise : promise nums moveFrom moveTo)
    (hres : relocate_marbles nums moveFrom moveTo = ok r), ∀ (k : Nat) (hk : k < (resVals r).length),
      (∃ (j : Nat) (hj : j < (vals nums).length),
        (resVals r)[k] = (vals nums)[j]) ∨
      (∃ (i : Nat) (hi : i < (vals moveTo).length),
        (resVals r)[k] = (vals moveTo)[i])) := by
  sorry

end AegisSpec.RelocateMarbles
