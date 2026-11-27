import Aegis.TargetIndices.Code.Funs

/-!
# Specifications of `Aegis.TargetIndices.target_indices`

LeetCode problem `find-target-indices-after-sorting-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TargetIndices

  open Aeneas Aeneas.Std Result

  def countLt (ns : List Std.I64) (t : Std.I64) : Nat :=
    ns.countP (fun x => decide (x.val < t.val))

  def countEq (ns : List Std.I64) (t : Std.I64) : Nat :=
    ns.countP (fun x => decide (x.val = t.val))

  def countVal (ns : List Std.I64) (v : Int) : Nat :=
    ns.countP (fun x => decide (x.val = v))

  def sortedUp (ns : List Std.I64) : List Std.I64 :=
    ns.insertionSort (fun a b => a.val ≤ b.val)

  def valAt (ns : List Std.I64) (i : Nat) : Option Int :=
    ns[i]?.map (fun x => x.val)

  /-- Let L = the number of indices j with 0 <= j < len(nums) and nums[j] < target, and let E = the number of indices j with 0 <= j < len(nums) and nums[j] = target. The function returns a result r such that len(r) = E and, for every k with 0 <= k < len(r), r[k] = L + k. Equivalently, r is the list [L, L+1, ..., L+E-1] (the empty list when E = 0).
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_1
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r ∧
        r.val.length = countEq nums.val target ∧
        ∀ (k : Nat) (hk : k < r.val.length),
          (r.val[k]).val = (countLt nums.val target : Int) + (k : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r ∧
          r.val.length = countEq nums.val target ∧
          ∀ (k : Nat) (hk : k < r.val.length),
            (r.val[k]).val = (countLt nums.val target : Int) + (k : Int)) := by
    sorry

  /-- Let E = the number of indices j with 0 <= j < len(nums) and nums[j] = target. Whenever the function returns a result r, len(r) = E.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_2
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        r.val.length = countEq nums.val target := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          r.val.length = countEq nums.val target) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k and k+1 < len(r), r[k+1] = r[k] + 1.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_3
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        ∀ (k : Nat) (hk : k + 1 < r.val.length), (r.val[k + 1]).val = (r.val[k]).val + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          ∀ (k : Nat) (hk : k + 1 < r.val.length), (r.val[k + 1]).val = (r.val[k]).val + 1) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 0 <= r[k] < len(nums).
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_4
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        ∀ (k : Nat) (hk : k < r.val.length),
          0 ≤ (r.val[k]).val ∧ (r.val[k]).val < (nums.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          ∀ (k : Nat) (hk : k < r.val.length),
            0 ≤ (r.val[k]).val ∧ (r.val[k]).val < (nums.val.length : Int)) := by
    sorry

  /-- Let E = the number of indices j with 0 <= j < len(nums) and nums[j] = target. Whenever the function returns a result r, len(r) = 0 if and only if E = 0.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_5
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        (r.val.length = 0 ↔ countEq nums.val target = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          (r.val.length = 0 ↔ countEq nums.val target = 0)) := by
    sorry

  /-- Let L = the number of indices j with 0 <= j < len(nums) and nums[j] < target, and let E = the number of indices j with 0 <= j < len(nums) and nums[j] = target. Whenever the function returns a result r, if E > 0 then len(r) > 0 and r[0] = L.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_6
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        countEq nums.val target > 0 →
        r.val.length > 0 ∧ valAt r.val 0 = some (countLt nums.val target : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          countEq nums.val target > 0 →
          r.val.length > 0 ∧ valAt r.val 0 = some (countLt nums.val target : Int)) := by
    sorry

  /-- Let L = the number of indices j with 0 <= j < len(nums) and nums[j] < target, and let E = the number of indices j with 0 <= j < len(nums) and nums[j] = target. Whenever the function returns a result r, if E > 0 then len(r) > 0 and r[len(r)-1] = L + E - 1.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_7
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        countEq nums.val target > 0 →
        r.val.length > 0 ∧
          valAt r.val (r.val.length - 1) =
            some ((countLt nums.val target : Int) + (countEq nums.val target : Int) - 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          countEq nums.val target > 0 →
          r.val.length > 0 ∧
            valAt r.val (r.val.length - 1) =
              some ((countLt nums.val target : Int) + (countEq nums.val target : Int) - 1)) := by
    sorry

  /-- Let sorted(nums) be the unique non-decreasing permutation of nums. Whenever the function returns a result r, for every k with 0 <= k < len(r), sorted(nums)[r[k]] = target.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_8
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        ∀ (k : Nat) (hk : k < r.val.length),
          valAt (sortedUp nums.val) ((r.val[k]).val).toNat = some target.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          ∀ (k : Nat) (hk : k < r.val.length),
            valAt (sortedUp nums.val) ((r.val[k]).val).toNat = some target.val) := by
    sorry

  /-- Let sorted(nums) be the unique non-decreasing permutation of nums. Whenever the function returns a result r, for every p with 0 <= p < len(nums), if sorted(nums)[p] = target then there exists k with 0 <= k < len(r) and r[k] = p.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_9
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∀ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r →
        ∀ (p : Nat) (hp : p < nums.val.length),
          valAt (sortedUp nums.val) p = some target.val →
          ∃ (k : Nat) (hk : k < r.val.length), (r.val[k]).val = (p : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r →
          ∀ (p : Nat) (hp : p < nums.val.length),
            valAt (sortedUp nums.val) p = some target.val →
            ∃ (k : Nat) (hk : k < r.val.length), (r.val[k]).val = (p : Int)) := by
    sorry

  /-- For any array nums' with len(nums') = len(nums) and 1 <= nums'[j] <= 100 for every j with 0 <= j < len(nums), if for every such j we have (nums'[j] < target if and only if nums[j] < target) and (nums'[j] = target if and only if nums[j] = target), then whenever the function returns results r and r' for (nums,target) and (nums',target) respectively, r = r'.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_10
      (nums nums' : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100)
      (hlen' : nums'.val.length = nums.val.length)
      (hnums' : ∀ (j : Nat) (hj : j < nums'.val.length),
        1 ≤ (nums'.val[j]).val ∧ (nums'.val[j]).val ≤ 100)
      (hlt : ∀ (j : Nat) (hj' : j < nums'.val.length) (hj : j < nums.val.length),
        ((nums'.val[j]).val < target.val ↔ (nums.val[j]).val < target.val))
      (heq : ∀ (j : Nat) (hj' : j < nums'.val.length) (hj : j < nums.val.length),
        ((nums'.val[j]).val = target.val ↔ (nums.val[j]).val = target.val)) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.TargetIndices.target_indices nums target = ok r →
        Aegis.TargetIndices.target_indices nums' target = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100)
        (hlen' : nums'.val.length = nums.val.length)
        (hnums' : ∀ (j : Nat) (hj : j < nums'.val.length),
          1 ≤ (nums'.val[j]).val ∧ (nums'.val[j]).val ≤ 100)
        (hlt : ∀ (j : Nat) (hj' : j < nums'.val.length) (hj : j < nums.val.length),
          ((nums'.val[j]).val < target.val ↔ (nums.val[j]).val < target.val))
        (heq : ∀ (j : Nat) (hj' : j < nums'.val.length) (hj : j < nums.val.length),
          ((nums'.val[j]).val = target.val ↔ (nums.val[j]).val = target.val)), ∀ (r r' : alloc.vec.Vec Std.I64),
          Aegis.TargetIndices.target_indices nums target = ok r →
          Aegis.TargetIndices.target_indices nums' target = ok r' → r = r') := by
    sorry

  /-- For any array nums' that is a permutation of nums (same length and, for every integer v, v occurs in nums' as many times as in nums), whenever the function returns results r and r' for (nums,target) and (nums',target) respectively, r = r'.
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_11
      (nums nums' : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100)
      (hlen' : nums'.val.length = nums.val.length)
      (hperm : ∀ v : Int, countVal nums'.val v = countVal nums.val v) :
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.TargetIndices.target_indices nums target = ok r →
        Aegis.TargetIndices.target_indices nums' target = ok r' → r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100)
        (hlen' : nums'.val.length = nums.val.length)
        (hperm : ∀ v : Int, countVal nums'.val v = countVal nums.val v), ∀ (r r' : alloc.vec.Vec Std.I64),
          Aegis.TargetIndices.target_indices nums target = ok r →
          Aegis.TargetIndices.target_indices nums' target = ok r' → r = r') := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: 1 <= len(nums) <= 100; for every j with 0 <= j < len(nums), 1 <= nums[j] <= 100; 1 <= target <= 100. -/
  theorem spec_12
      (nums : Slice Std.I64) (target : Std.I64)
      (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
      (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
        1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
      (htarget : 1 ≤ target.val ∧ target.val ≤ 100) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.TargetIndices.target_indices nums target = ok r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hnelo : 1 ≤ nums.val.length) (hnehi : nums.val.length ≤ 100)
        (hnums : ∀ (j : Nat) (hj : j < nums.val.length),
          1 ≤ (nums.val[j]).val ∧ (nums.val[j]).val ≤ 100)
        (htarget : 1 ≤ target.val ∧ target.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.TargetIndices.target_indices nums target = ok r) := by
    sorry

  end AegisSpec.TargetIndices
