import Aegis.NumOfPairs.Code.Funs

/-!
# Specifications of `Aegis.NumOfPairs.num_of_pairs`

LeetCode problem `number-of-pairs-of-strings-with-concatenation-equal-to-target`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open scoped BigOperators

  namespace AegisSpec.NumOfPairs

  def bytesAt (nums : List (alloc.vec.Vec Std.U8)) (i : ℕ) : List Std.U8 :=
    match nums[i]? with
    | some v => v.val
    | none => []

  def byteAt (l : List Std.U8) (k : ℕ) : ℕ :=
    ((l[k]?).map (fun b => b.val)).getD 0

  def ConcatEq (a b t : List Std.U8) : Prop :=
    a.length + b.length = t.length ∧
      (∀ k, k < a.length → a[k]? = t[k]?) ∧
      (∀ k, k < b.length → b[k]? = t[a.length + k]?)

  def Pre (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8) : Prop :=
    2 ≤ nums.val.length ∧
      nums.val.length ≤ 100 ∧
      (∀ i, i < nums.val.length →
        1 ≤ (bytesAt nums.val i).length ∧
          (bytesAt nums.val i).length ≤ 100 ∧
          (∀ k, k < (bytesAt nums.val i).length →
            48 ≤ byteAt (bytesAt nums.val i) k ∧ byteAt (bytesAt nums.val i) k ≤ 57) ∧
          (1 < (bytesAt nums.val i).length → byteAt (bytesAt nums.val i) 0 ≠ 48)) ∧
      2 ≤ target.val.length ∧
      target.val.length ≤ 100 ∧
      (∀ k, k < target.val.length → 48 ≤ byteAt target.val k ∧ byteAt target.val k ≤ 57) ∧
      byteAt target.val 0 ≠ 48

  noncomputable def pairSet (nums : List (alloc.vec.Vec Std.U8)) (target : List Std.U8) :
      Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range nums.length).product (Finset.range nums.length)).filter
      (fun p => p.1 ≠ p.2 ∧ ConcatEq (bytesAt nums p.1) (bytesAt nums p.2) target)

  noncomputable def pairSetSwap (nums : List (alloc.vec.Vec Std.U8)) (target : List Std.U8) :
      Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range nums.length).product (Finset.range nums.length)).filter
      (fun p => p.1 ≠ p.2 ∧ ConcatEq (bytesAt nums p.2) (bytesAt nums p.1) target)

  noncomputable def pairSetAt (nums : List (alloc.vec.Vec Std.U8)) (target : List Std.U8)
      (L : ℕ) : Finset (ℕ × ℕ) := by
    classical
    exact ((Finset.range nums.length).product (Finset.range nums.length)).filter
      (fun p => p.1 ≠ p.2 ∧ (bytesAt nums p.1).length = L ∧
        (bytesAt nums p.2).length = target.length - L ∧
        ConcatEq (bytesAt nums p.1) (bytesAt nums p.2) target)

  def PermutedBy (nums nums' : List (alloc.vec.Vec Std.U8))
      (π : Equiv.Perm (Fin nums.length)) : Prop :=
    nums'.length = nums.length ∧
      ∀ i : Fin nums.length, nums'[i.val]? = some (nums.get (π i))

  /-- Let P be the set of ordered pairs (i,j) of integers such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and the byte-list concatenation nums[i] ++ nums[j] equals target. Here nums[i] ++ nums[j] = target means len(nums[i]) + len(nums[j]) = len(target), for every 0 <= k < len(nums[i]) we have nums[i][k] = target[k], and for every 0 <= k < len(nums[j]) we have nums[j][k] = target[len(nums[i]) + k]. Whenever num_of_pairs(nums, target) returns a result r, r is the number of elements of P, i.e. the number of ordered index pairs (i,j) with i != j whose concatenated digit strings equal target.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_1 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (r : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r) :
      r.val = ((pairSet nums.val target.val).card : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (r : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r), r.val = ((pairSet nums.val target.val).card : ℤ)) := by
    sorry

  /-- num_of_pairs(nums, target) returns a result r; equivalently, the call does not fail, panic, overflow, or access outside the bounds of nums or target.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_2 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) :
      ∃ r : Std.I64, Aegis.NumOfPairs.num_of_pairs nums target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target), ∃ r : Std.I64, Aegis.NumOfPairs.num_of_pairs nums target = ok r) := by
    sorry

  /-- Whenever num_of_pairs(nums, target) returns a result r, r <= len(nums) * (len(nums) - 1).
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_3 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (r : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r) :
      r.val ≤ ((nums.val.length * (nums.val.length - 1) : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (r : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r), r.val ≤ ((nums.val.length * (nums.val.length - 1) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever num_of_pairs(nums, target) returns a result r, r equals the number of ordered pairs (i,j) such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and nums[j] ++ nums[i] = target.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_4 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (r : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r) :
      r.val = ((pairSetSwap nums.val target.val).card : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (r : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r), r.val = ((pairSetSwap nums.val target.val).card : ℤ)) := by
    sorry

  /-- For every array nums' of byte strings and every bijection π from {0, 1, ..., len(nums)-1} to itself such that len(nums') = len(nums) and nums'[i] = nums[π(i)] for every 0 <= i < len(nums), if num_of_pairs(nums, target) returns a result r and num_of_pairs(nums', target) returns a result r', then r = r'.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_5 (nums nums' : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (π : Equiv.Perm (Fin nums.val.length))
      (hperm : PermutedBy nums.val nums'.val π) (r r' : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r)
      (hr' : Aegis.NumOfPairs.num_of_pairs nums' target = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums nums' : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (π : Equiv.Perm (Fin nums.val.length))
        (hperm : PermutedBy nums.val nums'.val π) (r r' : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r)
        (hr' : Aegis.NumOfPairs.num_of_pairs nums' target = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever num_of_pairs(nums, target) returns a result r, r equals the sum, over all integers L with 1 <= L <= len(target) - 1, of the number of ordered pairs (i,j) such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, len(nums[i]) = L, len(nums[j]) = len(target) - L, nums[i][k] = target[k] for every 0 <= k < L, and nums[j][k] = target[L + k] for every 0 <= k < len(target) - L.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_6 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (r : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r) :
      r.val = ((∑ L ∈ Finset.Icc 1 (target.val.length - 1),
        (pairSetAt nums.val target.val L).card : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (r : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r), r.val = ((∑ L ∈ Finset.Icc 1 (target.val.length - 1),
          (pairSetAt nums.val target.val L).card : ℕ) : ℤ)) := by
    sorry

  /-- Whenever num_of_pairs(nums, target) returns a result r, r = 0 if and only if there do not exist integers i and j such that 0 <= i < len(nums), 0 <= j < len(nums), i != j, and the byte-list concatenation nums[i] ++ nums[j] equals target.
    Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] is a byte list with 1 <= len(nums[i]) <= 100 and every byte nums[i][k] for 0 <= k < len(nums[i]) satisfies 48 <= nums[i][k] <= 57; for every i, if len(nums[i]) > 1 then nums[i][0] != 48 (no leading zero); target is a byte list with 2 <= len(target) <= 100 and every byte target[k] for 0 <= k < len(target) satisfies 48 <= target[k] <= 57, and target[0] != 48 (no leading zero, since len(target) >= 2). -/
  theorem spec_7 (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
      (hpre : Pre nums target) (r : Std.I64)
      (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r) :
      (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
        ConcatEq (bytesAt nums.val i) (bytesAt nums.val j) target.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice (alloc.vec.Vec Std.U8)) (target : Slice Std.U8)
        (hpre : Pre nums target) (r : Std.I64)
        (hr : Aegis.NumOfPairs.num_of_pairs nums target = ok r), (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
          ConcatEq (bytesAt nums.val i) (bytesAt nums.val j) target.val)) := by
    sorry

  end AegisSpec.NumOfPairs
