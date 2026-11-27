import Aegis.FindLonely.Code.Funs

/-!
# Specifications of `Aegis.FindLonely.find_lonely`

LeetCode problem `find-all-lonely-numbers-in-the-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindLonely

  namespace AegisSpec.FindLonely

  def nth (l : List Std.I64) (i : Nat) : Int :=
    match l[i]? with
    | some x => x.val
    | none => 0

  def occ (l : List Std.I64) (v : Int) : Nat :=
    (l.filter (fun x => x.val = v)).length

  abbrev occurs (l : List Std.I64) (v : Int) : Prop :=
    v ∈ l.map (fun x => x.val)

  abbrev lonely (l : List Std.I64) (v : Int) : Prop :=
    occ l v = 1 ∧ ¬ occurs l (v - 1) ∧ ¬ occurs l (v + 1)

  /-- Whenever the function returns a result r, for every integer v, if occ(v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v, then the number of indices i with 0 <= i < len(r) and r[i] = v is 1 when occ(v) = 1 and there is no j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1, and is 0 otherwise.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_1
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (v : Int) :
      occ r.val v = if lonely nums.val v then 1 else 0 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (v : Int), occ r.val v = if lonely nums.val v then 1 else 0) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_2
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000) :
      ∃ r : alloc.vec.Vec Std.I64, find_lonely nums = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64, find_lonely nums = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), if v = r[i] and occ(v) is the number of indices j with 0 <= j < len(nums) and nums[j] = v, then occ(v) = 1 and there is no j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_3
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (i : Nat)
      (h_i : i < r.val.length)
      (v : Int)
      (h_v : v = nth r.val i) :
      lonely nums.val v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (i : Nat)
        (h_i : i < r.val.length)
        (v : Int)
        (h_v : v = nth r.val i), lonely nums.val v) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(nums), if v = nums[j], occ(v) is the number of indices k with 0 <= k < len(nums) and nums[k] = v, and occ(v) = 1 and there is no k with 0 <= k < len(nums) such that nums[k] = v - 1 or nums[k] = v + 1, then there exists i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_4
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (j : Nat)
      (h_j : j < nums.val.length)
      (v : Int)
      (h_v : v = nth nums.val j)
      (h_occ : occ nums.val v = 1)
      (h_nb : ¬ occurs nums.val (v - 1) ∧ ¬ occurs nums.val (v + 1)) :
      ∃ i, i < r.val.length ∧ nth r.val i = v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (j : Nat)
        (h_j : j < nums.val.length)
        (v : Int)
        (h_v : v = nth nums.val j)
        (h_occ : occ nums.val v = 1)
        (h_nb : ¬ occurs nums.val (v - 1) ∧ ¬ occurs nums.val (v + 1)), ∃ i, i < r.val.length ∧ nth r.val i = v) := by
    sorry

  /-- Whenever the function returns a result r, for every i and k with 0 <= i < k < len(r), r[i] != r[k].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_5
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (i k : Nat)
      (h_ik : i < k)
      (h_k : k < r.val.length) :
      nth r.val i ≠ nth r.val k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (i k : Nat)
        (h_ik : i < k)
        (h_k : k < r.val.length), nth r.val i ≠ nth r.val k) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of integers v such that the number of indices j with 0 <= j < len(nums) and nums[j] = v is 1 and there is no j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_6
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r) :
      r.val.length = (Set.ncard {v : Int | lonely nums.val v}) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r), r.val.length = (Set.ncard {v : Int | lonely nums.val v})) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(r), there exists j with 0 <= j < len(nums) such that r[i] = nums[j].
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_7
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (i : Nat)
      (h_i : i < r.val.length) :
      ∃ j, j < nums.val.length ∧ nth r.val i = nth nums.val j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (i : Nat)
        (h_i : i < r.val.length), ∃ j, j < nums.val.length ∧ nth r.val i = nth nums.val j) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, if the number of indices j with 0 <= j < len(nums) and nums[j] = v is at least 2, then there is no i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_8
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (v : Int)
      (h_occ : 2 ≤ occ nums.val v) :
      ¬ ∃ i, i < r.val.length ∧ nth r.val i = v := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (v : Int)
        (h_occ : 2 ≤ occ nums.val v), ¬ ∃ i, i < r.val.length ∧ nth r.val i = v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, if there exists j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1, then there is no i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_9
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (v : Int)
      (h_nb : occurs nums.val (v - 1) ∨ occurs nums.val (v + 1)) :
      ¬ ∃ i, i < r.val.length ∧ nth r.val i = v := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (v : Int)
        (h_nb : occurs nums.val (v - 1) ∨ occurs nums.val (v + 1)), ¬ ∃ i, i < r.val.length ∧ nth r.val i = v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, if the number of indices j with 0 <= j < len(nums) and nums[j] = v is 1 and there is no j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1, then there is exactly one i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_10
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (v : Int)
      (h_lonely : lonely nums.val v) :
      ∃! i, i < r.val.length ∧ nth r.val i = v := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (v : Int)
        (h_lonely : lonely nums.val v), ∃! i, i < r.val.length ∧ nth r.val i = v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, if it is not the case that (the number of indices j with 0 <= j < len(nums) and nums[j] = v is 1 and there is no j with 0 <= j < len(nums) such that nums[j] = v - 1 or nums[j] = v + 1), then there is no i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000. -/
  theorem spec_11
      (nums : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (r : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (v : Int)
      (h_not_lonely : ¬ lonely nums.val v) :
      ¬ ∃ i, i < r.val.length ∧ nth r.val i = v := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (r : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (v : Int)
        (h_not_lonely : ¬ lonely nums.val v), ¬ ∃ i, i < r.val.length ∧ nth r.val i = v) := by
    sorry

  /-- For any two inputs nums and nums' satisfying the preconditions, if for every integer v, the number of indices j with 0 <= j < len(nums) and nums[j] = v equals the number of indices j with 0 <= j < len(nums') and nums'[j] = v, then whenever the function returns r on nums and r' on nums', for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(r') and r'[i] = v.
    Preconditions: len(nums) >= 1 and len(nums) <= 100000, for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000, and len(nums') >= 1 and len(nums') <= 100000, for every i with 0 <= i < len(nums'), 0 <= nums'[i] <= 1000000. -/
  theorem spec_12
      (nums nums' : Slice Std.I64)
      (h_len_ge : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
      (h_len_ge' : 1 ≤ nums'.val.length)
      (h_len_le' : nums'.val.length ≤ 100000)
      (h_bounds' : ∀ i, i < nums'.val.length → 0 ≤ nth nums'.val i ∧ nth nums'.val i ≤ 1000000)
      (h_occ : ∀ v : Int, occ nums.val v = occ nums'.val v)
      (r r' : alloc.vec.Vec Std.I64)
      (h_ret : find_lonely nums = Result.ok r)
      (h_ret' : find_lonely nums' = Result.ok r')
      (v : Int) :
      occ r.val v = occ r'.val v := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_len_ge : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bounds : ∀ i, i < nums.val.length → 0 ≤ nth nums.val i ∧ nth nums.val i ≤ 1000000)
        (h_len_ge' : 1 ≤ nums'.val.length)
        (h_len_le' : nums'.val.length ≤ 100000)
        (h_bounds' : ∀ i, i < nums'.val.length → 0 ≤ nth nums'.val i ∧ nth nums'.val i ≤ 1000000)
        (h_occ : ∀ v : Int, occ nums.val v = occ nums'.val v)
        (r r' : alloc.vec.Vec Std.I64)
        (h_ret : find_lonely nums = Result.ok r)
        (h_ret' : find_lonely nums' = Result.ok r')
        (v : Int), occ r.val v = occ r'.val v) := by
    sorry

  end AegisSpec.FindLonely
