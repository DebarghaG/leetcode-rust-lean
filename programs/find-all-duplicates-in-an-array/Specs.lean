import Aegis.FindDuplicates.Code.Funs

/-!
# Specifications of `Aegis.FindDuplicates.find_duplicates`

LeetCode problem `find-all-duplicates-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindDuplicates

  def countOcc (l : List Std.I64) (v : Int) : Nat :=
    l.countP (fun x => x.val = v)

  def duplicateCount (l : List Std.I64) : Nat :=
    ((List.range l.length).map (fun k => (k : Int) + 1)).countP (fun v => countOcc l v = 2)

  /-- Whenever the function returns a result r, for every integer v, the number of indices j with 0 <= j < len(r) and r[j] = v is 1 if 1 <= v <= n and the number of indices i with 0 <= i < n and nums[i] = v equals 2, and is 0 otherwise.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_1 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ v : Int,
        countOcc r.val v =
          (if 1 ≤ v ∧ v ≤ (nums.val.length : Int) ∧ countOcc nums.val v = 2 then 1 else 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ v : Int,
          countOcc r.val v =
            (if 1 ≤ v ∧ v ≤ (nums.val.length : Int) ∧ countOcc nums.val v = 2 then 1 else 0)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail or panic.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.FindDuplicates.find_duplicates nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2), ∃ r : alloc.vec.Vec Std.I64, Aegis.FindDuplicates.find_duplicates nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), 1 <= r[j] <= n.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_3 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ j : Fin r.val.length,
        1 ≤ (r.val.get j).val ∧ (r.val.get j).val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ j : Fin r.val.length,
          1 ≤ (r.val.get j).val ∧ (r.val.get j).val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), the value r[j] occurs exactly twice in nums, i.e. the number of indices i with 0 <= i < n and nums[i] = r[j] equals 2.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_4 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ j : Fin r.val.length, countOcc nums.val (r.val.get j).val = 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ j : Fin r.val.length, countOcc nums.val (r.val.get j).val = 2) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v with 1 <= v <= n, if v occurs exactly twice in nums, then there exists an index j with 0 <= j < len(r) and r[j] = v.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_5 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v = 2 →
        ∃ j : Fin r.val.length, (r.val.get j).val = v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v = 2 →
          ∃ j : Fin r.val.length, (r.val.get j).val = v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices j with 0 <= j < len(r) and r[j] = v is at most 1.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_6 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ v : Int, countOcc r.val v ≤ 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ v : Int, countOcc r.val v ≤ 1) := by
    sorry

  /-- Whenever the function returns a result r, len(r) equals the number of integers v with 1 <= v <= n such that the number of indices i with 0 <= i < n and nums[i] = v equals 2.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_7 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      r.val.length = duplicateCount nums.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), r.val.length = duplicateCount nums.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v with 1 <= v <= n, there exists an index j with 0 <= j < len(r) and r[j] = v if and only if the number of indices i with 0 <= i < n and nums[i] = v equals 2.
    Preconditions: Let n = len(nums). The slice nums satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= n; and for every integer v with 1 <= v <= n, the number of indices i with 0 <= i < n and nums[i] = v is at most 2. -/
  theorem spec_8 (nums : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      {r : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r) :
      ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) →
        ((∃ j : Fin r.val.length, (r.val.get j).val = v) ↔ countOcc nums.val v = 2) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        {r : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r), ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) →
          ((∃ j : Fin r.val.length, (r.val.get j).val = v) ↔ countOcc nums.val v = 2)) := by
    sorry

  /-- Whenever find_duplicates(nums) returns r and find_duplicates(nums') returns r', for every integer v, the number of indices j with 0 <= j < len(r) and r[j] = v equals the number of indices j' with 0 <= j' < len(r') and r'[j'] = v.
    Preconditions: Let n = len(nums) and n' = len(nums'). Both nums and nums' satisfy their input constraints: 1 <= n <= 100000, 1 <= n' <= 100000, all entries of nums lie in [1,n], all entries of nums' lie in [1,n'], and every value occurs at most twice in each slice. Additionally, for every integer v, the number of indices i with 0 <= i < n and nums[i] = v equals the number of indices i' with 0 <= i' < n' and nums'[i'] = v (so nums' is a permutation of nums). -/
  theorem spec_9 (nums nums' : Slice Std.I64)
      (h_pos : 1 ≤ nums.val.length)
      (h_len : nums.val.length ≤ 100000)
      (h_range : ∀ i : Fin nums.val.length,
        1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
      (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
      (h_pos' : 1 ≤ nums'.val.length)
      (h_len' : nums'.val.length ≤ 100000)
      (h_range' : ∀ i : Fin nums'.val.length,
        1 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ (nums'.val.length : Int))
      (h_dup' : ∀ v : Int, 1 ≤ v → v ≤ (nums'.val.length : Int) → countOcc nums'.val v ≤ 2)
      (h_perm : ∀ v : Int, countOcc nums'.val v = countOcc nums.val v)
      {r r' : alloc.vec.Vec Std.I64}
      (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r)
      (h_r' : Aegis.FindDuplicates.find_duplicates nums' = ok r') :
      ∀ v : Int, countOcc r'.val v = countOcc r.val v := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (h_pos : 1 ≤ nums.val.length)
        (h_len : nums.val.length ≤ 100000)
        (h_range : ∀ i : Fin nums.val.length,
          1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ (nums.val.length : Int))
        (h_dup : ∀ v : Int, 1 ≤ v → v ≤ (nums.val.length : Int) → countOcc nums.val v ≤ 2)
        (h_pos' : 1 ≤ nums'.val.length)
        (h_len' : nums'.val.length ≤ 100000)
        (h_range' : ∀ i : Fin nums'.val.length,
          1 ≤ (nums'.val.get i).val ∧ (nums'.val.get i).val ≤ (nums'.val.length : Int))
        (h_dup' : ∀ v : Int, 1 ≤ v → v ≤ (nums'.val.length : Int) → countOcc nums'.val v ≤ 2)
        (h_perm : ∀ v : Int, countOcc nums'.val v = countOcc nums.val v)
        {r r' : alloc.vec.Vec Std.I64}
        (h_r : Aegis.FindDuplicates.find_duplicates nums = ok r)
        (h_r' : Aegis.FindDuplicates.find_duplicates nums' = ok r'), ∀ v : Int, countOcc r'.val v = countOcc r.val v) := by
    sorry

  end AegisSpec.FindDuplicates
