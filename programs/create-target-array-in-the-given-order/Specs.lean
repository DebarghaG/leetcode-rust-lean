import Aegis.CreateTargetArray.Code.Funs

/-!
# Specifications of `Aegis.CreateTargetArray.create_target_array`

LeetCode problem `create-target-array-in-the-given-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CreateTargetArray

  open Aegis.CreateTargetArray (create_target_array)

  def insertAt (l : List Std.I64) (p : Nat) (v : Std.I64) : List Std.I64 :=
    l.take p ++ v :: l.drop p

  def insertNatAt (l : List Nat) (p : Nat) (x : Nat) : List Nat :=
    l.take p ++ x :: l.drop p

  def posAt (index : Slice Std.I64) (i : Nat) : Nat :=
    match index.val[i]? with
    | none => 0
    | some p => if p.val < 0 then i else min p.val.toNat i

  def positions (index : Slice Std.I64) : List Nat :=
    (List.range index.val.length).map (posAt index)

  def steps (nums index : Slice Std.I64) : List (Std.I64 × Nat) :=
    nums.val.zip (positions index)

  def stepArrays (s : List (Std.I64 × Nat)) : Nat → List Std.I64
    | 0 => []
    | k + 1 =>
      match s[k]? with
      | none => stepArrays s k
      | some q => insertAt (stepArrays s k) q.2 q.1

  def targetAfter (nums index : Slice Std.I64) : List Std.I64 :=
    stepArrays (steps nums index) nums.val.length

  def stepOrder (ps : List Nat) : List Nat :=
    (List.range ps.length).foldl (fun order i => insertNatAt order (ps[i]?.getD 0) i) []

  def finalPos (index : Slice Std.I64) (i : Nat) : Nat :=
    (stepOrder (positions index)).idxOf i

  def minNums (nums : Slice Std.I64) : Int :=
    match nums.val.map (fun v => v.val) with
    | [] => 0
    | v :: vs => vs.foldl min v

  def maxNums (nums : Slice Std.I64) : Int :=
    match nums.val.map (fun v => v.val) with
    | [] => 0
    | v :: vs => vs.foldl max v

  def ValidInputCore (nums index : Slice Std.I64) : Prop :=
    index.val.length = nums.val.length ∧
    (∀ v : Std.I64, v ∈ nums.val → 0 ≤ v.val ∧ v.val ≤ 100) ∧
    (∀ (i : Nat) (h : i < index.val.length),
      0 ≤ (index.val[i]'h).val ∧ (index.val[i]'h).val ≤ (i : Int))

  def ValidInput (nums index : Slice Std.I64) : Prop :=
    ValidInputCore nums index ∧ 1 ≤ nums.val.length ∧ nums.val.length ≤ 100

  /-- Define sequences t_0, t_1, ..., t_n of 64-bit integers by t_0 = [] (the empty sequence) and, for each i with 0 <= i < n, t_{i+1} is the sequence of length len(t_i)+1 obtained from t_i by inserting nums[i] at position index[i]: for 0 <= k < index[i], t_{i+1}[k] = t_i[k]; t_{i+1}[index[i]] = nums[i]; and for index[i] < k <= len(t_i), t_{i+1}[k] = t_i[k-1]. The function returns a result r with len(r) = n and r[k] = t_n[k] for every 0 <= k < n.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_1 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        r.val.length = nums.val.length ∧
        r.val = stepArrays (steps nums index) nums.val.length := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          r.val.length = nums.val.length ∧
          r.val = stepArrays (steps nums index) nums.val.length) := by
    sorry

  /-- The function returns a result r with len(r) = len(nums).
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_2 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧ r.val.length = nums.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧ r.val.length = nums.val.length) := by
    sorry

  /-- The function returns a result r such that for every 64-bit integer v, the number of indices k with 0 <= k < len(r) and r[k] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_3 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ v : Int,
          (r.val.filter (fun x => x.val = v)).length =
            (nums.val.filter (fun x => x.val = v)).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ v : Int,
            (r.val.filter (fun x => x.val = v)).length =
              (nums.val.filter (fun x => x.val = v)).length) := by
    sorry

  /-- The function returns a result r (it does not fail) on every input satisfying the preconditions.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_4 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64, create_target_array nums index = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64, create_target_array nums index = ok r) := by
    sorry

  /-- The function returns a result r with r[index[n-1]] = nums[n-1].
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_5 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        r.val[posAt index (nums.val.length - 1)]? = nums.val.getLast? := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          r.val[posAt index (nums.val.length - 1)]? = nums.val.getLast?) := by
    sorry

  /-- Let m be the largest integer i with 0 <= i < n and index[i] = 0. (Such m exists because index[0] = 0 follows from 0 <= index[0] <= 0.) The function returns a result r with r[0] = nums[m].
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_6 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ m : Nat,
          m < nums.val.length →
          posAt index m = 0 →
          (∀ j : Nat, m < j → j < nums.val.length → posAt index j ≠ 0) →
          r.val[0]? = nums.val[m]? := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ m : Nat,
            m < nums.val.length →
            posAt index m = 0 →
            (∀ j : Nat, m < j → j < nums.val.length → posAt index j ≠ 0) →
            r.val[0]? = nums.val[m]?) := by
    sorry

  /-- The function returns a result r such that for every i, j with 0 <= i < j < n and index[i] = index[j], if a is the final position in r of the element inserted at step i and b is the final position in r of the element inserted at step j (elements distinguished by insertion step even if their values coincide), then b < a.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_7 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ i j : Nat,
          i < j → j < nums.val.length → posAt index i = posAt index j →
          finalPos index j < finalPos index i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ i j : Nat,
            i < j → j < nums.val.length → posAt index i = posAt index j →
            finalPos index j < finalPos index i) := by
    sorry

  /-- The function returns a result r such that for every i, j with 0 <= i < j < n and index[i] > index[j], if a is the final position in r of the element inserted at step i and b is the final position in r of the element inserted at step j (elements distinguished by insertion step even if their values coincide), then b < a.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_8 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ i j : Nat,
          i < j → j < nums.val.length → posAt index j < posAt index i →
          finalPos index j < finalPos index i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ i j : Nat,
            i < j → j < nums.val.length → posAt index j < posAt index i →
            finalPos index j < finalPos index i) := by
    sorry

  /-- If n = 1, the function returns a result r with len(r) = 1 and r[0] = nums[0].
    Preconditions: Let n = len(nums). Then len(index) = n, n = 1, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_9 (nums index : Slice Std.I64) (h : ValidInputCore nums index)
      (hn : nums.val.length = 1) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        r.val.length = 1 ∧ r.val[0]? = nums.val[0]? := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInputCore nums index)
        (hn : nums.val.length = 1), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          r.val.length = 1 ∧ r.val[0]? = nums.val[0]?) := by
    sorry

  /-- If index[i] = 0 for every i with 0 <= i < n, the function returns a result r with len(r) = n and r[k] = nums[n-1-k] for every 0 <= k < n.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i, and in addition index[i] = 0 for every i with 0 <= i < n. -/
  theorem spec_10 (nums index : Slice Std.I64) (h : ValidInput nums index)
      (hzero : ∀ j : Nat, j < nums.val.length → posAt index j = 0) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        r.val.length = nums.val.length ∧
        ∀ k : Nat,
          k < nums.val.length →
          r.val[k]? = nums.val[nums.val.length - 1 - k]? := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index)
        (hzero : ∀ j : Nat, j < nums.val.length → posAt index j = 0), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          r.val.length = nums.val.length ∧
          ∀ k : Nat,
            k < nums.val.length →
            r.val[k]? = nums.val[nums.val.length - 1 - k]?) := by
    sorry

  /-- If index[i] = i for every i with 0 <= i < n, the function returns a result r with r[k] = nums[k] for every 0 <= k < n.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i, and in addition index[i] = i for every i with 0 <= i < n. -/
  theorem spec_11 (nums index : Slice Std.I64) (h : ValidInput nums index)
      (hident : ∀ j : Nat, j < nums.val.length → posAt index j = j) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        r.val.length = nums.val.length ∧
        ∀ k : Nat, k < nums.val.length → r.val[k]? = nums.val[k]? := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index)
        (hident : ∀ j : Nat, j < nums.val.length → posAt index j = j), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          r.val.length = nums.val.length ∧
          ∀ k : Nat, k < nums.val.length → r.val[k]? = nums.val[k]?) := by
    sorry

  /-- The function returns a result r such that for every k with 0 <= k < len(r), min_{0 <= i < n} nums[i] <= r[k] <= max_{0 <= i < n} nums[i].
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_12 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ k : Fin r.val.length,
          minNums nums ≤ (r.val.get k).val ∧ (r.val.get k).val ≤ maxNums nums := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ k : Fin r.val.length,
            minNums nums ≤ (r.val.get k).val ∧ (r.val.get k).val ≤ maxNums nums) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < n, there exists k with 0 <= k < len(r) and r[k] = nums[i].
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_13 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ i : Fin nums.val.length, ∃ k : Fin r.val.length, r.val.get k = nums.val.get i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ i : Fin nums.val.length, ∃ k : Fin r.val.length, r.val.get k = nums.val.get i) := by
    sorry

  /-- The function returns a result r such that for every i with 0 <= i < n, letting a be the final position in r of the element inserted at step i (elements distinguished by insertion step even if their values coincide), we have index[i] <= a < n.
    Preconditions: Let n = len(nums). Then len(index) = n, 1 <= n <= 100, and for every i with 0 <= i < n, 0 <= nums[i] <= 100 and 0 <= index[i] <= i. -/
  theorem spec_14 (nums index : Slice Std.I64) (h : ValidInput nums index) :
      ∃ r : alloc.vec.Vec Std.I64,
        create_target_array nums index = ok r ∧
        ∀ i : Nat,
          i < nums.val.length →
          posAt index i ≤ finalPos index i ∧ finalPos index i < nums.val.length := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums index : Slice Std.I64) (h : ValidInput nums index), ∃ r : alloc.vec.Vec Std.I64,
          create_target_array nums index = ok r ∧
          ∀ i : Nat,
            i < nums.val.length →
            posAt index i ≤ finalPos index i ∧ finalPos index i < nums.val.length) := by
    sorry

  end AegisSpec.CreateTargetArray
