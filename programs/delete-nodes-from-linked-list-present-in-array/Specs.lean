import Aegis.ModifiedList.Code.Funs

/-!
# Specifications of `Aegis.ModifiedList.modified_list`

LeetCode problem `delete-nodes-from-linked-list-present-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ModifiedList

  def vals : Aegis.ModifiedList.List → List Int
    | .Nil => []
    | .Cons v t => v.val :: vals t

  def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def occursIn (nums : Slice Std.I64) (v : Int) : Prop := v ∈ sliceVals nums

  instance decidableOccursIn (nums : Slice Std.I64) (v : Int) : Decidable (occursIn nums v) := by
    unfold occursIn
    infer_instance

  def countOcc (v : Int) : List Int → Nat
    | [] => 0
    | x :: xs => (if x = v then 1 else 0) + countOcc v xs

  def IsSubsequenceOf (l₁ l₂ : List Int) : Prop :=
    ∃ idx : Fin l₁.length → Fin l₂.length,
      (∀ a b : Fin l₁.length, a < b → (idx a : Nat) < (idx b)) ∧
        ∀ a : Fin l₁.length, l₂[idx a] = l₁[a]

  inductive Interleaving : List Int → List Int → List Int → Prop
    | nil : Interleaving [] [] []
    | left {a b c : List Int} {x : Int} : Interleaving a b c → Interleaving (x :: a) b (x :: c)
    | right {a b c : List Int} {x : Int} : Interleaving a b c → Interleaving a (x :: b) (x :: c)

  /-- Let vals(l) be the sequence of node values of l from head to tail: vals(Nil) = [] and vals(Cons(v, t)) = v :: vals(t). Say that a value v occurs in nums iff there exists an index i with 0 <= i < len(nums) and nums[i] = v. The function returns a result r (i.e., modified_list nums head = Ok r) and vals(r) is exactly the sequence obtained from vals(head) by deleting every element v for which v occurs in nums, preserving the relative order of the remaining elements. Formally, vals(r) = filter (fun v => not (v occurs in nums)) (vals(head)), where filter keeps exactly the elements satisfying the predicate.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_1 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        vals r = (vals head).filter (fun v => decide (¬ occursIn nums v)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          vals r = (vals head).filter (fun v => decide (¬ occursIn nums v))) := by
    sorry

  /-- For every nums and head satisfying the preconditions, there exists a list r such that modified_list nums head = Ok r; the function never returns Err on these inputs.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_2 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r) := by
    sorry

  /-- The function returns a result r (modified_list nums head = Ok r) and for every value v that occurs in vals(r), v does not occur in nums (i.e., there is no index i with 0 <= i < len(nums) and nums[i] = v).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_3 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∀ (v : Int), v ∈ vals r → ¬ occursIn nums v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∀ (v : Int), v ∈ vals r → ¬ occursIn nums v) := by
    sorry

  /-- The function returns a result r and for every integer v that does not occur in nums, the number of occurrences of v in vals(r) equals the number of occurrences of v in vals(head).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_4 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∀ (v : Int), ¬ occursIn nums v → countOcc v (vals r) = countOcc v (vals head) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∀ (v : Int), ¬ occursIn nums v → countOcc v (vals r) = countOcc v (vals head)) := by
    sorry

  /-- The function returns a result r and vals(r) is a subsequence of vals(head): there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_0 and i_{k-1} < len(vals(head)) such that for every j with 0 <= j < k, vals(r)[j] = vals(head)[i_j], where k = len(vals(r)).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_5 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        IsSubsequenceOf (vals r) (vals head) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          IsSubsequenceOf (vals r) (vals head)) := by
    sorry

  /-- The function returns a result r and len(vals(r)) equals the number of indices i with 0 <= i < len(vals(head)) such that vals(head)[i] does not occur in nums.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_6 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        (vals r).length =
          ((List.finRange (vals head).length).filter
            (fun i => decide (¬ occursIn nums (vals head)[i]))).length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          (vals r).length =
            ((List.finRange (vals head).length).filter
              (fun i => decide (¬ occursIn nums (vals head)[i]))).length) := by
    sorry

  /-- The function returns a result r and r is not Nil; equivalently, len(vals(r)) >= 1.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_7 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        r ≠ Aegis.ModifiedList.List.Nil ∧ 1 ≤ (vals r).length := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          r ≠ Aegis.ModifiedList.List.Nil ∧ 1 ≤ (vals r).length) := by
    sorry

  /-- The function returns a result r and, since r is non-empty, its first value vals(r)[0] is the first value in vals(head) that does not occur in nums. That is, vals(r)[0] = vals(head)[i] where i is the smallest index with 0 <= i < len(vals(head)) and vals(head)[i] does not occur in nums.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_8 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∃ (i : Nat) (hi : i < (vals head).length),
          ¬ occursIn nums (vals head)[i] ∧
            (∀ (j : Nat) (hj : j < i), occursIn nums (vals head)[j]) ∧
            (vals r).head? = some (vals head)[i] := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∃ (i : Nat) (hi : i < (vals head).length),
            ¬ occursIn nums (vals head)[i] ∧
              (∀ (j : Nat) (hj : j < i), occursIn nums (vals head)[j]) ∧
              (vals r).head? = some (vals head)[i]) := by
    sorry

  /-- The function returns a result r and, since r is non-empty, its last value vals(r)[len(vals(r))-1] is the last value in vals(head) that does not occur in nums. That is, vals(r)[len(vals(r))-1] = vals(head)[i] where i is the largest index with 0 <= i < len(vals(head)) and vals(head)[i] does not occur in nums.
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_9 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∃ (i : Nat) (hi : i < (vals head).length),
          ¬ occursIn nums (vals head)[i] ∧
            (∀ (j : Nat) (hij : i < j) (hj : j < (vals head).length),
              occursIn nums (vals head)[j]) ∧
            (vals r).getLast? = some (vals head)[i] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∃ (i : Nat) (hi : i < (vals head).length),
            ¬ occursIn nums (vals head)[i] ∧
              (∀ (j : Nat) (hij : i < j) (hj : j < (vals head).length),
                occursIn nums (vals head)[j]) ∧
              (vals r).getLast? = some (vals head)[i]) := by
    sorry

  /-- There exist lists r1 and r2 such that modified_list nums1 head = Ok r1 and modified_list nums2 head = Ok r2, and r1 = r2 (equivalently vals(r1) = vals(r2)).
    Preconditions: nums1 and nums2 each satisfy the problem constraints: 1 <= len(nums1), len(nums2) <= 100000; all elements of nums1 and nums2 lie in [1, 100000] and are distinct within each slice; head satisfies 1 <= len(vals(head)) <= 100000 with all node values in [1, 100000]; there is at least one node value in head that does not occur in nums1 (equivalently, not in nums2); and for every integer v, v occurs in nums1 if and only if v occurs in nums2. -/
  theorem spec_10 (nums1 nums2 : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums1_pos : 1 ≤ nums1.val.length) (h_nums1_le : nums1.val.length ≤ 100000)
      (h_nums1_range :
        ∀ (i : Nat) (hi : i < nums1.val.length),
          1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 100000)
      (h_nums1_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums1.val.length),
          (nums1.val[i]).val ≠ (nums1.val[j]).val)
      (h_nums2_pos : 1 ≤ nums2.val.length) (h_nums2_le : nums2.val.length ≤ 100000)
      (h_nums2_range :
        ∀ (i : Nat) (hi : i < nums2.val.length),
          1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100000)
      (h_nums2_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums2.val.length),
          (nums2.val[i]).val ≠ (nums2.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums1 (vals head)[j])
      (h_occurs_iff : ∀ (v : Int), occursIn nums1 v ↔ occursIn nums2 v) :
      ∃ r1 r2, Aegis.ModifiedList.modified_list nums1 head = ok r1 ∧
        Aegis.ModifiedList.modified_list nums2 head = ok r2 ∧ r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums1_pos : 1 ≤ nums1.val.length) (h_nums1_le : nums1.val.length ≤ 100000)
        (h_nums1_range :
          ∀ (i : Nat) (hi : i < nums1.val.length),
            1 ≤ (nums1.val[i]).val ∧ (nums1.val[i]).val ≤ 100000)
        (h_nums1_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums1.val.length),
            (nums1.val[i]).val ≠ (nums1.val[j]).val)
        (h_nums2_pos : 1 ≤ nums2.val.length) (h_nums2_le : nums2.val.length ≤ 100000)
        (h_nums2_range :
          ∀ (i : Nat) (hi : i < nums2.val.length),
            1 ≤ (nums2.val[i]).val ∧ (nums2.val[i]).val ≤ 100000)
        (h_nums2_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums2.val.length),
            (nums2.val[i]).val ≠ (nums2.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums1 (vals head)[j])
        (h_occurs_iff : ∀ (v : Int), occursIn nums1 v ↔ occursIn nums2 v), ∃ r1 r2, Aegis.ModifiedList.modified_list nums1 head = ok r1 ∧
          Aegis.ModifiedList.modified_list nums2 head = ok r2 ∧ r1 = r2) := by
    sorry

  /-- The function returns a result r and for every integer v, the number of occurrences of v in vals(r) is less than or equal to the number of occurrences of v in vals(head).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_11 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∀ (v : Int), countOcc v (vals r) ≤ countOcc v (vals head) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∀ (v : Int), countOcc v (vals r) ≤ countOcc v (vals head)) := by
    sorry

  /-- Let vals(l) be the sequence of node values of l from head to tail. The function returns a result r and there exist sequences A and B such that vals(head) is the interleaving of A and B that preserves the original order, B = vals(r), and A is exactly the subsequence of vals(head) consisting of those values v for which v occurs in nums (i.e., A is obtained from vals(head) by keeping only the elements v with v occurring in nums, in their original order).
    Preconditions: 1 <= len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100000; for every i, j with 0 <= i < j < len(nums), nums[i] != nums[j]; 1 <= len(vals(head)) <= 100000; for every value v in vals(head), 1 <= v <= 100000; and there exists an index j with 0 <= j < len(vals(head)) such that vals(head)[j] does not occur in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = vals(head)[j]). -/
  theorem spec_12 (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
      (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
      (h_nums_range :
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
      (h_nums_distinct :
        ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
          (nums.val[i]).val ≠ (nums.val[j]).val)
      (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
      (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
      (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]) :
      ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
        ∃ A B : List Int, B = vals r ∧
          A = (vals head).filter (fun v => decide (occursIn nums v)) ∧
          Interleaving A B (vals head) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (head : Aegis.ModifiedList.List)
        (h_nums_pos : 1 ≤ nums.val.length) (h_nums_le : nums.val.length ≤ 100000)
        (h_nums_range :
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000)
        (h_nums_distinct :
          ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
            (nums.val[i]).val ≠ (nums.val[j]).val)
        (h_head_pos : 1 ≤ (vals head).length) (h_head_le : (vals head).length ≤ 100000)
        (h_head_range : ∀ (v : Int), v ∈ vals head → 1 ≤ v ∧ v ≤ 100000)
        (h_head_survives : ∃ (j : Nat) (hj : j < (vals head).length), ¬ occursIn nums (vals head)[j]), ∃ r, Aegis.ModifiedList.modified_list nums head = ok r ∧
          ∃ A B : List Int, B = vals r ∧
            A = (vals head).filter (fun v => decide (occursIn nums v)) ∧
            Interleaving A B (vals head)) := by
    sorry

  end AegisSpec.ModifiedList
