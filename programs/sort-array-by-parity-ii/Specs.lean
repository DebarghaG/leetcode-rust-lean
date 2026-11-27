import Aegis.SortArrayByParityIi.Code.Funs

/-!
# Specifications of `Aegis.SortArrayByParityIi.sort_array_by_parity_ii`

LeetCode problem `sort-array-by-parity-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SortArrayByParityIi

  set_option autoImplicit false

  def sliceVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def vecVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  def len (nums : Slice Std.I64) : ℕ := nums.val.length

  def countIdx (l : List ℤ) (p : ℕ → Prop) [DecidablePred p] (v : ℤ) : ℕ :=
    (List.range l.length).countP (fun i => decide (p i) && decide (l[i]? = some v))

  def countIdxWith (l : List ℤ) (p : ℕ → Prop) [DecidablePred p]
      (q : ℤ → Prop) [DecidablePred q] (v : ℤ) : ℕ :=
    (List.range l.length).countP
      (fun i => decide (p i) && decide (l[i]? = some v) && decide (q v))

  def countParity (l : List ℤ) (par : ℤ) : ℕ :=
    (List.range l.length).countP (fun i => decide (l.getD i 0 % 2 = par))

  /-- Whenever the function returns a result r, all of the following hold: (1) len(r) = len(nums); (2) for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices j with 0 <= j < len(nums) and nums[j] = v; (3) for every index i with 0 <= i < len(r), if i is even then r[i] % 2 = 0, and if i is odd then r[i] % 2 = 1.
    Preconditions: len(nums) >= 2 and len(nums) <= 20000; len(nums) is even (len(nums) % 2 = 0); the number of indices j with 0 <= j < len(nums) and nums[j] % 2 = 0 is exactly len(nums)/2 (and the number of indices j with nums[j] % 2 = 1 is also len(nums)/2); and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
      (h_len_even : len nums % 2 = 0)
      (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
      (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
      (h_bounds : ∀ j, j < len nums →
        0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000) :
      (vecVals r).length = len nums ∧
        (∀ v : ℤ,
          countIdx (vecVals r) (fun _ => True) v
            = countIdx (sliceVals nums) (fun _ => True) v) ∧
        (∀ i, i < (vecVals r).length →
          (i % 2 = 0 → (vecVals r).getD i 0 % 2 = 0) ∧
            (i % 2 = 1 → (vecVals r).getD i 0 % 2 = 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
        (h_len_even : len nums % 2 = 0)
        (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
        (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
        (h_bounds : ∀ j, j < len nums →
          0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000), (vecVals r).length = len nums ∧
          (∀ v : ℤ,
            countIdx (vecVals r) (fun _ => True) v
              = countIdx (sliceVals nums) (fun _ => True) v) ∧
          (∀ i, i < (vecVals r).length →
            (i % 2 = 0 → (vecVals r).getD i 0 % 2 = 0) ∧
              (i % 2 = 1 → (vecVals r).getD i 0 % 2 = 1))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail, panic, or overflow).
    Preconditions: len(nums) >= 2 and len(nums) <= 20000; len(nums) is even (len(nums) % 2 = 0); the number of indices j with 0 <= j < len(nums) and nums[j] % 2 = 0 is exactly len(nums)/2 (and the number of indices j with nums[j] % 2 = 1 is also len(nums)/2); and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
      (h_len_even : len nums % 2 = 0)
      (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
      (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
      (h_bounds : ∀ j, j < len nums →
        0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000) :
      ∃ r : alloc.vec.Vec Std.I64,
        Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
        (h_len_even : len nums % 2 = 0)
        (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
        (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
        (h_bounds : ∀ j, j < len nums →
          0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000), ∃ r : alloc.vec.Vec Std.I64,
          Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r), i even, and r[i] = v equals the number of indices j with 0 <= j < len(nums), nums[j] = v, and v is even.
    Preconditions: len(nums) >= 2 and len(nums) <= 20000; len(nums) is even (len(nums) % 2 = 0); the number of indices j with 0 <= j < len(nums) and nums[j] % 2 = 0 is exactly len(nums)/2 (and the number of indices j with nums[j] % 2 = 1 is also len(nums)/2); and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
      (h_len_even : len nums % 2 = 0)
      (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
      (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
      (h_bounds : ∀ j, j < len nums →
        0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000) :
      ∀ v : ℤ,
        countIdx (vecVals r) (fun i => i % 2 = 0) v
          = countIdxWith (sliceVals nums) (fun _ => True) (fun v => v % 2 = 0) v := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
        (h_len_even : len nums % 2 = 0)
        (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
        (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
        (h_bounds : ∀ j, j < len nums →
          0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000), ∀ v : ℤ,
          countIdx (vecVals r) (fun i => i % 2 = 0) v
            = countIdxWith (sliceVals nums) (fun _ => True) (fun v => v % 2 = 0) v) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r), i odd, and r[i] = v equals the number of indices j with 0 <= j < len(nums), nums[j] = v, and v is odd.
    Preconditions: len(nums) >= 2 and len(nums) <= 20000; len(nums) is even (len(nums) % 2 = 0); the number of indices j with 0 <= j < len(nums) and nums[j] % 2 = 0 is exactly len(nums)/2 (and the number of indices j with nums[j] % 2 = 1 is also len(nums)/2); and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
      (h_len_even : len nums % 2 = 0)
      (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
      (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
      (h_bounds : ∀ j, j < len nums →
        0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000) :
      ∀ v : ℤ,
        countIdx (vecVals r) (fun i => i % 2 = 1) v
          = countIdxWith (sliceVals nums) (fun _ => True) (fun v => v % 2 = 1) v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
        (h_len_even : len nums % 2 = 0)
        (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
        (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
        (h_bounds : ∀ j, j < len nums →
          0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000), ∀ v : ℤ,
          countIdx (vecVals r) (fun i => i % 2 = 1) v
            = countIdxWith (sliceVals nums) (fun _ => True) (fun v => v % 2 = 1) v) := by
    sorry

  /-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), 0 <= r[i] <= 1000.
    Preconditions: len(nums) >= 2 and len(nums) <= 20000; len(nums) is even (len(nums) % 2 = 0); the number of indices j with 0 <= j < len(nums) and nums[j] % 2 = 0 is exactly len(nums)/2 (and the number of indices j with nums[j] % 2 = 1 is also len(nums)/2); and for every j with 0 <= j < len(nums), 0 <= nums[j] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
      (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
      (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
      (h_len_even : len nums % 2 = 0)
      (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
      (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
      (h_bounds : ∀ j, j < len nums →
        0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000) :
      ∀ i, i < (vecVals r).length →
        0 ≤ (vecVals r).getD i 0 ∧ (vecVals r).getD i 0 ≤ 1000 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
        (h_ret : Aegis.SortArrayByParityIi.sort_array_by_parity_ii nums = ok r)
        (h_len_ge : 2 ≤ len nums) (h_len_le : len nums ≤ 20000)
        (h_len_even : len nums % 2 = 0)
        (h_even_count : countParity (sliceVals nums) 0 = len nums / 2)
        (h_odd_count : countParity (sliceVals nums) 1 = len nums / 2)
        (h_bounds : ∀ j, j < len nums →
          0 ≤ (sliceVals nums).getD j 0 ∧ (sliceVals nums).getD j 0 ≤ 1000), ∀ i, i < (vecVals r).length →
          0 ≤ (vecVals r).getD i 0 ∧ (vecVals r).getD i 0 ≤ 1000) := by
    sorry

  end AegisSpec.SortArrayByParityIi
