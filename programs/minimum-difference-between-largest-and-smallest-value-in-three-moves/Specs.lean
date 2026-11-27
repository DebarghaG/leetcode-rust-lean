import Aegis.MinDifference.Code.Funs

/-!
# Specifications of `Aegis.MinDifference.min_difference`

LeetCode problem `minimum-difference-between-largest-and-smallest-value-in-three-moves`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinDifference

  def toInts (s : Slice I64) : List Int := s.val.map (fun x => x.val)

  def changeCount (a b : List Int) : Nat :=
    (a.zipWith (fun x y => if x = y then 0 else 1) b).sum

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def spreads (a : List Int) : Set Int :=
    { d | ∃ b : List Int, b.length = a.length ∧ changeCount a b ≤ 3 ∧
            d = listMax b - listMin b }

  def occCount (x : Int) (a : List Int) : Nat := a.countP (fun y => y = x)

  def inRangeCount (L U : Int) (a : List Int) : Nat :=
    a.countP (fun y => L ≤ y ∧ y ≤ U)

  def pairAbsDiffs (a : List Int) : Set Int :=
    { d | ∃ i j : Fin a.length, i < j ∧ d = |a.get i - a.get j| }

  def windowWidths (a : List Int) : Set Int :=
    { d | ∃ i : Nat, i ≤ 3 ∧ d = a.getD (i + (a.length - 4)) 0 - a.getD i 0 }

  /-- Let n = len(nums). The function returns a result r, and r equals the minimum of (max(b) - min(b)) over all integer arrays b of length n such that the number of indices i with b[i] != nums[i] is at most 3; here max(b) and min(b) are the largest and smallest entries of b. Equivalently, r is the smallest possible difference between the largest and smallest value after changing at most three entries of nums to arbitrary integer values.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        IsLeast (spreads (toInts nums)) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          IsLeast (spreads (toInts nums)) r.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ (0 : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ (0 : Int) ≤ r.val) := by
    sorry

  /-- For every pair of integers L and U with L <= U such that at least len(nums)-3 indices i satisfy L <= nums[i] <= U, the function returns a result r and r <= U - L.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, len(nums) >= 4, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_len_ge : 4 ≤ nums.val.length)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∀ L U : Int, L ≤ U → nums.val.length - 3 ≤ inRangeCount L U (toInts nums) →
        ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ r.val ≤ U - L := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_len_ge : 4 ≤ nums.val.length)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∀ L U : Int, L ≤ U → nums.val.length - 3 ≤ inRangeCount L U (toInts nums) →
          ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ r.val ≤ U - L) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: len(nums) >= 1, len(nums) <= 3, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 3)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 3)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if there exists an integer x such that at least len(nums)-3 indices i with 0 <= i < len(nums) satisfy nums[i] = x.
    Preconditions: len(nums) > 3, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice I64)
      (h_len_gt : 3 < nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        (r.val = 0 ↔ ∃ x : Int, nums.val.length - 3 ≤ occCount x (toInts nums)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_gt : 3 < nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          (r.val = 0 ↔ ∃ x : Int, nums.val.length - 3 ≤ occCount x (toInts nums))) := by
    sorry

  /-- The function returns a result r and r = min { abs(nums[i] - nums[j]) : 0 <= i < j < len(nums) }, where abs denotes absolute value.
    Preconditions: len(nums) = 5 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice I64)
      (h_len : nums.val.length = 5)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        IsLeast (pairAbsDiffs (toInts nums)) r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : nums.val.length = 5)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          IsLeast (pairAbsDiffs (toInts nums)) r.val) := by
    sorry

  /-- The function returns a result r and there exists an integer array b of length len(nums) such that (i) the number of indices i with b[i] != nums[i] is at most 3, and (ii) (max over i of b[i]) - (min over i of b[i]) = r.
    Preconditions: len(nums) >= 1, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        ∃ b : List Int, b.length = nums.val.length ∧
          changeCount (toInts nums) b ≤ 3 ∧ listMax b - listMin b = r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          ∃ b : List Int, b.length = nums.val.length ∧
            changeCount (toInts nums) b ≤ 3 ∧ listMax b - listMin b = r.val) := by
    sorry

  /-- The function returns results r and r' on nums and nums', respectively, and r = r'.
    Preconditions: Both nums and nums' satisfy len >= 1, len <= 100000, and all entries in [-1000000000, 1000000000]; len(nums') = len(nums); and there exists a bijection f from indices of nums' to indices of nums such that nums'[i] = nums[f(i)] for every i with 0 <= i < len(nums'). -/
  theorem spec_9 (nums nums' : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000)
      (h_len_pos' : 1 ≤ nums'.val.length)
      (h_len_le' : nums'.val.length ≤ 100000)
      (h_bound' : ∀ (i : Nat) (hi : i < nums'.val.length),
        -1000000000 ≤ (nums'.val.get ⟨i, hi⟩).val ∧
          (nums'.val.get ⟨i, hi⟩).val ≤ 1000000000)
      (h_len_eq : nums'.val.length = nums.val.length)
      (h_witness : ∃ f : Fin nums'.val.length → Fin nums.val.length,
        Function.Bijective f ∧ ∀ i : Fin nums'.val.length,
          nums'.val.get i = nums.val.get (f i)) :
      ∃ r r' : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        Aegis.MinDifference.min_difference nums' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000)
        (h_len_pos' : 1 ≤ nums'.val.length)
        (h_len_le' : nums'.val.length ≤ 100000)
        (h_bound' : ∀ (i : Nat) (hi : i < nums'.val.length),
          -1000000000 ≤ (nums'.val.get ⟨i, hi⟩).val ∧
            (nums'.val.get ⟨i, hi⟩).val ≤ 1000000000)
        (h_len_eq : nums'.val.length = nums.val.length)
        (h_witness : ∃ f : Fin nums'.val.length → Fin nums.val.length,
          Function.Bijective f ∧ ∀ i : Fin nums'.val.length,
            nums'.val.get i = nums.val.get (f i)), ∃ r r' : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          Aegis.MinDifference.min_difference nums' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The function returns results r and r' on nums and nums', respectively, and r' <= r.
    Preconditions: Both nums and nums' satisfy len >= 1, len <= 100000, and all entries in [-1000000000, 1000000000]; and there exists an injective function f from indices of nums' to indices of nums such that nums'[i] = nums[f(i)] for every i with 0 <= i < len(nums'). -/
  theorem spec_10 (nums nums' : Slice I64)
      (h_len_pos : 1 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000)
      (h_len_pos' : 1 ≤ nums'.val.length)
      (h_len_le' : nums'.val.length ≤ 100000)
      (h_bound' : ∀ (i : Nat) (hi : i < nums'.val.length),
        -1000000000 ≤ (nums'.val.get ⟨i, hi⟩).val ∧
          (nums'.val.get ⟨i, hi⟩).val ≤ 1000000000)
      (h_witness : ∃ f : Fin nums'.val.length → Fin nums.val.length,
        Function.Injective f ∧ ∀ i : Fin nums'.val.length,
          nums'.val.get i = nums.val.get (f i)) :
      ∃ r r' : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        Aegis.MinDifference.min_difference nums' = ok r' ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (h_len_pos : 1 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000)
        (h_len_pos' : 1 ≤ nums'.val.length)
        (h_len_le' : nums'.val.length ≤ 100000)
        (h_bound' : ∀ (i : Nat) (hi : i < nums'.val.length),
          -1000000000 ≤ (nums'.val.get ⟨i, hi⟩).val ∧
            (nums'.val.get ⟨i, hi⟩).val ≤ 1000000000)
        (h_witness : ∃ f : Fin nums'.val.length → Fin nums.val.length,
          Function.Injective f ∧ ∀ i : Fin nums'.val.length,
            nums'.val.get i = nums.val.get (f i)), ∃ r r' : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          Aegis.MinDifference.min_difference nums' = ok r' ∧ r'.val ≤ r.val) := by
    sorry

  /-- Let a be nums sorted in nondecreasing order. The function returns a result r and r = min { a[i + len(nums) - 4] - a[i] : 0 <= i <= 3 }.
    Preconditions: len(nums) >= 4, len(nums) <= 100000, and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
  theorem spec_11 (nums : Slice I64)
      (h_len_ge : 4 ≤ nums.val.length)
      (h_len_le : nums.val.length ≤ 100000)
      (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
        -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
          (nums.val.get ⟨i, hi⟩).val ≤ 1000000000) :
      ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
        ∀ a : List Int, a.length = nums.val.length → a.Pairwise (· ≤ ·) →
          a.Perm (toInts nums) → IsLeast (windowWidths a) r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 4 ≤ nums.val.length)
        (h_len_le : nums.val.length ≤ 100000)
        (h_bound : ∀ (i : Nat) (hi : i < nums.val.length),
          -1000000000 ≤ (nums.val.get ⟨i, hi⟩).val ∧
            (nums.val.get ⟨i, hi⟩).val ≤ 1000000000), ∃ r : I64, Aegis.MinDifference.min_difference nums = ok r ∧
          ∀ a : List Int, a.length = nums.val.length → a.Pairwise (· ≤ ·) →
            a.Perm (toInts nums) → IsLeast (windowWidths a) r.val) := by
    sorry

  end AegisSpec.MinDifference
