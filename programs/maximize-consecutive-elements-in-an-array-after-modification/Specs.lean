import Aegis.MaxSelectedElements.Code.Funs

/-!
# Specifications of `Aegis.MaxSelectedElements.max_selected_elements`

LeetCode problem `maximize-consecutive-elements-in-an-array-after-modification`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxSelectedElements

namespace AegisSpec.MaxSelectedElements

def slen (nums : Slice I64) : ℕ := nums.val.length

def vals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

def entry (nums : Slice I64) (i : Fin (slen nums)) : ℤ := (nums.val.get i).val

def Occurs (x : ℤ) (nums : Slice I64) : Prop := x ∈ vals nums

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldr min x

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: xs => xs.foldr max x

def lo (nums : Slice I64) : ℤ := listMin (vals nums)

def hi (nums : Slice I64) : ℤ := listMax (vals nums)

def numDistinct (nums : Slice I64) : ℕ := (vals nums).toFinset.card

def block (a : ℤ) (k : ℕ) : Finset ℤ := (Finset.range k).image (fun j : ℕ => a + (j : ℤ))

def Admissible (nums : Slice I64) (S : Finset (Fin (slen nums))) : Prop :=
  S.Nonempty ∧
    ∃ a : ℤ, ∃ f : Fin (slen nums) → ℤ,
      S.image f = block a S.card ∧
        ∀ i ∈ S, f i = entry nums i ∨ f i = entry nums i + 1

/-- The function returns a result r, and r is the maximum cardinality of a nonempty set S of distinct indices from {0,...,len(nums)-1} for which there exist an integer a and a bijection f from S to {a, a+1, ..., a+|S|-1} such that f(i) = nums[i] or f(i) = nums[i]+1 for every i in S. In other words, after increasing each selected element by either 0 or 1, the selected values are exactly |S| distinct consecutive integers, and r is the largest possible number of selected elements.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_1 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64,
      max_selected_elements nums = ok r ∧
        ∃ S : Finset (Fin (slen nums)),
          Admissible nums S ∧ (S.card : ℤ) = r.val ∧
            ∀ T : Finset (Fin (slen nums)), Admissible nums T → T.card ≤ S.card := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64,
      max_selected_elements nums = ok r ∧
        ∃ S : Finset (Fin (slen nums)),
          Admissible nums S ∧ (S.card : ℤ) = r.val ∧
            ∀ T : Finset (Fin (slen nums)), Admissible nums T → T.card ≤ S.card) := by
  sorry

/-- The function returns a result r for every nums satisfying the precondition; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_2 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64, max_selected_elements nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64, max_selected_elements nums = ok r) := by
  sorry

/-- The function returns a result r and r <= len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_3 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ (slen nums : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ (slen nums : ℤ)) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_4 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64, max_selected_elements nums = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- If len(nums) = 2, then the function returns r = 2 when |nums[0] - nums[1]| <= 2, and r = 1 otherwise.
  Preconditions: nums is a slice of 64-bit integers with len(nums) = 2 and, for i = 0 and i = 1, 1 <= nums[i] <= 1000000. -/
theorem spec_5 (nums : Slice I64) (x y : ℤ)
    (hvals : vals nums = [x, y])
    (hx : 1 ≤ x ∧ x ≤ 1000000) (hy : 1 ≤ y ∧ y ≤ 1000000) :
    ∃ r : I64,
      max_selected_elements nums = ok r ∧
        (if |x - y| ≤ 2 then r.val = 2 else r.val = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (x y : ℤ)
    (hvals : vals nums = [x, y])
    (hx : 1 ≤ x ∧ x ≤ 1000000) (hy : 1 ≤ y ∧ y ≤ 1000000), ∃ r : I64,
      max_selected_elements nums = ok r ∧
        (if |x - y| ≤ 2 then r.val = 2 else r.val = 1)) := by
  sorry

/-- Let lo = min(nums) and hi = max(nums) over all entries. If hi - lo <= 1, then the function returns r = min(len(nums), hi - lo + 2).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_6 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hwindow : hi nums - lo nums ≤ 1) :
    ∃ r : I64,
      max_selected_elements nums = ok r ∧
        r.val = min (slen nums : ℤ) (hi nums - lo nums + 2) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hwindow : hi nums - lo nums ≤ 1), ∃ r : I64,
      max_selected_elements nums = ok r ∧
        r.val = min (slen nums : ℤ) (hi nums - lo nums + 2)) := by
  sorry

/-- Let lo = min(nums) and hi = max(nums) over all entries. The function returns a result r and r <= hi - lo + 2.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_7 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ hi nums - lo nums + 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ hi nums - lo nums + 2) := by
  sorry

/-- Let D be the number of distinct integer values appearing among nums[0],...,nums[len(nums)-1]. The function returns a result r and r <= 2*D.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_8 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ 2 * (numDistinct nums : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64, max_selected_elements nums = ok r ∧ r.val ≤ 2 * (numDistinct nums : ℤ)) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r' = r.
  Preconditions: nums and nums' are slices of 64-bit integers, each satisfying 1 <= len <= 100000 and all entries between 1 and 1000000 inclusive; nums' is a permutation of nums (same length and the same number of occurrences of every integer value). -/
theorem spec_9 (nums nums' : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hperm : (vals nums').Perm (vals nums)) :
    ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hperm : (vals nums').Perm (vals nums)), ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' → r' = r) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r' >= r.
  Preconditions: nums and nums' are slices of 64-bit integers, each satisfying 1 <= len <= 100000 and all entries between 1 and 1000000 inclusive; x is an integer with 1 <= x <= 1000000, and nums' is obtained from nums by inserting one extra occurrence of x at some position. -/
theorem spec_10 (nums nums' : Slice I64) (x : ℤ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hx : 1 ≤ x ∧ x ≤ 1000000)
    (hins : ∃ pre post : List ℤ, vals nums = pre ++ post ∧ vals nums' = pre ++ x :: post) :
    ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice I64) (x : ℤ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hx : 1 ≤ x ∧ x ≤ 1000000)
    (hins : ∃ pre post : List ℤ, vals nums = pre ++ post ∧ vals nums' = pre ++ x :: post), ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r for which there exist r distinct indices i_1,...,i_r and an integer a such that, after choosing for each j one value v_j in {nums[i_j], nums[i_j]+1}, the set {v_1,...,v_r} is exactly {a, a+1, ..., a+r-1}.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_11 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64,
      max_selected_elements nums = ok r ∧
        ∃ (S : Finset (Fin (slen nums))) (a : ℤ) (v : Fin (slen nums) → ℤ),
          (S.card : ℤ) = r.val ∧
            S.image v = block a S.card ∧
              ∀ i ∈ S, v i = entry nums i ∨ v i = entry nums i + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64,
      max_selected_elements nums = ok r ∧
        ∃ (S : Finset (Fin (slen nums))) (a : ℤ) (v : Fin (slen nums) → ℤ),
          (S.card : ℤ) = r.val ∧
            S.image v = block a S.card ∧
              ∀ i ∈ S, v i = entry nums i ∨ v i = entry nums i + 1) := by
  sorry

/-- If the entries of nums are pairwise distinct and, after sorting them increasingly, they form a consecutive sequence (that is, there exists an integer a such that the sorted entries are a, a+1, ..., a+len(nums)-1), then the function returns r = len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_12 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hnodup : (vals nums).Nodup)
    (hconsec : ∃ a : ℤ, (vals nums).toFinset = block a (slen nums)) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ r.val = (slen nums : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hnodup : (vals nums).Nodup)
    (hconsec : ∃ a : ℤ, (vals nums).toFinset = block a (slen nums)), ∃ r : I64, max_selected_elements nums = ok r ∧ r.val = (slen nums : ℤ)) := by
  sorry

/-- The function returns a result r, and r >= 2 if and only if there exist distinct indices i and j with 0 <= i < len(nums), 0 <= j < len(nums) such that |nums[i] - nums[j]| <= 2. Equivalently, r = 1 if and only if |nums[i] - nums[j]| > 2 for every pair of distinct indices i and j.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_13 (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000) :
    ∃ r : I64,
      max_selected_elements nums = ok r ∧
        (2 ≤ r.val ↔
          ∃ i j : Fin (slen nums), i ≠ j ∧ |entry nums i - entry nums j| ≤ 2) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000), ∃ r : I64,
      max_selected_elements nums = ok r ∧
        (2 ≤ r.val ↔
          ∃ i j : Fin (slen nums), i ≠ j ∧ |entry nums i - entry nums j| ≤ 2)) := by
  sorry

/-- If k is an integer with 1 <= k <= len(nums) and there exist k distinct integer values v_1 < ... < v_k, each appearing among the entries of nums, such that v_k - v_1 <= k, then the function returns a result r with r >= k.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_14 (nums : Slice I64) (k : ℕ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k) (hk2 : k ≤ slen nums)
    (hcluster : ∃ (T : Finset ℤ) (l u : ℤ),
      T.card = k ∧ (∀ v ∈ T, Occurs v nums) ∧ (∀ v ∈ T, l ≤ v ∧ v ≤ u) ∧ u - l ≤ (k : ℤ)) :
    ∃ r : I64, max_selected_elements nums = ok r ∧ (k : ℤ) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice I64) (k : ℕ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (hk1 : 1 ≤ k) (hk2 : k ≤ slen nums)
    (hcluster : ∃ (T : Finset ℤ) (l u : ℤ),
      T.card = k ∧ (∀ v ∈ T, Occurs v nums) ∧ (∀ v ∈ T, l ≤ v ∧ v ≤ u) ∧ u - l ≤ (k : ℤ)), ∃ r : I64, max_selected_elements nums = ok r ∧ (k : ℤ) ≤ r.val) := by
  sorry

/-- If the function returns r on nums and r' on nums', then r' <= r + 1.
  Preconditions: nums and nums' are slices of 64-bit integers, each satisfying 1 <= len <= 100000 and all entries between 1 and 1000000 inclusive; x is an integer with 1 <= x <= 1000000, and nums' is obtained from nums by inserting one extra occurrence of x at some position. -/
theorem spec_15 (nums nums' : Slice I64) (x : ℤ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hx : 1 ≤ x ∧ x ≤ 1000000)
    (hins : ∃ pre post : List ℤ, vals nums = pre ++ post ∧ vals nums' = pre ++ x :: post) :
    ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' →
        r'.val ≤ r.val + 1 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums nums' : Slice I64) (x : ℤ)
    (h1 : 1 ≤ slen nums) (h2 : slen nums ≤ 100000)
    (hn : ∀ i : Fin (slen nums), 1 ≤ entry nums i ∧ entry nums i ≤ 1000000)
    (h1' : 1 ≤ slen nums') (h2' : slen nums' ≤ 100000)
    (hn' : ∀ i : Fin (slen nums'), 1 ≤ entry nums' i ∧ entry nums' i ≤ 1000000)
    (hx : 1 ≤ x ∧ x ≤ 1000000)
    (hins : ∃ pre post : List ℤ, vals nums = pre ++ post ∧ vals nums' = pre ++ x :: post), ∀ r r' : I64,
      max_selected_elements nums = ok r → max_selected_elements nums' = ok r' →
        r'.val ≤ r.val + 1) := by
  sorry

end AegisSpec.MaxSelectedElements
