import Aegis.FindUnsortedSubarray.Code.Funs

/-!
# Specifications of `Aegis.FindUnsortedSubarray.find_unsorted_subarray`

LeetCode problem `shortest-unsorted-continuous-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindUnsortedSubarray

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def len (nums : Slice Std.I64) : Nat := (vals nums).length

def valAt (l : List Int) (i : Nat) : Int := l.getD i 0

def Nondec (l : List Int) : Prop := ∀ i, i + 1 < l.length → valAt l i ≤ valAt l (i + 1)

def SortedVersion (a s : List Int) : Prop := s.Perm a ∧ Nondec s

def swapAdj (l : List Int) (i : Nat) : List Int :=
  (l.set i (valAt l (i + 1))).set (i + 1) (valAt l i)

def segment (l : List Int) (a b : Nat) : List Int := (l.drop a).take (b + 1 - a)

def replaceSorted (l : List Int) (a b : Nat) (s : List Int) : List Int :=
  l.take a ++ s ++ l.drop (b + 1)

def minVal (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl min x

def maxVal (l : List Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl max x

def IsFirstDiff (a s : List Int) (i : Nat) : Prop :=
  i < a.length ∧ valAt a i ≠ valAt s i ∧ ∀ j, j < i → valAt a j = valAt s j

def IsLastDiff (a s : List Int) (i : Nat) : Prop :=
  i < a.length ∧ valAt a i ≠ valAt s i ∧ ∀ j, i < j → j < a.length → valAt a j = valAt s j

def IsDescent (l : List Int) (i : Nat) : Prop :=
  i + 1 < l.length ∧ valAt l i > valAt l (i + 1)

def IsFirstDescent (l : List Int) (i : Nat) : Prop :=
  IsDescent l i ∧ ∀ j, j < i → ¬ IsDescent l j

def IsLastDescent (l : List Int) (i : Nat) : Prop :=
  IsDescent l i ∧ ∀ j, i < j → ¬ IsDescent l j

/-- Let s be the non-decreasing sequence obtained by sorting the multiset of values in nums (so s is a permutation of nums with s[0] <= ... <= s[len(nums)-1]). Whenever the function returns a result r, the following holds. If nums is non-decreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]), then r = 0. Otherwise, let l be the least index with 0 <= l < len(nums) and nums[l] != s[l], and let m be the greatest index with 0 <= m < len(nums) and nums[m] != s[m]; then r = m - l + 1.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (s : List Int) (hs : SortedVersion (vals nums) s)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    (Nondec (vals nums) → r.val = 0) ∧
      (¬ Nondec (vals nums) →
        ∀ l m : Nat, IsFirstDiff (vals nums) s l → IsLastDiff (vals nums) s m →
          r.val = (m : Int) - (l : Int) + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (s : List Int) (hs : SortedVersion (vals nums) s)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), (Nondec (vals nums) → r.val = 0) ∧
      (¬ Nondec (vals nums) →
        ∀ l m : Nat, IsFirstDiff (vals nums) s l → IsLastDiff (vals nums) s m →
          r.val = (m : Int) - (l : Int) + 1)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ (len nums : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), 0 ≤ r.val ∧ r.val ≤ (len nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if nums is non-decreasing, i.e., for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1].
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    r.val = 0 ↔ Nondec (vals nums) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), r.val = 0 ↔ Nondec (vals nums)) := by
  sorry

/-- Whenever the function returns a result r, r != 1.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    r.val ≠ 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), r.val ≠ 1) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if and only if there exists an index i with 0 <= i < len(nums)-1 such that nums[i] > nums[i+1] and the array obtained from nums by swapping the two entries nums[i] and nums[i+1] is non-decreasing.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    r.val = 2 ↔ ∃ i : Nat, IsDescent (vals nums) i ∧ Nondec (swapAdj (vals nums) i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), r.val = 2 ↔ ∃ i : Nat, IsDescent (vals nums) i ∧ Nondec (swapAdj (vals nums) i)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, there exist indices a and b with 0 <= a <= b < len(nums) and b - a + 1 = r such that, if the contiguous subarray nums[a..b] is replaced by its non-decreasing sorted version, the resulting whole array of length len(nums) is non-decreasing.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    r.val > 0 →
      ∃ a b : Nat, a ≤ b ∧ b < len nums ∧ (b : Int) - (a : Int) + 1 = r.val ∧
        ∃ s : List Int, Nondec s ∧ s.Perm (segment (vals nums) a b) ∧
          Nondec (replaceSorted (vals nums) a b s) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), r.val > 0 →
      ∃ a b : Nat, a ≤ b ∧ b < len nums ∧ (b : Int) - (a : Int) + 1 = r.val ∧
        ∃ s : List Int, Nondec s ∧ s.Perm (segment (vals nums) a b) ∧
          Nondec (replaceSorted (vals nums) a b s)) := by
  sorry

/-- Whenever the function returns a result r with r > 0, for every pair of indices a and b with 0 <= a <= b < len(nums) and b - a + 1 < r, replacing the contiguous subarray nums[a..b] by its non-decreasing sorted version does not make the whole array non-decreasing.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    r.val > 0 →
      ∀ a b : Nat, a ≤ b → b < len nums → (b : Int) - (a : Int) + 1 < r.val →
        ∀ s : List Int, Nondec s → s.Perm (segment (vals nums) a b) →
          ¬ Nondec (replaceSorted (vals nums) a b s) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), r.val > 0 →
      ∀ a b : Nat, a ≤ b → b < len nums → (b : Int) - (a : Int) + 1 < r.val →
        ∀ s : List Int, Nondec s → s.Perm (segment (vals nums) a b) →
          ¬ Nondec (replaceSorted (vals nums) a b s)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail (in particular, there is no arithmetic overflow, out-of-bounds access, or panic).
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5) :
    ∃ r : Std.I64, Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5), ∃ r : Std.I64, Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) if and only if nums[0] > min(nums) and nums[len(nums)-1] < max(nums), where min(nums) and max(nums) are respectively the minimum and maximum values among all entries of nums.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    (r.val = (len nums : Int) ↔
      valAt (vals nums) 0 > minVal (vals nums) ∧
        valAt (vals nums) (len nums - 1) < maxVal (vals nums)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), (r.val = (len nums : Int) ↔
      valAt (vals nums) 0 > minVal (vals nums) ∧
        valAt (vals nums) (len nums - 1) < maxVal (vals nums))) := by
  sorry

/-- For any two arrays nums and nums' satisfying the preconditions with len(nums) = len(nums'), if for all indices i and j with 0 <= i,j < len(nums) we have nums[i] <= nums[j] if and only if nums'[i] <= nums'[j], then whenever find_unsorted_subarray(nums) returns r and find_unsorted_subarray(nums') returns r', we have r = r'.
  Preconditions: nums and nums' each satisfy 1 <= len <= 10^4 and all entries in [-10^5,10^5]. -/
theorem spec_10 (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (hlen1' : 1 ≤ len nums') (hlen2' : len nums' ≤ 10 ^ 4)
    (hbound' : ∀ i, i < len nums' → -10 ^ 5 ≤ valAt (vals nums') i ∧ valAt (vals nums') i ≤ 10 ^ 5)
    (hlen : len nums = len nums')
    (hpat : ∀ i j, i < len nums → j < len nums →
      (valAt (vals nums) i ≤ valAt (vals nums) j ↔
        valAt (vals nums') i ≤ valAt (vals nums') j))
    (r r' : Std.I64)
    (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r)
    (hr' : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (hlen1' : 1 ≤ len nums') (hlen2' : len nums' ≤ 10 ^ 4)
    (hbound' : ∀ i, i < len nums' → -10 ^ 5 ≤ valAt (vals nums') i ∧ valAt (vals nums') i ≤ 10 ^ 5)
    (hlen : len nums = len nums')
    (hpat : ∀ i j, i < len nums → j < len nums →
      (valAt (vals nums) i ≤ valAt (vals nums) j ↔
        valAt (vals nums') i ≤ valAt (vals nums') j))
    (r r' : Std.I64)
    (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r)
    (hr' : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, if there exists at least one index i with 0 <= i < len(nums)-1 and nums[i] > nums[i+1], let a be the smallest such index and b the largest such index; then r >= b - a + 2.
  Preconditions: 1 <= len(nums) <= 10^4; for every i with 0 <= i < len(nums), -10^5 <= nums[i] <= 10^5. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r) :
    (∃ i : Nat, IsDescent (vals nums) i) →
      ∀ a b : Nat, IsFirstDescent (vals nums) a → IsLastDescent (vals nums) b →
        (b : Int) - (a : Int) + 2 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ len nums) (hlen2 : len nums ≤ 10 ^ 4)
    (hbound : ∀ i, i < len nums → -10 ^ 5 ≤ valAt (vals nums) i ∧ valAt (vals nums) i ≤ 10 ^ 5)
    (r : Std.I64) (hr : Aegis.FindUnsortedSubarray.find_unsorted_subarray nums = ok r), (∃ i : Nat, IsDescent (vals nums) i) →
      ∀ a b : Nat, IsFirstDescent (vals nums) a → IsLastDescent (vals nums) b →
        (b : Int) - (a : Int) + 2 ≤ r.val) := by
  sorry

end AegisSpec.FindUnsortedSubarray
