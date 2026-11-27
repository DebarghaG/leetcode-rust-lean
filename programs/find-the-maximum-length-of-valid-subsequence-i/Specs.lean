import Aegis.MaximumLength.Code.Funs

/-!
# Specifications of `Aegis.MaximumLength.maximum_length`

LeetCode problem `find-the-maximum-length-of-valid-subsequence-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false

namespace AegisSpec.MaximumLength

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def StrictInc (l : List Nat) : Prop := l.Pairwise (· < ·)

def IsIndexSeq (nums : Slice Std.I64) (is : List (Fin (vals nums).length)) : Prop :=
  StrictInc (is.map fun i => i.val)

def valuesAt (nums : Slice Std.I64) (is : List (Fin (vals nums).length)) : List Int :=
  is.map fun i => (vals nums).get i

def IsSubsequence (nums : Slice Std.I64) (sub : List Int) : Prop :=
  ∃ is : List (Fin (vals nums).length), IsIndexSeq nums is ∧ valuesAt nums is = sub

def ValidSeq (sub : List Int) : Prop :=
  ∃ b : Int, (b = 0 ∨ b = 1) ∧ ∀ p : Int × Int, p ∈ sub.zip sub.tail → (p.1 + p.2) % 2 = b

def ValidLengths (nums : Slice Std.I64) : Set Nat :=
  {k | ∃ sub : List Int, sub.length = k ∧ IsSubsequence nums sub ∧ ValidSeq sub}

def oddCount (nums : Slice Std.I64) : Nat :=
  (vals nums).countP fun x => decide (x % 2 = 1)

def evenCount (nums : Slice Std.I64) : Nat :=
  (vals nums).countP fun x => decide (x % 2 = 0)

def maxClassCount (nums : Slice Std.I64) : Nat := max (oddCount nums) (evenCount nums)

def alternationCount (nums : Slice Std.I64) : Nat :=
  ((vals nums).zip (vals nums).tail).countP fun p => decide (p.1 % 2 ≠ p.2 % 2)

def blockCount (nums : Slice Std.I64) : Nat := 1 + alternationCount nums

def Pre (nums : Slice Std.I64) : Prop :=
  2 ≤ (vals nums).length ∧ (vals nums).length ≤ 200000 ∧
    ∀ x : Int, x ∈ vals nums → 1 ≤ x ∧ x ≤ 10000000

def AllSameParity (nums : Slice Std.I64) : Prop :=
  (∀ x : Int, x ∈ vals nums → x % 2 = 0) ∨ (∀ x : Int, x ∈ vals nums → x % 2 = 1)

/-- The function returns a result r and r (as an integer) equals the maximum length of a valid subsequence of nums. Here a sequence sub of length k is a subsequence of nums iff there exist indices i_0 < i_1 < ... < i_{k-1} such that 0 <= i_j < len(nums) and sub[j] = nums[i_j] for every 0 <= j < k. Such a sub is valid iff there exists b in {0,1} such that for every 0 <= j < k-1, (sub[j] + sub[j+1]) mod 2 = b. The maximum is over all k >= 0 for which a valid subsequence of length k exists.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_1 (nums : Slice Std.I64) (h : Pre nums) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      ∃ k : Nat, IsGreatest (ValidLengths nums) k ∧ r.val = (k : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      ∃ k : Nat, IsGreatest (ValidLengths nums) k ∧ r.val = (k : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_2 (nums : Slice Std.I64) (h : Pre nums) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_3 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      r.val ≤ (vals nums).length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      r.val ≤ (vals nums).length) := by
  sorry

/-- Whenever the function returns a result r, r >= 2.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_4 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r → 2 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r → 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= max(O, E), where O = #{i | 0 <= i < len(nums) and nums[i] is odd} and E = #{i | 0 <= i < len(nums) and nums[i] is even}.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_5 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ↑(maxClassCount nums) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ↑(maxClassCount nums) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= R, where R = 1 + #{i | 0 <= i < len(nums)-1 and (nums[i] mod 2) != (nums[i+1] mod 2)}. Equivalently, R is the number of maximal non-empty contiguous blocks of nums all of whose entries have the same parity.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_6 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ↑(blockCount nums) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ↑(blockCount nums) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = len(nums).
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. All entries of nums have the same parity (either every nums[i] is odd or every nums[i] is even). -/
theorem spec_7 (nums : Slice Std.I64) (h : Pre nums) (hpar : AllSameParity nums) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      r.val = (vals nums).length := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums) (hpar : AllSameParity nums), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧
      r.val = (vals nums).length) := by
  sorry

/-- The function returns a result r and r = 2.
  Preconditions: len(nums) = 2 and for i=0,1, 1 <= nums[i] <= 10000000. -/
theorem spec_8 (nums : Slice Std.I64) (h : Pre nums) (hlen : (vals nums).length = 2) :
    ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧ r.val = 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums) (hlen : (vals nums).length = 2), ∃ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r ∧ r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, there exist indices i_0 < i_1 < ... < i_{r-1} with 0 <= i_j < len(nums) such that the sequence (nums[i_0], nums[i_1], ..., nums[i_{r-1}]) is valid, i.e. there exists b in {0,1} with (nums[i_j] + nums[i_{j+1}]) mod 2 = b for every 0 <= j < r-1.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_9 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ∃ is : List (Fin (vals nums).length),
        IsIndexSeq nums is ∧ (is.length : Int) = r.val ∧ ValidSeq (valuesAt nums is) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ∃ is : List (Fin (vals nums).length),
        IsIndexSeq nums is ∧ (is.length : Int) = r.val ∧ ValidSeq (valuesAt nums is)) := by
  sorry

/-- Whenever the function returns a result r, for every k >= 0 and every indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums), if there exists b in {0,1} such that (nums[i_j] + nums[i_{j+1}]) mod 2 = b for every 0 <= j < k-1, then k <= r.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_10 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ∀ (k : Nat) (is : List (Fin (vals nums).length)),
        is.length = k → IsIndexSeq nums is → ValidSeq (valuesAt nums is) → (k : Int) ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      ∀ (k : Nat) (is : List (Fin (vals nums).length)),
        is.length = k → IsIndexSeq nums is → ValidSeq (valuesAt nums is) → (k : Int) ≤ r.val) := by
  sorry

/-- Whenever maximum_length(nums) returns a result r and maximum_length(nums') returns a result r', one has r = r'.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. Let nums' be any integer array with len(nums') = len(nums), 2 <= len(nums') <= 200000, for every i, 1 <= nums'[i] <= 10000000, and for every i with 0 <= i < len(nums), nums'[i] mod 2 = nums[i] mod 2. -/
theorem spec_11 (nums nums' : Slice Std.I64) (h : Pre nums) (h' : Pre nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hpar : ∀ p : Int × Int, p ∈ (vals nums).zip (vals nums') → p.1 % 2 = p.2 % 2) :
    ∀ r r' : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      Aegis.MaximumLength.maximum_length nums' = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (h : Pre nums) (h' : Pre nums')
    (hlen : (vals nums').length = (vals nums).length)
    (hpar : ∀ p : Int × Int, p ∈ (vals nums).zip (vals nums') → p.1 % 2 = p.2 % 2), ∀ r r' : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      Aegis.MaximumLength.maximum_length nums' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, r <= max(max(O, E), R), where O = #{i | 0 <= i < len(nums) and nums[i] is odd}, E = #{i | 0 <= i < len(nums) and nums[i] is even}, and R = 1 + #{i | 0 <= i < len(nums)-1 and (nums[i] mod 2) != (nums[i+1] mod 2)}.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_12 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      r.val ≤ ↑(max (maxClassCount nums) (blockCount nums)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      r.val ≤ ↑(max (maxClassCount nums) (blockCount nums))) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums) if and only if there exists b in {0,1} such that for every i with 0 <= i < len(nums)-1, (nums[i] + nums[i+1]) mod 2 = b.
  Preconditions: 2 <= len(nums) <= 200000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000000. -/
theorem spec_13 (nums : Slice Std.I64) (h : Pre nums) :
    ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      (r.val = (vals nums).length ↔ ValidSeq (vals nums)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : Pre nums), ∀ r : Std.I64, Aegis.MaximumLength.maximum_length nums = ok r →
      (r.val = (vals nums).length ↔ ValidSeq (vals nums))) := by
  sorry

end AegisSpec.MaximumLength
