import Aegis.LongestNiceSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestNiceSubarray.longest_nice_subarray`

LeetCode problem `longest-nice-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestNiceSubarray

def len (nums : Slice Std.I64) : Nat := nums.val.length

def elem (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def bit (x : Int) (b : Nat) : Prop := x.testBit b = true

def andZero (x : Int) (y : Int) : Prop := ∀ b : Nat, ¬ (bit x b ∧ bit y b)

def nice (nums : Slice Std.I64) (s L : Nat) : Prop :=
  ∀ i j : Nat, i < j → j < L → andZero (elem nums (s + i)) (elem nums (s + j))

def pairwiseDistinct (nums : Slice Std.I64) (s L : Nat) : Prop :=
  ∀ i j : Nat, i < j → j < L → elem nums (s + i) ≠ elem nums (s + j)

def popcount (x : Int) : Nat := ((List.range 63).filter (fun b => x.testBit b)).length

def orAll (nums : Slice Std.I64) : Int :=
  Int.ofNat <|
    (List.range 63).foldl
      (fun acc b => if nums.val.any (fun x => x.val.testBit b) then acc + 2 ^ b else acc) 0

def InputOK (nums : Slice Std.I64) : Prop :=
  1 ≤ len nums ∧ len nums ≤ 100000 ∧
    ∀ i, i < len nums → 1 ≤ elem nums i ∧ elem nums i ≤ 1000000000

/-- Whenever the function returns a result r, r is the length of a longest nice subarray of nums. Here a contiguous subarray nums[s..s+L) is nice when 0 <= s, 0 <= L, s+L <= n, and for every i,j with 0 <= i < j < L, (nums[s+i] AND nums[s+j]) = 0. Thus: (1) there exists s with 0 <= s, 0 <= r, and s+r <= n such that nums[s..s+r) is nice; and (2) for every s and L with 0 <= s, 0 <= L, and s+L <= n, if nums[s..s+L) is nice then L <= r.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ L : Nat, r.val = (L : Int) ∧
        (∃ s : Nat, s + L ≤ len nums ∧ nice nums s L) ∧
        (∀ s L' : Nat, s + L' ≤ len nums → nice nums s L' → L' ≤ L) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ L : Nat, r.val = (L : Int) ∧
        (∃ s : Nat, s + L ≤ len nums ∧ nice nums s L) ∧
        (∀ s L' : Nat, s + L' ≤ len nums → nice nums s L' → L' ≤ L)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; in particular it does not panic and no arithmetic overflow or out-of-bounds access occurs.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (h : InputOK nums) :
    ∃ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∃ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= n.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (1 : Int) ≤ r.val ∧ r.val ≤ (len nums : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (1 : Int) ≤ r.val ∧ r.val ≤ (len nums : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= popcount(nums[0] OR nums[1] OR ... OR nums[n-1]), where popcount(x) is the number of bit positions b with 0 <= b < 63 such that bit b of x is 1.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      r.val ≤ (popcount (orAll nums) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      r.val ≤ (popcount (orAll nums) : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists an index s such that 0 <= s, 0 <= r, s+r <= n, and for every i,j with 0 <= i < j < r, (nums[s+i] AND nums[s+j]) = 0.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ s L : Nat, r.val = (L : Int) ∧ s + L ≤ len nums ∧ nice nums s L := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ s L : Nat, r.val = (L : Int) ∧ s + L ≤ len nums ∧ nice nums s L) := by
  sorry

/-- Whenever the function returns a result r, for every index s and length L with 0 <= s, 0 <= L, and s+L <= n, if (nums[s+i] AND nums[s+j]) = 0 for every i,j with 0 <= i < j < L, then L <= r.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∀ s L : Nat, s + L ≤ len nums → nice nums s L → (L : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∀ s L : Nat, s + L ≤ len nums → nice nums s L → (L : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if (nums[i] AND nums[j]) = 0 for every i,j with 0 <= i < j < n.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (r.val = (len nums : Int) ↔ nice nums 0 (len nums)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (r.val = (len nums : Int) ↔ nice nums 0 (len nums))) := by
  sorry

/-- Whenever the function returns a result r and n >= 2, r = 1 if and only if (nums[i] AND nums[i+1]) != 0 for every i with 0 <= i < n-1.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      2 ≤ len nums →
        (r.val = 1 ↔ ∀ i, i < len nums - 1 → ¬ andZero (elem nums i) (elem nums (i + 1))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      2 ≤ len nums →
        (r.val = 1 ↔ ∀ i, i < len nums - 1 → ¬ andZero (elem nums i) (elem nums (i + 1)))) := by
  sorry

/-- Whenever the function returns a result r, there exists an index s such that 0 <= s, 0 <= r, s+r <= n, and for every bit position b with 0 <= b < 63, at most one index i with 0 <= i < r has bit b set in nums[s+i].
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ s L : Nat, r.val = (L : Int) ∧ s + L ≤ len nums ∧
        ∀ b : Nat, b < 63 →
          ∀ i j : Nat, i < j → j < L →
            ¬ (bit (elem nums (s + i)) b ∧ bit (elem nums (s + j)) b) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      ∃ s L : Nat, r.val = (L : Int) ∧ s + L ≤ len nums ∧
        ∀ b : Nat, b < 63 →
          ∀ i j : Nat, i < j → j < L →
            ¬ (bit (elem nums (s + i)) b ∧ bit (elem nums (s + j)) b)) := by
  sorry

/-- Whenever the function returns a result r, if every nums[i] is a power of two (that is, for every i there exists b with 0 <= b < 63 and nums[i] = 2^b), then r is the maximum length of a contiguous subarray of nums whose values are pairwise distinct. Precisely: there exists s with 0 <= s, 0 <= r, and s+r <= n such that nums[s],...,nums[s+r-1] are pairwise distinct, and for every s and L with 0 <= s, 0 <= L, and s+L <= n, if nums[s],...,nums[s+L-1] are pairwise distinct then L <= r.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000000000. -/
theorem spec_10 (nums : Slice Std.I64) (h : InputOK nums) :
    ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (∀ i, i < len nums → ∃ b, b < 63 ∧ elem nums i = (2 : Int) ^ b) →
        ∃ L : Nat, r.val = (L : Int) ∧
          (∃ s : Nat, s + L ≤ len nums ∧ pairwiseDistinct nums s L) ∧
          (∀ s L' : Nat, s + L' ≤ len nums → pairwiseDistinct nums s L' → L' ≤ L) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (h : InputOK nums), ∀ r, Aegis.LongestNiceSubarray.longest_nice_subarray nums = ok r →
      (∀ i, i < len nums → ∃ b, b < 63 ∧ elem nums i = (2 : Int) ^ b) →
        ∃ L : Nat, r.val = (L : Int) ∧
          (∃ s : Nat, s + L ≤ len nums ∧ pairwiseDistinct nums s L) ∧
          (∀ s L' : Nat, s + L' ≤ len nums → pairwiseDistinct nums s L' → L' ≤ L)) := by
  sorry

end AegisSpec.LongestNiceSubarray
