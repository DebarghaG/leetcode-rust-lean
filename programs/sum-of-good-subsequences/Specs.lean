import Aegis.SumOfGoodSubsequences.Code.Funs

/-!
# Specifications of `Aegis.SumOfGoodSubsequences.sum_of_good_subsequences`

LeetCode problem `sum-of-good-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumOfGoodSubsequences

def M : Int := 1000000007

def valAt (nums : Slice Std.I64) (i : Fin nums.val.length) : Int :=
  (nums.val.get i).val

def entriesSum (nums : Slice Std.I64) : Int := (nums.val.map (fun x => x.val)).sum

@[reducible] def StepOK (nums : Slice Std.I64) (a b : Fin nums.val.length) : Prop :=
  a.val < b.val ∧ |valAt nums b - valAt nums a| = 1

def ChainAdj (nums : Slice Std.I64) : List (Fin nums.val.length) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => StepOK nums a b ∧ ChainAdj nums (b :: rest)

def chainAdjB (nums : Slice Std.I64) : List (Fin nums.val.length) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (StepOK nums a b) && chainAdjB nums (b :: rest)

def IsGoodIdxSeq (nums : Slice Std.I64) (s : List (Fin nums.val.length)) : Prop :=
  s ≠ [] ∧ ChainAdj nums s

def isGoodIdxSeqB (nums : Slice Std.I64) (s : List (Fin nums.val.length)) : Bool :=
  decide (s ≠ []) && chainAdjB nums s

def goodIdxSeqs (nums : Slice Std.I64) : Finset (List (Fin nums.val.length)) :=
  ((List.finRange nums.val.length).sublists.filter (isGoodIdxSeqB nums)).toFinset

def T (nums : Slice Std.I64) : Int :=
  (goodIdxSeqs nums).sum (fun s => (s.map (valAt nums)).sum)

def N (nums : Slice Std.I64) : Int :=
  (goodIdxSeqs nums).sum (fun s => (s.length : Int))

/-- Whenever the function returns a result r, define a good subsequence to be a non-empty increasing sequence of indices i_0 < i_1 < ... < i_{k-1} (k >= 1) such that for every j with 0 <= j < k-1, |nums[i_{j+1}] - nums[i_j]| = 1. Let T be the sum over all such index sequences of nums[i_0] + ... + nums[i_{k-1}], counting different index sequences separately. Then 0 <= r < M and r ≡ T (mod M); equivalently, r is the unique integer in [0, M-1] congruent to T modulo M.
  Preconditions: nums is a slice with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. Let M = 1000000007. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (T nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (T nums)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail by panic, out-of-bounds access, or 64-bit overflow.
  Preconditions: nums is a slice with 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∃ r : Std.I64, Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r : Std.I64, Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0] (and hence 0 <= r < M).
  Preconditions: len(nums) = 1 and 0 <= nums[0] <= 100000. Let M = 1000000007. -/
theorem spec_3 (nums : Slice Std.I64) (hlen : nums.val.length = 1)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧ r.val = (nums.val.get ⟨0, by omega⟩).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 1)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧ r.val = (nums.val.get ⟨0, by omega⟩).val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M and r ≡ n*c (mod M); equivalently r = (n*c) mod M.
  Preconditions: len(nums) = n with 1 <= n <= 100000, and there is c with 1 <= c <= 100000 such that nums[i] = c for every i with 0 <= i < n. Let M = 1000000007. -/
theorem spec_4 (nums : Slice Std.I64) (n : Nat) (c : Int)
    (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 100000)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = c)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val ((n : Int) * c) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat) (c : Int)
    (hlen : nums.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hc1 : 1 ≤ c) (hc2 : c ≤ 100000)
    (hconst : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = c)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val ((n : Int) * c)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: len(nums) >= 1 and nums[i] = 0 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (hlen : 1 ≤ nums.val.length)
    (hzero : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = 0)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 1 ≤ nums.val.length)
    (hzero : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = 0)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M and r ≡ D + (if |nums[1] - nums[0]| = 1 then D else 0) (mod M).
  Preconditions: len(nums) = 2, 0 <= nums[0] <= 100000, 0 <= nums[1] <= 100000. Let M = 1000000007 and D = nums[0] + nums[1]. -/
theorem spec_6 (nums : Slice Std.I64) (hlen : nums.val.length = 2)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M r.val
        ((nums.val.get ⟨0, by omega⟩).val + (nums.val.get ⟨1, by omega⟩).val +
          (if |(nums.val.get ⟨1, by omega⟩).val - (nums.val.get ⟨0, by omega⟩).val| = 1
           then (nums.val.get ⟨0, by omega⟩).val + (nums.val.get ⟨1, by omega⟩).val
           else 0)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 2)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M r.val
        ((nums.val.get ⟨0, by omega⟩).val + (nums.val.get ⟨1, by omega⟩).val +
          (if |(nums.val.get ⟨1, by omega⟩).val - (nums.val.get ⟨0, by omega⟩).val| = 1
           then (nums.val.get ⟨0, by omega⟩).val + (nums.val.get ⟨1, by omega⟩).val
           else 0))) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M and r ≡ (sum_{i=0}^{len(nums)-1} nums[i]) (mod M).
  Preconditions: 1 <= len(nums) <= 100000, 0 <= nums[i] <= 100000 for every i, and for every i,j with 0 <= i < j < len(nums), |nums[j] - nums[i]| != 1. Let M = 1000000007. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hno : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
      |(nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val| ≠ 1)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (entriesSum nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hno : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length), i < j →
      |(nums.val.get ⟨j, hj⟩).val - (nums.val.get ⟨i, hi⟩).val| ≠ 1)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (entriesSum nums)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M and r ≡ (sum_{i=0}^{n-1} (a+i)*(i+1)*(n-i)) (mod M).
  Preconditions: There are integers a and n such that n = len(nums) >= 1, 0 <= a, a+n-1 <= 100000, and nums[i] = a+i for every i with 0 <= i < n. Let M = 1000000007. -/
theorem spec_8 (nums : Slice Std.I64) (n : Nat) (a : Int)
    (hlen : nums.val.length = n) (hn : 1 ≤ n)
    (ha0 : 0 ≤ a) (han : a + (n : Int) - 1 ≤ 100000)
    (hseq : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = a + (i : Int))
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M r.val
        ((Finset.range n).sum
          (fun i => (a + (i : Int)) * ((i : Int) + 1) * ((n : Int) - (i : Int)))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : Nat) (a : Int)
    (hlen : nums.val.length = n) (hn : 1 ≤ n)
    (ha0 : 0 ≤ a) (han : a + (n : Int) - 1 ≤ 100000)
    (hseq : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums.val.get ⟨i, hi⟩).val = a + (i : Int))
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧
      Int.ModEq M r.val
        ((Finset.range n).sum
          (fun i => (a + (i : Int)) * ((i : Int) + 1) * ((n : Int) - (i : Int))))) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M and r ≡ 10*a + 4 (mod M).
  Preconditions: len(nums) = 3 and there is an integer a with 0 <= a <= 99999 such that nums[0] = a, nums[1] = a+1, and nums[2] = a. Let M = 1000000007. -/
theorem spec_9 (nums : Slice Std.I64) (a : Int)
    (hlen : nums.val.length = 3) (ha0 : 0 ≤ a) (ha1 : a ≤ 99999)
    (h0 : (nums.val.get ⟨0, by omega⟩).val = a)
    (h1 : (nums.val.get ⟨1, by omega⟩).val = a + 1)
    (h2 : (nums.val.get ⟨2, by omega⟩).val = a)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r) :
    0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (10 * a + 4) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (a : Int)
    (hlen : nums.val.length = 3) (ha0 : 0 ≤ a) (ha1 : a ≤ 99999)
    (h0 : (nums.val.get ⟨0, by omega⟩).val = a)
    (h1 : (nums.val.get ⟨1, by omega⟩).val = a + 1)
    (h2 : (nums.val.get ⟨2, by omega⟩).val = a)
    (r : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r), 0 ≤ r.val ∧ r.val < M ∧ Int.ModEq M r.val (10 * a + 4)) := by
  sorry

/-- Whenever the function returns a result r on nums and a result r' on ys, r = r'.
  Preconditions: 1 <= len(nums) <= 100000, 0 <= nums[i] <= 100000 for every i. Let ys be the slice with len(ys) = len(nums) and ys[i] = nums[len(nums)-1-i] for every i with 0 <= i < len(nums). Let M = 1000000007. -/
theorem spec_10 (nums ys : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hlen_ys : ys.val.length = nums.val.length)
    (hys : ∀ (i : Nat) (hi : i < nums.val.length),
      (ys.val.get ⟨i, by omega⟩).val =
        (nums.val.get ⟨nums.val.length - 1 - i, by omega⟩).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r)
    (hr' : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences ys = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums ys : Slice Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hlen_ys : ys.val.length = nums.val.length)
    (hys : ∀ (i : Nat) (hi : i < nums.val.length),
      (ys.val.get ⟨i, by omega⟩).val =
        (nums.val.get ⟨nums.val.length - 1 - i, by omega⟩).val)
    (r r' : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r)
    (hr' : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences ys = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r on nums and a result r' on nums', 0 <= r < M, 0 <= r' < M, and r' ≡ r + c*N(nums) (mod M).
  Preconditions: 1 <= len(nums) <= 100000, 0 <= nums[i] <= 100000 for every i. Let c be an integer and let nums' be defined by nums'[i] = nums[i] + c. Assume 0 <= nums'[i] <= 100000 for every i. Let M = 1000000007. A good index sequence of an array z is a non-empty increasing sequence i_0 < ... < i_{k-1} with |z[i_{j+1}] - z[i_j]| = 1 for every 0 <= j < k-1. Let N(nums) be the sum, over every good index sequence of nums, of its length, counting index sequences separately. -/
theorem spec_11 (nums nums' : Slice Std.I64) (c : Int)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hlen' : nums'.val.length = nums.val.length)
    (hshift : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums'.val.get ⟨i, by omega⟩).val = (nums.val.get ⟨i, hi⟩).val + c)
    (hbound' : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums'.val.get ⟨i, by omega⟩).val ∧ (nums'.val.get ⟨i, by omega⟩).val ≤ 100000)
    (r r' : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r)
    (hr' : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums' = ok r') :
    0 ≤ r.val ∧ r.val < M ∧ 0 ≤ r'.val ∧ r'.val < M ∧
      Int.ModEq M r'.val (r.val + c * N nums) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : Int)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hlen' : nums'.val.length = nums.val.length)
    (hshift : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums'.val.get ⟨i, by omega⟩).val = (nums.val.get ⟨i, hi⟩).val + c)
    (hbound' : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums'.val.get ⟨i, by omega⟩).val ∧ (nums'.val.get ⟨i, by omega⟩).val ≤ 100000)
    (r r' : Std.I64)
    (hr : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums = ok r)
    (hr' : Aegis.SumOfGoodSubsequences.sum_of_good_subsequences nums' = ok r'), 0 ≤ r.val ∧ r.val < M ∧ 0 ≤ r'.val ∧ r'.val < M ∧
      Int.ModEq M r'.val (r.val + c * N nums)) := by
  sorry

end AegisSpec.SumOfGoodSubsequences
