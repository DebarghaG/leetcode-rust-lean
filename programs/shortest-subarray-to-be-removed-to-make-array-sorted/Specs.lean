import Aegis.FindLengthOfShortestSubarray.Code.Funs

/-!
# Specifications of `Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray`

LeetCode problem `shortest-subarray-to-be-removed-to-make-array-sorted`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLengthOfShortestSubarray

def content (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def elem (arr : Slice Std.I64) (i : Nat) : Int := (content arr).getD i 0

def NonDecreasing (l : List Int) : Prop :=
  ∀ i : Nat, i + 1 < l.length → l.getD i 0 ≤ l.getD (i + 1) 0

def rem (l : List Int) (lo hi : Nat) : List Int := l.take lo ++ l.drop hi

def IsRemLen (l : List Int) (k : Nat) : Prop :=
  ∃ lo hi : Nat, lo ≤ hi ∧ hi ≤ l.length ∧ k = hi - lo ∧ NonDecreasing (rem l lo hi)

def IsShortestRem (l : List Int) (k : Nat) : Prop :=
  IsRemLen l k ∧ ∀ k' : Nat, IsRemLen l k' → k ≤ k'

def SplitOk (l : List Int) (p q : Nat) : Prop :=
  p + q ≤ l.length ∧
    NonDecreasing (l.take p) ∧
    NonDecreasing (l.drop (l.length - q)) ∧
    (0 < p → 0 < q → l.getD (p - 1) 0 ≤ l.getD (l.length - q) 0)

def IsMaxSplit (l : List Int) (M : Nat) : Prop :=
  (∃ p q : Nat, SplitOk l p q ∧ M = p + q) ∧ ∀ p q : Nat, SplitOk l p q → p + q ≤ M

def descentCount (l : List Int) : Nat :=
  ((List.range (l.length - 1)).filter (fun i => l.getD (i + 1) 0 < l.getD i 0)).length

/-- The function returns a result r (it does not fail) such that r equals the minimum of the set { r_idx - l | 0 <= l <= r_idx <= n and Rem(l, r_idx) is non-decreasing }, where for 0 <= l <= r_idx <= n, Rem(l, r_idx) denotes the sequence arr[0], arr[1], ..., arr[l-1], arr[r_idx], arr[r_idx+1], ..., arr[n-1] (with empty parts when l=0 or r_idx=n). The set is non-empty because choosing l=0 and r_idx=n-1 leaves the single element arr[n-1], which is non-decreasing.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_1 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat, IsShortestRem (content arr) k ∧ r.val = (k : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat, IsShortestRem (content arr) k ∧ r.val = (k : Int)) := by
  sorry

/-- The function returns a result r and 0 <= r <= n - 1.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_2 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (n : Int) - 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        0 ≤ r.val ∧ r.val ≤ (n : Int) - 1) := by
  sorry

/-- The function returns a result r and r = 0 if and only if the whole array arr is non-decreasing, i.e., for every i with 0 <= i < n-1, arr[i] <= arr[i+1].
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_3 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        (r.val = 0 ↔ NonDecreasing (content arr)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        (r.val = 0 ↔ NonDecreasing (content arr))) := by
  sorry

/-- The function returns a result r and r = n - 1.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9; and for every i with 0 <= i < n-1, arr[i] > arr[i+1] (the array is strictly decreasing; vacuously true for n=1). -/
theorem spec_4 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9)
    (hdec : ∀ i : Nat, i + 1 < n → elem arr (i + 1) < elem arr i) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        r.val = (n : Int) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9)
    (hdec : ∀ i : Nat, i + 1 < n → elem arr (i + 1) < elem arr i), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        r.val = (n : Int) - 1) := by
  sorry

/-- The function returns a result r and there exist integers l and r_idx with 0 <= l <= r_idx <= n such that r_idx - l = r and Rem(l, r_idx) is non-decreasing, where Rem(l, r_idx) is the concatenation of arr[0..l] and arr[r_idx..n] as defined in spec_1.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_5 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ l r_idx : Nat,
          l ≤ r_idx ∧ r_idx ≤ n ∧ r.val = (r_idx : Int) - (l : Int) ∧
            NonDecreasing (rem (content arr) l r_idx) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ l r_idx : Nat,
          l ≤ r_idx ∧ r_idx ≤ n ∧ r.val = (r_idx : Int) - (l : Int) ∧
            NonDecreasing (rem (content arr) l r_idx)) := by
  sorry

/-- The function returns a result r and for every pair of integers l and r_idx with 0 <= l <= r_idx <= n and r_idx - l < r, the sequence Rem(l, r_idx) (the concatenation of arr[0..l] and arr[r_idx..n]) is not non-decreasing; that is, there exist consecutive elements x, y in Rem(l, r_idx) with x > y.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_6 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∀ l r_idx : Nat, l ≤ r_idx → r_idx ≤ n →
          (r_idx : Int) - (l : Int) < r.val → ¬ NonDecreasing (rem (content arr) l r_idx) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∀ l r_idx : Nat, l ≤ r_idx → r_idx ≤ n →
          (r_idx : Int) - (l : Int) < r.val → ¬ NonDecreasing (rem (content arr) l r_idx)) := by
  sorry

/-- The function returns a result r and r = n - M, where M is the maximum over all pairs (p, q) of integers with 0 <= p, 0 <= q, and p + q <= n such that (a) the prefix arr[0..p] is non-decreasing (for all i with 0 <= i < p-1, arr[i] <= arr[i+1]), (b) the suffix arr[n-q..n] is non-decreasing (for all i with n-q <= i < n-1, arr[i] <= arr[i+1]), and (c) if p > 0 and q > 0 then arr[p-1] <= arr[n-q], of the value p + q. (The set of such pairs is non-empty, e.g., p=q=0, so M is well-defined.)
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_7 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ M : Nat, IsMaxSplit (content arr) M ∧ r.val = (n : Int) - (M : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ M : Nat, IsMaxSplit (content arr) M ∧ r.val = (n : Int) - (M : Int)) := by
  sorry

/-- Let r be the result returned by the function on arr. For every strictly increasing function f: Z -> Z (i.e., x < y implies f(x) < f(y)) such that f(arr[i]) is in the range [-2^63, 2^63-1] for all i with 0 <= i < n, define brr[i] = f(arr[i]) for 0 <= i < n. Then the minimum length of a contiguous subarray whose removal from brr leaves a non-decreasing sequence is also r.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_8 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat,
          IsShortestRem (content arr) k ∧ r.val = (k : Int) ∧
            ∀ f : Int → Int,
              (∀ x y : Int, x < y → f x < f y) →
                (∀ i : Nat, i < n → -((2 : Int) ^ 63) ≤ f (elem arr i) ∧
                  f (elem arr i) ≤ (2 : Int) ^ 63 - 1) →
                IsShortestRem ((List.range n).map (fun i => f (elem arr i))) k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat,
          IsShortestRem (content arr) k ∧ r.val = (k : Int) ∧
            ∀ f : Int → Int,
              (∀ x y : Int, x < y → f x < f y) →
                (∀ i : Nat, i < n → -((2 : Int) ^ 63) ≤ f (elem arr i) ∧
                  f (elem arr i) ≤ (2 : Int) ^ 63 - 1) →
                IsShortestRem ((List.range n).map (fun i => f (elem arr i))) k) := by
  sorry

/-- For every arr satisfying the preconditions, the function returns a result (i.e., it does not fail, panic, overflow, or access out-of-bounds memory).
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_9 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r) := by
  sorry

/-- Let r be the result returned by the function on arr. Define brr by brr[i] = -arr[n-1-i] for 0 <= i < n. (Since 0 <= arr[i] <= 10^9, -arr[i] is in [-10^9, 0], which fits in i64.) Then the minimum length of a contiguous subarray whose removal from brr leaves a non-decreasing sequence is also r.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_10 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat,
          IsShortestRem (content arr) k ∧ r.val = (k : Int) ∧
            IsShortestRem ((List.range n).map (fun i => -(elem arr (n - 1 - i)))) k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ∃ k : Nat,
          IsShortestRem (content arr) k ∧ r.val = (k : Int) ∧
            IsShortestRem ((List.range n).map (fun i => -(elem arr (n - 1 - i)))) k) := by
  sorry

/-- Let D be the number of descents in arr, i.e., D = |{ i | 0 <= i < n-1 and arr[i] > arr[i+1] }|. The function returns a result r and r >= D.
  Preconditions: n = len(arr); 1 <= n <= 10^5; for every i with 0 <= i < n, 0 <= arr[i] <= 10^9. -/
theorem spec_11 (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9) :
    ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ((descentCount (content arr) : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (n : Nat)
    (hn : n = arr.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 10 ^ 5)
    (hb : ∀ i : Nat, i < n → 0 ≤ elem arr i ∧ elem arr i ≤ 10 ^ 9), ∃ r : Std.I64,
      Aegis.FindLengthOfShortestSubarray.find_length_of_shortest_subarray arr = ok r ∧
        ((descentCount (content arr) : Nat) : Int) ≤ r.val) := by
  sorry

end AegisSpec.FindLengthOfShortestSubarray
