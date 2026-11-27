import Aegis.NumOfSubarrays.Code.Funs

/-!
# Specifications of `Aegis.NumOfSubarrays.num_of_subarrays`

LeetCode problem `number-of-sub-arrays-with-odd-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumOfSubarrays

def MOD : Nat := 1000000007

def modM (k : Nat) : Nat := k % MOD

def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

@[reducible] def IsOdd (z : Int) : Prop := z % 2 = 1

@[reducible] def IsEven (z : Int) : Prop := z % 2 = 0

def entryAt (l : List Std.I64) (i : Nat) (h : i < l.length) : Int := (l[i]'h).val

def windowSum (l : List Std.I64) (left right : Nat) : Int :=
  (((vals l).drop left).take (right - left)).sum

def prefixParity (l : List Std.I64) (k : Nat) : Int := windowSum l 0 k % 2

def IsOddAt (l : List Std.I64) (i : Nat) : Prop := ∃ h : i < l.length, IsOdd (l[i]'h)

def indexPairs (n : Nat) : List (Nat × Nat) :=
  (List.range (n + 1)).product (List.range (n + 1))

def oddSubarrayCount (l : List Std.I64) : Nat :=
  (indexPairs l.length).countP
    (fun p => decide (p.1 < p.2 ∧ IsOdd (windowSum l p.1 p.2)))

def oddPrefixCount (l : List Std.I64) : Nat :=
  (List.range (l.length + 1)).countP (fun k => decide (IsOdd (windowSum l 0 k)))

def prefixParityDiffCount (l : List Std.I64) : Nat :=
  (indexPairs l.length).countP
    (fun p => decide (p.1 < p.2 ∧ prefixParity l p.1 ≠ prefixParity l p.2))

def LengthBounds (l : List Std.I64) : Prop := 1 ≤ l.length ∧ l.length ≤ 100000

def EntriesIn1To100 (l : List Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < l.length), 1 ≤ entryAt l i h ∧ entryAt l i h ≤ 100

def EntriesIn1To100Even (l : List Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < l.length), IsEven (entryAt l i h) ∧ 1 ≤ entryAt l i h ∧ entryAt l i h ≤ 100

def EntriesIn1To100Odd (l : List Std.I64) : Prop :=
  ∀ (i : Nat) (h : i < l.length), IsOdd (entryAt l i h) ∧ 1 ≤ entryAt l i h ∧ entryAt l i h ≤ 100

def SameParity (l₁ l₂ : List Std.I64) : Prop :=
  l₁.length = l₂.length ∧
    ∀ (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      entryAt l₁ i h₁ % 2 = entryAt l₂ i h₂ % 2

def ExactlyOneOdd (l : List Std.I64) : Prop := ∃! i : Nat, IsOddAt l i

/-- Let n = len(arr). Let C be the number of pairs (l, r) of integers such that 0 <= l < r <= n and the sum arr[l] + arr[l+1] + ... + arr[r-1] is odd. The function returns a result ans and ans = C mod 1000000007, where C mod 1000000007 is the unique integer in [0, 1000000007) congruent to C modulo 1000000007.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_1 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (oddSubarrayCount arr.val) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (oddSubarrayCount arr.val) : Int)) := by
  sorry

/-- The function returns a result ans and 0 <= ans < 1000000007.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_2 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        0 ≤ ans.val ∧ ans.val < 1000000007 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        0 ≤ ans.val ∧ ans.val < 1000000007) := by
  sorry

/-- For every arr satisfying the preconditions, the function returns a result ans; it does not overflow, trap, panic, or fail.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_3 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64, Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64, Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans) := by
  sorry

/-- The function returns a result ans and ans = 0.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), arr[i] is even and 1 <= arr[i] <= 100. -/
theorem spec_4 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100Even arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧ ans.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100Even arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧ ans.val = 0) := by
  sorry

/-- Let n = len(arr). The function returns a result ans and ans = (((n + 1) / 2) * ((n + 2) / 2)) mod 1000000007, where / denotes integer division rounding down.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), arr[i] is odd and 1 <= arr[i] <= 100. -/
theorem spec_5 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100Odd arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (((arr.val.length + 1) / 2) * ((arr.val.length + 2) / 2)) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100Odd arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (((arr.val.length + 1) / 2) * ((arr.val.length + 2) / 2)) : Int)) := by
  sorry

/-- The function returns a result ans and ans = 2 if arr[0] is odd or arr[1] is odd, and ans = 0 otherwise.
  Preconditions: arr is a finite list of 64-bit integers with len(arr) = 2 and, for i = 0 and i = 1, 1 <= arr[i] <= 100. -/
theorem spec_6 (arr : Slice Std.I64) (hlen : arr.val.length = 2)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val =
          (if IsOdd (entryAt arr.val 0 (by simp [hlen])) ∨
              IsOdd (entryAt arr.val 1 (by simp [hlen]))
           then 2 else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : arr.val.length = 2)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val =
          (if IsOdd (entryAt arr.val 0 (by simp [hlen])) ∨
              IsOdd (entryAt arr.val 1 (by simp [hlen]))
           then 2 else 0)) := by
  sorry

/-- When the function is called on arr it returns a result ans_arr, and when it is called on b it returns a result ans_b, and ans_arr = ans_b.
  Preconditions: arr and b are finite lists of 64-bit integers, each satisfying 1 <= length <= 100000 with entries in [1, 100], and len(arr) = len(b) and, for every integer i with 0 <= i < len(arr), arr[i] mod 2 = b[i] mod 2. -/
theorem spec_7 (arr b : Slice Std.I64) (hlen_arr : LengthBounds arr.val)
    (hval_arr : EntriesIn1To100 arr.val) (hlen_b : LengthBounds b.val)
    (hval_b : EntriesIn1To100 b.val) (hpar : SameParity arr.val b.val) :
    ∃ ans_arr ans_b : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans_arr ∧
        Aegis.NumOfSubarrays.num_of_subarrays b = ok ans_b ∧
          ans_arr.val = ans_b.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr b : Slice Std.I64) (hlen_arr : LengthBounds arr.val)
    (hval_arr : EntriesIn1To100 arr.val) (hlen_b : LengthBounds b.val)
    (hval_b : EntriesIn1To100 b.val) (hpar : SameParity arr.val b.val), ∃ ans_arr ans_b : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans_arr ∧
        Aegis.NumOfSubarrays.num_of_subarrays b = ok ans_b ∧
          ans_arr.val = ans_b.val) := by
  sorry

/-- Let n = len(arr) and let rev be the list of length n with rev[i] = arr[n - 1 - i] for 0 <= i < n. When the function is called on arr it returns a result ans, and when it is called on rev it returns a result ans_rev, and ans = ans_rev.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_8 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ∀ rev : Slice Std.I64, rev.val = arr.val.reverse →
          ∃ ans_rev : Std.I64,
            Aegis.NumOfSubarrays.num_of_subarrays rev = ok ans_rev ∧
              ans.val = ans_rev.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ∀ rev : Slice Std.I64, rev.val = arr.val.reverse →
          ∃ ans_rev : Std.I64,
            Aegis.NumOfSubarrays.num_of_subarrays rev = ok ans_rev ∧
              ans.val = ans_rev.val) := by
  sorry

/-- Let n = len(arr). Define P(0) = 0 and, for 1 <= k <= n, P(k) = (arr[0] + arr[1] + ... + arr[k-1]) mod 2. Let D be the number of pairs (i, j) of integers such that 0 <= i < j <= n and P(i) != P(j). The function returns a result ans and ans = D mod 1000000007.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_9 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (prefixParityDiffCount arr.val) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val = (modM (prefixParityDiffCount arr.val) : Int)) := by
  sorry

/-- Let n = len(arr). Let A be the number of integers k with 0 <= k <= n such that arr[0] + ... + arr[k-1] is odd, where the sum for k = 0 is the empty sum 0. Let B = n + 1 - A. The function returns a result ans and ans = (A * B) mod 1000000007.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_10 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val =
          (modM (oddPrefixCount arr.val *
              (arr.val.length + 1 - oddPrefixCount arr.val)) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ans.val =
          (modM (oddPrefixCount arr.val *
              (arr.val.length + 1 - oddPrefixCount arr.val)) : Int)) := by
  sorry

/-- Whenever the function returns a result ans, if ans != 0 then there exist integers l and r with 0 <= l < r <= len(arr) such that arr[l] + arr[l+1] + ... + arr[r-1] is odd.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_11 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∀ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans → ans.val ≠ 0 →
        ∃ l r : Nat, l < r ∧ r ≤ arr.val.length ∧ IsOdd (windowSum arr.val l r) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∀ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans → ans.val ≠ 0 →
        ∃ l r : Nat, l < r ∧ r ≤ arr.val.length ∧ IsOdd (windowSum arr.val l r)) := by
  sorry

/-- The function returns a result ans and if ans = 0 then, for every integer i with 0 <= i < len(arr), arr[i] is even.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. -/
theorem spec_12 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        (ans.val = 0 →
          ∀ (i : Nat) (h : i < arr.val.length), IsEven (entryAt arr.val i h)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        (ans.val = 0 →
          ∀ (i : Nat) (h : i < arr.val.length), IsEven (entryAt arr.val i h))) := by
  sorry

/-- Let n = len(arr) and let p be the unique index with 0 <= p < n such that arr[p] is odd. The function returns a result ans and ans = ((p + 1) * (n - p)) mod 1000000007.
  Preconditions: arr is a finite list of 64-bit integers with 1 <= len(arr) <= 100000 and, for every integer i with 0 <= i < len(arr), 1 <= arr[i] <= 100. There is exactly one integer p with 0 <= p < len(arr) such that arr[p] is odd. -/
theorem spec_13 (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) (hunique : ExactlyOneOdd arr.val) :
    ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ∃ p : Nat,
          IsOddAt arr.val p ∧
            ans.val = (modM ((p + 1) * (arr.val.length - p)) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice Std.I64) (hlen : LengthBounds arr.val)
    (hval : EntriesIn1To100 arr.val) (hunique : ExactlyOneOdd arr.val), ∃ ans : Std.I64,
      Aegis.NumOfSubarrays.num_of_subarrays arr = ok ans ∧
        ∃ p : Nat,
          IsOddAt arr.val p ∧
            ans.val = (modM ((p + 1) * (arr.val.length - p)) : Int)) := by
  sorry

end AegisSpec.NumOfSubarrays
