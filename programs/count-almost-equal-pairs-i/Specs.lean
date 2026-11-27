import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-almost-equal-pairs-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountPairs

namespace AegisSpec.CountPairs

noncomputable section

def sliceVals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def entry (s : Slice Std.I64) (k : Nat) : Int := (sliceVals s).getD k 0

def digitsRevAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n + 1 => (n + 1) % 10 :: digitsRevAux fuel ((n + 1) / 10)

def digitsRev (n : Nat) : List Nat := digitsRevAux (n + 1) n

def natDigits (n : Nat) : List Nat := if n = 0 then [0] else (digitsRev n).reverse

def digitsValue (ds : List Nat) : Nat := ds.foldl (fun acc d => acc * 10 + d) 0

def swapDigits (ds : List Nat) (p q : Nat) : List Nat :=
  match ds[p]?, ds[q]? with
  | some a, some b => (ds.set p b).set q a
  | _, _ => ds

def nearlyEqualNat (x y : Nat) : Prop :=
  x = y ∨
    (∃ p q, p < q ∧ q < (natDigits x).length ∧
      digitsValue (swapDigits (natDigits x) p q) = y) ∨
    (∃ p q, p < q ∧ q < (natDigits y).length ∧
      digitsValue (swapDigits (natDigits y) p q) = x)

def almostEqual (x y : Int) : Prop := nearlyEqualNat x.toNat y.toNat

def ind (p : Prop) : Nat := @ite Nat p (Classical.propDecidable p) 1 0

def pairCount (l : List Int) (rel : Int → Int → Prop) : Nat :=
  ((List.range l.length).map (fun i =>
    ((List.range l.length).map (fun j => ind (i < j ∧ rel (l.getD i 0) (l.getD j 0)))).sum)).sum

def countWith (l : List Int) (m : Nat) (pred : Int → Prop) : Nat :=
  ((List.range m).map (fun i => ind (pred (l.getD i 0)))).sum

def allPairs (n : Nat) : Nat := n * (n - 1) / 2

/-- The function returns a result r and r equals the number of pairs (i,j) with 0 <= i < j < len(nums) such that nums[i] and nums[j] are almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∃ r : Std.I64, count_pairs nums = ok r ∧
      r.val = (pairCount (sliceVals nums) almostEqual : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∃ r : Std.I64, count_pairs nums = ok r ∧
      r.val = (pairCount (sliceVals nums) almostEqual : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∃ r : Std.I64, count_pairs nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∃ r : Std.I64, count_pairs nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums)*(len(nums)-1)/2.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (allPairs nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r →
      0 ≤ r.val ∧ r.val ≤ (allPairs nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is at least the number E of pairs (i,j) with 0 <= i < j < len(nums) and nums[i] = nums[j].
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      (pairCount (sliceVals nums) (fun x y => x = y) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r →
      (pairCount (sliceVals nums) (fun x y => x = y) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums)*(len(nums)-1)/2.
  Preconditions: len(nums) is between 2 and 100 inclusive, for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6, and there is a positive integer c such that nums[k] = c for every 0 <= k < len(nums). -/
theorem spec_5 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hconst : ∃ c : Int, 0 < c ∧ ∀ k, k < nums.val.length → entry nums k = c) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      r.val = (allPairs nums.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hconst : ∃ c : Int, 0 < c ∧ ∀ k, k < nums.val.length → entry nums k = c), ∀ r : Std.I64, count_pairs nums = ok r →
      r.val = (allPairs nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if nums[0] and nums[1] are almost equal, and r = 0 otherwise. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6, and len(nums) = 2. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hlen : nums.val.length = 2) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      (almostEqual (entry nums 0) (entry nums 1) → r.val = 1) ∧
      (¬ almostEqual (entry nums 0) (entry nums 1) → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hlen : nums.val.length = 2), ∀ r : Std.I64, count_pairs nums = ok r →
      (almostEqual (entry nums 0) (entry nums 1) → r.val = 1) ∧
      (¬ almostEqual (entry nums 0) (entry nums 1) → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i,j with 0 <= i < j < len(nums), nums[i] and nums[j] are not almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      (r.val = 0 ↔
        ∀ i j, i < j → j < nums.val.length →
          ¬ almostEqual (entry nums i) (entry nums j)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r →
      (r.val = 0 ↔
        ∀ i j, i < j → j < nums.val.length →
          ¬ almostEqual (entry nums i) (entry nums j))) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums)*(len(nums)-1)/2 if and only if for every i,j with 0 <= i < j < len(nums), nums[i] and nums[j] are almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      (r.val = (allPairs nums.val.length : Int) ↔
        ∀ i j, i < j → j < nums.val.length →
          almostEqual (entry nums i) (entry nums j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r →
      (r.val = (allPairs nums.val.length : Int) ↔
        ∀ i j, i < j → j < nums.val.length →
          almostEqual (entry nums i) (entry nums j))) := by
  sorry

/-- If count_pairs(nums) returns r and count_pairs(nums') returns r', then r = r'.
  Preconditions: nums and nums' both satisfy: len is between 2 and 100 inclusive, and every entry is between 1 and 10^6 inclusive. Also len(nums') = len(nums), and there is a permutation pi of {0,...,len(nums)-1} such that nums'[k] = nums[pi(k)] for every 0 <= k < len(nums). -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hlo' : 2 ≤ nums'.val.length) (hhi' : nums'.val.length ≤ 100)
    (hrange' : ∀ k, k < nums'.val.length → 1 ≤ entry nums' k ∧ entry nums' k ≤ 1000000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ pi : Fin nums.val.length → Fin nums.val.length,
      Function.Bijective pi ∧
        ∀ k : Fin nums.val.length, entry nums' ↑k = entry nums ↑(pi k)) :
    ∀ r r' : Std.I64, count_pairs nums = ok r → count_pairs nums' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000)
    (hlo' : 2 ≤ nums'.val.length) (hhi' : nums'.val.length ≤ 100)
    (hrange' : ∀ k, k < nums'.val.length → 1 ≤ entry nums' k ∧ entry nums' k ≤ 1000000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : ∃ pi : Fin nums.val.length → Fin nums.val.length,
      Function.Bijective pi ∧
        ∀ k : Fin nums.val.length, entry nums' ↑k = entry nums ↑(pi k)), ∀ r r' : Std.I64, count_pairs nums = ok r → count_pairs nums' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Let n = len(nums) and let p be the slice consisting of nums[0], nums[1], ..., nums[n-2] (the first n-1 entries). If count_pairs(p) returns r_p and count_pairs(nums) returns r, then r = r_p + C, where C is the number of indices i with 0 <= i < n-1 such that nums[i] and nums[n-1] are almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 3 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ (p : Slice Std.I64) (r_p r : Std.I64),
      p.val = nums.val.take (nums.val.length - 1) →
      count_pairs p = ok r_p → count_pairs nums = ok r →
      r.val = r_p.val +
        (countWith (sliceVals nums) (nums.val.length - 1)
          (fun x => almostEqual x (entry nums (nums.val.length - 1))) : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 3 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ (p : Slice Std.I64) (r_p r : Std.I64),
      p.val = nums.val.take (nums.val.length - 1) →
      count_pairs p = ok r_p → count_pairs nums = ok r →
      r.val = r_p.val +
        (countWith (sliceVals nums) (nums.val.length - 1)
          (fun x => almostEqual x (entry nums (nums.val.length - 1))) : Int)) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exist indices i,j with 0 <= i < j < len(nums) such that nums[i] and nums[j] are almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r → 0 < r.val →
      ∃ i j, i < j ∧ j < nums.val.length ∧
        almostEqual (entry nums i) (entry nums j) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r → 0 < r.val →
      ∃ i j, i < j ∧ j < nums.val.length ∧
        almostEqual (entry nums i) (entry nums j)) := by
  sorry

/-- Whenever the function returns a result r and r < len(nums)*(len(nums)-1)/2, there exist indices i,j with 0 <= i < j < len(nums) such that nums[i] and nums[j] are not almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r → r.val < (allPairs nums.val.length : Int) →
      ∃ i j, i < j ∧ j < nums.val.length ∧
        ¬ almostEqual (entry nums i) (entry nums j) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r → r.val < (allPairs nums.val.length : Int) →
      ∃ i j, i < j ∧ j < nums.val.length ∧
        ¬ almostEqual (entry nums i) (entry nums j)) := by
  sorry

/-- Whenever the function returns a result r, r = E + U, where E is the number of pairs (i,j) with 0 <= i < j < len(nums) and nums[i] = nums[j], and U is the number of pairs (i,j) with 0 <= i < j < len(nums), nums[i] != nums[j], and nums[i] and nums[j] are almost equal. Here two positive integers x and y are almost equal if x = y, or there is a choice of one of x,y and two distinct positions in its usual decimal digit representation (written with no leading zero for the original number) such that swapping those two digits and reading the resulting digit string as a decimal number with leading zeros allowed (for example 03 denotes 3) gives the other integer.
  Preconditions: len(nums) is between 2 and 100 inclusive, and for every k with 0 <= k < len(nums), 1 <= nums[k] <= 10^6. -/
theorem spec_13 (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000) :
    ∀ r : Std.I64, count_pairs nums = ok r →
      r.val = ((pairCount (sliceVals nums) (fun x y => x = y) +
        pairCount (sliceVals nums) (fun x y => x ≠ y ∧ almostEqual x y) : Nat) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlo : 2 ≤ nums.val.length) (hhi : nums.val.length ≤ 100)
    (hrange : ∀ k, k < nums.val.length → 1 ≤ entry nums k ∧ entry nums k ≤ 1000000), ∀ r : Std.I64, count_pairs nums = ok r →
      r.val = ((pairCount (sliceVals nums) (fun x y => x = y) +
        pairCount (sliceVals nums) (fun x y => x ≠ y ∧ almostEqual x y) : Nat) : Int)) := by
  sorry

end

end AegisSpec.CountPairs
