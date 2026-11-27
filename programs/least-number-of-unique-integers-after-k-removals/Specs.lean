import Aegis.FindLeastNumOfUniqueInts.Code.Funs

/-!
# Specifications of `Aegis.FindLeastNumOfUniqueInts.find_least_num_of_unique_ints`

LeetCode problem `least-number-of-unique-integers-after-k-removals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindLeastNumOfUniqueInts

open Aegis.FindLeastNumOfUniqueInts (find_least_num_of_unique_ints)

def content (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def freq (l : List Int) (v : Int) : Nat := (l.filter (fun x => x = v)).length

def distinctVals (l : List Int) : Finset Int := l.toFinset

def numDistinct (l : List Int) : Nat := l.toFinset.card

def inBounds (l : List Int) : Prop := ∀ x ∈ l, 1 ≤ x ∧ x ≤ (10 ^ 9 : Int)

def allEqual (l : List Int) : Prop := ∀ x ∈ l, ∀ y ∈ l, x = y

def maxFreq (l : List Int) : Nat := (l.dedup.map (freq l)).foldr max 0

def minFreq (l : List Int) : Nat := (l.dedup.map (freq l)).foldr min (l.length + 1)

def maxPrefixLen (f : List Nat) (k : Nat) : Nat :=
  ((List.range (f.length + 1)).filter (fun q => (f.take q).sum ≤ k)).foldr max 0

def feasible (l : List Int) (k : Int) (x : Int → Int) : Prop :=
  (∀ v ∈ distinctVals l, 0 ≤ x v ∧ x v ≤ (freq l v : Int)) ∧
    (∑ v ∈ distinctVals l, x v) = k

def remainingCount (l : List Int) (x : Int → Int) : Nat :=
  ((distinctVals l).filter (fun v => x v < (freq l v : Int))).card

def achievable (arr : Slice Std.I64) (k : Int) : Set Int :=
  {y : Int | ∃ x : Int → Int, feasible (content arr) k x ∧ y = (remainingCount (content arr) x : Int)}

/-- The function returns a result r and r = min { |{v in D : count(v) - x_v > 0}| : for every v in D, x_v is an integer with 0 <= x_v <= count(v), and sum_{v in D} x_v = k }, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_1 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∃ r : Std.I64,
      find_least_num_of_unique_ints arr k = ok r ∧ IsLeast (achievable arr k.val) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∃ r : Std.I64,
      find_least_num_of_unique_ints arr k = ok r ∧ IsLeast (achievable arr k.val) r.val) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every arr and k satisfying the preconditions.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_2 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∃ r : Std.I64, find_least_num_of_unique_ints arr k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∃ r : Std.I64, find_least_num_of_unique_ints arr k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= max(0, m - k), where m is the number of distinct values occurring in arr.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_3 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      max 0 ((numDistinct (content arr) : Int) - k.val) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      max 0 ((numDistinct (content arr) : Int) - k.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= m, where m is the number of distinct values occurring in arr.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_4 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      r.val ≤ (numDistinct (content arr) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      r.val ≤ (numDistinct (content arr) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= len(arr) - k.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_5 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      r.val ≤ (arr.val.length : Int) - k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      r.val ≤ (arr.val.length : Int) - k.val) := by
  sorry

/-- Whenever k = 0 and the function returns a result r, r = m, where m is the number of distinct values occurring in arr.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_6 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → k.val = 0 →
      r.val = (numDistinct (content arr) : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → k.val = 0 →
      r.val = (numDistinct (content arr) : Int)) := by
  sorry

/-- Whenever k = len(arr) and the function returns a result r, r = 0.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_7 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      k.val = (arr.val.length : Int) → r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      k.val = (arr.val.length : Int) → r.val = 0) := by
  sorry

/-- Whenever all elements of arr are equal (so the number of distinct values in arr is 1) and the function returns a result r, r = 1 if k < len(arr), and r = 0 if k = len(arr).
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_8 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → allEqual (content arr) →
      (k.val < (arr.val.length : Int) → r.val = 1) ∧
        (k.val = (arr.val.length : Int) → r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → allEqual (content arr) →
      (k.val < (arr.val.length : Int) → r.val = 1) ∧
        (k.val = (arr.val.length : Int) → r.val = 0)) := by
  sorry

/-- Whenever the values arr[i] are pairwise distinct (so the number of distinct values in arr equals len(arr)) and the function returns a result r, r = len(arr) - k.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_9 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → (content arr).Nodup →
      r.val = (arr.val.length : Int) - k.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r → (content arr).Nodup →
      r.val = (arr.val.length : Int) - k.val) := by
  sorry

/-- Let r be the result returned by the function. There exist integers x_v, one for each distinct value v occurring in arr, such that 0 <= x_v <= count(v) for every v, sum_{v in D} x_v = k, and |{v in D : count(v) - x_v > 0}| = r, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with arr[i] = v.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_10 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∃ r : Std.I64,
      find_least_num_of_unique_ints arr k = ok r ∧
        ∃ x : Int → Int,
          feasible (content arr) k.val x ∧ (remainingCount (content arr) x : Int) = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∃ r : Std.I64,
      find_least_num_of_unique_ints arr k = ok r ∧
        ∃ x : Int → Int,
          feasible (content arr) k.val x ∧ (remainingCount (content arr) x : Int) = r.val) := by
  sorry

/-- Let r be the result returned by the function. For every choice of integers x_v, one for each distinct value v occurring in arr, satisfying 0 <= x_v <= count(v) for every v and sum_{v in D} x_v = k, one has |{v in D : count(v) - x_v > 0}| >= r, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with arr[i] = v.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_11 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      ∀ x : Int → Int, feasible (content arr) k.val x →
        r.val ≤ (remainingCount (content arr) x : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      ∀ x : Int → Int, feasible (content arr) k.val x →
        r.val ≤ (remainingCount (content arr) x : Int)) := by
  sorry

/-- Let f_1 <= f_2 <= ... <= f_m be the positive frequencies count(v) of the distinct values v occurring in arr, sorted in nondecreasing order, where m is the number of distinct values. Let q be the largest integer with 0 <= q <= m and sum_{i=1}^q f_i <= k, with the empty sum for q=0 equal to 0. Whenever the function returns a result r, r = m - q.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_12 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ f : List Nat, f.Pairwise (· ≤ ·) →
      f.Perm ((content arr).dedup.map (freq (content arr))) →
        ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
          r.val = (numDistinct (content arr) : Int) - (maxPrefixLen f k.val.toNat : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ f : List Nat, f.Pairwise (· ≤ ·) →
      f.Perm ((content arr).dedup.map (freq (content arr))) →
        ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
          r.val = (numDistinct (content arr) : Int) - (maxPrefixLen f k.val.toNat : Int)) := by
  sorry

/-- For every k1 and k2 with 0 <= k1 <= k2 <= len(arr), if the function returns r1 when called on arr with k1 and returns r2 when called on arr with k2, then r2 <= r1.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and the statement quantifies only over k1 and k2 with 0 <= k1 <= k2 <= len(arr). -/
theorem spec_13 (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr)) :
    ∀ k1 k2 : Std.I64, 0 ≤ k1.val → k1.val ≤ k2.val →
      k2.val ≤ (arr.val.length : Int) →
        ∀ r1 r2 : Std.I64,
          find_least_num_of_unique_ints arr k1 = ok r1 →
            find_least_num_of_unique_ints arr k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr)), ∀ k1 k2 : Std.I64, 0 ≤ k1.val → k1.val ≤ k2.val →
      k2.val ≤ (arr.val.length : Int) →
        ∀ r1 r2 : Std.I64,
          find_least_num_of_unique_ints arr k1 = ok r1 →
            find_least_num_of_unique_ints arr k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if k = len(arr).
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_14 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = 0 ↔ k.val = (arr.val.length : Int)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = 0 ↔ k.val = (arr.val.length : Int))) := by
  sorry

/-- Let D be the set of distinct values occurring in arr and let count(v) be the number of indices i with arr[i] = v. Whenever the function returns a result r, r = |D| if and only if k < min_{v in D} count(v).
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_15 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = (numDistinct (content arr) : Int) ↔ k.val < (minFreq (content arr) : Int)) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = (numDistinct (content arr) : Int) ↔ k.val < (minFreq (content arr) : Int))) := by
  sorry

/-- If the function returns r on input arr with k and returns r2 on input arr2 with the same k, then r2 = r.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; 0 <= k <= len(arr); and arr2 is any slice with len(arr2) = len(arr) such that for every value v, the number of indices i with 0 <= i < len(arr2) and arr2[i] = v equals the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
theorem spec_16 (arr arr2 : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int))
    (hlen2 : arr2.val.length = arr.val.length)
    (hcount : ∀ v : Int, freq (content arr2) v = freq (content arr) v) :
    ∀ r r2 : Std.I64,
      find_least_num_of_unique_ints arr k = ok r →
        find_least_num_of_unique_ints arr2 k = ok r2 → r2.val = r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (arr arr2 : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int))
    (hlen2 : arr2.val.length = arr.val.length)
    (hcount : ∀ v : Int, freq (content arr2) v = freq (content arr) v), ∀ r r2 : Std.I64,
      find_least_num_of_unique_ints arr k = ok r →
        find_least_num_of_unique_ints arr2 k = ok r2 → r2.val = r.val) := by
  sorry

/-- Let n = len(arr) and let M = max_{v in D} count(v), where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. Whenever the function returns a result r, r = 1 if and only if n - M <= k < n.
  Preconditions: len(arr) >= 1; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10^9; and 0 <= k <= len(arr). -/
theorem spec_17 (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)) :
    ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = 1 ↔
        (arr.val.length : Int) - (maxFreq (content arr) : Int) ≤ k.val ∧
          k.val < (arr.val.length : Int)) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ arr.val.length)
    (hrange : inBounds (content arr))
    (hk0 : 0 ≤ k.val) (hk1 : k.val ≤ (arr.val.length : Int)), ∀ r : Std.I64, find_least_num_of_unique_ints arr k = ok r →
      (r.val = 1 ↔
        (arr.val.length : Int) - (maxFreq (content arr) : Int) ≤ k.val ∧
          k.val < (arr.val.length : Int))) := by
  sorry

end AegisSpec.FindLeastNumOfUniqueInts
