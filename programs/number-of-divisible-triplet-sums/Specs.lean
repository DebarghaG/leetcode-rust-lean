import Aegis.DivisibleTripletCount.Code.Funs

/-!
# Specifications of `Aegis.DivisibleTripletCount.divisible_triplet_count`

LeetCode problem `number-of-divisible-triplet-sums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.DivisibleTripletCount (divisible_triplet_count)

namespace AegisSpec.DivisibleTripletCount

def valAt (l : List Std.I64) (i : Nat) : Int :=
  match l[i]? with
  | some x => x.val
  | none => 0

def indexTripleCount (l : List Std.I64) : Nat :=
  l.length.choose 3

def goodTripleCount (l : List Std.I64) (d : Int) : Nat :=
  ((List.range l.length).flatMap (fun i =>
    (List.range l.length).flatMap (fun j =>
      (List.range l.length).filter (fun k =>
        decide (i < j ∧ j < k ∧ (valAt l i + valAt l j + valAt l k) % d = 0))))).length

def evenCount (l : List Std.I64) : Nat :=
  l.countP (fun x => decide (x.val % 2 = 0))

def binom (n k : Nat) : Nat :=
  n.choose k

/-- Whenever the function returns a result r, r equals the number of triples (i,j,k) of indices such that 0 <= i < j < k < len(nums) and (nums[i] + nums[j] + nums[k]) mod d = 0. Here mod is remainder after division by the positive integer d, so this condition is equivalent to d dividing nums[i] + nums[j] + nums[k].
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9 -/
theorem spec_1 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val = (goodTripleCount nums.val d.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val = (goodTripleCount nums.val d.val : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r: it does not fail, panic, overflow, access out of bounds, or divide by zero.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9 -/
theorem spec_2 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, divisible_triplet_count nums d = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9), ∃ r : Std.I64, divisible_triplet_count nums d = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= T(nums), where T(nums) is the total number of index triples 0 <= i < j < k < len(nums).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9 -/
theorem spec_3 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    0 ≤ r.val ∧ r.val ≤ (indexTripleCount nums.val : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), 0 ≤ r.val ∧ r.val ≤ (indexTripleCount nums.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9; len(nums) < 3 -/
theorem spec_4 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_lt : nums.val.length < 3)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_lt : nums.val.length < 3)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if (nums[0] + nums[1] + nums[2]) mod d = 0, and r = 0 otherwise.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9; len(nums) = 3 -/
theorem spec_5 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_eq : nums.val.length = 3)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val =
      (if (valAt nums.val 0 + valAt nums.val 1 + valAt nums.val 2) % d.val = 0
       then (1 : Int) else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_eq : nums.val.length = 3)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val =
      (if (valAt nums.val 0 + valAt nums.val 1 + valAt nums.val 2) % d.val = 0
       then (1 : Int) else 0)) := by
  sorry

/-- Whenever the function returns a result r, r = T(nums), where T(nums) is the total number of index triples 0 <= i < j < k < len(nums).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9; for every i with 0 <= i < len(nums), nums[i] mod d = 0 -/
theorem spec_6 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hmod : ∀ (i : Nat) (hi : i < nums.val.length), valAt nums.val i % d.val = 0)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val = (indexTripleCount nums.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hmod : ∀ (i : Nat) (hi : i < nums.val.length), valAt nums.val i % d.val = 0)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val = (indexTripleCount nums.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = T(nums) if (3*a) mod d = 0, and r = 0 otherwise, where T(nums) is the total number of index triples 0 <= i < j < k < len(nums).
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9; there exists an integer a such that nums[i] = a for every i with 0 <= i < len(nums) -/
theorem spec_7 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (a : Int) (hconst : ∀ (i : Nat) (hi : i < nums.val.length), valAt nums.val i = a)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val =
      (if (3 * a) % d.val = 0 then (indexTripleCount nums.val : Int) else 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (a : Int) (hconst : ∀ (i : Nat) (hi : i < nums.val.length), valAt nums.val i = a)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val =
      (if (3 * a) % d.val = 0 then (indexTripleCount nums.val : Int) else 0)) := by
  sorry

/-- Whenever the function returns r on input (nums,d) and r' on input (nums',d), r = r'.
  Preconditions: Both nums and nums' satisfy: 1 <= len <= 1000 and 1 <= value <= 10^9 for every entry; len(nums) = len(nums'); 1 <= d <= 10^9; there exists a bijection pi of {0,...,len(nums)-1} onto itself such that nums'[i] = nums[pi(i)] for every i with 0 <= i < len(nums) -/
theorem spec_8 (nums nums' : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hlen' : 1 ≤ nums'.val.length) (hlen'_le : nums'.val.length ≤ 1000)
    (hval' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ valAt nums'.val i ∧ valAt nums'.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_eq : nums.val.length = nums'.val.length)
    (hpi : ∃ (pi : Nat → Nat) (hmem : ∀ i, i < nums.val.length → pi i < nums.val.length),
      (∀ (i j : Nat), i < nums.val.length → j < nums.val.length → pi i = pi j → i = j) ∧
      (∀ (i : Nat) (hi : i < nums'.val.length), nums'.val[i] = nums.val[pi i]'(hmem i (by omega))))
    (r r' : Std.I64)
    (hr : divisible_triplet_count nums d = ok r)
    (hr' : divisible_triplet_count nums' d = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hlen' : 1 ≤ nums'.val.length) (hlen'_le : nums'.val.length ≤ 1000)
    (hval' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ valAt nums'.val i ∧ valAt nums'.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hlen_eq : nums.val.length = nums'.val.length)
    (hpi : ∃ (pi : Nat → Nat) (hmem : ∀ i, i < nums.val.length → pi i < nums.val.length),
      (∀ (i j : Nat), i < nums.val.length → j < nums.val.length → pi i = pi j → i = j) ∧
      (∀ (i : Nat) (hi : i < nums'.val.length), nums'.val[i] = nums.val[pi i]'(hmem i (by omega))))
    (r r' : Std.I64)
    (hr : divisible_triplet_count nums d = ok r)
    (hr' : divisible_triplet_count nums' d = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on input (nums,d) and r' on input (nums,d'), r' <= r.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9; 1 <= d' <= 10^9; d' is a positive multiple of d (there exists a positive integer m with d' = m*d) -/
theorem spec_9 (nums : Slice Std.I64) (d d' : Std.I64) (m : Nat)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hd' : 1 ≤ d'.val) (hd'_le : d'.val ≤ 10 ^ 9)
    (hm : 1 ≤ m) (hmul : d'.val = (m : Int) * d.val)
    (r r' : Std.I64)
    (hr : divisible_triplet_count nums d = ok r)
    (hr' : divisible_triplet_count nums d' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (d d' : Std.I64) (m : Nat)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (hd' : 1 ≤ d'.val) (hd'_le : d'.val ≤ 10 ^ 9)
    (hm : 1 ≤ m) (hmul : d'.val = (m : Int) * d.val)
    (r r' : Std.I64)
    (hr : divisible_triplet_count nums d = ok r)
    (hr' : divisible_triplet_count nums d' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r > 0 if and only if there exist indices 0 <= i < j < k < len(nums) such that (nums[i] + nums[j] + nums[k]) mod d = 0.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= d <= 10^9 -/
theorem spec_10 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    0 < r.val ↔
      ∃ (i j k : Nat), i < j ∧ j < k ∧ k < nums.val.length ∧
        (valAt nums.val i + valAt nums.val j + valAt nums.val k) % d.val = 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd : 1 ≤ d.val) (hd_le : d.val ≤ 10 ^ 9)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), 0 < r.val ↔
      ∃ (i j k : Nat), i < j ∧ j < k ∧ k < nums.val.length ∧
        (valAt nums.val i + valAt nums.val j + valAt nums.val k) % d.val = 0) := by
  sorry

/-- Let E be the number of indices i with 0 <= i < len(nums) and nums[i] mod 2 = 0, and let O = len(nums) - E. Whenever the function returns a result r, r = binom(E,3) + E * binom(O,2), where binom(n,k) is the number of k-element subsets of an n-element set, taken as 0 when n < k.
  Preconditions: 1 <= len(nums) <= 1000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; d = 2 -/
theorem spec_11 (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd_eq : d.val = 2)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r) :
    r.val =
      (binom (evenCount nums.val) 3 : Int) +
        (evenCount nums.val : Int) *
          (binom (nums.val.length - evenCount nums.val) 2 : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (d : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 1000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ valAt nums.val i ∧ valAt nums.val i ≤ 10 ^ 9)
    (hd_eq : d.val = 2)
    (r : Std.I64) (hr : divisible_triplet_count nums d = ok r), r.val =
      (binom (evenCount nums.val) 3 : Int) +
        (evenCount nums.val : Int) *
          (binom (nums.val.length - evenCount nums.val) 2 : Int)) := by
  sorry

end AegisSpec.DivisibleTripletCount
