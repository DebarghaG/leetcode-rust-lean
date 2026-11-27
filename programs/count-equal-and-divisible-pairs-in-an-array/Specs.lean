import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-equal-and-divisible-pairs-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountPairs

def valAt (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some x => x.val
  | none => 0

def Bounded (nums : Slice Std.I64) : Prop :=
  ∀ i : Nat, i < nums.val.length → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100

def countedPairs (nums : Slice Std.I64) (k : Int) : Finset (Nat × Nat) :=
  ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p : Nat × Nat =>
      p.1 < p.2 ∧ valAt nums p.1 = valAt nums p.2 ∧ k ∣ (p.1 : Int) * (p.2 : Int))

def pairCount (nums : Slice Std.I64) (k : Int) : Nat :=
  (countedPairs nums k).card

def equalPairCount (nums : Slice Std.I64) : Nat :=
  (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p : Nat × Nat => p.1 < p.2 ∧ valAt nums p.1 = valAt nums p.2)).card

def divisiblePairCount (nums : Slice Std.I64) (k : Int) : Nat :=
  (((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p : Nat × Nat => p.1 < p.2 ∧ k ∣ (p.1 : Int) * (p.2 : Int))).card

def totalPairCount (n : Nat) : Nat := n * (n - 1) / 2

def firstValueCount (nums : Slice Std.I64) : Nat :=
  ((Finset.range nums.val.length).filter
    (fun j : Nat => 1 ≤ j ∧ valAt nums j = valAt nums 0)).card

def perIndexSum (nums : Slice Std.I64) (k : Int) : Nat :=
  ((Finset.range nums.val.length).filter (fun j : Nat => 1 ≤ j)).sum
    (fun j : Nat =>
      ((Finset.range j).filter
        (fun i : Nat => valAt nums i = valAt nums j ∧ k ∣ (i : Int) * (j : Int))).card)

def appendContrib (nums : Slice Std.I64) (v : Int) (k : Int) : Nat :=
  ((Finset.range nums.val.length).filter
    (fun i : Nat => valAt nums i = v ∧ k ∣ (i : Int) * (nums.val.length : Int))).card

def snocListN {α : Type} : {n : Nat} → Aeneas.Data.ListN.ListN α n → α →
    Aeneas.Data.ListN.ListN α (n + 1)
  | _, .nil, v => .cons v .nil
  | _, .cons x xs, v => .cons x (snocListN xs v)

def push (nums : Slice Std.I64) (v : Std.I64) : Slice Std.I64 :=
  if h : nums.leng + 1 ≤ Usize.max then
    { leng := nums.leng + 1, list := snocListN nums.list v, bound := h }
  else nums

theorem snocListN_toList {α : Type} {n : Nat} (xs : Aeneas.Data.ListN.ListN α n) (v : α) :
    (snocListN xs v).toList = xs.toList ++ [v] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [snocListN, Aeneas.Data.ListN.ListN.toList, ih]

theorem push_val (nums : Slice Std.I64) (v : Std.I64) (h : nums.leng + 1 ≤ Usize.max) :
    (push nums v).val = nums.val ++ [v] := by
  rw [push, dite_eq_left h]
  show (snocListN nums.list v).toList = nums.val ++ [v]
  rw [snocListN_toList]
  rfl

/-- Whenever count_pairs(nums, k) returns a result r, r is exactly the number of pairs (i, j) of indices such that 0 <= i < j < len(nums), nums[i] = nums[j], and k divides i*j (that is, there exists an integer q with i*j = q*k). Each such pair is counted once, and no other pair is counted.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (pairCount nums k.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (pairCount nums k.val : Int)) := by
  sorry

/-- The function returns a result (it does not fail, overflow, panic, or access an index out of bounds).
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∃ r, Aegis.CountPairs.count_pairs nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∃ r, Aegis.CountPairs.count_pairs nums k = ok r) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, 0 <= r <= len(nums) * (len(nums) - 1) / 2.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairCount nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairCount nums.val.length : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r <= E, where E is the number of pairs (i, j) with 0 <= i < j < len(nums) and nums[i] = nums[j].
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val ≤ (equalPairCount nums : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val ≤ (equalPairCount nums : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r = 0.
  Preconditions: nums is a slice of i64 with len(nums) = 1; nums[0] satisfies 1 <= nums[0] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 1)
    (hbdd : 1 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 100)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r → r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 1)
    (hbdd : 1 ≤ valAt nums 0 ∧ valAt nums 0 ≤ 100)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r → r.val = 0) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r = 1 if nums[0] = nums[1], and r = 0 otherwise. In particular, the value of k does not affect the result for length two.
  Preconditions: nums is a slice of i64 with len(nums) = 2; for i in {0,1}, 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 2)
    (hbdd : ∀ i : Nat, i < 2 → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (if valAt nums 0 = valAt nums 1 then 1 else 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : nums.val.length = 2)
    (hbdd : ∀ i : Nat, i < 2 → 1 ≤ valAt nums i ∧ valAt nums i ≤ 100)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (if valAt nums 0 = valAt nums 1 then 1 else 0)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r equals the number of pairs (i, j) with 0 <= i < j < len(nums) and nums[i] = nums[j].
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k = 1. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : k.val = 1) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (equalPairCount nums : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : k.val = 1), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (equalPairCount nums : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r >= C0, where C0 is the number of indices j with 1 <= j < len(nums) and nums[j] = nums[0].
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      (firstValueCount nums : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      (firstValueCount nums : Int) ≤ r.val) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r = 0 if and only if there is no pair (i, j) with 0 <= i < j < len(nums), nums[i] = nums[j], and k divides i*j.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      (r.val = 0 ↔ pairCount nums k.val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      (r.val = 0 ↔ pairCount nums k.val = 0)) := by
  sorry

/-- Whenever count_pairs(a, k) returns a result r_a and count_pairs(b, k) returns a result r_b, r_a = r_b.
  Preconditions: Let a and b be slices of i64 and let k be an i64. Suppose 1 <= len(a) = len(b) <= 100, all elements of a and b lie in [1,100], 1 <= k <= 100, and for every i, j with 0 <= i < len(a) and 0 <= j < len(a), a[i] = a[j] if and only if b[i] = b[j]. -/
theorem spec_10 (a b : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ a.val.length) (hlen_eq : a.val.length = b.val.length)
    (hlen_le : b.val.length ≤ 100)
    (hbdd_a : Bounded a) (hbdd_b : Bounded b)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100)
    (hpat : ∀ i j : Nat, i < a.val.length → j < a.val.length →
      (valAt a i = valAt a j ↔ valAt b i = valAt b j)) :
    ∀ ra rb, Aegis.CountPairs.count_pairs a k = ok ra →
      Aegis.CountPairs.count_pairs b k = ok rb → ra.val = rb.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ a.val.length) (hlen_eq : a.val.length = b.val.length)
    (hlen_le : b.val.length ≤ 100)
    (hbdd_a : Bounded a) (hbdd_b : Bounded b)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100)
    (hpat : ∀ i j : Nat, i < a.val.length → j < a.val.length →
      (valAt a i = valAt a j ↔ valAt b i = valAt b j)), ∀ ra rb, Aegis.CountPairs.count_pairs a k = ok ra →
      Aegis.CountPairs.count_pairs b k = ok rb → ra.val = rb.val) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r equals the number of indices j with 1 <= j < len(nums) and nums[j] = nums[0].
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100; and k > (len(nums)-1)*(len(nums)-1). -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100)
    (hbig : ((nums.val.length : Int) - 1) * ((nums.val.length : Int) - 1) < k.val) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (firstValueCount nums : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100)
    (hbig : ((nums.val.length : Int) - 1) * ((nums.val.length : Int) - 1) < k.val), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (firstValueCount nums : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k1) returns a result r1 and count_pairs(nums, k2) returns a result r2, r1 >= r2.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k1 and k2 are i64 values with 1 <= k1 <= 100, 1 <= k2 <= 100, and k1 divides k2. -/
theorem spec_12 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk1 : 1 ≤ k1.val) (hk1_le : k1.val ≤ 100)
    (hk2 : 1 ≤ k2.val) (hk2_le : k2.val ≤ 100)
    (hdvd : k1.val ∣ k2.val) :
    ∀ r1 r2, Aegis.CountPairs.count_pairs nums k1 = ok r1 →
      Aegis.CountPairs.count_pairs nums k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk1 : 1 ≤ k1.val) (hk1_le : k1.val ≤ 100)
    (hk2 : 1 ≤ k2.val) (hk2_le : k2.val ≤ 100)
    (hdvd : k1.val ∣ k2.val), ∀ r1 r2, Aegis.CountPairs.count_pairs nums k1 = ok r1 →
      Aegis.CountPairs.count_pairs nums k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r = sum over j with 1 <= j < len(nums) of the cardinality of { i : 0 <= i < j, nums[i] = nums[j], k divides i*j }. That is, each index j contributes exactly the number of earlier equal-valued indices i whose product i*j is divisible by k.
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (perIndexSum nums k.val : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hbdd : Bounded nums) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (perIndexSum nums k.val : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r and count_pairs(nums ++ [v], k) returns a result r', then r' = r + the cardinality of { i : 0 <= i < len(nums), nums[i] = v, k divides i*len(nums) } (the appending of one element can only add the pairs formed with the new last index len(nums)).
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 99; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; v is an i64 with 1 <= v <= 100; k is an i64 with 1 <= k <= 100. -/
theorem spec_14 (nums : Slice Std.I64) (v k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 99)
    (hbdd : Bounded nums)
    (hv : 1 ≤ v.val ∧ v.val ≤ 100) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r r', Aegis.CountPairs.count_pairs nums k = ok r →
      Aegis.CountPairs.count_pairs (push nums v) k = ok r' →
      r'.val = r.val + (appendContrib nums v.val k.val : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (v k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 99)
    (hbdd : Bounded nums)
    (hv : 1 ≤ v.val ∧ v.val ≤ 100) (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r r', Aegis.CountPairs.count_pairs nums k = ok r →
      Aegis.CountPairs.count_pairs (push nums v) k = ok r' →
      r'.val = r.val + (appendContrib nums v.val k.val : Int)) := by
  sorry

/-- Whenever count_pairs(nums, k) returns a result r, r equals the number of pairs (i, j) of indices with 0 <= i < j < len(nums) such that k divides i*j (all values being equal, the equality test imposes no further restriction).
  Preconditions: nums is a slice of i64 with 1 <= len(nums) <= 100; there is an i64 v with 1 <= v <= 100 such that nums[i] = v for every i with 0 <= i < len(nums); k is an i64 with 1 <= k <= 100. -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hv : ∃ v : Int, 1 ≤ v ∧ v ≤ 100 ∧ ∀ i : Nat, i < nums.val.length → valAt nums i = v)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100) :
    ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (divisiblePairCount nums k.val : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100)
    (hv : ∃ v : Int, 1 ≤ v ∧ v ≤ 100 ∧ ∀ i : Nat, i < nums.val.length → valAt nums i = v)
    (hk : 1 ≤ k.val) (hk_le : k.val ≤ 100), ∀ r, Aegis.CountPairs.count_pairs nums k = ok r →
      r.val = (divisiblePairCount nums k.val : Int)) := by
  sorry

end AegisSpec.CountPairs
