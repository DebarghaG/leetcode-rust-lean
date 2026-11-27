import Aegis.GoodIndices.Code.Funs

/-!
# Specifications of `Aegis.GoodIndices.good_indices`

LeetCode problem `find-all-good-indices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.GoodIndices (good_indices)

namespace AegisSpec.GoodIndices

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def entry (nums : Slice Std.I64) (j : Nat) : Int := (vals nums).getD j 0

def out (r : alloc.vec.Vec Std.I64) : List Int := r.val.map (fun x => x.val)

def oget (r : alloc.vec.Vec Std.I64) (p : Nat) : Int := (out r).getD p 0

def Good (nums : Slice Std.I64) (k i : Int) : Prop :=
  k ≤ i ∧ i < (nums.val.length : Int) - k ∧
    (∀ t : Nat, i - k ≤ (t : Int) → (t : Int) < i - 1 → entry nums t ≥ entry nums (t + 1)) ∧
    (∀ t : Nat, i + 1 ≤ (t : Int) → (t : Int) < i + k → entry nums t ≤ entry nums (t + 1))

noncomputable def numGoodBelow (nums : Slice Std.I64) (k b : Int) : Nat := by
  classical
  exact ((List.range b.toNat).filter (fun j => decide (Good nums k (j : Int)))).length

noncomputable def numGood (nums : Slice Std.I64) (k : Int) : Nat :=
  numGoodBelow nums k (nums.val.length : Int)

/-- The function returns a result r and does not fail. Define an integer i to be good when: (1) k <= i < n-k; (2) for every t with i-k <= t < i-1, nums[t] >= nums[t+1]; and (3) for every t with i+1 <= t < i+k, nums[t] <= nums[t+1]. Then r is exactly the increasing list of all good integers: for every p with 0 <= p < len(r), r[p] is good and there are exactly p good integers smaller than r[p]; also, for every good integer i there is exactly one p with 0 <= p < len(r) and r[p] = i. In particular, len(r) is the number of good integers.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      good_indices nums k = ok r ∧
        (∀ p : Nat, p < (out r).length →
          Good nums k.val (oget r p) ∧ numGoodBelow nums k.val (oget r p) = p) ∧
        (∀ i : Int, Good nums k.val i → ∃! p : Nat, p < (out r).length ∧ oget r p = i) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64,
      good_indices nums k = ok r ∧
        (∀ p : Nat, p < (out r).length →
          Good nums k.val (oget r p) ∧ numGoodBelow nums k.val (oget r p) = p) ∧
        (∀ i : Int, Good nums k.val i → ∃! p : Nat, p < (out r).length ∧ oget r p = i)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∃ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, every element of r is a valid candidate index: for every p with 0 <= p < len(r), k <= r[p] < n-k.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length →
        k.val ≤ oget r p ∧ oget r p < (nums.val.length : Int) - k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length →
        k.val ≤ oget r p ∧ oget r p < (nums.val.length : Int) - k.val) := by
  sorry

/-- Whenever the function returns a result r, its entries are strictly increasing in position: for every p and q with 0 <= p < q < len(r), r[p] < r[q]. In particular, r contains no duplicates.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p q : Nat, p < q → q < (out r).length → oget r p < oget r q := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p q : Nat, p < q → q < (out r).length → oget r p < oget r q) := by
  sorry

/-- Whenever the function returns a result r, every returned index is good. That is, for every p with 0 <= p < len(r), with i = r[p], we have k <= i < n-k, for every t with i-k <= t < i-1, nums[t] >= nums[t+1], and for every t with i+1 <= t < i+k, nums[t] <= nums[t+1].
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length → Good nums k.val (oget r p) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length → Good nums k.val (oget r p)) := by
  sorry

/-- Whenever the function returns a result r, every good index is present in r. That is, for every integer i with k <= i < n-k, if for every t with i-k <= t < i-1, nums[t] >= nums[t+1], and for every t with i+1 <= t < i+k, nums[t] <= nums[t+1], then there exists p with 0 <= p < len(r) and r[p] = i.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ i : Int, Good nums k.val i → ∃ p : Nat, p < (out r).length ∧ oget r p = i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ i : Int, Good nums k.val i → ∃ p : Nat, p < (out r).length ∧ oget r p = i) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of good indices, i.e. the number of integers i for which k <= i < n-k, for every t with i-k <= t < i-1, nums[t] >= nums[t+1], and for every t with i+1 <= t < i+k, nums[t] <= nums[t+1].
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (out r).length = numGood nums k.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (out r).length = numGood nums k.val) := by
  sorry

/-- Whenever the function returns a result r, 0 <= len(r) <= n-2*k.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (0 : Int) ≤ ((out r).length : Int) ∧
        ((out r).length : Int) ≤ (nums.val.length : Int) - 2 * k.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (0 : Int) ≤ ((out r).length : Int) ∧
        ((out r).length : Int) ≤ (nums.val.length : Int) - 2 * k.val) := by
  sorry

/-- Whenever the function returns a result r, r is empty: len(r) = 0.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 1000000; and n = 2*k. -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_n_eq : (nums.val.length : Int) = 2 * k.val) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r → (out r).length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_n_eq : (nums.val.length : Int) = 2 * k.val), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r → (out r).length = 0) := by
  sorry

/-- Whenever the function returns a result r, r is exactly the list of all interior indices in increasing order: len(r) = n-2 and for every p with 0 <= p < len(r), r[p] = p+1.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 1000000; and k = 1. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_k_eq : k.val = 1) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ((out r).length : Int) = (nums.val.length : Int) - 2 ∧
        ∀ p : Nat, p < (out r).length → oget r p = (p : Int) + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_k_eq : k.val = 1), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ((out r).length : Int) = (nums.val.length : Int) - 2 ∧
        ∀ p : Nat, p < (out r).length → oget r p = (p : Int) + 1) := by
  sorry

/-- Whenever the function returns a result r, r is exactly the increasing list of all candidate indices: len(r) = n-2*k and for every p with 0 <= p < len(r), r[p] = k+p.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n; for every j with 0 <= j < n, 1 <= nums[j] <= 1000000; and all entries of nums are equal, i.e. there exists an integer c with nums[j] = c for every 0 <= j < n. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_const : ∃ c : Int, ∀ j : Nat, j < nums.val.length → entry nums j = c) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ((out r).length : Int) = (nums.val.length : Int) - 2 * k.val ∧
        ∀ p : Nat, p < (out r).length → oget r p = k.val + (p : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (h_const : ∃ c : Int, ∀ j : Nat, j < nums.val.length → entry nums j = c), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ((out r).length : Int) = (nums.val.length : Int) - 2 * k.val ∧
        ∀ p : Nat, p < (out r).length → oget r p = k.val + (p : Int)) := by
  sorry

/-- Whenever the function returns a nonempty result r, r[0] is the smallest good index and r[len(r)-1] is the largest good index, where an integer i is good when k <= i < n-k, for every t with i-k <= t < i-1, nums[t] >= nums[t+1], and for every t with i+1 <= t < i+k, nums[t] <= nums[t+1]. Formally: r[0] is good and r[0] <= i for every good integer i; r[len(r)-1] is good and i <= r[len(r)-1] for every good integer i.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r → (out r).length ≠ 0 →
      (Good nums k.val (oget r 0) ∧ ∀ i : Int, Good nums k.val i → oget r 0 ≤ i) ∧
        (Good nums k.val (oget r ((out r).length - 1)) ∧
          ∀ i : Int, Good nums k.val i → i ≤ oget r ((out r).length - 1)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r → (out r).length ≠ 0 →
      (Good nums k.val (oget r 0) ∧ ∀ i : Int, Good nums k.val i → oget r 0 ≤ i) ∧
        (Good nums k.val (oget r ((out r).length - 1)) ∧
          ∀ i : Int, Good nums k.val i → i ≤ oget r ((out r).length - 1))) := by
  sorry

/-- Whenever the function returns a result r, the returned indices remain good for every smaller positive window. More precisely, for every p with 0 <= p < len(r), for every integer k' with 1 <= k' <= k, if i = r[p], then k' <= i < n-k', for every t with i-k' <= t < i-1, nums[t] >= nums[t+1], and for every t with i+1 <= t < i+k', nums[t] <= nums[t+1].
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length →
        ∀ k' : Int, 1 ≤ k' → k' ≤ k.val → Good nums k' (oget r p) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      ∀ p : Nat, p < (out r).length →
        ∀ k' : Int, 1 ≤ k' → k' ≤ k.val → Good nums k' (oget r p)) := by
  sorry

/-- Whenever the function returns a result r, the same r is the exact increasing list of good indices for any other slice nums' of length n that has the same adjacent comparison pattern. More precisely, let nums' be any integer slice with len(nums') = n and such that for every t with 0 <= t < n-1, nums[t] < nums[t+1] iff nums'[t] < nums'[t+1], and nums[t] = nums[t+1] iff nums'[t] = nums'[t+1]. Then for every p with 0 <= p < len(r), r[p] is good with respect to nums' (same definition with nums' in place of nums), and every integer that is good with respect to nums' occurs in r.
  Preconditions: Let n = len(nums). All arithmetic in this specification is mathematical integer arithmetic and all indices are 0-based. 3 <= n <= 100000; 1 <= k and 2*k <= n (equivalently k <= floor(n/2)); for every j with 0 <= j < n, 1 <= nums[j] <= 1000000. -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (nums' : Slice Std.I64)
    (h_len : nums'.val.length = nums.val.length)
    (h_pat : ∀ t : Nat, t < nums.val.length - 1 →
      (entry nums t < entry nums (t + 1) ↔ entry nums' t < entry nums' (t + 1)) ∧
        (entry nums t = entry nums (t + 1) ↔ entry nums' t = entry nums' (t + 1))) :
    ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (∀ p : Nat, p < (out r).length → Good nums' k.val (oget r p)) ∧
        (∀ i : Int, Good nums' k.val i → ∃ p : Nat, p < (out r).length ∧ oget r p = i) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_n_lo : 3 ≤ nums.val.length) (h_n_hi : nums.val.length ≤ 100000)
    (h_k_lo : 1 ≤ k.val) (h_k_hi : 2 * k.val ≤ (nums.val.length : Int))
    (h_entries : ∀ j : Nat, j < nums.val.length → 1 ≤ entry nums j ∧ entry nums j ≤ 1000000)
    (nums' : Slice Std.I64)
    (h_len : nums'.val.length = nums.val.length)
    (h_pat : ∀ t : Nat, t < nums.val.length - 1 →
      (entry nums t < entry nums (t + 1) ↔ entry nums' t < entry nums' (t + 1)) ∧
        (entry nums t = entry nums (t + 1) ↔ entry nums' t = entry nums' (t + 1))), ∀ r : alloc.vec.Vec Std.I64, good_indices nums k = ok r →
      (∀ p : Nat, p < (out r).length → Good nums' k.val (oget r p)) ∧
        (∀ i : Int, Good nums' k.val i → ∃ p : Nat, p < (out r).length ∧ oget r p = i)) := by
  sorry

end AegisSpec.GoodIndices
