import Aegis.MaximumOr.Code.Funs

/-!
# Specifications of `Aegis.MaximumOr.maximum_or`

LeetCode problem `maximum-or`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumOr

def bor (a b : Int) : Int := ((a.toNat ||| b.toNat : Nat) : Int)

def orAll (xs : List I64) : Int := xs.foldr (fun x acc => bor x.val acc) 0

def orShiftAux : Nat → List I64 → (Nat → Nat) → Int
  | _, [], _ => 0
  | i, x :: rest, t => bor (x.val * 2 ^ t i) (orShiftAux (i + 1) rest t)

def orShift (xs : List I64) (t : Nat → Nat) : Int := orShiftAux 0 xs t

def tSum (n : Nat) (t : Nat → Nat) : Nat := ((List.range n).map t).sum

def orExcept (xs : List I64) (i : Nat) : Int := orAll (xs.eraseIdx i)

def elemAt (xs : List I64) (i : Nat) : Int := (xs.getD i (0#i64)).val

def maxRange (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).foldr max 0

def IsMaxOf (xs : List I64) (M : Int) : Prop :=
  (∀ x ∈ xs, x.val ≤ M) ∧ ∃ x ∈ xs, x.val = M

def bitSet (x : Int) (i : Nat) : Prop := x.toNat.testBit i = true

instance instDecidableBitSet (x : Int) (i : Nat) : Decidable (bitSet x i) := by
  unfold bitSet
  infer_instance

def Pre (nums : Slice I64) (k : I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000 ∧
    (∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) ∧
      1 ≤ k.val ∧ k.val ≤ 15

/-- The function returns a result r and r is the maximum, over all choices of nonnegative integers t_0, ..., t_{n-1} with sum_{i=0}^{n-1} t_i <= k, of the value (nums[0] * 2^{t_0}) | (nums[1] * 2^{t_1}) | ... | (nums[n-1] * 2^{t_{n-1}}). Here | denotes 64-bit bitwise OR and multiplication by 2^{t_i} is ordinary integer multiplication.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_1 (nums : Slice I64) (k : I64) (h : Pre nums k) :
    ∃ r : I64,
      Aegis.MaximumOr.maximum_or nums k = ok r ∧
        (∀ t : Nat → Nat,
          tSum nums.val.length t ≤ k.val.toNat → orShift nums.val t ≤ r.val) ∧
        ∃ t : Nat → Nat, tSum nums.val.length t ≤ k.val.toNat ∧ orShift nums.val t = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k), ∃ r : I64,
      Aegis.MaximumOr.maximum_or nums k = ok r ∧
        (∀ t : Nat → Nat,
          tSum nums.val.length t ≤ k.val.toNat → orShift nums.val t ≤ r.val) ∧
        ∃ t : Nat → Nat, tSum nums.val.length t ≤ k.val.toNat ∧ orShift nums.val t = r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail from overflow, out-of-bounds access, or a panic).
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_2 (nums : Slice I64) (k : I64) (h : Pre nums k) :
    ∃ r : I64, Aegis.MaximumOr.maximum_or nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k), ∃ r : I64, Aegis.MaximumOr.maximum_or nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exist nonnegative integers t_0, ..., t_{n-1} with sum_{i=0}^{n-1} t_i = k (exactly k operations) such that r = (nums[0] * 2^{t_0}) | (nums[1] * 2^{t_1}) | ... | (nums[n-1] * 2^{t_{n-1}}).
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_3 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    ∃ t : Nat → Nat, tSum nums.val.length t = k.val.toNat ∧ orShift nums.val t = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), ∃ t : Nat → Nat, tSum nums.val.length t = k.val.toNat ∧ orShift nums.val t = r.val) := by
  sorry

/-- Whenever the function returns a result r, for every choice of nonnegative integers t_0, ..., t_{n-1} with sum_{i=0}^{n-1} t_i <= k, the value (nums[0] * 2^{t_0}) | (nums[1] * 2^{t_1}) | ... | (nums[n-1] * 2^{t_{n-1}}) is <= r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_4 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    ∀ t : Nat → Nat, tSum nums.val.length t ≤ k.val.toNat → orShift nums.val t ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), ∀ t : Nat → Nat, tSum nums.val.length t ≤ k.val.toNat → orShift nums.val t ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= i < n} ( (OR_{0 <= j < n, j != i} nums[j]) | (nums[i] * 2^k) ), where the OR over an empty set (the case n = 1) is defined to be 0.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_5 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    r.val =
      maxRange nums.val.length
        (fun i => bor (orExcept nums.val i) (elemAt nums.val i * 2 ^ k.val.toNat)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), r.val =
      maxRange nums.val.length
        (fun i => bor (orExcept nums.val i) (elemAt nums.val i * 2 ^ k.val.toNat))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r >= nums[i] * 2^k.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_6 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    ∀ i : Nat, i < nums.val.length → elemAt nums.val i * 2 ^ k.val.toNat ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), ∀ i : Nat, i < nums.val.length → elemAt nums.val i * 2 ^ k.val.toNat ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, bit B+k of r is 1 (bits are 0-indexed from the least significant bit).
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. Let M = max_{0 <= i < n} nums[i], and let B be the unique integer with 2^B <= M < 2^{B+1}. -/
theorem spec_7 (nums : Slice I64) (k : I64) (h : Pre nums k) (M : Int) (B : Nat)
    (hM : IsMaxOf nums.val M) (hB : 2 ^ B ≤ M ∧ M < 2 ^ (B + 1)) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    bitSet r.val (B + k.val.toNat) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (M : Int) (B : Nat)
    (hM : IsMaxOf nums.val M) (hB : 2 ^ B ≤ M ∧ M < 2 ^ (B + 1)) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), bitSet r.val (B + k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, r < 2^{B+k+1}; equivalently, r has no set bit at any position greater than B+k.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. Let M = max_{0 <= i < n} nums[i], and let B be the unique integer with 2^B <= M < 2^{B+1}. -/
theorem spec_8 (nums : Slice I64) (k : I64) (h : Pre nums k) (M : Int) (B : Nat)
    (hM : IsMaxOf nums.val M) (hB : 2 ^ B ≤ M ∧ M < 2 ^ (B + 1)) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    r.val < 2 ^ (B + k.val.toNat + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (M : Int) (B : Nat)
    (hM : IsMaxOf nums.val M) (hB : 2 ^ B ≤ M ∧ M < 2 ^ (B + 1)) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), r.val < 2 ^ (B + k.val.toNat + 1)) := by
  sorry

/-- Whenever the function returns a result r for nums, for every slice nums' of length n that is a permutation of nums (the same values with the same multiplicities, possibly in a different order), the call maximum_or(nums', k) returns the same result r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_9 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) (nums' : Slice I64)
    (hperm : nums'.val.Perm nums.val) :
    Aegis.MaximumOr.maximum_or nums' k = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) (nums' : Slice I64)
    (hperm : nums'.val.Perm nums.val), Aegis.MaximumOr.maximum_or nums' k = ok r) := by
  sorry

/-- Whenever the function returns a result r for the given k, for every integer k' with 1 <= k' <= k, if maximum_or(nums, k') returns a result r', then r' <= r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_10 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) (k' : I64)
    (hk' : 1 ≤ k'.val ∧ k'.val ≤ k.val) (r' : I64)
    (hr' : Aegis.MaximumOr.maximum_or nums k' = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) (k' : I64)
    (hk' : 1 ≤ k'.val ∧ k'.val ≤ k.val) (r' : I64)
    (hr' : Aegis.MaximumOr.maximum_or nums k' = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer c with c >= 0 such that 2^c divides nums[i] for every i with 0 <= i < n, the integer 2^c divides r.
  Preconditions: Let n = len(nums). The input satisfies 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 1000000000, and 1 <= k <= 15. -/
theorem spec_11 (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r) :
    ∀ c : Nat, (∀ x ∈ nums.val, (2 : Int) ^ c ∣ x.val) → (2 : Int) ^ c ∣ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (h : Pre nums k) (r : I64)
    (hr : Aegis.MaximumOr.maximum_or nums k = ok r), ∀ c : Nat, (∀ x ∈ nums.val, (2 : Int) ^ c ∣ x.val) → (2 : Int) ^ c ∣ r.val) := by
  sorry

end AegisSpec.MaximumOr
