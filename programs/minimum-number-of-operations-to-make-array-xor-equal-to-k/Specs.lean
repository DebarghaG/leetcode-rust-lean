import Aegis.MinOperations.Code.Funs

/-!
# Specifications of `Aegis.MinOperations.min_operations`

LeetCode problem `minimum-number-of-operations-to-make-array-xor-equal-to-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.MinOperations

def bitOf (n : Int) (b : Nat) : Bool := n.testBit b

def xorInt (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

def xorAll : List Int → Int
  | [] => 0
  | x :: xs => xorInt x (xorAll xs)

def values (nums : Slice Std.I64) : List Int := nums.val.map fun x => x.val

def xorOf (nums : Slice Std.I64) : Int := xorAll (values nums)

def popcountUpTo (n : Int) (w : Nat) : Nat :=
  ((List.range w).filter fun b => bitOf n b).length

def popcount64 (n : Int) : Nat := popcountUpTo n 64

abbrev BitOp : Type := Nat × Nat

def flipBit (x : Int) (b : Nat) : Int := xorInt x ((2 : Int) ^ b)

def applyOp (xs : List Int) (op : BitOp) : List Int :=
  if h : op.1 < xs.length then xs.set op.1 (flipBit xs[op.1] op.2) else xs

def applyOps (xs : List Int) : List BitOp → List Int
  | [] => xs
  | op :: ops => applyOps (applyOp xs op) ops

def AllInBounds (n : Nat) (ops : List BitOp) : Prop := ∀ op ∈ ops, op.1 < n

/-- The function returns a result r, and r is the minimum number of operations of the following kind needed to make the bitwise XOR of the array equal to k: one operation chooses an index j with 0 <= j < len(nums) and a bit position b >= 0 (including leading zero positions), and flips the b-th bit of the element at index j; the array length remains len(nums).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      (∃ ops : List BitOp,
        AllInBounds nums.val.length ops ∧
        xorAll (applyOps (values nums) ops) = k.val ∧
        ops.length = r.val.toNat) ∧
      (∀ ops : List BitOp,
        AllInBounds nums.val.length ops →
        xorAll (applyOps (values nums) ops) = k.val →
        r.val.toNat ≤ ops.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      (∃ ops : List BitOp,
        AllInBounds nums.val.length ops ∧
        xorAll (applyOps (values nums) ops) = k.val ∧
        ops.length = r.val.toNat) ∧
      (∀ ops : List BitOp,
        AllInBounds nums.val.length ops →
        xorAll (applyOps (values nums) ops) = k.val →
        r.val.toNat ≤ ops.length)) := by
  sorry

/-- Let X = nums[0] xor nums[1] xor ... xor nums[len(nums)-1]. The returned r equals the number of bit positions b with 0 <= b < 64 such that the b-th bit of X differs from the b-th bit of k; equivalently, r = popcount(X xor k).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      r.val = ((popcount64 (xorInt (xorOf nums) k.val) : Nat) : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      r.val = ((popcount64 (xorInt (xorOf nums) k.val) : Nat) : Int)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result and does not fail: there is no panic, out-of-bounds access, or 64-bit arithmetic overflow.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r) := by
  sorry

/-- The returned r satisfies 0 <= r <= 20.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 20 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      0 ≤ r.val ∧ r.val ≤ 20) := by
  sorry

/-- There exists a sequence of exactly r operations, each flipping one bit (possibly a leading zero bit) of one element of nums with the array length unchanged, such that the bitwise XOR of the resulting array equals k.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000) :
    ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      ∃ ops : List BitOp,
        AllInBounds nums.val.length ops ∧
        ops.length = r.val.toNat ∧
        xorAll (applyOps (values nums) ops) = k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000), ∃ r : Std.I64, Aegis.MinOperations.min_operations nums k = ok r ∧
      ∃ ops : List BitOp,
        AllInBounds nums.val.length ops ∧
        ops.length = r.val.toNat ∧
        xorAll (applyOps (values nums) ops) = k.val) := by
  sorry

/-- Let r be the result of min_operations(nums, k) and r' the result of min_operations(nums', k). Then r' = r.
  Preconditions: nums and nums' are slices with len(nums) >= 1, len(nums) <= 100000, len(nums') = len(nums); for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000 and 0 <= nums'[i] <= 1000000; 0 <= k <= 1000000; XOR(nums') = XOR(nums). -/
theorem spec_6 (nums nums' : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_nums' : ∀ (i : Nat) (h_i : i < nums'.val.length),
      0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000)
    (h_xor : xorOf nums' = xorOf nums) :
    ∀ r r' : Std.I64,
      Aegis.MinOperations.min_operations nums k = ok r →
      Aegis.MinOperations.min_operations nums' k = ok r' → r' = r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_len_eq : nums'.val.length = nums.val.length)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_nums' : ∀ (i : Nat) (h_i : i < nums'.val.length),
      0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000)
    (h_xor : xorOf nums' = xorOf nums), ∀ r r' : Std.I64,
      Aegis.MinOperations.min_operations nums k = ok r →
      Aegis.MinOperations.min_operations nums' k = ok r' → r' = r) := by
  sorry

/-- Let X = nums[0] xor nums[1] xor ... xor nums[len(nums)-1]. Let r be the result for (nums, k) and r' the result for (nums, k'). If the b-th bit of X equals the b-th bit of k, then r' = r + 1; otherwise r' = r - 1.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; 0 <= k <= 1000000; b is an integer with 0 <= b < 20; k' = k xor (1 << b) satisfies 0 <= k' <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64) (k k' b : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000)
    (h_b_lo : 0 ≤ b.val) (h_b_hi : b.val < 20)
    (h_k' : k'.val = xorInt k.val ((2 : Int) ^ b.val.toNat))
    (h_k'_lo : 0 ≤ k'.val) (h_k'_hi : k'.val ≤ 1000000) :
    ∀ r r' : Std.I64,
      Aegis.MinOperations.min_operations nums k = ok r →
      Aegis.MinOperations.min_operations nums k' = ok r' →
        ((bitOf (xorOf nums) b.val.toNat = bitOf k.val b.val.toNat → r'.val = r.val + 1) ∧
         (bitOf (xorOf nums) b.val.toNat ≠ bitOf k.val b.val.toNat → r'.val = r.val - 1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k k' b : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k_lo : 0 ≤ k.val) (h_k_hi : k.val ≤ 1000000)
    (h_b_lo : 0 ≤ b.val) (h_b_hi : b.val < 20)
    (h_k' : k'.val = xorInt k.val ((2 : Int) ^ b.val.toNat))
    (h_k'_lo : 0 ≤ k'.val) (h_k'_hi : k'.val ≤ 1000000), ∀ r r' : Std.I64,
      Aegis.MinOperations.min_operations nums k = ok r →
      Aegis.MinOperations.min_operations nums k' = ok r' →
        ((bitOf (xorOf nums) b.val.toNat = bitOf k.val b.val.toNat → r'.val = r.val + 1) ∧
         (bitOf (xorOf nums) b.val.toNat ≠ bitOf k.val b.val.toNat → r'.val = r.val - 1))) := by
  sorry

/-- Let r1 be the result of min_operations(nums, k1) and r2 the result of min_operations(nums, k2). Then |r1 - r2| <= popcount(k1 xor k2), where popcount counts set bits among positions 0 through 63.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000; k1 and k2 are integers with 0 <= k1 <= 1000000 and 0 <= k2 <= 1000000. -/
theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k1_lo : 0 ≤ k1.val) (h_k1_hi : k1.val ≤ 1000000)
    (h_k2_lo : 0 ≤ k2.val) (h_k2_hi : k2.val ≤ 1000000) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinOperations.min_operations nums k1 = ok r1 →
      Aegis.MinOperations.min_operations nums k2 = ok r2 →
        Int.natAbs (r1.val - r2.val) ≤ popcount64 (xorInt k1.val k2.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (h_len_lo : 1 ≤ nums.val.length) (h_len_hi : nums.val.length ≤ 100000)
    (h_nums : ∀ (i : Nat) (h_i : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
    (h_k1_lo : 0 ≤ k1.val) (h_k1_hi : k1.val ≤ 1000000)
    (h_k2_lo : 0 ≤ k2.val) (h_k2_hi : k2.val ≤ 1000000), ∀ r1 r2 : Std.I64,
      Aegis.MinOperations.min_operations nums k1 = ok r1 →
      Aegis.MinOperations.min_operations nums k2 = ok r2 →
        Int.natAbs (r1.val - r2.val) ≤ popcount64 (xorInt k1.val k2.val)) := by
  sorry

end AegisSpec.MinOperations
