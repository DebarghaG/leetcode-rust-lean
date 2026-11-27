import Aegis.MaxGoodNumber.Code.Funs

/-!
# Specifications of `Aegis.MaxGoodNumber.max_good_number`

LeetCode problem `maximum-possible-number-by-binary-concatenation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxGoodNumber

def getVal (nums : Slice I64) (i : Nat) : Int :=
  ((nums.val[i]?).map fun x => x.val).getD 0

def InRange (nums : Slice I64) : Prop :=
  nums.val.length = 3 ∧
    1 ≤ getVal nums 0 ∧ getVal nums 0 ≤ 127 ∧
    1 ≤ getVal nums 1 ∧ getVal nums 1 ≤ 127 ∧
    1 ≤ getVal nums 2 ∧ getVal nums 2 ≤ 127

def IsBitLen (v : Int) (k : Nat) : Prop :=
  1 ≤ k ∧ (2 : Int) ^ (k - 1) ≤ v ∧ v < (2 : Int) ^ k

def bitLen (v : Int) : Nat :=
  v.toNat.log2 + 1

theorem isBitLen_bitLen {v : Int} (hv : 1 ≤ v) : IsBitLen v (bitLen v) := by
  have hv0 : v.toNat ≠ 0 := by omega
  have hcast : (v.toNat : Int) = v := by omega
  obtain ⟨hlo, hhi⟩ := (Nat.log2_eq_iff hv0).mp rfl
  refine ⟨by simp [bitLen], ?_, ?_⟩
  · rw [show bitLen v - 1 = v.toNat.log2 by simp [bitLen]]
    calc (2 : Int) ^ v.toNat.log2 = ((2 : Nat) ^ v.toNat.log2 : Int) := by push_cast; ring
      _ ≤ (v.toNat : Int) := by exact_mod_cast hlo
      _ = v := hcast
  · rw [show bitLen v = v.toNat.log2 + 1 by simp [bitLen]]
    calc v = (v.toNat : Int) := hcast.symm
      _ < ((2 : Nat) ^ (v.toNat.log2 + 1) : Int) := by exact_mod_cast hhi
      _ = (2 : Int) ^ (v.toNat.log2 + 1) := by push_cast; ring

def concat (a b c : Int) : Int :=
  a * (2 : Int) ^ (bitLen b + bitLen c) + b * (2 : Int) ^ (bitLen c) + c

def concatAt (nums : Slice I64) (p : Nat × Nat × Nat) : Int :=
  concat (getVal nums p.1) (getVal nums p.2.1) (getVal nums p.2.2)

def perms3 : List (Nat × Nat × Nat) :=
  [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

def IsPerm3 (i0 i1 i2 : Nat) : Prop :=
  (i0, i1, i2) ∈ perms3

def IsPermTriple (a b c x y z : Int) : Prop :=
  List.Perm [a, b, c] [x, y, z]

/-- Let P be the set of all triples (i0,i1,i2) that are permutations of (0,1,2). For a positive integer v, let bitlen(v) be the unique k >= 1 such that 2^(k-1) <= v < 2^k. For positive integers a,b,c define concat(a,b,c) = a * 2^(bitlen(b)+bitlen(c)) + b * 2^bitlen(c) + c. The function returns a result r and r = max_{(i0,i1,i2) in P} concat(nums[i0], nums[i1], nums[i2]).
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_1 (nums : Slice I64) (h : InRange nums) :
    ∃ r : I64, Aegis.MaxGoodNumber.max_good_number nums = ok r ∧
      (∀ p ∈ perms3, concatAt nums p ≤ r.val) ∧
      (∃ p ∈ perms3, concatAt nums p = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums), ∃ r : I64, Aegis.MaxGoodNumber.max_good_number nums = ok r ∧
      (∀ p ∈ perms3, concatAt nums p ≤ r.val) ∧
      (∃ p ∈ perms3, concatAt nums p = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_2 (nums : Slice I64) (h : InRange nums) :
    ∃ r : I64, Aegis.MaxGoodNumber.max_good_number nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums), ∃ r : I64, Aegis.MaxGoodNumber.max_good_number nums = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, there exists a permutation (i0,i1,i2) of (0,1,2) such that r = nums[i0] * 2^(bitlen(nums[i1])+bitlen(nums[i2])) + nums[i1] * 2^bitlen(nums[i2]) + nums[i2], where bitlen(v) is the unique k >= 1 with 2^(k-1) <= v < 2^k.
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_3 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    ∃ p ∈ perms3, r.val = concatAt nums p := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), ∃ p ∈ perms3, r.val = concatAt nums p) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, for every permutation (i0,i1,i2) of (0,1,2), nums[i0] * 2^(bitlen(nums[i1])+bitlen(nums[i2])) + nums[i1] * 2^bitlen(nums[i2]) + nums[i2] <= r, where bitlen(v) is the unique k >= 1 with 2^(k-1) <= v < 2^k.
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_4 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    ∀ p ∈ perms3, concatAt nums p ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), ∀ p ∈ perms3, concatAt nums p ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, r <= 2097151 (equivalently r <= 2^21 - 1).
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_5 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    r.val ≤ 2097151 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), r.val ≤ 2097151) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, r > nums[0], r > nums[1], and r > nums[2].
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_6 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    r.val > getVal nums 0 ∧ r.val > getVal nums 1 ∧ r.val > getVal nums 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), r.val > getVal nums 0 ∧ r.val > getVal nums 1 ∧ r.val > getVal nums 2) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the preconditions, bitlen(r) = bitlen(nums[0]) + bitlen(nums[1]) + bitlen(nums[2]), where bitlen(v) is the unique k >= 1 with 2^(k-1) <= v < 2^k.
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_7 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    bitLen r.val = bitLen (getVal nums 0) + bitLen (getVal nums 1) + bitLen (getVal nums 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), bitLen r.val = bitLen (getVal nums 0) + bitLen (getVal nums 1) + bitLen (getVal nums 2)) := by
  sorry

/-- Whenever the function returns r on an input nums satisfying the preconditions, then for every permutation (j0,j1,j2) of (0,1,2), any slice xs with len(xs)=3 and xs[0]=nums[j0], xs[1]=nums[j1], xs[2]=nums[j2] also satisfies the preconditions, and the function on xs returns a result r' with r' = r.
  Preconditions: len(nums) = 3 and 1 <= nums[0] <= 127 and 1 <= nums[1] <= 127 and 1 <= nums[2] <= 127. -/
theorem spec_8 (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    ∀ (j0 j1 j2 : Nat), IsPerm3 j0 j1 j2 → ∀ xs : Slice I64,
      xs.val.length = 3 →
      getVal xs 0 = getVal nums j0 →
      getVal xs 1 = getVal nums j1 →
      getVal xs 2 = getVal nums j2 →
      InRange xs ∧ ∃ r' : I64, Aegis.MaxGoodNumber.max_good_number xs = ok r' ∧ r' = r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), ∀ (j0 j1 j2 : Nat), IsPerm3 j0 j1 j2 → ∀ xs : Slice I64,
      xs.val.length = 3 →
      getVal xs 0 = getVal nums j0 →
      getVal xs 1 = getVal nums j1 →
      getVal xs 2 = getVal nums j2 →
      InRange xs ∧ ∃ r' : I64, Aegis.MaxGoodNumber.max_good_number xs = ok r' ∧ r' = r) := by
  sorry

/-- Whenever the function returns r on nums and r' on xs, if nums[0] <= xs[0], nums[1] <= xs[1], and nums[2] <= xs[2], then r <= r'.
  Preconditions: nums and xs are slices with len(nums)=len(xs)=3, and 1 <= nums[i] <= 127 and 1 <= xs[i] <= 127 for i=0,1,2. -/
theorem spec_9 (nums xs : Slice I64) (hn : InRange nums) (hx : InRange xs) (r r' : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r)
    (hr' : Aegis.MaxGoodNumber.max_good_number xs = ok r')
    (h0 : getVal nums 0 ≤ getVal xs 0) (h1 : getVal nums 1 ≤ getVal xs 1)
    (h2 : getVal nums 2 ≤ getVal xs 2) :
    r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums xs : Slice I64) (hn : InRange nums) (hx : InRange xs) (r r' : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r)
    (hr' : Aegis.MaxGoodNumber.max_good_number xs = ok r')
    (h0 : getVal nums 0 ≤ getVal xs 0) (h1 : getVal nums 1 ≤ getVal xs 1)
    (h2 : getVal nums 2 ≤ getVal xs 2), r.val ≤ r'.val) := by
  sorry

/-- Whenever the function returns a result r on such an input, if (a,b,c) is a permutation of (nums[0],nums[1],nums[2]) with a >= b >= c, then r = a * 2^(2L) + b * 2^L + c.
  Preconditions: len(nums)=3, 1 <= nums[i] <= 127 for i=0,1,2, and there is L >= 1 such that bitlen(nums[0])=bitlen(nums[1])=bitlen(nums[2])=L, where bitlen(v) is the unique k >= 1 with 2^(k-1) <= v < 2^k. -/
theorem spec_10 (nums : Slice I64) (h : InRange nums) (L : Nat) (hL : 1 ≤ L)
    (hL0 : bitLen (getVal nums 0) = L) (hL1 : bitLen (getVal nums 1) = L)
    (hL2 : bitLen (getVal nums 2) = L) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r) :
    ∀ a b c : Int,
      IsPermTriple a b c (getVal nums 0) (getVal nums 1) (getVal nums 2) →
      a ≥ b → b ≥ c → r.val = a * (2 : Int) ^ (2 * L) + b * (2 : Int) ^ L + c := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (h : InRange nums) (L : Nat) (hL : 1 ≤ L)
    (hL0 : bitLen (getVal nums 0) = L) (hL1 : bitLen (getVal nums 1) = L)
    (hL2 : bitLen (getVal nums 2) = L) (r : I64)
    (hr : Aegis.MaxGoodNumber.max_good_number nums = ok r), ∀ a b c : Int,
      IsPermTriple a b c (getVal nums 0) (getVal nums 1) (getVal nums 2) →
      a ≥ b → b ≥ c → r.val = a * (2 : Int) ^ (2 * L) + b * (2 : Int) ^ L + c) := by
  sorry

end AegisSpec.MaxGoodNumber
