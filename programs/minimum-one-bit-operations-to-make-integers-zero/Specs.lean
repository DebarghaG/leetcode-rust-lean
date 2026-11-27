import Aegis.MinimumOneBitOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOneBitOperations.minimum_one_bit_operations`

LeetCode problem `minimum-one-bit-operations-to-make-integers-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOneBitOperations

  open Aegis.MinimumOneBitOperations (minimum_one_bit_operations)

  def bit (x : Int) (j : Nat) : Int := x / (2 : Int) ^ j % 2

  def flipBit (x : Int) (i : Nat) : Int := if bit x i = 0 then x + 2 ^ i else x - 2 ^ i

  def Step (x y : Nat) : Prop :=
    y = (flipBit (x : Int) 0).toNat ∨
      ∃ i : Nat, 1 ≤ i ∧ bit (x : Int) (i - 1) = 1 ∧
        (∀ j : Nat, j + 2 ≤ i → bit (x : Int) j = 0) ∧
        y = (flipBit (x : Int) i).toNat

  inductive Reach : Nat → Nat → Nat → Prop where

    | refl (x : Nat) : Reach x x 0

    | step {x y z L : Nat} (h : Reach x y L) (hs : Step y z) : Reach x z (L + 1)

  def MinOps (n L : Nat) : Prop := Reach n 0 L ∧ ∀ L' : Nat, Reach n 0 L' → L ≤ L'

  def xorRange (K : Nat) (f : Nat → Nat) : Nat :=
    (List.range K).foldl (fun acc k => Nat.xor acc (f k)) 0

  def grayXor (n : Nat) : Nat := xorRange (n + 1) (fun k => n / 2 ^ k)

  def bitSum (n : Nat) : Nat :=
    (List.range (n + 1)).foldl (fun acc k => acc + (if Nat.testBit n k then 1 else 0)) 0

  def halfArg (n : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000) :
      Aeneas.Std.I64 :=
    Aeneas.Std.I64.ofInt (n.val / 2) (by
      rw [Aeneas.Std.IScalar.cMin_I64_eq, Aeneas.Std.IScalar.cMax_I64_eq]
      omega)

  /-- Whenever minimum_one_bit_operations n returns a result r, r is the minimum possible number of operations to transform n into 0, where an operation on a nonnegative integer x is either: (O0) flip bit 0 of x; or (O1) for some i >= 1, if bit_{i-1}(x) = 1 and bit_j(x) = 0 for every j with 0 <= j <= i-2, flip bit i of x. Here bit_j(x) = floor(x / 2^j) mod 2, and flipping bit i means replacing x by x + 2^i when bit_i(x)=0 and by x - 2^i when bit_i(x)=1. The minimum is over all finite sequences x_0, x_1, ..., x_L of nonnegative integers with x_0 = n, x_L = 0, and each consecutive pair related by O0 or O1.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. The symbol r denotes a returned I64 value, also regarded as a mathematical integer. -/
  theorem spec_1 (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r) :
      MinOps n.val.toNat r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r), MinOps n.val.toNat r.val.toNat) := by
    sorry

  /-- For every n with 0 <= n <= 1,000,000,000, the call minimum_one_bit_operations n returns a result: there exists an I64 value r such that the call evaluates to an ok result r and does not fail.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. -/
  theorem spec_2 (n : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000) :
      ∃ r : Aeneas.Std.I64, minimum_one_bit_operations n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000), ∃ r : Aeneas.Std.I64, minimum_one_bit_operations n = ok r) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, r = n XOR floor(n/2) XOR floor(n/4) XOR floor(n/8) XOR ..., where only finitely many terms are nonzero (all terms floor(n/2^k) with 2^k > n are zero) and XOR denotes bitwise exclusive-or of nonnegative integers.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_3 (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r) :
      r.val = (grayXor n.val.toNat : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r), r.val = (grayXor n.val.toNat : Int)) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, r is nonnegative and n = r XOR floor(r/2), where XOR denotes bitwise exclusive-or of nonnegative integers and floor is integer division.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_4 (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r) :
      0 ≤ r.val ∧ n.val = (Nat.xor r.val.toNat (r.val.toNat / 2) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r), 0 ≤ r.val ∧ n.val = (Nat.xor r.val.toNat (r.val.toNat / 2) : Int)) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, 0 <= r < 2^30 = 1,073,741,824.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_5 (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r) :
      0 ≤ r.val ∧ r.val < (2 : Int) ^ 30 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r), 0 ≤ r.val ∧ r.val < (2 : Int) ^ 30) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, 2^k <= r < 2^{k+1}.
    Preconditions: n is the I64 argument, regarded mathematically, with 0 < n <= 1,000,000,000. Let k be the unique integer such that 2^k <= n < 2^{k+1}. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_6 (n r : Aeneas.Std.I64) (k : Nat) (hn : 0 < n.val)
      (hnle : n.val ≤ 1000000000) (hk1 : (2 : Int) ^ k ≤ n.val)
      (hk2 : n.val < (2 : Int) ^ (k + 1)) (hres : minimum_one_bit_operations n = ok r) :
      (2 : Int) ^ k ≤ r.val ∧ r.val < (2 : Int) ^ (k + 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (k : Nat) (hn : 0 < n.val)
        (hnle : n.val ≤ 1000000000) (hk1 : (2 : Int) ^ k ≤ n.val)
        (hk2 : n.val < (2 : Int) ^ (k + 1)) (hres : minimum_one_bit_operations n = ok r), (2 : Int) ^ k ≤ r.val ∧ r.val < (2 : Int) ^ (k + 1)) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, r = 2^{k+1} - 1.
    Preconditions: There is an integer k with 0 <= k <= 29 and n = 2^k. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_7 (n r : Aeneas.Std.I64) (k : Nat) (hk : k ≤ 29)
      (hn : n.val = (2 : Int) ^ k) (hres : minimum_one_bit_operations n = ok r) :
      r.val = (2 : Int) ^ (k + 1) - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (k : Nat) (hk : k ≤ 29)
        (hn : n.val = (2 : Int) ^ k) (hres : minimum_one_bit_operations n = ok r), r.val = (2 : Int) ^ (k + 1) - 1) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, r = floor(2^{k+1} / 3).
    Preconditions: There is an integer k with 1 <= k <= 29 and n = 2^k - 1. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_8 (n r : Aeneas.Std.I64) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 29)
      (hn : n.val = (2 : Int) ^ k - 1) (hres : minimum_one_bit_operations n = ok r) :
      r.val = (2 : Int) ^ (k + 1) / 3 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (k : Nat) (hk1 : 1 ≤ k) (hk2 : k ≤ 29)
        (hn : n.val = (2 : Int) ^ k - 1) (hres : minimum_one_bit_operations n = ok r), r.val = (2 : Int) ^ (k + 1) / 3) := by
    sorry

  /-- Whenever minimum_one_bit_operations n returns r, r is odd exactly when the binary expansion of n contains an odd number of 1-bits.
    Preconditions: n is the I64 argument, regarded as a mathematical integer, and 0 <= n <= 1,000,000,000. The symbol r denotes a returned I64 value, regarded mathematically. -/
  theorem spec_9 (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r) :
      (r.val % 2 = 1 ↔ bitSum n.val.toNat % 2 = 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n r : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r), (r.val % 2 = 1 ↔ bitSum n.val.toNat % 2 = 1)) := by
    sorry

  /-- For every such n, if minimum_one_bit_operations n returns r and minimum_one_bit_operations (floor(n/2)) returns r', then r and r' are nonnegative and r = n XOR r', where XOR is bitwise exclusive-or.
    Preconditions: n is the I64 argument, regarded mathematically, with 0 <= n <= 1,000,000,000. The values r and r' denote returned I64 values, regarded mathematically. -/
  theorem spec_10 (n r r' : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
      (hres : minimum_one_bit_operations n = ok r)
      (hres' : minimum_one_bit_operations (halfArg n hn0 hn) = ok r') :
      0 ≤ r.val ∧ 0 ≤ r'.val ∧ r.val = (Nat.xor n.val.toNat r'.val.toNat : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n r r' : Aeneas.Std.I64) (hn0 : 0 ≤ n.val) (hn : n.val ≤ 1000000000)
        (hres : minimum_one_bit_operations n = ok r)
        (hres' : minimum_one_bit_operations (halfArg n hn0 hn) = ok r'), 0 ≤ r.val ∧ 0 ≤ r'.val ∧ r.val = (Nat.xor n.val.toNat r'.val.toNat : Int)) := by
    sorry

  end AegisSpec.MinimumOneBitOperations
