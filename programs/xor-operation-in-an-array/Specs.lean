import Aegis.XorOperation.Code.Funs

/-!
# Specifications of `Aegis.XorOperation.xor_operation`

LeetCode problem `xor-operation-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.XorOperation

  open Aegis.XorOperation

  def xorInt (a b : Int) : Int := (Nat.xor a.toNat b.toNat : Int)

  def bitAt (x : Int) (b : Nat) : Nat := (x.toNat / 2 ^ b) % 2

  def term (start : Int) (i : Nat) : Int := start + 2 * (i : Int)

  def xorRange (n : Nat) (start : Int) : Int :=
    (List.range n).foldr (fun i acc => xorInt (term start i) acc) 0

  def oddBitCount (n : Nat) (start : Int) (b : Nat) : Nat :=
    ((Finset.range n).filter (fun i => bitAt (term start i) b = 1)).card % 2

  /-- The function returns a result r and r equals the bitwise XOR of the n integers a_i = start + 2*i for i = 0, 1, ..., n-1. Equivalently, r = a_0 XOR a_1 XOR ... XOR a_{n-1}. Here each a_i is computed as an integer (it is at most 2998 and hence fits in i64), and XOR is the 64-bit bitwise exclusive-or operation. For every bit position b with 0 <= b < 64, bit b of r is 1 exactly when the number of indices i with 0 <= i < n and bit b of a_i equal to 1 is odd.
    Preconditions: 1 <= n <= 1000 and 0 <= start <= 1000. -/
  theorem spec_1 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000) :
      ∃ r : Std.I64,
        xor_operation n start = .ok r ∧
          r.val = xorRange n.val.toNat start.val ∧
          ∀ b : Nat, b < 64 → bitAt r.val b = oddBitCount n.val.toNat start.val b := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000), ∃ r : Std.I64,
          xor_operation n start = Result.ok r ∧
            r.val = xorRange n.val.toNat start.val ∧
            ∀ b : Nat, b < 64 → bitAt r.val b = oddBitCount n.val.toNat start.val b) := by
    sorry

  /-- For every n and start satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 1 <= n <= 1000 and 0 <= start <= 1000. -/
  theorem spec_2 (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000) :
      ∃ r : Std.I64, xor_operation n start = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n start : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000), ∃ r : Std.I64, xor_operation n start = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 4096 (equivalently 0 <= r <= 4095).
    Preconditions: 1 <= n <= 1000 and 0 <= start <= 1000. -/
  theorem spec_3 (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
      (hr : xor_operation n start = .ok r) :
      0 ≤ r.val ∧ r.val < 4096 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
        (hr : xor_operation n start = Result.ok r), 0 ≤ r.val ∧ r.val < 4096) := by
    sorry

  /-- Whenever the function returns a result r, r mod 2 = (start mod 2) * (n mod 2). In other words, the least significant bit of r is 1 exactly when start is odd and n is odd.
    Preconditions: 1 <= n <= 1000 and 0 <= start <= 1000. -/
  theorem spec_4 (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
      (hr : xor_operation n start = .ok r) :
      r.val % 2 = (start.val % 2) * (n.val % 2) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
        (hr : xor_operation n start = Result.ok r), r.val % 2 = (start.val % 2) * (n.val % 2)) := by
    sorry

  /-- If the function returns r for input (n, start) and returns r' for input (n+1, start), then r' = r XOR (start + 2*n).
    Preconditions: 1 <= n < 1000 and 0 <= start <= 1000. -/
  theorem spec_5 (n start : Std.I64) (r r' : Std.I64) (hn1 : 1 ≤ n.val)
      (hn2 : n.val < 1000) (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
      (hr : xor_operation n start = .ok r)
      (hr' : (do let n' ← n + 1#i64; xor_operation n' start) = .ok r') :
      r'.val = xorInt r.val (start.val + 2 * n.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n start : Std.I64) (r r' : Std.I64) (hn1 : 1 ≤ n.val)
        (hn2 : n.val < 1000) (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
        (hr : xor_operation n start = Result.ok r)
        (hr' : (do let n' ← n + 1#i64; xor_operation n' start) = Result.ok r'), r'.val = xorInt r.val (start.val + 2 * n.val)) := by
    sorry

  /-- If the function returns r for input (n, start+2) and returns r' for input (n+1, start), then r = r' XOR start.
    Preconditions: 1 <= n < 1000 and 0 <= start <= 998. -/
  theorem spec_6 (n start : Std.I64) (r r' : Std.I64) (hn1 : 1 ≤ n.val)
      (hn2 : n.val < 1000) (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 998)
      (hr : (do let s' ← start + 2#i64; xor_operation n s') = .ok r)
      (hr' : (do let n' ← n + 1#i64; xor_operation n' start) = .ok r') :
      r.val = xorInt r'.val start.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n start : Std.I64) (r r' : Std.I64) (hn1 : 1 ≤ n.val)
        (hn2 : n.val < 1000) (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 998)
        (hr : (do let s' ← start + 2#i64; xor_operation n s') = Result.ok r)
        (hr' : (do let n' ← n + 1#i64; xor_operation n' start) = Result.ok r'), r.val = xorInt r'.val start.val) := by
    sorry

  /-- Whenever the function returns a result r, let b = (r / 2) mod 2 (integer division). Then b = 1 if and only if ((start mod 4 = 0 or start mod 4 = 1) and (floor(n/2) mod 2 = 1)) or ((start mod 4 = 2 or start mod 4 = 3) and (floor((n+1)/2) mod 2 = 1)).
    Preconditions: 1 <= n <= 1000 and 0 <= start <= 1000. -/
  theorem spec_7 (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
      (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
      (hr : xor_operation n start = .ok r) :
      (r.val / 2) % 2 = 1 ↔
        ((start.val % 4 = 0 ∨ start.val % 4 = 1) ∧ (n.val / 2) % 2 = 1) ∨
          ((start.val % 4 = 2 ∨ start.val % 4 = 3) ∧ ((n.val + 1) / 2) % 2 = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n start : Std.I64) (r : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000)
        (hs1 : 0 ≤ start.val) (hs2 : start.val ≤ 1000)
        (hr : xor_operation n start = Result.ok r), (r.val / 2) % 2 = 1 ↔
          ((start.val % 4 = 0 ∨ start.val % 4 = 1) ∧ (n.val / 2) % 2 = 1) ∨
            ((start.val % 4 = 2 ∨ start.val % 4 = 3) ∧ ((n.val + 1) / 2) % 2 = 1)) := by
    sorry

  end AegisSpec.XorOperation
