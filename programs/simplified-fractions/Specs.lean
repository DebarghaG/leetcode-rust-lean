import Aegis.SimplifiedFractions.Code.Funs

/-!
# Specifications of `Aegis.SimplifiedFractions.simplified_fractions`

LeetCode problem `simplified-fractions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SimplifiedFractions

namespace AegisSpec.SimplifiedFractions

abbrev ByteVec : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

abbrev FracVec : Type := Aeneas.Std.alloc.vec.Vec ByteVec

def u8OfNat (m : Nat) : Aeneas.Std.U8 := ⟨BitVec.ofNat 8 m⟩

def decDigitsRev : Nat → List Nat
  | 0 => []
  | (n + 1) => (n + 1) % 10 :: decDigitsRev ((n + 1) / 10)
termination_by m => m
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def decDigits (m : Nat) : List Nat :=
  if m = 0 then [0] else (decDigitsRev m).reverse

def decBytes (m : Nat) : List Aeneas.Std.U8 := (decDigits m).map (fun d => u8OfNat (48 + d))

def enc (a b : Nat) : List Aeneas.Std.U8 := decBytes a ++ [47#u8] ++ decBytes b

def IsDigitByte (c : Aeneas.Std.U8) : Prop := 48 ≤ c.val ∧ c.val ≤ 57

def IsFractionBytes (l : List Aeneas.Std.U8) : Prop :=
  ∃ d e : List Aeneas.Std.U8,
    l = d ++ 47#u8 :: e ∧
      d ≠ [] ∧ e ≠ [] ∧
      (∀ c ∈ d, IsDigitByte c) ∧ (∀ c ∈ e, IsDigitByte c) ∧
      d.head? ≠ some 48#u8 ∧ e.head? ≠ some 48#u8 ∧
      l.countP (fun c => decide (c = 47#u8)) = 1

def IsEncBelow (n : Nat) (s : ByteVec) : Prop :=
  ∃ a b : Nat, 1 ≤ a ∧ a < b ∧ b ≤ n ∧ Nat.Coprime a b ∧ s.val = enc a b

def contents (r : FracVec) : List (List Aeneas.Std.U8) := r.val.map (fun s => s.val)

def OccursOnce (l : List ByteVec) (a b : Nat) : Prop :=
  ∃! i : Nat, ∃ hi : i < l.length, (l[i]'hi).val = enc a b

def eulerPhi (b : Nat) : Nat :=
  ((List.range b).filter (fun i => decide (Nat.Coprime (i + 1) b))).length

def phiSum (n : Nat) : Nat :=
  (((List.range (n + 1)).filter (fun b => decide (2 ≤ b))).map eulerPhi).sum

def encodesDenB (b : Nat) (s : ByteVec) : Bool :=
  (List.range b).any (fun a => decide (1 ≤ a ∧ Nat.Coprime a b ∧ s.val = enc a b))

def countWithDen (r : FracVec) (b : Nat) : Nat := r.val.countP (encodesDenB b)

/-- The function returns a result r (it does not fail). Writing enc(a,b) for the byte sequence consisting of the ASCII decimal representation of a without leading zeros, then byte 47 ('/'), then the ASCII decimal representation of b without leading zeros, the following hold: (a) for every index i with 0 <= i < len(r), there exist integers a,b with 1 <= a < b <= n and gcd(a,b)=1 such that r[i] = enc(a,b); (b) for every pair of integers a,b with 1 <= a < b <= n and gcd(a,b)=1, there is exactly one index i with 0 <= i < len(r) such that r[i] = enc(a,b).
  Preconditions: n is the integer value of the i64 parameter and 1 <= n <= 100. -/
theorem spec_1 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        (∀ (i : Nat) (hi : i < r.val.length), IsEncBelow n.val.toNat (r.val[i]'hi)) ∧
        (∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
          OccursOnce r.val a b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        (∀ (i : Nat) (hi : i < r.val.length), IsEncBelow n.val.toNat (r.val[i]'hi)) ∧
        (∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
          OccursOnce r.val a b)) := by
  sorry

/-- The function returns a result r and len(r) = sum_{b=2}^{n} phi(b), where phi is Euler's totient function (phi(b) is the number of integers a with 1 <= a <= b and gcd(a,b)=1).
  Preconditions: 1 <= n <= 100. -/
theorem spec_2 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : FracVec,
      simplified_fractions n = ok r ∧ r.val.length = phiSum n.val.toNat := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : FracVec,
      simplified_fractions n = ok r ∧ r.val.length = phiSum n.val.toNat) := by
  sorry

/-- The function returns a result r and len(r) = 0 (r is the empty vector).
  Preconditions: n = 1. -/
theorem spec_3 (n : Aeneas.Std.I64) (hn : n.val = 1) :
    ∃ r : FracVec, simplified_fractions n = ok r ∧ r.val.length = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 1), ∃ r : FracVec, simplified_fractions n = ok r ∧ r.val.length = 0) := by
  sorry

/-- The function returns a result r and r = [enc(1,2)] (a one-element vector whose only entry is the ASCII bytes for "1/2").
  Preconditions: n = 2. -/
theorem spec_4 (n : Aeneas.Std.I64) (hn : n.val = 2) :
    ∃ r : FracVec, simplified_fractions n = ok r ∧ contents r = [enc 1 2] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 2), ∃ r : FracVec, simplified_fractions n = ok r ∧ contents r = [enc 1 2]) := by
  sorry

/-- The function returns a result r and there exists an index i with 0 <= i < len(r) such that r[i] = enc(1,2), i.e., the bytes for "1/2".
  Preconditions: 2 <= n <= 100. -/
theorem spec_5 (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = enc 1 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 100), ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = enc 1 2) := by
  sorry

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(r), there exist integers a,b with 1 <= a < b <= n and gcd(a,b)=1 such that r[i] = enc(a,b).
  Preconditions: 1 <= n <= 100. -/
theorem spec_6 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), IsEncBelow n.val.toNat (r.val[i]'hi) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (i : Nat) (hi : i < r.val.length), IsEncBelow n.val.toNat (r.val[i]'hi)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers a,b with 1 <= a < b <= n and gcd(a,b)=1, there exists an index i with 0 <= i < len(r) such that r[i] = enc(a,b).
  Preconditions: 1 <= n <= 100. -/
theorem spec_7 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
        ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = enc a b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
        ∃ (i : Nat) (hi : i < r.val.length), (r.val[i]'hi).val = enc a b) := by
  sorry

/-- Whenever the function returns a result r, for all indices i,j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: 1 <= n <= 100. -/
theorem spec_8 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
        (r.val[i]'hi).val ≠ (r.val[j]'hj).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ (i j : Nat) (hi : i < r.val.length) (hj : j < r.val.length), i < j →
        (r.val[i]'hi).val ≠ (r.val[j]'hj).val) := by
  sorry

/-- Whenever the function returns a result r, for every integer b with 2 <= b <= n, the number of indices i with 0 <= i < len(r) for which there exists an integer a with 1 <= a < b, gcd(a,b)=1, and r[i] = enc(a,b) is exactly phi(b), where phi is Euler's totient function.
  Preconditions: 1 <= n <= 100. -/
theorem spec_9 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ b : Nat, 2 ≤ b → b ≤ n.val.toNat → countWithDen r b = eulerPhi b := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ b : Nat, 2 ≤ b → b ≤ n.val.toNat → countWithDen r b = eulerPhi b) := by
  sorry

/-- Whenever the function returns a result r, every element s of r is a byte sequence of the form d_1 ... d_p '/' e_1 ... e_q, where p >= 1, q >= 1, each d_j and e_j is an ASCII digit byte (48 <= byte <= 57), d_1 != 48, e_1 != 48, and byte 47 ('/') occurs exactly once in s (at the separator).
  Preconditions: 1 <= n <= 100. -/
theorem spec_10 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ s ∈ r.val, IsFractionBytes s.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ s ∈ r.val, IsFractionBytes s.val) := by
  sorry

/-- Whenever the function returns a result r, for every permutation r' of r (a vector of the same length whose elements are exactly the elements of r, with the same multiplicities, in some order), r' also satisfies the main characterization: every element of r' is enc(a,b) for some 1 <= a < b <= n with gcd(a,b)=1, and every such pair (a,b) appears exactly once in r'.
  Preconditions: 1 <= n <= 100. -/
theorem spec_11 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ r' : FracVec, r'.val.length = r.val.length → r'.val.Perm r.val →
        (∀ (i : Nat) (hi : i < r'.val.length), IsEncBelow n.val.toNat (r'.val[i]'hi)) ∧
          (∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
            OccursOnce r'.val a b) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∀ r : FracVec, simplified_fractions n = ok r →
      ∀ r' : FracVec, r'.val.length = r.val.length → r'.val.Perm r.val →
        (∀ (i : Nat) (hi : i < r'.val.length), IsEncBelow n.val.toNat (r'.val[i]'hi)) ∧
          (∀ (a b : Nat), 1 ≤ a → a < b → b ≤ n.val.toNat → Nat.Coprime a b →
            OccursOnce r'.val a b)) := by
  sorry

/-- The function returns a result r; in particular, no arithmetic overflow, out-of-bounds access, or other panic occurs for any n in the stated range.
  Preconditions: 1 <= n <= 100. -/
theorem spec_12 (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : FracVec, simplified_fractions n = ok r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : FracVec, simplified_fractions n = ok r) := by
  sorry

/-- The function returns a result r and there exists an index i with 0 <= i < len(r) such that r[i] = enc(n-1,n), i.e., the bytes for the fraction (n-1)/n.
  Preconditions: 2 <= n <= 100. -/
theorem spec_13 (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        ∃ (i : Nat) (hi : i < r.val.length),
          (r.val[i]'hi).val = enc (n.val.toNat - 1) n.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Aeneas.Std.I64) (hn : 2 ≤ n.val ∧ n.val ≤ 100), ∃ r : FracVec,
      simplified_fractions n = ok r ∧
        ∃ (i : Nat) (hi : i < r.val.length),
          (r.val[i]'hi).val = enc (n.val.toNat - 1) n.val.toNat) := by
  sorry

end AegisSpec.SimplifiedFractions
