import Aegis.CheckRecord.Code.Funs

/-!
# Specifications of `Aegis.CheckRecord.check_record`

LeetCode problem `student-attendance-record-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CheckRecord

inductive Letter where
  | A
  | L
  | P
  deriving DecidableEq, Repr

def isL : Letter → Bool
  | .L => true
  | _ => false

def modulus : Int := 1000000007

def countA : List Letter → Nat
  | [] => 0
  | .A :: rest => countA rest + 1
  | _ :: rest => countA rest

def noThreeL : List Letter → Bool
  | [] => true
  | [_] => true
  | [_, _] => true
  | a :: b :: c :: rest => !(isL a && isL b && isL c) && noThreeL (b :: c :: rest)

def words (letters : List Letter) : Nat → List (List Letter)
  | 0 => [[]]
  | k + 1 => (words letters k).flatMap (fun w => letters.map (fun c => w ++ [c]))

def words3 (k : Nat) : List (List Letter) := words [Letter.A, Letter.L, Letter.P] k

def words2 (k : Nat) : List (List Letter) := words [Letter.L, Letter.P] k

def countS (k : Nat) : Nat :=
  ((words3 k).filter (fun s => decide (countA s ≤ 1) && noThreeL s)).length

def countLP (k : Nat) : Nat := ((words2 k).filter noThreeL).length

def countBad (k : Nat) : Nat :=
  ((words3 k).filter (fun s => decide (2 ≤ countA s) || !noThreeL s)).length

def countE0 (k : Nat) : Nat :=
  ((words3 k).filter (fun s => decide (countA s = 0) && noThreeL s)).length

def countE1 (k : Nat) : Nat :=
  ((words3 k).filter (fun s => decide (countA s = 1) && noThreeL s)).length

def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumRange f k + f k

def specS10Value (n : Nat) : Nat :=
  countLP n + sumRange (fun p => countLP p * countLP (n - 1 - p)) n

/-- Let M = 1000000007. Let S(n) be the set of all strings s of length n over the alphabet {'A','L','P'} such that (i) the number of indices i with 0 <= i < n and s[i] = 'A' is at most 1, and (ii) there is no index j with 0 <= j <= n-3 such that s[j] = s[j+1] = s[j+2] = 'L'. Let C(n) = |S(n)| be the number of such strings. Whenever check_record(n) returns a result r, r is the least nonnegative integer congruent to C(n) modulo M; equivalently, 0 <= r < M and r = C(n) mod M.
  Preconditions: n is an integer with 1 <= n <= 100000. -/
theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.CheckRecord.check_record n = .ok r →
      0 ≤ r.val ∧ r.val < modulus ∧ r.val ≡ (countS n.val.toNat : Int) [ZMOD modulus] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∀ r : Std.I64, Aegis.CheckRecord.check_record n = Result.ok r →
      0 ≤ r.val ∧ r.val < modulus ∧ r.val ≡ (countS n.val.toNat : Int) [ZMOD modulus]) := by
  sorry

/-- The call check_record(n) returns a result (an Ok value). It does not fail, overflow, panic, or go out of bounds.
  Preconditions: n is an integer with 1 <= n <= 100000. -/
theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
    ∃ r : Std.I64, Aegis.CheckRecord.check_record n = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∃ r : Std.I64, Aegis.CheckRecord.check_record n = Result.ok r) := by
  sorry

/-- For each integer k >= 0, let a(k) be the number of strings of length k over {'L','P'} with no index j such that 0 <= j <= k-3 and all three of positions j, j+1, j+2 are 'L'; thus a(0)=1 and the condition is vacuous for k<3. Whenever check_record(n) returns a result r, r is the least nonnegative residue modulo M = 1000000007 of a(n) + sum_{p=0}^{n-1} a(p) * a(n-1-p).
  Preconditions: n is an integer with 1 <= n <= 100000. -/
theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.CheckRecord.check_record n = .ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ (specS10Value n.val.toNat : Int) [ZMOD modulus] := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∀ r : Std.I64, Aegis.CheckRecord.check_record n = Result.ok r →
      0 ≤ r.val ∧ r.val < modulus ∧
        r.val ≡ (specS10Value n.val.toNat : Int) [ZMOD modulus]) := by
  sorry

/-- Let B(n) be the number of strings of length n over {'A','L','P'} that either contain at least two 'A' characters or contain three consecutive 'L' characters, or both. Whenever check_record(n) returns a result r, r is congruent modulo M = 1000000007 to 3^n - B(n).
  Preconditions: n is an integer with 1 <= n <= 100000. -/
theorem spec_4 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.CheckRecord.check_record n = .ok r →
      r.val ≡ (3 : Int) ^ n.val.toNat - (countBad n.val.toNat : Int) [ZMOD modulus] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∀ r : Std.I64, Aegis.CheckRecord.check_record n = Result.ok r →
      r.val ≡ (3 : Int) ^ n.val.toNat - (countBad n.val.toNat : Int) [ZMOD modulus]) := by
  sorry

/-- Let E0(n) be the number of length-n strings over {'A','L','P'} containing no 'A' and no three consecutive 'L'; let E1(n) be the number of length-n strings over {'A','L','P'} containing exactly one 'A' and no three consecutive 'L'. Whenever check_record(n) returns a result r, r is congruent modulo M = 1000000007 to E0(n) + E1(n).
  Preconditions: n is an integer with 1 <= n <= 100000. -/
theorem spec_5 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000) :
    ∀ r : Std.I64, Aegis.CheckRecord.check_record n = .ok r →
      r.val ≡ (countE0 n.val.toNat : Int) + (countE1 n.val.toNat : Int) [ZMOD modulus] := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100000), ∀ r : Std.I64, Aegis.CheckRecord.check_record n = Result.ok r →
      r.val ≡ (countE0 n.val.toNat : Int) + (countE1 n.val.toNat : Int) [ZMOD modulus]) := by
  sorry

end AegisSpec.CheckRecord
