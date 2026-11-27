import Aegis.FindStrobogrammatic.Code.Funs

/-!
# Specifications of `Aegis.FindStrobogrammatic.find_strobogrammatic`

LeetCode problem `strobogrammatic-number-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindStrobogrammatic

  abbrev ByteVector := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

  abbrev ByteMatrix := Aeneas.Std.alloc.vec.Vec ByteVector

  def getByte (x : ByteVector) (i : Nat) : Nat :=
    match x.val[i]? with
    | some b => b.val
    | none => 0

  def rot (b : Nat) : Nat :=
    if b = 48 then 48
    else if b = 49 then 49
    else if b = 54 then 57
    else if b = 56 then 56
    else if b = 57 then 54
    else b

  def isStrobogrammaticDigit (b : Nat) : Prop :=
    b = 48 ∨ b = 49 ∨ b = 54 ∨ b = 56 ∨ b = 57

  def allBytesAreDigits (x : ByteVector) : Prop :=
    ∀ b ∈ x.val, isStrobogrammaticDigit b.val

  def rotationSymmetric (n : Nat) (x : ByteVector) : Prop :=
    x.val.length = n ∧
      allBytesAreDigits x ∧
        ∀ i, i < n → rot (getByte x i) = getByte x (n - 1 - i)

  def isStrobogrammatic (n : Nat) (x : ByteVector) : Prop :=
    rotationSymmetric n x ∧ (n > 1 → getByte x 0 ≠ 48)

  def countOcc {α : Type} [DecidableEq α] (l : List α) (x : α) : Nat :=
    (l.filter (fun y => y = x)).length

  def expectedCount (n : Nat) : Nat :=
    if n = 1 then 3
    else
      let k := n / 2
      4 * 5 ^ (k - 1) * (if n % 2 = 1 then 3 else 1)

  /-- Let V be the set of byte vectors x such that (a) len(x)=n; (b) every entry of x is in {48,49,54,56,57} (the ASCII codes of '0','1','6','8','9'); (c) for every i with 0 <= i < n, rot(x[i]) = x[n-1-i], where rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54; and (d) if n > 1 then x[0] != 48. Then find_strobogrammatic(n) returns a result r and does not fail, and for every byte vector x, the number of indices j with 0 <= j < len(r) and r[j] = x is 1 if x is in V and 0 otherwise.
    Preconditions: 1 <= n <= 14. -/
  theorem spec_1 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∃ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r ∧
          ∀ x : ByteVector,
            (isStrobogrammatic n.val.toNat x → countOcc r.val x = 1) ∧
            (¬ isStrobogrammatic n.val.toNat x → countOcc r.val x = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∃ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r ∧
            ∀ x : ByteVector,
              (isStrobogrammatic n.val.toNat x → countOcc r.val x = 1) ∧
              (¬ isStrobogrammatic n.val.toNat x → countOcc r.val x = 0)) := by
    sorry

  /-- find_strobogrammatic(n) returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: 1 <= n <= 14. -/
  theorem spec_2 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∃ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∃ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = n.
    Preconditions: 1 <= n <= 14. -/
  theorem spec_3 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ j : Nat, j < r.val.length → (r.val[j]!).val.length = n.val.toNat := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ j : Nat, j < r.val.length → (r.val[j]!).val.length = n.val.toNat) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every j with 0 <= j < len(r) and every i with 0 <= i < len(r[j]), r[j][i] is in {48,49,54,56,57}.
    Preconditions: 1 <= n <= 14. -/
  theorem spec_4 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ j : Nat, j < r.val.length →
            ∀ i : Nat, i < (r.val[j]!).val.length →
              isStrobogrammaticDigit (getByte (r.val[j]!) i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ j : Nat, j < r.val.length →
              ∀ i : Nat, i < (r.val[j]!).val.length →
                isStrobogrammaticDigit (getByte (r.val[j]!) i)) := by
    sorry

  /-- Define rot on bytes by rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54, and define it arbitrarily on all other bytes. Whenever find_strobogrammatic(n) returns a result r, for every j with 0 <= j < len(r), letting x = r[j], we have len(x)=n, every entry of x is in {48,49,54,56,57}, and for every i with 0 <= i < n, rot(x[i]) = x[n-1-i].
    Preconditions: 1 <= n <= 14. -/
  theorem spec_5 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ j : Nat, j < r.val.length → rotationSymmetric n.val.toNat (r.val[j]!) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ j : Nat, j < r.val.length → rotationSymmetric n.val.toNat (r.val[j]!)) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, every element x of r is a valid strobogrammatic number of length n: len(x)=n; every entry of x is in {48,49,54,56,57}; for every i with 0 <= i < n, rot(x[i]) = x[n-1-i] with rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54; and if n > 1 then x[0] != 48.
    Preconditions: 1 <= n <= 14. -/
  theorem spec_6 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ x ∈ r.val, isStrobogrammatic n.val.toNat x := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ x ∈ r.val, isStrobogrammatic n.val.toNat x) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every byte vector x satisfying len(x)=n, every entry of x in {48,49,54,56,57}, rot(x[i]) = x[n-1-i] for all 0 <= i < n (with rot(48)=48, rot(49)=49, rot(54)=57, rot(56)=56, rot(57)=54), and x[0] != 48 if n > 1, there exists j with 0 <= j < len(r) and r[j] = x.
    Preconditions: 1 <= n <= 14. -/
  theorem spec_7 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ x : ByteVector, isStrobogrammatic n.val.toNat x →
            ∃ j : Nat, j < r.val.length ∧ r.val[j]! = x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ x : ByteVector, isStrobogrammatic n.val.toNat x →
              ∃ j : Nat, j < r.val.length ∧ r.val[j]! = x) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: 1 <= n <= 14. -/
  theorem spec_8 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ i j : Nat, i < j → j < r.val.length → r.val[i]! ≠ r.val[j]! := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ i j : Nat, i < j → j < r.val.length → r.val[i]! ≠ r.val[j]!) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every j with 0 <= j < len(r), len(r[j]) = n and r[j][0] != 48.
    Preconditions: 2 <= n <= 14. -/
  theorem spec_9 (n : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ j : Nat, j < r.val.length →
            (r.val[j]!).val.length = n.val.toNat ∧ getByte (r.val[j]!) 0 ≠ 48 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ j : Nat, j < r.val.length →
              (r.val[j]!).val.length = n.val.toNat ∧ getByte (r.val[j]!) 0 ≠ 48) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, for every j with 0 <= j < len(r), letting x = r[j] and m = (n-1)/2, we have len(x)=n and x[m] is in {48,49,56}.
    Preconditions: 1 <= n <= 14 and n is odd. -/
  theorem spec_10 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14)
      (hodd : Odd n.val) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          ∀ j : Nat, j < r.val.length →
            (r.val[j]!).val.length = n.val.toNat ∧
              (getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 48 ∨
                getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 49 ∨
                getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 56) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14)
        (hodd : Odd n.val), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            ∀ j : Nat, j < r.val.length →
              (r.val[j]!).val.length = n.val.toNat ∧
                (getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 48 ∨
                  getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 49 ∨
                  getByte (r.val[j]!) ((n.val.toNat - 1) / 2) = 56)) := by
    sorry

  /-- Whenever find_strobogrammatic(n) returns a result r, len(r) = C(n), where C(1)=3 and, for n >= 2, with k = floor(n/2), C(n) = 4 * 5^(k-1) * (3 if n is odd, 1 if n is even).
    Preconditions: 1 <= n <= 14. -/
  theorem spec_11 (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14) :
      ∀ r : ByteMatrix,
        Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
          r.val.length = expectedCount n.val.toNat := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 14), ∀ r : ByteMatrix,
          Aegis.FindStrobogrammatic.find_strobogrammatic n = Aeneas.Std.Result.ok r →
            r.val.length = expectedCount n.val.toNat) := by
    sorry

  end AegisSpec.FindStrobogrammatic
