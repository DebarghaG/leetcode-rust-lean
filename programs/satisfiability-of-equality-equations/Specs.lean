import Aegis.EquationsPossible.Code.Funs

/-!
# Specifications of `Aegis.EquationsPossible.equations_possible`

LeetCode problem `satisfiability-of-equality-equations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EquationsPossible

abbrev Vec8 := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

abbrev Equations := Aeneas.Std.Slice Vec8

def IsLowerByte (n : Nat) : Prop := 97 ≤ n ∧ n ≤ 122

def byteAt (v : Vec8) (i : Nat) : Nat := ((v.val[i]?).map (fun b => b.val)).getD 0

def eqLhs (v : Vec8) : Nat := byteAt v 0

def eqOp (v : Vec8) : Nat := byteAt v 1

def eqMid (v : Vec8) : Nat := byteAt v 2

def eqRhs (v : Vec8) : Nat := byteAt v 3

def IsEquation (v : Vec8) : Prop :=
  v.val.length = 4 ∧ IsLowerByte (eqLhs v) ∧ IsLowerByte (eqRhs v) ∧
    (eqOp v = 61 ∨ eqOp v = 33) ∧ eqMid v = 61

def IsValidInput (equations : Equations) : Prop :=
  1 ≤ equations.val.length ∧ equations.val.length ≤ 500 ∧
    ∀ v ∈ equations.val, IsEquation v

def Satisfies {M : Type} (A : Nat → M) (v : Vec8) : Prop :=
  (eqOp v = 61 → A (eqLhs v) = A (eqRhs v)) ∧ (eqOp v = 33 → A (eqLhs v) ≠ A (eqRhs v))

def SatisfiesAll {M : Type} (A : Nat → M) (equations : Equations) : Prop :=
  ∀ v ∈ equations.val, Satisfies A v

def countOcc (v : Vec8) (l : List Vec8) : Nat := (l.filter (fun w => w = v)).length

def SubMultiset (l₁ l₂ : List Vec8) : Prop := ∀ v : Vec8, countOcc v l₁ ≤ countOcc v l₂

def EqualEdge (equations : Equations) (a b : Nat) : Prop :=
  ∃ v ∈ equations.val,
    eqOp v = 61 ∧ ((eqLhs v = a ∧ eqRhs v = b) ∨ (eqLhs v = b ∧ eqRhs v = a))

def ForcedEqual (equations : Equations) (a b : Nat) : Prop :=
  Relation.ReflTransGen (EqualEdge equations) a b

/-- Whenever equations_possible(equations) returns a result r, r is true if and only if there exists a total function A from the 26 lowercase ASCII letters {97,98,...,122} to the mathematical integers such that, for every i with 0 <= i < len(equations), the i-th equation is satisfied by A: if equations[i][1] = 61 then A(equations[i][0]) = A(equations[i][3]); if equations[i][1] = 33 then A(equations[i][0]) != A(equations[i][3]). Consequently r is false exactly when no such assignment A exists.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). -/
theorem spec_1 (equations : Equations) (hvalid : IsValidInput equations) :
    ∀ r : Bool,
      Aegis.EquationsPossible.equations_possible equations = ok r →
        ((r = true ↔ ∃ A : Nat → Int, SatisfiesAll A equations) ∧
          (r = false ↔ ¬ ∃ A : Nat → Int, SatisfiesAll A equations)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations), ∀ r : Bool,
      Aegis.EquationsPossible.equations_possible equations = ok r →
        ((r = true ↔ ∃ A : Nat → Int, SatisfiesAll A equations) ∧
          (r = false ↔ ¬ ∃ A : Nat → Int, SatisfiesAll A equations))) := by
  sorry

/-- The call equations_possible(equations) returns a Boolean result (true or false); it does not fail, panic, access an index outside a byte vector, or overflow any machine integer.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). -/
theorem spec_2 (equations : Equations) (hvalid : IsValidInput equations) :
    ∃ r : Bool, Aegis.EquationsPossible.equations_possible equations = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations), ∃ r : Bool, Aegis.EquationsPossible.equations_possible equations = ok r) := by
  sorry

/-- If e[1] = 61 (the equation is x==y), then equations_possible(equations) returns true. If e[1] = 33 (the equation is x!=y), then equations_possible(equations) returns true exactly when e[0] != e[3], and returns false exactly when e[0] = e[3].
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). Also len(equations) = 1. Let e = equations[0]. -/
theorem spec_3 (equations : Equations) (e : Vec8) (hvalid : IsValidInput equations)
    (hlen : equations.val.length = 1) (he : equations.val = [e]) :
    (eqOp e = 61 → Aegis.EquationsPossible.equations_possible equations = ok true) ∧
      (eqOp e = 33 →
        (Aegis.EquationsPossible.equations_possible equations = ok true ↔ eqLhs e ≠ eqRhs e)) ∧
      (eqOp e = 33 →
        (Aegis.EquationsPossible.equations_possible equations = ok false ↔ eqLhs e = eqRhs e)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (equations : Equations) (e : Vec8) (hvalid : IsValidInput equations)
    (hlen : equations.val.length = 1) (he : equations.val = [e]), (eqOp e = 61 → Aegis.EquationsPossible.equations_possible equations = ok true) ∧
      (eqOp e = 33 →
        (Aegis.EquationsPossible.equations_possible equations = ok true ↔ eqLhs e ≠ eqRhs e)) ∧
      (eqOp e = 33 →
        (Aegis.EquationsPossible.equations_possible equations = ok false ↔ eqLhs e = eqRhs e))) := by
  sorry

/-- equations_possible(equations) returns true.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). Also, for every i with 0 <= i < len(equations), equations[i][1] = 61. -/
theorem spec_4 (equations : Equations) (hvalid : IsValidInput equations)
    (hAllEq : ∀ v ∈ equations.val, eqOp v = 61) :
    Aegis.EquationsPossible.equations_possible equations = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations)
    (hAllEq : ∀ v ∈ equations.val, eqOp v = 61), Aegis.EquationsPossible.equations_possible equations = ok true) := by
  sorry

/-- equations_possible(equations) returns false.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). Also, there exists an index i with 0 <= i < len(equations) such that equations[i][1] = 33 and equations[i][0] = equations[i][3]. -/
theorem spec_5 (equations : Equations) (hvalid : IsValidInput equations)
    (hBad : ∃ v ∈ equations.val, eqOp v = 33 ∧ eqLhs v = eqRhs v) :
    Aegis.EquationsPossible.equations_possible equations = ok false := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations)
    (hBad : ∃ v ∈ equations.val, eqOp v = 33 ∧ eqLhs v = eqRhs v), Aegis.EquationsPossible.equations_possible equations = ok false) := by
  sorry

/-- The calls equations_possible(equations) and equations_possible(equations') return the same Boolean result.
  Preconditions: Both equations and equations' are lists satisfying the problem constraints: 1 <= len <= 500; every entry is a four-byte vector with lowercase letters at positions 0 and 3, byte 61 or 33 at position 1, and byte 61 at position 2. Additionally, equations' is a permutation of equations as a multiset of four-byte vectors (the two lists have the same length and every four-byte vector occurs the same number of times in each). -/
theorem spec_6 (equations equations' : Equations) (hvalid : IsValidInput equations)
    (hvalid' : IsValidInput equations') (hperm : equations.val.Perm equations'.val) :
    ∀ r r' : Bool,
      Aegis.EquationsPossible.equations_possible equations = ok r →
        Aegis.EquationsPossible.equations_possible equations' = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (equations equations' : Equations) (hvalid : IsValidInput equations)
    (hvalid' : IsValidInput equations') (hperm : equations.val.Perm equations'.val), ∀ r r' : Bool,
      Aegis.EquationsPossible.equations_possible equations = ok r →
        Aegis.EquationsPossible.equations_possible equations' = ok r' → r = r') := by
  sorry

/-- If equations_possible(F) returns true, then equations_possible(equations) returns true.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). Let F be any list satisfying the same constraints. Assume that every four-byte equation q occurs in equations with multiplicity at most its multiplicity in F (equivalently, the multiset of equations is a sub-multiset of the multiset of equations in F). -/
theorem spec_7 (equations F : Equations) (hvalid : IsValidInput equations)
    (hvalidF : IsValidInput F) (hsub : SubMultiset equations.val F.val) :
    Aegis.EquationsPossible.equations_possible F = ok true →
      Aegis.EquationsPossible.equations_possible equations = ok true := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (equations F : Equations) (hvalid : IsValidInput equations)
    (hvalidF : IsValidInput F) (hsub : SubMultiset equations.val F.val), Aegis.EquationsPossible.equations_possible F = ok true →
      Aegis.EquationsPossible.equations_possible equations = ok true) := by
  sorry

/-- Whenever equations_possible(equations) returns false, there exists an index i with 0 <= i < len(equations) such that equations[i][1] = 33 and, writing x = equations[i][0] and y = equations[i][3], there is a finite sequence of lowercase ASCII letters v0,...,vk with k >= 0, v0 = x, vk = y, and with the following property: for every t with 0 <= t < k, there is an index j with 0 <= j < len(equations) such that equations[j][1] = 61 and the unordered pair {equations[j][0], equations[j][3]} equals {v_t, v_{t+1}}. In words, some disequality x!=y has its two sides forced equal by a chain of equality equations.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). -/
theorem spec_8 (equations : Equations) (hvalid : IsValidInput equations)
    (hFalse : Aegis.EquationsPossible.equations_possible equations = ok false) :
    ∃ v ∈ equations.val, eqOp v = 33 ∧ ForcedEqual equations (eqLhs v) (eqRhs v) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations)
    (hFalse : Aegis.EquationsPossible.equations_possible equations = ok false), ∃ v ∈ equations.val, eqOp v = 33 ∧ ForcedEqual equations (eqLhs v) (eqRhs v)) := by
  sorry

/-- Whenever equations_possible(equations) returns true, there exists a total function A from the 26 lowercase ASCII letters {97,...,122} to the set {0,1,...,25} such that for every i with 0 <= i < len(equations), if equations[i][1] = 61 then A(equations[i][0]) = A(equations[i][3]), and if equations[i][1] = 33 then A(equations[i][0]) != A(equations[i][3]).
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). -/
theorem spec_9 (equations : Equations) (hvalid : IsValidInput equations)
    (hTrue : Aegis.EquationsPossible.equations_possible equations = ok true) :
    ∃ A : Nat → Fin 26, SatisfiesAll A equations := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations)
    (hTrue : Aegis.EquationsPossible.equations_possible equations = ok true), ∃ A : Nat → Fin 26, SatisfiesAll A equations) := by
  sorry

/-- If there exists an index i with 0 <= i < len(equations) such that equations[i][1] = 33, and, writing x = equations[i][0] and y = equations[i][3], there is a finite sequence of lowercase ASCII letters v0,...,vk with k >= 0, v0 = x, vk = y, and for every t with 0 <= t < k there is an index j with 0 <= j < len(equations) such that equations[j][1] = 61 and the unordered pair {equations[j][0], equations[j][3]} equals {v_t, v_{t+1}}, then equations_possible(equations) returns false.
  Preconditions: The input list equations satisfies the problem constraints: 1 <= len(equations) <= 500; for every i with 0 <= i < len(equations), len(equations[i]) = 4; equations[i][0] and equations[i][3] are lowercase ASCII letters (byte codes 97 through 122 inclusive); equations[i][1] is either 61 ('=') or 33 ('!'); equations[i][2] is 61 ('='). -/
theorem spec_10 (equations : Equations) (hvalid : IsValidInput equations)
    (hChain : ∃ v ∈ equations.val, eqOp v = 33 ∧ ForcedEqual equations (eqLhs v) (eqRhs v)) :
    Aegis.EquationsPossible.equations_possible equations = ok false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (equations : Equations) (hvalid : IsValidInput equations)
    (hChain : ∃ v ∈ equations.val, eqOp v = 33 ∧ ForcedEqual equations (eqLhs v) (eqRhs v)), Aegis.EquationsPossible.equations_possible equations = ok false) := by
  sorry

end AegisSpec.EquationsPossible
