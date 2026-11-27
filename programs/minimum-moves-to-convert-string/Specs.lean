import Aegis.MinimumMoves.Code.Funs

/-!
# Specifications of `Aegis.MinimumMoves.minimum_moves`

LeetCode problem `minimum-moves-to-convert-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumMoves

def allOX (l : List U8) : Prop := ∀ b ∈ l, b.val = 79 ∨ b.val = 88

def XAt (s : Slice U8) (i : Int) : Prop :=
  ∃ b : U8, s.val[i.toNat]? = some b ∧ b.val = 88

def OAt (s : Slice U8) (i : Int) : Prop :=
  ∃ b : U8, s.val[i.toNat]? = some b ∧ b.val = 79

def countX (s : Slice U8) : Nat := s.val.countP (fun b => b.val == 88)

def ceilDiv3 (c : Nat) : Nat := (c + 2) / 3

def IsMoveStart (n : Nat) (j : Int) : Prop := 0 ≤ j ∧ j ≤ (n : Int) - 3

def CoversX (s : Slice U8) (J : Finset Int) : Prop :=
  ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → XAt s i → ∃ j ∈ J, j ≤ i ∧ i ≤ j + 2

def IsMoveCover (s : Slice U8) (J : Finset Int) : Prop :=
  (∀ j ∈ J, IsMoveStart s.val.length j) ∧ CoversX s J

def IsMinMoveCover (s : Slice U8) (r : Int) : Prop :=
  (∃ J : Finset Int, IsMoveCover s J ∧ (J.card : Int) = r) ∧
    ∀ J : Finset Int, IsMoveCover s J → r ≤ (J.card : Int)

def IsXPacking (s : Slice U8) (P : Finset Int) : Prop :=
  (∀ p ∈ P, 0 ≤ p ∧ p < (s.val.length : Int) ∧ XAt s p) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 3 ≤ (p - q).natAbs

def IsMaxPacking (s : Slice U8) (r : Int) : Prop :=
  (∃ P : Finset Int, IsXPacking s P ∧ (P.card : Int) = r) ∧
    ∀ P : Finset Int, IsXPacking s P → (P.card : Int) ≤ r

def isXb (b : U8) : Bool := b.val == 88

def greedyPicksAux : Nat → List U8 → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, b :: bs =>
      if isXb b then 0 :: (greedyPicksAux k (bs.drop 2)).map (fun i => i + 3)
      else (greedyPicksAux k bs).map (fun i => i + 1)

def greedyPicks (l : List U8) : List Nat := greedyPicksAux l.length l

/-- The function returns a result r and r is the minimum cardinality of a set J of integers such that: (a) every j in J satisfies 0 <= j <= n - 3; and (b) for every i with 0 <= i < n and s[i] = 88 ('X'), there is some j in J with j <= i <= j + 2. The empty set J is allowed; if there is no 'X', the minimum is 0. Each j in J represents one move applied to the three consecutive positions j, j+1, j+2.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_1 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ IsMinMoveCover s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ IsMinMoveCover s r.val) := by
  sorry

/-- The function returns a result r and does not fail: there is no panic, no out-of-bounds access, and no arithmetic overflow for any input satisfying the preconditions.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_2 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_3 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= C, where C is the number of indices i with 0 <= i < n and s[i] = 88 ('X').
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_4 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → r.val ≤ (countX s : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → r.val ≤ (countX s : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= ceil(C/3), where C is the number of indices i with 0 <= i < n and s[i] = 88 ('X'), and ceil(C/3) is the least integer k with 3k >= C.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_5 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → (ceilDiv3 (countX s) : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → (ceilDiv3 (countX s) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= ceil(n/3), where ceil(n/3) is the least integer k with 3k >= n.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_6 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → r.val ≤ (ceilDiv3 s.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r → r.val ≤ (ceilDiv3 s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < n and s[i] = 88 ('X'). Equivalently, r = 0 if and only if s[i] = 79 ('O') for every i with 0 <= i < n.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_7 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → ¬ XAt s i) ∧
      (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → OAt s i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → ¬ XAt s i) ∧
      (r.val = 0 ↔ ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → OAt s i)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if both: (a) there exists i with 0 <= i < n and s[i] = 88 ('X'); and (b) there exists j with 0 <= j <= n - 3 such that for every i with 0 <= i < n and s[i] = 88 ('X'), j <= i <= j + 2.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_8 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (r.val = 1 ↔
        (∃ i : Int, 0 ≤ i ∧ i < (s.val.length : Int) ∧ XAt s i) ∧
        ∃ j : Int, IsMoveStart s.val.length j ∧
          ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → XAt s i → j ≤ i ∧ i ≤ j + 2) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (r.val = 1 ↔
        (∃ i : Int, 0 ≤ i ∧ i < (s.val.length : Int) ∧ XAt s i) ∧
        ∃ j : Int, IsMoveStart s.val.length j ∧
          ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → XAt s i → j ≤ i ∧ i ≤ j + 2)) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if b - a <= 2; otherwise r = 2.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; there are exactly two indices a and b with 0 <= a < b < n, s[a] = s[b] = 88 ('X'), and s[i] = 79 ('O') for every other i with 0 <= i < n. -/
theorem spec_9 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) (a b : Int) (ha0 : 0 ≤ a) (hab : a < b)
    (hb : b < (s.val.length : Int)) (hXa : XAt s a) (hXb : XAt s b)
    (hother : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → i ≠ a → i ≠ b → OAt s i) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (b - a ≤ 2 → r.val = 1) ∧ (2 < b - a → r.val = 2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) (a b : Int) (ha0 : 0 ≤ a) (hab : a < b)
    (hb : b < (s.val.length : Int)) (hXa : XAt s a) (hXb : XAt s b)
    (hother : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → i ≠ a → i ≠ b → OAt s i), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      (b - a ≤ 2 → r.val = 1) ∧ (2 < b - a → r.val = 2)) := by
  sorry

/-- If for every i with 0 <= i < n, s[i] = 88 ('X') implies t[i] = 88 ('X'), then whenever the calls minimum_moves(s) and minimum_moves(t) return results r_s and r_t, we have r_s <= r_t.
  Preconditions: Let s and t be two byte slices of the same length n with 3 <= n <= 1000, and assume every byte of each is 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_10 (s t : Slice U8) (hlen : s.val.length = t.val.length)
    (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hoxs : allOX s.val) (hoxt : allOX t.val)
    (hmono : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → XAt s i → XAt t i) :
    ∀ r_s r_t : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t → r_s.val ≤ r_t.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s t : Slice U8) (hlen : s.val.length = t.val.length)
    (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hoxs : allOX s.val) (hoxt : allOX t.val)
    (hmono : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → XAt s i → XAt t i), ∀ r_s r_t : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t → r_s.val ≤ r_t.val) := by
  sorry

/-- Whenever minimum_moves(s) returns r_s and minimum_moves(t) returns r_t, r_s = r_t.
  Preconditions: Let s be a byte slice with n = len(s), 3 <= n <= 1000, and every s[i] either 79 (ASCII 'O') or 88 (ASCII 'X'). Let t be the byte slice of the same length defined by t[i] = s[n-1-i] for all i with 0 <= i < n. -/
theorem spec_11 (s t : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) (ht : t.val = s.val.reverse) :
    ∀ r_s r_t : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t → r_s = r_t := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) (ht : t.val = s.val.reverse), ∀ r_s r_t : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t → r_s = r_t) := by
  sorry

/-- Whenever minimum_moves(s), minimum_moves(t), and minimum_moves(u) return results r_s, r_t, and r_u, we have r_t = r_s and r_u = r_s.
  Preconditions: Let s be a byte slice with n = len(s), 3 <= n <= 999, and every s[i] either 79 (ASCII 'O') or 88 (ASCII 'X'). Let t be the length n+1 byte slice with t[0] = 79 ('O') and t[i+1] = s[i] for 0 <= i < n. Let u be the length n+1 byte slice with u[i] = s[i] for 0 <= i < n and u[n] = 79 ('O'). -/
theorem spec_12 (s t u : Slice U8) (h3 : 3 ≤ s.val.length) (h999 : s.val.length ≤ 999)
    (hox : allOX s.val) (ht : t.val = 79#u8 :: s.val) (hu : u.val = s.val ++ [79#u8]) :
    ∀ r_s r_t r_u : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t →
      Aegis.MinimumMoves.minimum_moves u = ok r_u → r_t = r_s ∧ r_u = r_s := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s t u : Slice U8) (h3 : 3 ≤ s.val.length) (h999 : s.val.length ≤ 999)
    (hox : allOX s.val) (ht : t.val = 79#u8 :: s.val) (hu : u.val = s.val ++ [79#u8]), ∀ r_s r_t r_u : I64, Aegis.MinimumMoves.minimum_moves s = ok r_s →
      Aegis.MinimumMoves.minimum_moves t = ok r_t →
      Aegis.MinimumMoves.minimum_moves u = ok r_u → r_t = r_s ∧ r_u = r_s) := by
  sorry

/-- Whenever the function returns a result r, for every set P of integers such that 0 <= p < n and s[p] = 88 ('X') for every p in P, and |p - q| >= 3 for every two distinct p,q in P, we have r >= |P|.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_13 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      ∀ P : Finset Int, IsXPacking s P → (P.card : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      ∀ P : Finset Int, IsXPacking s P → (P.card : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists a set P of exactly r indices such that: (a) for every p in P, 0 <= p < n and s[p] = 88 ('X'); and (b) for every two distinct p,q in P, |p - q| >= 3.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_14 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      ∃ P : Finset Int, (P.card : Int) = r.val ∧ IsXPacking s P := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∀ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r →
      ∃ P : Finset Int, (P.card : Int) = r.val ∧ IsXPacking s P) := by
  sorry

/-- The function returns a result r and r = max { |P| : P is a set of indices such that 0 <= p < n and s[p] = 88 ('X') for every p in P, and |p - q| >= 3 for every two distinct p,q in P }.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_15 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ IsMaxPacking s r.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ IsMaxPacking s r.val) := by
  sorry

/-- Define a finite increasing sequence p_0 < p_1 < ... < p_{m-1} of indices by: p_0 is the least i with s[i] = 88 ('X') (if none, m=0); and for each k, p_{k+1} is the least i such that p_k + 3 <= i < n and s[i] = 88 ('X'), if such an i exists. Then the function returns m.
  Preconditions: Let n = len(s). Preconditions: 3 <= n <= 1000; for every i with 0 <= i < n, s[i] is either 79 (ASCII 'O') or 88 (ASCII 'X'). -/
theorem spec_16 (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val) :
    ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ r.val = ((greedyPicks s.val).length : Int) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (s : Slice U8) (h3 : 3 ≤ s.val.length) (h1000 : s.val.length ≤ 1000)
    (hox : allOX s.val), ∃ r : I64, Aegis.MinimumMoves.minimum_moves s = ok r ∧ r.val = ((greedyPicks s.val).length : Int)) := by
  sorry

end AegisSpec.MinimumMoves
