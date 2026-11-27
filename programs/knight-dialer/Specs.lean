import Aegis.KnightDialer.Code.Funs

/-!
# Specifications of `Aegis.KnightDialer.knight_dialer`

LeetCode problem `knight-dialer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KnightDialer

  def knightPairs : List (Nat × Nat) :=
    [(0, 4), (0, 6), (1, 6), (1, 8), (2, 7), (2, 9), (3, 4), (3, 8), (4, 9), (6, 7)]

  def knightMove (a b : Nat) : Prop :=
    (a, b) ∈ knightPairs ∨ (b, a) ∈ knightPairs

  instance instDecidableKnightMove (a b : Nat) : Decidable (knightMove a b) :=
    decidable_of_iff ((a, b) ∈ knightPairs ∨ (b, a) ∈ knightPairs) Iff.rfl

  def allDigits : Finset Nat :=
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}

  def nineDigits : Finset Nat :=
    {0, 1, 2, 3, 4, 6, 7, 8, 9}

  def IsKnightSeq (D : Finset Nat) {n : Nat} (d : Fin n → Fin 10) : Prop :=
    (∀ i : Fin n, (d i).val ∈ D) ∧
      ∀ i j : Fin n, i.val + 1 = j.val → knightMove (d i).val (d j).val

  instance instDecidablePredIsKnightSeq (D : Finset Nat) (n : Nat) :
      DecidablePred (fun d : Fin n → Fin 10 => IsKnightSeq D d) :=
    fun d =>
      decidable_of_iff
        ((∀ i : Fin n, (d i).val ∈ D) ∧
          ∀ i j : Fin n, i.val + 1 = j.val → knightMove (d i).val (d j).val)
        Iff.rfl

  def knightCount (D : Finset Nat) (n : Nat) : Nat :=
    (Finset.univ.filter (fun d : Fin n → Fin 10 => IsKnightSeq D d)).card

  /-- Let M = 1000000007. For digits a,b in {0,1,2,3,4,5,6,7,8,9}, say knightMove(a,b) holds exactly when the unordered pair {a,b} is one of {0,4}, {0,6}, {1,6}, {1,8}, {2,7}, {2,9}, {3,4}, {3,8}, {4,9}, {6,7}. Let C(n) be the number of sequences (d_0,...,d_{n-1}) such that every d_i is in {0,1,2,3,4,5,6,7,8,9} and knightMove(d_i,d_{i+1}) holds for every i with 0 <= i < n-1. Then knight_dialer(n) returns a result r and r is the unique integer in the interval [0,M-1] congruent to C(n) modulo M.
    Preconditions: n is an I64 satisfying 1 <= n <= 5000. -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000) :
      ∃ r : Std.I64,
        Aegis.KnightDialer.knight_dialer n = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val ≡ ((knightCount allDigits n.val.toNat : Nat) : ℤ) [ZMOD 1000000007] := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000), ∃ r : Std.I64,
          Aegis.KnightDialer.knight_dialer n = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
              r.val ≡ ((knightCount allDigits n.val.toNat : Nat) : ℤ) [ZMOD 1000000007]) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and 0 <= r < 1000000007.
    Preconditions: n is an I64 satisfying 1 <= n <= 5000. -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000) :
      ∃ r : Std.I64,
        Aegis.KnightDialer.knight_dialer n = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000), ∃ r : Std.I64,
          Aegis.KnightDialer.knight_dialer n = ok r ∧ 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- For every n with 1 <= n <= 5000, the call knight_dialer(n) returns a result; it does not fail, panic, or overflow.
    Preconditions: n is an I64 satisfying 1 <= n <= 5000. -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 5000), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 10.
    Preconditions: n is an I64 and n = 1. -/
  theorem spec_4 (n : Std.I64) (hn : n.val = 1) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 10 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 10) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 20.
    Preconditions: n is an I64 and n = 2. -/
  theorem spec_5 (n : Std.I64) (hn : n.val = 2) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 20 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 20) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 46.
    Preconditions: n is an I64 and n = 3. -/
  theorem spec_6 (n : Std.I64) (hn : n.val = 3) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 46 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 3), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 46) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 104.
    Preconditions: n is an I64 and n = 4. -/
  theorem spec_7 (n : Std.I64) (hn : n.val = 4) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 104 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 4), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 104) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 267287516.
    Preconditions: n is an I64 and n = 50. -/
  theorem spec_8 (n : Std.I64) (hn : n.val = 50) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 267287516 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 50), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 267287516) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 540641702.
    Preconditions: n is an I64 and n = 100. -/
  theorem spec_9 (n : Std.I64) (hn : n.val = 100) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 540641702 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 540641702) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 136006598.
    Preconditions: n is an I64 and n = 3131. -/
  theorem spec_10 (n : Std.I64) (hn : n.val = 3131) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 136006598 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 3131), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 136006598) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 851996060.
    Preconditions: n is an I64 and n = 2500. -/
  theorem spec_11 (n : Std.I64) (hn : n.val = 2500) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 851996060 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2500), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 851996060) := by
    sorry

  /-- The call knight_dialer(n) returns a result r, and r = 406880451.
    Preconditions: n is an I64 and n = 5000. -/
  theorem spec_12 (n : Std.I64) (hn : n.val = 5000) :
      ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 406880451 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 5000), ∃ r : Std.I64, Aegis.KnightDialer.knight_dialer n = ok r ∧ r.val = 406880451) := by
    sorry

  /-- Let C9(n) be the number of sequences (d_0,...,d_{n-1}) such that every d_i is in {0,1,2,3,4,6,7,8,9} and knightMove(d_i,d_{i+1}) holds for every i with 0 <= i < n-1, where knightMove is the relation defined by the unordered pairs {0,4}, {0,6}, {1,6}, {1,8}, {2,7}, {2,9}, {3,4}, {3,8}, {4,9}, {6,7}. Then knight_dialer(n) returns a result r and r is the unique integer in [0,1000000006] congruent to C9(n) modulo 1000000007.
    Preconditions: n is an I64 satisfying 2 <= n <= 5000. -/
  theorem spec_13 (n : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 5000) :
      ∃ r : Std.I64,
        Aegis.KnightDialer.knight_dialer n = ok r ∧
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val ≡ ((knightCount nineDigits n.val.toNat : Nat) : ℤ) [ZMOD 1000000007] := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 5000), ∃ r : Std.I64,
          Aegis.KnightDialer.knight_dialer n = ok r ∧
            0 ≤ r.val ∧ r.val < 1000000007 ∧
              r.val ≡ ((knightCount nineDigits n.val.toNat : Nat) : ℤ) [ZMOD 1000000007]) := by
    sorry

  end AegisSpec.KnightDialer
