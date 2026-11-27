import Aegis.NumOfWays.Code.Funs

/-!
# Specifications of `Aegis.NumOfWays.num_of_ways`

LeetCode problem `number-of-ways-to-paint-n-3-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfWays

  def M : Nat := 1000000007

  def modM (a : Nat) : Nat := a % M

  def CongruentMod (a b : Int) : Prop := ∃ k : Int, a = b + k * (M : Int)

  abbrev GridCell (n : Nat) : Type := Fin n × Fin 3

  def IsProperColoring (n : Nat) (c : GridCell n → Fin 3) : Prop :=
    (∀ (i : Fin n) (j k : Fin 3), j.val + 1 = k.val → c (i, j) ≠ c (i, k)) ∧
      ∀ (i i' : Fin n) (j : Fin 3), i.val + 1 = i'.val → c (i, j) ≠ c (i', j)

  noncomputable def C (n : Nat) : Nat :=
    Nat.card { c : GridCell n → Fin 3 // IsProperColoring n c }

  def TopRowABA {n : Nat} (hn : 0 < n) (c : GridCell n → Fin 3) : Prop :=
    ∃ a b : Fin 3, a ≠ b ∧ c (⟨0, hn⟩, 0) = a ∧ c (⟨0, hn⟩, 1) = b ∧ c (⟨0, hn⟩, 2) = a

  def TopRowDistinct {n : Nat} (hn : 0 < n) (c : GridCell n → Fin 3) : Prop :=
    ∃ a b d : Fin 3,
      a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c (⟨0, hn⟩, 0) = a ∧ c (⟨0, hn⟩, 1) = b ∧
        c (⟨0, hn⟩, 2) = d

  noncomputable def A (n : Nat) (hn : 0 < n) : Nat :=
    Nat.card { c : GridCell n → Fin 3 // IsProperColoring n c ∧ TopRowABA hn c }

  noncomputable def B (n : Nat) (hn : 0 < n) : Nat :=
    Nat.card { c : GridCell n → Fin 3 // IsProperColoring n c ∧ TopRowDistinct hn c }

  /-- Let C(n) be the number of functions c from the cell set {0,...,n-1} x {0,1,2} to the color set {0,1,2} such that c(i,j) != c(i,j+1) for all 0 <= i < n and 0 <= j < 2, and c(i,j) != c(i+1,j) for all 0 <= i < n-1 and 0 <= j < 3. The function returns a result r and r = C(n) mod M, where M = 1000000007 and a mod M denotes the unique integer in [0,M-1] congruent to a modulo M.
    Preconditions: n is an integer with 1 <= n <= 5000. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000) :
      ∃ r : Std.I64,
        Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = (modM (C n.val.toNat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000), ∃ r : Std.I64,
          Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = (modM (C n.val.toNat) : Int)) := by
    sorry

  /-- For every such n, the function returns a result r and does not fail: no arithmetic overflow, panic, or out-of-bounds access occurs.
    Preconditions: n is an integer with 1 <= n <= 5000. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r) := by
    sorry

  /-- For every such n, whenever the function returns a result r, 0 <= r <= 1000000006.
    Preconditions: n is an integer with 1 <= n <= 5000. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000) :
      ∀ r : Std.I64,
        Aegis.NumOfWays.num_of_ways n = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000), ∀ r : Std.I64,
          Aegis.NumOfWays.num_of_ways n = ok r → 0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- The function returns r = 12.
    Preconditions: n = 1. -/
  theorem spec_4 (n : Std.I64) (hn : n.val = 1) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 12 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 12) := by
    sorry

  /-- The function returns r = 54.
    Preconditions: n = 2. -/
  theorem spec_5 (n : Std.I64) (hn : n.val = 2) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 54 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 54) := by
    sorry

  /-- The function returns r = 246.
    Preconditions: n = 3. -/
  theorem spec_6 (n : Std.I64) (hn : n.val = 3) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 246 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 3), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 246) := by
    sorry

  /-- The function returns r = 1122.
    Preconditions: n = 4. -/
  theorem spec_7 (n : Std.I64) (hn : n.val = 4) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 1122 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 4), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 1122) := by
    sorry

  /-- The function returns r = 905790447.
    Preconditions: n = 100. -/
  theorem spec_8 (n : Std.I64) (hn : n.val = 100) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 905790447 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 100), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 905790447) := by
    sorry

  /-- The function returns r = 650420578.
    Preconditions: n = 1000. -/
  theorem spec_9 (n : Std.I64) (hn : n.val = 1000) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 650420578 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1000), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 650420578) := by
    sorry

  /-- The function returns r = 80958521.
    Preconditions: n = 2500. -/
  theorem spec_10 (n : Std.I64) (hn : n.val = 2500) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 80958521 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 2500), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 80958521) := by
    sorry

  /-- The function returns r = 30228214.
    Preconditions: n = 5000. -/
  theorem spec_11 (n : Std.I64) (hn : n.val = 5000) :
      ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 30228214 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 5000), ∃ r : Std.I64, Aegis.NumOfWays.num_of_ways n = ok r ∧ r.val = 30228214) := by
    sorry

  /-- Let C(k) be the number of proper colorings of a k-by-3 grid (each cell colored 0,1,2 so that side-adjacent cells differ). Whenever the function returns r, r is congruent modulo M = 1000000007 to 5*C(n-1) - 2*C(n-2).
    Preconditions: n is an integer with 3 <= n <= 5000. -/
  theorem spec_12 (n : Std.I64) (hn : 3 ≤ n.val ∧ n.val ≤ 5000) :
      ∀ r : Std.I64,
        Aegis.NumOfWays.num_of_ways n = ok r →
          CongruentMod r.val
            (5 * (C (n.val.toNat - 1) : Int) - 2 * (C (n.val.toNat - 2) : Int)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (hn : 3 ≤ n.val ∧ n.val ≤ 5000), ∀ r : Std.I64,
          Aegis.NumOfWays.num_of_ways n = ok r →
            CongruentMod r.val
              (5 * (C (n.val.toNat - 1) : Int) - 2 * (C (n.val.toNat - 2) : Int))) := by
    sorry

  /-- Let A(n) be the number of proper colorings of an n-by-3 grid whose top row has the form (a,b,a) with a != b, and let B(n) be the number of proper colorings whose top row has the form (a,b,c) with a,b,c pairwise distinct. Whenever the function returns r, r is congruent modulo M = 1000000007 to A(n) + B(n).
    Preconditions: n is an integer with 1 <= n <= 5000. -/
  theorem spec_13 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000) :
      ∀ r : Std.I64,
        Aegis.NumOfWays.num_of_ways n = ok r →
          CongruentMod r.val
            ((A n.val.toNat (by omega) : Int) + (B n.val.toNat (by omega) : Int)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 5000), ∀ r : Std.I64,
          Aegis.NumOfWays.num_of_ways n = ok r →
            CongruentMod r.val
              ((A n.val.toNat (by omega) : Int) + (B n.val.toNat (by omega) : Int))) := by
    sorry

  end AegisSpec.NumOfWays
