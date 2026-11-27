import Aegis.ColorTheGrid.Code.Funs

/-!
# Specifications of `Aegis.ColorTheGrid.color_the_grid`

LeetCode problem `painting-a-grid-with-three-different-colors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aeneas.Std.Result

  namespace AegisSpec.ColorTheGrid

  abbrev Coloring (m n : Nat) : Type := Fin m → Fin n → Fin 3

  def IsValidColoring (m n : Nat) (c : Coloring m n) : Prop :=
    (∀ (i i' : Fin m) (j : Fin n), i.val + 1 = i'.val → c i j ≠ c i' j) ∧
    (∀ (i : Fin m) (j j' : Fin n), j.val + 1 = j'.val → c i j ≠ c i j')

  instance isValidColoringDecidable (m n : Nat) : DecidablePred (IsValidColoring m n) :=
    fun c => by unfold IsValidColoring; infer_instance

  def numColorings (m n : Nat) : Nat :=
    Fintype.card { c : Coloring m n // IsValidColoring m n c }

  /-- Let MOD = 1000000007. For a coloring c : {0,...,m-1} x {0,...,n-1} -> {0,1,2}, call c valid if whenever two cells share an edge their colors differ: c(i,j) != c(i+1,j) for every 0 <= i < m-1 and every 0 <= j < n, and c(i,j) != c(i,j+1) for every 0 <= i < m and every 0 <= j < n-1. Let C(m,n) be the number of such valid colorings. Whenever color_the_grid(m,n) returns a result r, r is the unique integer such that 0 <= r < MOD and r = C(m,n) mod MOD.
    Preconditions: m and n are integers satisfying 1 <= m <= 5 and 1 <= n <= 1000. -/
  theorem spec_1 (m n : Std.I64)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 ∧
          r.val = ((numColorings m.val.toNat n.val.toNat : Int) % 1000000007) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (m n : Std.I64)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
          0 ≤ r.val ∧ r.val < 1000000007 ∧
            r.val = ((numColorings m.val.toNat n.val.toNat : Int) % 1000000007)) := by
    sorry

  /-- For every such m and n, color_the_grid(m,n) returns a result r; it does not fail, panic, or return an error due to overflow or out-of-bounds access.
    Preconditions: m and n are integers satisfying 1 <= m <= 5 and 1 <= n <= 1000. -/
  theorem spec_2 (m n : Std.I64)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (m n : Std.I64)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∃ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r) := by
    sorry

  /-- Whenever color_the_grid(m,n) returns a result r, we have 0 <= r <= 1000000006.
    Preconditions: m and n are integers satisfying 1 <= m <= 5 and 1 <= n <= 1000. -/
  theorem spec_3 (m n : Std.I64)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
        0 ≤ r.val ∧ r.val ≤ 1000000006 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (m n : Std.I64)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
          0 ≤ r.val ∧ r.val ≤ 1000000006) := by
    sorry

  /-- Whenever color_the_grid(m,n) returns a result r, r = 3 * 2^(m-1) modulo 1000000007. Equivalently, since m <= 5 and the exact value is at most 48, r is exactly 3 * 2^(m-1).
    Preconditions: m and n are integers satisfying 1 <= m <= 5 and n = 1. -/
  theorem spec_4 (m n : Std.I64)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
      (hn : n.val = 1) :
      ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
        r.val = 3 * 2 ^ (m.val.toNat - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (m n : Std.I64)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
        (hn : n.val = 1), ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
          r.val = 3 * 2 ^ (m.val.toNat - 1)) := by
    sorry

  /-- Whenever color_the_grid(m,n) returns a result r, r = (3 * 2^(n-1)) mod 1000000007.
    Preconditions: m and n are integers satisfying m = 1 and 1 <= n <= 1000. -/
  theorem spec_5 (m n : Std.I64)
      (hm : m.val = 1)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
        r.val = (3 * 2 ^ (n.val.toNat - 1) : Int) % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (m n : Std.I64)
        (hm : m.val = 1)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
          r.val = (3 * 2 ^ (n.val.toNat - 1) : Int) % 1000000007) := by
    sorry

  /-- Whenever color_the_grid(m,n) returns a result r1 and color_the_grid(n,m) returns a result r2, we have r1 = r2.
    Preconditions: m and n are integers satisfying 1 <= m <= 5 and 1 <= n <= 5. -/
  theorem spec_6 (m n : Std.I64)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 5) :
      ∀ r1 r2 : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r1 →
        Aegis.ColorTheGrid.color_the_grid n m = ok r2 → r1 = r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (m n : Std.I64)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 5)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 5), ∀ r1 r2 : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r1 →
          Aegis.ColorTheGrid.color_the_grid n m = ok r2 → r1 = r2) := by
    sorry

  /-- Whenever color_the_grid(m,n) returns a result r, r = (6 * 3^(n-1)) mod 1000000007.
    Preconditions: m and n are integers satisfying m = 2 and 1 <= n <= 1000. -/
  theorem spec_7 (m n : Std.I64)
      (hm : m.val = 2)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
        r.val = (6 * 3 ^ (n.val.toNat - 1) : Int) % 1000000007 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (m n : Std.I64)
        (hm : m.val = 2)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000), ∀ r : Std.I64, Aegis.ColorTheGrid.color_the_grid m n = ok r →
          r.val = (6 * 3 ^ (n.val.toNat - 1) : Int) % 1000000007) := by
    sorry

  end AegisSpec.ColorTheGrid
