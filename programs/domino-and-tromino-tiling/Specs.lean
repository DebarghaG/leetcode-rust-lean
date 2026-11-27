import Aegis.NumTilings.Code.Funs

/-!
# Specifications of `Aegis.NumTilings.num_tilings`

LeetCode problem `domino-and-tromino-tiling`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumTilings

def i64OfInt (v : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 v⟩

def board (k : ℕ) : Finset (ℕ × ℕ) := (Finset.range 2).product (Finset.range k)

def IsDomino (t : Finset (ℕ × ℕ)) : Prop :=
  ∃ r c : ℕ, t = {(r, c), (r, c + 1)} ∨ t = {(r, c), (r + 1, c)}

def IsLTromino (t : Finset (ℕ × ℕ)) : Prop :=
  ∃ r c : ℕ,
    t = {(r, c), (r, c + 1), (r + 1, c)} ∨
      t = {(r, c), (r, c + 1), (r + 1, c + 1)} ∨
        t = {(r, c), (r + 1, c), (r + 1, c + 1)} ∨
          t = {(r, c + 1), (r + 1, c), (r + 1, c + 1)}

def IsTile (t : Finset (ℕ × ℕ)) : Prop := IsDomino t ∨ IsLTromino t

def IsTiling (k : ℕ) (ts : Finset (Finset (ℕ × ℕ))) : Prop :=
  (∀ t ∈ ts, IsTile t) ∧ (∀ t ∈ ts, t ⊆ board k) ∧
    ∀ p ∈ board k, ∃! t, t ∈ ts ∧ p ∈ t

def Tilings (k : ℕ) : Type := { ts : Finset (Finset (ℕ × ℕ)) // IsTiling k ts }

noncomputable def T (k : ℕ) : ℕ := Nat.card (Tilings k)

/-- Let M = 1000000007. For k >= 0, let T(k) be the number of distinct tilings of the 2 x k board by tiles that lie inside the board and cover every cell exactly once, where each tile is either a domino (two 4-adjacent cells forming a 1 x 2 or 2 x 1 rectangle) or an L-tromino (three cells forming a 2 x 2 square with exactly one cell removed, in any rotation); T(0) = 1 for the empty board. Whenever the function returns a result r, the integer value of r is the unique integer in [0, M-1] congruent to T(n) modulo M.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∃ r : Std.I64,
      Aegis.NumTilings.num_tilings n = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧ (r.val ≡ (T n.val.toNat : ℤ) [ZMOD 1000000007]) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∃ r : Std.I64,
      Aegis.NumTilings.num_tilings n = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧ (r.val ≡ (T n.val.toNat : ℤ) [ZMOD 1000000007])) := by
  sorry

/-- For every n with 1 <= n <= 1000, the function returns a result r; it does not fail, overflow, panic, or access out of bounds for these inputs.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000) :
    ∃ r : Std.I64, Aegis.NumTilings.num_tilings n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000), ∃ r : Std.I64, Aegis.NumTilings.num_tilings n = ok r) := by
  sorry

/-- Let M = 1000000007. Whenever the function returns a result r, the integer value of r satisfies 0 <= r < M.
  Preconditions: 1 <= n <= 1000. -/
theorem spec_3 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000)
    (hr : Aegis.NumTilings.num_tilings n = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 1000)
    (hr : Aegis.NumTilings.num_tilings n = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Let M = 1000000007. If the function returns r for input n, r1 for input n-1, and r3 for input n-3, then the integer value of r equals the unique integer in [0, M-1] congruent to 2*(integer value of r1) + (integer value of r3) modulo M.
  Preconditions: 4 <= n <= 1000. -/
theorem spec_4 (n r r1 r3 : Std.I64) (hlo : 4 ≤ n.val) (hhi : n.val ≤ 1000)
    (hr : Aegis.NumTilings.num_tilings n = ok r)
    (hr1 : Aegis.NumTilings.num_tilings (i64OfInt (n.val - 1)) = ok r1)
    (hr3 : Aegis.NumTilings.num_tilings (i64OfInt (n.val - 3)) = ok r3) :
    0 ≤ r.val ∧ r.val < 1000000007 ∧ (r.val ≡ 2 * r1.val + r3.val [ZMOD 1000000007]) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n r r1 r3 : Std.I64) (hlo : 4 ≤ n.val) (hhi : n.val ≤ 1000)
    (hr : Aegis.NumTilings.num_tilings n = ok r)
    (hr1 : Aegis.NumTilings.num_tilings (i64OfInt (n.val - 1)) = ok r1)
    (hr3 : Aegis.NumTilings.num_tilings (i64OfInt (n.val - 3)) = ok r3), 0 ≤ r.val ∧ r.val < 1000000007 ∧ (r.val ≡ 2 * r1.val + r3.val [ZMOD 1000000007])) := by
  sorry

end AegisSpec.NumTilings
