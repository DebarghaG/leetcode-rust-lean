import Aegis.MinimumBoxes.Code.Funs

/-!
# Specifications of `Aegis.MinimumBoxes.minimum_boxes`

LeetCode problem `building-boxes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumBoxes

namespace AegisSpec.MinimumBoxes

def tri (a : ℤ) : ℤ := a * (a + 1) / 2

def tetra (a : ℤ) : ℤ := a * (a + 1) * (a + 2) / 6

def floorTri (m : ℤ) : ℤ :=
  if 0 ≤ m then ((Nat.findGreatest (fun a : ℕ => tri (a : ℤ) ≤ m) m.toNat : ℕ) : ℤ) else 0

def C (m : ℤ) : ℤ :=
  if m ≤ 0 then 0 else tetra (floorTri m) + tri (m - tri (floorTri m))

structure Point where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

def inRoom (n : ℤ) (p : Point) : Prop :=
  0 ≤ p.x ∧ p.x < n ∧ 0 ≤ p.y ∧ p.y < n ∧ 0 ≤ p.z ∧ p.z < n

def shiftBelow (p : Point) (dx dy : ℤ) : Point := ⟨p.x + dx, p.y + dy, p.z - 1⟩

def isNeighbourDir (dx dy : ℤ) : Prop :=
  (dx, dy) = (1, 0) ∨ (dx, dy) = (-1, 0) ∨ (dx, dy) = (0, 1) ∨ (dx, dy) = (0, -1)

def outsideHoriz (n : ℤ) (p : Point) (dx dy : ℤ) : Prop :=
  p.x + dx < 0 ∨ n ≤ p.x + dx ∨ p.y + dy < 0 ∨ n ≤ p.y + dy

def supported (n : ℤ) (P : Finset Point) : Prop :=
  ∀ p ∈ P, 1 ≤ p.z →
    (⟨p.x, p.y, p.z - 1⟩ : Point) ∈ P ∧
      ∀ dx dy : ℤ, isNeighbourDir dx dy →
        outsideHoriz n p dx dy ∨ shiftBelow p dx dy ∈ P

def validPlacement (n : ℤ) (P : Finset Point) : Prop :=
  P.card = n.toNat ∧ (∀ p ∈ P, inRoom n p) ∧ supported n P

def floorCount (P : Finset Point) : ℕ := (P.filter (fun p => p.z = 0)).card

/-- Let A be the largest integer a >= 1 such that a*(a+1)*(a+2)/6 <= n. Let R = n - A*(A+1)*(A+2)/6. Let F be the least integer f >= 0 such that f*(f+1)/2 >= R. The function returns a result r and r = A*(A+1)/2 + F.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (A F : ℤ)
    (hA_lo : 1 ≤ A)
    (hA_le : tetra A ≤ n.val)
    (hA_max : ∀ a : ℤ, 1 ≤ a → tetra a ≤ n.val → a ≤ A)
    (hF_lo : 0 ≤ F)
    (hF_ge : tri F ≥ n.val - tetra A)
    (hF_min : ∀ f : ℤ, 0 ≤ f → tri f ≥ n.val - tetra A → F ≤ f) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ r.val = tri A + F := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (A F : ℤ)
    (hA_lo : 1 ≤ A)
    (hA_le : tetra A ≤ n.val)
    (hA_max : ∀ a : ℤ, 1 ≤ a → tetra a ≤ n.val → a ≤ A)
    (hF_lo : 0 ≤ F)
    (hF_ge : tri F ≥ n.val - tetra A)
    (hF_min : ∀ f : ℤ, 0 ≤ f → tri f ≥ n.val - tetra A → F ≤ f), ∃ r : Std.I64, minimum_boxes n = ok r ∧ r.val = tri A + F) := by
  sorry

/-- The function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r) := by
  sorry

/-- The function returns r and 1 <= r <= n.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_3 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧ 1 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- Define C(0) = 0. For m >= 1, let a be the largest integer with a*(a+1)/2 <= m, let e = m - a*(a+1)/2, and define C(m) = a*(a+1)*(a+2)/6 + e*(e+1)/2. The function returns r and n <= C(r).
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_4 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ n.val ≤ C r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧ n.val ≤ C r.val) := by
  sorry

/-- Define C(0) = 0. For m >= 1, let a be the largest integer with a*(a+1)/2 <= m, let e = m - a*(a+1)/2, and define C(m) = a*(a+1)*(a+2)/6 + e*(e+1)/2. The function returns r and C(r-1) < n.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_5 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ C (r.val - 1) < n.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧ C (r.val - 1) < n.val) := by
  sorry

/-- The function returns r. Consider every valid placement P: a set of n integer triples (x,y,z) with 0 <= x,y,z < n such that for every (x,y,z) in P with z > 0, the triple (x,y,z-1) is in P, and for each (dx,dy) in {(1,0),(-1,0),(0,1),(0,-1)}, either (x+dx,y+dy,z-1) lies outside the room (x+dx < 0 or x+dx >= n or y+dy < 0 or y+dy >= n) or (x+dx,y+dy,z-1) is in P. For every such P, the number of triples in P with z=0 is at least r.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_6 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧
      ∀ P : Finset Point, validPlacement n.val P → r.val ≤ (floorCount P : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧
      ∀ P : Finset Point, validPlacement n.val P → r.val ≤ (floorCount P : ℤ)) := by
  sorry

/-- The function returns r. There exists a valid placement P, defined as a set of n integer triples (x,y,z) with 0 <= x,y,z < n such that for every (x,y,z) in P with z > 0, the triple (x,y,z-1) is in P, and for each (dx,dy) in {(1,0),(-1,0),(0,1),(0,-1)}, either (x+dx,y+dy,z-1) lies outside the room or (x+dx,y+dy,z-1) is in P, such that exactly r triples in P have z=0.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_7 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧
      ∃ P : Finset Point, validPlacement n.val P ∧ (floorCount P : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧
      ∃ P : Finset Point, validPlacement n.val P ∧ (floorCount P : ℤ) = r.val) := by
  sorry

/-- Let r1 = minimum_boxes(n1) and r2 = minimum_boxes(n2). Both calls return results and r1 <= r2.
  Preconditions: n1 and n2 are integers with 1 <= n1 <= n2 <= 1000000000. -/
theorem spec_8 (n1 n2 : Std.I64) (h1_lo : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val)
    (h2_hi : n2.val ≤ 1000000000) :
    ∃ r1 r2 : Std.I64,
      minimum_boxes n1 = ok r1 ∧ minimum_boxes n2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n1 n2 : Std.I64) (h1_lo : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val)
    (h2_hi : n2.val ≤ 1000000000), ∃ r1 r2 : Std.I64,
      minimum_boxes n1 = ok r1 ∧ minimum_boxes n2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Let r = minimum_boxes(n) and r' = minimum_boxes(n+1). Both calls return results and r <= r' <= r+1.
  Preconditions: n is an integer with 1 <= n < 1000000000. -/
theorem spec_9 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val < 1000000000) :
    ∃ nm r r' : Std.I64,
      (n + 1#i64 : Result Std.I64) = ok nm ∧
        minimum_boxes n = ok r ∧ minimum_boxes nm = ok r' ∧
          r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val < 1000000000), ∃ nm r r' : Std.I64,
      (n + 1#i64 : Result Std.I64) = ok nm ∧
        minimum_boxes n = ok r ∧ minimum_boxes nm = ok r' ∧
          r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- The function returns r and r = 1 if and only if n = 1.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_10 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ (r.val = 1 ↔ n.val = 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧ (r.val = 1 ↔ n.val = 1)) := by
  sorry

/-- Let A be the largest integer a >= 1 such that a*(a+1)*(a+2)/6 <= n. The function returns r and A*(A+1)/2 <= r <= (A+1)*(A+2)/2.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_11 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (A : ℤ)
    (hA_lo : 1 ≤ A)
    (hA_le : tetra A ≤ n.val)
    (hA_max : ∀ a : ℤ, 1 ≤ a → tetra a ≤ n.val → a ≤ A) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ tri A ≤ r.val ∧ r.val ≤ tri (A + 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (A : ℤ)
    (hA_lo : 1 ≤ A)
    (hA_le : tetra A ≤ n.val)
    (hA_max : ∀ a : ℤ, 1 ≤ a → tetra a ≤ n.val → a ≤ A), ∃ r : Std.I64, minimum_boxes n = ok r ∧ tri A ≤ r.val ∧ r.val ≤ tri (A + 1)) := by
  sorry

/-- The function returns r and r <= 1650467.
  Preconditions: n is an integer with 1 <= n <= 1000000000. -/
theorem spec_12 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000) :
    ∃ r : Std.I64, minimum_boxes n = ok r ∧ r.val ≤ 1650467 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000), ∃ r : Std.I64, minimum_boxes n = ok r ∧ r.val ≤ 1650467) := by
  sorry

end AegisSpec.MinimumBoxes
