import Aegis.TilingRectangle.Code.Funs

/-!
# Specifications of `Aegis.TilingRectangle.tiling_rectangle`

LeetCode problem `tiling-a-rectangle-with-the-fewest-squares`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TilingRectangle

  structure Square where

    x : ℤ

    y : ℤ

    s : ℤ

  def Square.cells (q : Square) : Set (ℤ × ℤ) :=
    { p | q.x ≤ p.1 ∧ p.1 < q.x + q.s ∧ q.y ≤ p.2 ∧ p.2 < q.y + q.s }

  def rectCells (n m : ℕ) : Set (ℤ × ℤ) :=
    { p | 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 < (m : ℤ) }

  def IsTiling (n m : ℕ) (l : List Square) : Prop :=

    (∀ q ∈ l, 0 < q.s) ∧

    (∀ q ∈ l, 0 ≤ q.x ∧ q.x + q.s ≤ (n : ℤ) ∧ 0 ≤ q.y ∧ q.y + q.s ≤ (m : ℤ)) ∧

    (∀ q ∈ l, ∀ q' ∈ l, q ≠ q' → Disjoint q.cells q'.cells) ∧

    rectCells n m = { p | ∃ q ∈ l, p ∈ q.cells }

  noncomputable def mu (n m : ℕ) : ℕ :=
    sInf { k : ℕ | ∃ l : List Square, IsTiling n m l ∧ l.length = k }

  /-- Let T(n,m) be the set of all tilings of the n by m rectangle by axis-aligned squares with integer side lengths and integer corner coordinates, whose interiors are pairwise disjoint and whose union is exactly the rectangle. Let mu(n,m) = min { |F| : F in T(n,m) }. Whenever tiling_rectangle(n,m) returns a result r, r = mu(n,m).
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_1 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      r.val = (mu n.val.toNat m.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), r.val = (mu n.val.toNat m.val.toNat : ℤ)) := by
    sorry

  /-- tiling_rectangle(n,m) returns a result r; it does not fail by overflow, out-of-bounds access, panic, or any other failure.
    Preconditions: 1 <= n <= 13 and 1 <= m <= 13. -/
  theorem spec_2 (n m : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 13)
      (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 13) :
      ∃ r, Aegis.TilingRectangle.tiling_rectangle n m = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n m : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 13)
        (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 13), ∃ r, Aegis.TilingRectangle.tiling_rectangle n m = ok r) := by
    sorry

  /-- If tiling_rectangle(n,m) returns r and tiling_rectangle(m,n) returns s, then r = s.
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_3 (n m r s : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r)
      (hs : Aegis.TilingRectangle.tiling_rectangle m n = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m r s : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r)
        (hs : Aegis.TilingRectangle.tiling_rectangle m n = ok s), r.val = s.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r * min(n,m) >= max(n,m) (integer inequality).
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_4 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      max n.val m.val ≤ r.val * min n.val m.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), max n.val m.val ≤ r.val * min n.val m.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r <= max(n,m).
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_5 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      r.val ≤ max n.val m.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), r.val ≤ max n.val m.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r = max(n,m) / min(n,m).
    Preconditions: 1 <= n, 1 <= m, and min(n,m) divides max(n,m). -/
  theorem spec_6 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hdvd : min n.val m.val ∣ max n.val m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      r.val = max n.val m.val / min n.val m.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hdvd : min n.val m.val ∣ max n.val m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), r.val = max n.val m.val / min n.val m.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, there exists a tiling of the n by m rectangle by axis-aligned integer-sided squares with integer corner coordinates that consists of exactly r squares.
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_7 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      ∃ l : List Square, IsTiling n.val.toNat m.val.toNat l ∧ (l.length : ℤ) = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), ∃ l : List Square, IsTiling n.val.toNat m.val.toNat l ∧ (l.length : ℤ) = r.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, every tiling of the n by m rectangle by axis-aligned integer-sided squares with integer corner coordinates has at least r squares.
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_8 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      ∀ l : List Square, IsTiling n.val.toNat m.val.toNat l → r.val ≤ (l.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), ∀ l : List Square, IsTiling n.val.toNat m.val.toNat l → r.val ≤ (l.length : ℤ)) := by
    sorry

  /-- Let a = max(n,m). Whenever tiling_rectangle(n,m) returns r, either a is even and r = a/2, or a is odd and r = (a+3)/2.
    Preconditions: 1 <= n, 1 <= m, and min(n,m) = 2. -/
  theorem spec_9 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hmin : min n.val m.val = 2)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      (∃ k : ℤ, max n.val m.val = 2 * k ∧ r.val = k) ∨
        (∃ k : ℤ, max n.val m.val = 2 * k + 1 ∧ r.val = k + 2) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hmin : min n.val m.val = 2)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), (∃ k : ℤ, max n.val m.val = 2 * k ∧ r.val = k) ∨
          (∃ k : ℤ, max n.val m.val = 2 * k + 1 ∧ r.val = k + 2)) := by
    sorry

  /-- If tiling_rectangle(k*n, k*m) returns r and tiling_rectangle(n,m) returns s, then r <= s.
    Preconditions: k, n, m are positive integers, and k*n and k*m are within the i64 range. -/
  theorem spec_10 (k n m kn km r s : Std.I64) (hk : 1 ≤ k.val) (hn : 1 ≤ n.val)
      (hm : 1 ≤ m.val) (hkn : kn.val = k.val * n.val) (hkm : km.val = k.val * m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle kn km = ok r)
      (hs : Aegis.TilingRectangle.tiling_rectangle n m = ok s) :
      r.val ≤ s.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k n m kn km r s : Std.I64) (hk : 1 ≤ k.val) (hn : 1 ≤ n.val)
        (hm : 1 ≤ m.val) (hkn : kn.val = k.val * n.val) (hkm : km.val = k.val * m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle kn km = ok r)
        (hs : Aegis.TilingRectangle.tiling_rectangle n m = ok s), r.val ≤ s.val) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r = 1 if and only if n = m.
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_11 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      (r.val = 1 ↔ n.val = m.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), (r.val = 1 ↔ n.val = m.val)) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r = 2 if and only if max(n,m) = 2 * min(n,m).
    Preconditions: 1 <= n and 1 <= m. -/
  theorem spec_12 (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      (r.val = 2 ↔ max n.val m.val = 2 * min n.val m.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n m r : Std.I64) (hn : 1 ≤ n.val) (hm : 1 ≤ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), (r.val = 2 ↔ max n.val m.val = 2 * min n.val m.val)) := by
    sorry

  /-- Whenever tiling_rectangle(n,m) returns r, r <= max(n,m) / k.
    Preconditions: k, n, m are positive integers with k >= 2, k divides n, and k divides m. -/
  theorem spec_13 (k n m r : Std.I64) (hk2 : 2 ≤ k.val) (hn : 1 ≤ n.val)
      (hm : 1 ≤ m.val) (hdn : k.val ∣ n.val) (hdm : k.val ∣ m.val)
      (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r) :
      r.val ≤ max n.val m.val / k.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (k n m r : Std.I64) (hk2 : 2 ≤ k.val) (hn : 1 ≤ n.val)
        (hm : 1 ≤ m.val) (hdn : k.val ∣ n.val) (hdm : k.val ∣ m.val)
        (hr : Aegis.TilingRectangle.tiling_rectangle n m = ok r), r.val ≤ max n.val m.val / k.val) := by
    sorry

  end AegisSpec.TilingRectangle
