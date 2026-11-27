import Aegis.PrisonAfterNDays.Code.Funs

/-!
# Specifications of `Aegis.PrisonAfterNDays.prison_after_n_days`

LeetCode problem `prison-cells-after-n-days`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PrisonAfterNDays

namespace AegisSpec.PrisonAfterNDays

def sliceVals (cells : Slice I64) : List ℤ := cells.val.map (fun x => x.val)

def vecVals (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

def cellAt (l : List I64) (i : ℕ) : Option ℤ := (l[i]?).map (fun x => x.val)

def step (s : List ℤ) : List ℤ :=
  match s with
  | [a0, a1, a2, a3, a4, a5, a6, a7] =>
      [0,
       if a0 = a2 then 1 else 0,
       if a1 = a3 then 1 else 0,
       if a2 = a4 then 1 else 0,
       if a3 = a5 then 1 else 0,
       if a4 = a6 then 1 else 0,
       if a5 = a7 then 1 else 0,
       0]
  | _ => s

def stateAfter (s : List ℤ) (k : ℕ) : List ℤ := Nat.iterate step k s

def T (cells : Slice I64) : List ℤ := step (sliceVals cells)

def comp (s : List ℤ) : List ℤ := s.map (fun x => 1 - x)

def rev (s : List ℤ) : List ℤ := s.reverse

/-- Let S_0 be the input cells. For each integer k >= 0, let S_{k+1} be the length-8 state such that S_{k+1}[0] = 0, S_{k+1}[7] = 0, and for each i with 1 <= i <= 6, S_{k+1}[i] = 1 if and only if S_k[i-1] = S_k[i+1]. Under the preconditions, the function returns a result r with len(r) = 8, and for every i with 0 <= i <= 7, r[i] = S_n[i].
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_1 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64,
      prison_after_n_days cells n = ok r ∧
      r.val.length = 8 ∧
      (∀ (i : ℕ), i < 8 →
        cellAt r.val i = (stateAfter (sliceVals cells) n.val.toNat)[i]?) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∃ r : alloc.vec.Vec I64,
      prison_after_n_days cells n = ok r ∧
      r.val.length = 8 ∧
      (∀ (i : ℕ), i < 8 →
        cellAt r.val i = (stateAfter (sliceVals cells) n.val.toNat)[i]?)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_2 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec I64, prison_after_n_days cells n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∃ r : alloc.vec.Vec I64, prison_after_n_days cells n = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 8.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_3 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i] = 0 or r[i] = 1.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_4 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r →
      ∀ (i : ℕ), i < r.val.length → (cellAt r.val i = some 0 ∨ cellAt r.val i = some 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r →
      ∀ (i : ℕ), i < r.val.length → (cellAt r.val i = some 0 ∨ cellAt r.val i = some 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 8, r[0] = 0 and r[7] = 0.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_5 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8 →
      (cellAt r.val 0 = some 0 ∧ cellAt r.val 7 = some 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8 →
      (cellAt r.val 0 = some 0 ∧ cellAt r.val 7 = some 0)) := by
  sorry

/-- Whenever n = 1 and the function returns a result r with len(r) = 8, for every i with 1 <= i <= 6, r[i] = 1 if and only if cells[i-1] = cells[i+1].
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; n = 1. -/
theorem spec_6 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn : n.val = 1) :
    ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8 →
      ∀ (i : ℕ), 1 ≤ i → i ≤ 6 →
        (cellAt r.val i = some 1 ↔ cellAt cells.val (i - 1) = cellAt cells.val (i + 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn : n.val = 1), ∀ (r : alloc.vec.Vec I64), prison_after_n_days cells n = ok r → r.val.length = 8 →
      ∀ (i : ℕ), 1 ≤ i → i ≤ 6 →
        (cellAt r.val i = some 1 ↔ cellAt cells.val (i - 1) = cellAt cells.val (i + 1))) := by
  sorry

/-- For every integer m with 1 <= m < 1000000000, if the function returns r for input (cells, m) and r2 for input (cells, m+1), then len(r) = len(r2) = 8 and for every i with 1 <= i <= 6, r2[i] = 1 if and only if r[i-1] = r[i+1].
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1. -/
theorem spec_7 (cells : Slice I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1)) :
    ∀ (m m1 : I64), 1 ≤ m.val → m.val < 1000000000 → m1.val = m.val + 1 →
      ∀ (r r2 : alloc.vec.Vec I64),
        prison_after_n_days cells m = ok r →
        prison_after_n_days cells m1 = ok r2 →
        r.val.length = 8 ∧ r2.val.length = 8 ∧
        (∀ (i : ℕ), 1 ≤ i → i ≤ 6 →
          (cellAt r2.val i = some 1 ↔ cellAt r.val (i - 1) = cellAt r.val (i + 1))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cells : Slice I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1)), ∀ (m m1 : I64), 1 ≤ m.val → m.val < 1000000000 → m1.val = m.val + 1 →
      ∀ (r r2 : alloc.vec.Vec I64),
        prison_after_n_days cells m = ok r →
        prison_after_n_days cells m1 = ok r2 →
        r.val.length = 8 ∧ r2.val.length = 8 ∧
        (∀ (i : ℕ), 1 ≤ i → i ≤ 6 →
          (cellAt r2.val i = some 1 ↔ cellAt r.val (i - 1) = cellAt r.val (i + 1)))) := by
  sorry

/-- Let comp(cells) be the length-8 array defined by comp(cells)[i] = 1 - cells[i] for 0 <= i <= 7. If the function returns r for (cells, n) and r2 for (comp(cells), n), then r = r2 as length-8 sequences.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_8 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∀ (cellsC : Slice I64) (r r2 : alloc.vec.Vec I64),
      sliceVals cellsC = comp (sliceVals cells) →
      prison_after_n_days cells n = ok r →
      prison_after_n_days cellsC n = ok r2 →
      vecVals r = vecVals r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∀ (cellsC : Slice I64) (r r2 : alloc.vec.Vec I64),
      sliceVals cellsC = comp (sliceVals cells) →
      prison_after_n_days cells n = ok r →
      prison_after_n_days cellsC n = ok r2 →
      vecVals r = vecVals r2) := by
  sorry

/-- Let rev(cells) be the length-8 array defined by rev(cells)[i] = cells[7-i] for 0 <= i <= 7. If the function returns r for (cells, n) and r2 for (rev(cells), n), then len(r) = len(r2) = 8 and for every i with 0 <= i <= 7, r2[i] = r[7-i].
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_9 (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000) :
    ∀ (cellsR : Slice I64) (r r2 : alloc.vec.Vec I64),
      sliceVals cellsR = rev (sliceVals cells) →
      prison_after_n_days cells n = ok r →
      prison_after_n_days cellsR n = ok r2 →
      r.val.length = 8 ∧ r2.val.length = 8 ∧
      (∀ (i : ℕ), i ≤ 7 → cellAt r2.val i = cellAt r.val (7 - i)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cells : Slice I64) (n : I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000), ∀ (cellsR : Slice I64) (r r2 : alloc.vec.Vec I64),
      sliceVals cellsR = rev (sliceVals cells) →
      prison_after_n_days cells n = ok r →
      prison_after_n_days cellsR n = ok r2 →
      r.val.length = 8 ∧ r2.val.length = 8 ∧
      (∀ (i : ℕ), i ≤ 7 → cellAt r2.val i = cellAt r.val (7 - i))) := by
  sorry

/-- For every integer m with 1 <= m and m + 14 <= 1000000000, if the function returns r for (cells, m) and r2 for (cells, m+14), then r = r2 as length-8 sequences.
  Preconditions: len(cells) = 8; for every i with 0 <= i < 8, cells[i] is 0 or 1; 1 <= n <= 1000000000. -/
theorem spec_10 (cells : Slice I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1)) :
    ∀ (m m14 : I64), 1 ≤ m.val → m.val + 14 ≤ 1000000000 → m14.val = m.val + 14 →
      ∀ (r r2 : alloc.vec.Vec I64),
        prison_after_n_days cells m = ok r →
        prison_after_n_days cells m14 = ok r2 →
        vecVals r = vecVals r2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cells : Slice I64)
    (hlen : cells.val.length = 8)
    (hbin : ∀ (i : ℕ), i < 8 → (cellAt cells.val i = some 0 ∨ cellAt cells.val i = some 1)), ∀ (m m14 : I64), 1 ≤ m.val → m.val + 14 ≤ 1000000000 → m14.val = m.val + 14 →
      ∀ (r r2 : alloc.vec.Vec I64),
        prison_after_n_days cells m = ok r →
        prison_after_n_days cells m14 = ok r2 →
        vecVals r = vecVals r2) := by
  sorry

/-- Let T(x) be the one-day state defined by T(x)[0] = T(x)[7] = 0 and, for 1 <= i <= 6, T(x)[i] = 1 if and only if x[i-1] = x[i+1]. If T(c) = T(d), then the function returns the same result for (c, n) and for (d, n) as length-8 sequences.
  Preconditions: c and d are arrays of length 8 with entries in {0,1}; 1 <= n <= 1000000000. -/
theorem spec_11 (c d : Slice I64) (n : I64)
    (hlenc : c.val.length = 8)
    (hbinc : ∀ (i : ℕ), i < 8 → (cellAt c.val i = some 0 ∨ cellAt c.val i = some 1))
    (hlend : d.val.length = 8)
    (hbind : ∀ (i : ℕ), i < 8 → (cellAt d.val i = some 0 ∨ cellAt d.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000)
    (hT : T c = T d) :
    ∀ (r r2 : alloc.vec.Vec I64),
      prison_after_n_days c n = ok r →
      prison_after_n_days d n = ok r2 →
      vecVals r = vecVals r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (c d : Slice I64) (n : I64)
    (hlenc : c.val.length = 8)
    (hbinc : ∀ (i : ℕ), i < 8 → (cellAt c.val i = some 0 ∨ cellAt c.val i = some 1))
    (hlend : d.val.length = 8)
    (hbind : ∀ (i : ℕ), i < 8 → (cellAt d.val i = some 0 ∨ cellAt d.val i = some 1))
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 1000000000)
    (hT : T c = T d), ∀ (r r2 : alloc.vec.Vec I64),
      prison_after_n_days c n = ok r →
      prison_after_n_days d n = ok r2 →
      vecVals r = vecVals r2) := by
  sorry

end AegisSpec.PrisonAfterNDays
