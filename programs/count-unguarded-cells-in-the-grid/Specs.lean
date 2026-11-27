import Aegis.CountUnguarded.Code.Funs

/-!
# Specifications of `Aegis.CountUnguarded.count_unguarded`

LeetCode problem `count-unguarded-cells-in-the-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountUnguarded

namespace AegisSpec.CountUnguarded

abbrev VecI64 := alloc.vec.Vec Std.I64

abbrev SliceVecI64 := Slice VecI64

def IsVec2 (v : VecI64) : Prop := ∃ a b : Std.I64, v.val = [a, b]

def rowOf (v : VecI64) : ℤ :=
  match v.val with
  | a :: _ => a.val
  | [] => 0

def colOf (v : VecI64) : ℤ :=
  match v.val with
  | _ :: b :: _ => b.val
  | _ => 0

def posOf (v : VecI64) : ℤ × ℤ := (rowOf v, colOf v)

def positions (l : List VecI64) : List (ℤ × ℤ) := l.map posOf

def transposePos (p : ℤ × ℤ) : ℤ × ℤ := (p.2, p.1)

def reflectCol (n : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (p.1, n - 1 - p.2)

def inGrid (m n : ℤ) (p : ℤ × ℤ) : Prop := 0 ≤ p.1 ∧ p.1 < m ∧ 0 ≤ p.2 ∧ p.2 < n

def gridCells (m n : ℤ) : Set (ℤ × ℤ) := {p | inGrid m n p}

def isGuardOf (guards : SliceVecI64) (i j : ℤ) : Prop := ∃ v ∈ guards.val, posOf v = (i, j)

def isWallOf (walls : SliceVecI64) (i j : ℤ) : Prop := ∃ v ∈ walls.val, posOf v = (i, j)

def rowClear (guards walls : SliceVecI64) (i j gc : ℤ) : Prop :=
  ∀ k : ℤ, min gc j < k → k < max gc j → ¬ isGuardOf guards i k ∧ ¬ isWallOf walls i k

def colClear (guards walls : SliceVecI64) (j i gr : ℤ) : Prop :=
  ∀ k : ℤ, min gr i < k → k < max gr i → ¬ isGuardOf guards k j ∧ ¬ isWallOf walls k j

def seesCell (guards walls : SliceVecI64) (g : VecI64) (i j : ℤ) : Prop :=
  (rowOf g = i ∧ j ≠ colOf g ∧ rowClear guards walls i j (colOf g)) ∨
  (colOf g = j ∧ i ≠ rowOf g ∧ colClear guards walls j i (rowOf g))

def seenByGuard (guards walls : SliceVecI64) (i j : ℤ) : Prop :=
  ∃ g ∈ guards.val, seesCell guards walls g i j

def cellUnguarded (guards walls : SliceVecI64) (i j : ℤ) : Prop :=
  ¬ isGuardOf guards i j ∧ ¬ isWallOf walls i j ∧ ¬ seenByGuard guards walls i j

def unguardedCells (m n : ℤ) (guards walls : SliceVecI64) : Set (ℤ × ℤ) :=
  {p ∈ gridCells m n | cellUnguarded guards walls p.1 p.2}

def seenCells (m n : ℤ) (guards walls : SliceVecI64) : Set (ℤ × ℤ) :=
  {p ∈ gridCells m n |
    ¬ isGuardOf guards p.1 p.2 ∧ ¬ isWallOf walls p.1 p.2 ∧
      seenByGuard guards walls p.1 p.2}

noncomputable def nUnguarded (m n : ℤ) (guards walls : SliceVecI64) : ℕ :=
  (unguardedCells m n guards walls).ncard

noncomputable def nSeen (m n : ℤ) (guards walls : SliceVecI64) : ℕ :=
  (seenCells m n guards walls).ncard

noncomputable def nFree (m n : ℤ) (guards walls : SliceVecI64) : ℕ :=
  {p ∈ gridCells m n | ¬ isGuardOf guards p.1 p.2 ∧ ¬ isWallOf walls p.1 p.2}.ncard

def ValidInput (m n : Std.I64) (guards walls : SliceVecI64) : Prop :=
  1 ≤ m.val ∧ m.val ≤ 100000 ∧
  1 ≤ n.val ∧ n.val ≤ 100000 ∧
  2 ≤ m.val * n.val ∧ m.val * n.val ≤ 100000 ∧
  (∀ v ∈ guards.val, IsVec2 v) ∧
  (∀ v ∈ walls.val, IsVec2 v) ∧
  (∀ v ∈ guards.val, inGrid m.val n.val (posOf v)) ∧
  (∀ v ∈ walls.val, inGrid m.val n.val (posOf v)) ∧
  1 ≤ guards.val.length ∧ guards.val.length ≤ 50000 ∧
  1 ≤ walls.val.length ∧ walls.val.length ≤ 50000 ∧
  2 ≤ guards.val.length + walls.val.length ∧
  ((guards.val.length + walls.val.length : ℕ) : ℤ) ≤ m.val * n.val ∧
  (positions (guards.val ++ walls.val)).Nodup

/-- Whenever count_unguarded(m,n,guards,walls) returns a result r, r is the number of pairs (i,j) with 0<=i<m and 0<=j<n such that (i,j) is not a guard position and not a wall position, and there is no guard g=(gr,gc) for which either (A) gr=i, j!=gc, and every cell (i,k) with min(gc,j)<k<max(gc,j) is neither a guard nor a wall, or (B) gc=j, i!=gr, and every cell (k,j) with min(gr,i)<k<max(gr,i) is neither a guard nor a wall. Conditions (A) and (B) say that g has an unobstructed cardinal-direction view of (i,j).
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_1 (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls) :
    ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val = (nUnguarded m.val n.val guards walls : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls), ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val = (nUnguarded m.val n.val guards walls : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, count_unguarded(m,n,guards,walls) returns a result r (it does not fail, panic, or overflow).
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_2 (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls) :
    ∃ r : Std.I64, count_unguarded m n guards walls = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls), ∃ r : Std.I64, count_unguarded m n guards walls = ok r) := by
  sorry

/-- Whenever count_unguarded(m,n,guards,walls) returns a result r, r <= m*n - len(guards) - len(walls).
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_3 (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls) :
    ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val ≤ m.val * n.val - (guards.val.length : ℤ) - (walls.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls), ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val ≤ m.val * n.val - (guards.val.length : ℤ) - (walls.val.length : ℤ)) := by
  sorry

/-- Let guards' be any list containing exactly the same position vectors as guards, each once, and let walls' be any list containing exactly the same position vectors as walls, each once. Whenever count_unguarded(m,n,guards,walls) returns r and count_unguarded(m,n,guards',walls') returns r', we have r=r'.
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_4 (m n : Std.I64) (guards walls guards' walls' : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hg' : guards'.val.Perm guards.val) (hw' : walls'.val.Perm walls.val) :
    ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guards' walls' = ok r' → r = r' := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (m n : Std.I64) (guards walls guards' walls' : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hg' : guards'.val.Perm guards.val) (hw' : walls'.val.Perm walls.val), ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guards' walls' = ok r' → r = r') := by
  sorry

/-- Let guardsT be obtained from guards by replacing each [a,b] with [b,a], and let wallsT be obtained from walls by replacing each [a,b] with [b,a]. Whenever count_unguarded(m,n,guards,walls) returns r and count_unguarded(n,m,guardsT,wallsT) returns r', we have r=r'.
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_5 (m n : Std.I64) (guards walls guardsT wallsT : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hgT : positions guardsT.val = (positions guards.val).map (transposePos : ℤ × ℤ → ℤ × ℤ))
    (hwT : positions wallsT.val = (positions walls.val).map (transposePos : ℤ × ℤ → ℤ × ℤ))
    (hgT2 : ∀ v ∈ guardsT.val, IsVec2 v) (hwT2 : ∀ v ∈ wallsT.val, IsVec2 v) :
    ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded n m guardsT wallsT = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (m n : Std.I64) (guards walls guardsT wallsT : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hgT : positions guardsT.val = (positions guards.val).map (transposePos : ℤ × ℤ → ℤ × ℤ))
    (hwT : positions wallsT.val = (positions walls.val).map (transposePos : ℤ × ℤ → ℤ × ℤ))
    (hgT2 : ∀ v ∈ guardsT.val, IsVec2 v) (hwT2 : ∀ v ∈ wallsT.val, IsVec2 v), ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded n m guardsT wallsT = ok r' → r = r') := by
  sorry

/-- Let guardsH be obtained from guards by replacing each [a,b] with [a,n-1-b], and let wallsH be obtained from walls by replacing each [a,b] with [a,n-1-b]. Whenever count_unguarded(m,n,guards,walls) returns r and count_unguarded(m,n,guardsH,wallsH) returns r', we have r=r'.
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_6 (m n : Std.I64) (guards walls guardsH wallsH : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hgH : positions guardsH.val = (positions guards.val).map (reflectCol n.val))
    (hwH : positions wallsH.val = (positions walls.val).map (reflectCol n.val))
    (hgH2 : ∀ v ∈ guardsH.val, IsVec2 v) (hwH2 : ∀ v ∈ wallsH.val, IsVec2 v) :
    ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guardsH wallsH = ok r' → r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (m n : Std.I64) (guards walls guardsH wallsH : SliceVecI64)
    (h : ValidInput m n guards walls)
    (hgH : positions guardsH.val = (positions guards.val).map (reflectCol n.val))
    (hwH : positions wallsH.val = (positions walls.val).map (reflectCol n.val))
    (hgH2 : ∀ v ∈ guardsH.val, IsVec2 v) (hwH2 : ∀ v ∈ wallsH.val, IsVec2 v), ∀ r r' : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guardsH wallsH = ok r' → r = r') := by
  sorry

/-- Whenever count_unguarded(m,n,guards,walls) returns r, let E = m*n - len(guards) - len(walls). Let V be the number of cells (i,j) with 0<=i<m and 0<=j<n that are neither a guard nor a wall and are seen by at least one guard, with seen meaning same row or column and no guard or wall strictly between. Then r + V = E.
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. -/
theorem spec_7 (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls) :
    ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val + (nSeen m.val n.val guards walls : ℤ) =
        m.val * n.val - (guards.val.length : ℤ) - (walls.val.length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (m n : Std.I64) (guards walls : SliceVecI64)
    (h : ValidInput m n guards walls), ∀ r : Std.I64, count_unguarded m n guards walls = ok r →
      r.val + (nSeen m.val n.val guards walls : ℤ) =
        m.val * n.val - (guards.val.length : ℤ) - (walls.val.length : ℤ)) := by
  sorry

/-- Whenever count_unguarded(m,n,guards,walls) returns r and count_unguarded(m,n,guards2,walls) returns r2, we have r2 <= r. Moreover, if p is not seen by any guard in guards, where a guard g=(gr,gc) sees (i,j) exactly when either (gr=i, j!=gc, and every cell (i,k) with min(gc,j)<k<max(gc,j) is neither a guard nor a wall) or (gc=j, i!=gr, and every cell (k,j) with min(gr,i)<k<max(gr,i) is neither a guard nor a wall), then r2 <= r-1.
  Preconditions: m,n are integers with 1<=m,n<=100000 and 2<=m*n<=100000; guards and walls are slices of length-2 integer vectors; every guard and wall has row in [0,m) and column in [0,n); 1<=len(guards),len(walls)<=50000; 2<=len(guards)+len(walls)<=m*n; all positions appearing in guards or walls are pairwise distinct. Additionally, p=(pr,pc) is a cell with 0<=pr<m and 0<=pc<n that is neither a guard position nor a wall position, and guards2 is obtained by appending [pr,pc] to guards. -/
theorem spec_8 (m n : Std.I64) (guards walls guards2 : SliceVecI64)
    (pv : VecI64) (pr pc : ℤ)
    (h : ValidInput m n guards walls)
    (hp : inGrid m.val n.val (pr, pc))
    (hpv : IsVec2 pv) (hpvpos : posOf pv = (pr, pc))
    (hguard2 : guards2.val = guards.val ++ [pv])
    (hp_guard : ¬ isGuardOf guards pr pc) (hp_wall : ¬ isWallOf walls pr pc) :
    ∀ r r2 : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guards2 walls = ok r2 →
      r2.val ≤ r.val ∧ (¬ seenByGuard guards walls pr pc → r2.val ≤ r.val - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (m n : Std.I64) (guards walls guards2 : SliceVecI64)
    (pv : VecI64) (pr pc : ℤ)
    (h : ValidInput m n guards walls)
    (hp : inGrid m.val n.val (pr, pc))
    (hpv : IsVec2 pv) (hpvpos : posOf pv = (pr, pc))
    (hguard2 : guards2.val = guards.val ++ [pv])
    (hp_guard : ¬ isGuardOf guards pr pc) (hp_wall : ¬ isWallOf walls pr pc), ∀ r r2 : Std.I64, count_unguarded m n guards walls = ok r →
      count_unguarded m n guards2 walls = ok r2 →
      r2.val ≤ r.val ∧ (¬ seenByGuard guards walls pr pc → r2.val ≤ r.val - 1)) := by
  sorry

end AegisSpec.CountUnguarded
