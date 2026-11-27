import Aegis.ValidSquare.Code.Funs

/-!
# Specifications of `Aegis.ValidSquare.valid_square`

LeetCode problem `valid-square`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ValidSquare

  open Aegis.ValidSquare

  def coord (p : Slice Std.I64) (k : ℕ) : ℤ :=
    match p.val[k]? with
    | some v => v.val
    | none => 0

  def xCoord (p : Slice Std.I64) : ℤ := coord p 0

  def yCoord (p : Slice Std.I64) : ℤ := coord p 1

  def pts (p1 p2 p3 p4 : Slice Std.I64) : Fin 4 → Slice Std.I64 := ![p1, p2, p3, p4]

  def sqDist (a b : Slice Std.I64) : ℤ :=
    (xCoord a - xCoord b) ^ 2 + (yCoord a - yCoord b) ^ 2

  def dists (p1 p2 p3 p4 : Slice Std.I64) : List ℤ :=
    [sqDist p1 p2, sqDist p1 p3, sqDist p1 p4,
     sqDist p2 p3, sqDist p2 p4, sqDist p3 p4]

  def occ (l : List ℤ) (x : ℤ) : ℕ := l.countP (fun d => decide (d = x))

  def listMin : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldl min a

  def listMax : List ℤ → ℤ
    | [] => 0
    | a :: l => l.foldl max a

  def InRange (p : Slice Std.I64) : Prop :=
    -10000 ≤ xCoord p ∧ xCoord p ≤ 10000 ∧ -10000 ≤ yCoord p ∧ yCoord p ≤ 10000

  def InRangeShifted (p : Slice Std.I64) (tx ty : ℤ) : Prop :=
    -10000 ≤ xCoord p + tx ∧ xCoord p + tx ≤ 10000 ∧
      -10000 ≤ yCoord p + ty ∧ yCoord p + ty ≤ 10000

  def InRangeScaled (p : Slice Std.I64) (c : ℤ) : Prop :=
    -10000 ≤ c * xCoord p ∧ c * xCoord p ≤ 10000 ∧
      -10000 ≤ c * yCoord p ∧ c * yCoord p ≤ 10000

  def SamePoint (a b : Slice Std.I64) : Prop :=
    xCoord a = xCoord b ∧ yCoord a = yCoord b

  def crossZ (a b c : Slice Std.I64) : ℤ :=
    (xCoord b - xCoord a) * (yCoord c - yCoord a) -
      (yCoord b - yCoord a) * (xCoord c - xCoord a)

  def Collinear4 (p1 p2 p3 p4 : Slice Std.I64) : Prop :=
    ∃ A B C : ℤ, (A ≠ 0 ∨ B ≠ 0) ∧
      (A * xCoord p1 + B * yCoord p1 + C = 0) ∧
      (A * xCoord p2 + B * yCoord p2 + C = 0) ∧
      (A * xCoord p3 + B * yCoord p3 + C = 0) ∧
      (A * xCoord p4 + B * yCoord p4 + C = 0)

  def TwoAndDouble (a b c s : ℤ) : Prop :=
    (a = s ∧ b = s ∧ c = 2 * s) ∨
      (a = s ∧ c = s ∧ b = 2 * s) ∨
      (b = s ∧ c = s ∧ a = 2 * s)

  def PairWitness (pa pc pb pd : Slice Std.I64) : Prop :=
    xCoord pa + xCoord pc = xCoord pb + xCoord pd ∧
      yCoord pa + yCoord pc = yCoord pb + yCoord pd ∧
      sqDist pa pc = sqDist pb pd ∧
      0 < sqDist pa pc ∧
      (xCoord pc - xCoord pa) * (xCoord pd - xCoord pb) +
        (yCoord pc - yCoord pa) * (yCoord pd - yCoord pb) = 0

  def Shifted (q p : Slice Std.I64) (tx ty : ℤ) : Prop :=
    q.val.length = 2 ∧ xCoord q = xCoord p + tx ∧ yCoord q = yCoord p + ty

  def Scaled (q p : Slice Std.I64) (c : ℤ) : Prop :=
    q.val.length = 2 ∧ xCoord q = c * xCoord p ∧ yCoord q = c * yCoord p

  def Transposed (q p : Slice Std.I64) : Prop :=
    q.val.length = 2 ∧ xCoord q = yCoord p ∧ yCoord q = xCoord p

  def qx (p : Slice Std.I64) : ℚ := (xCoord p : ℚ)

  def qy (p : Slice Std.I64) : ℚ := (yCoord p : ℚ)

  def crossQ (a b c : Slice Std.I64) : ℚ :=
    (qx b - qx a) * (qy c - qy a) - (qy b - qy a) * (qx c - qx a)

  def triArea (a b c : Slice Std.I64) : ℚ := |crossQ a b c| / 2

  def diagArea (a b c d : Slice Std.I64) : ℚ :=
    if crossQ a b c * crossQ a b d < 0 then triArea a b c + triArea a b d else 0

  def hullArea (p1 p2 p3 p4 : Slice Std.I64) : ℚ :=
    max
      (max (max (triArea p1 p2 p3) (triArea p1 p2 p4))
        (max (triArea p1 p3 p4) (triArea p2 p3 p4)))
      (max
        (max (max (diagArea p1 p2 p3 p4) (diagArea p1 p3 p2 p4))
          (max (diagArea p1 p4 p2 p3) (diagArea p2 p3 p1 p4)))
        (max (diagArea p2 p4 p1 p3) (diagArea p3 p4 p1 p2)))

  def inHull3 (q a b c : Slice Std.I64) : Prop :=
    ∃ α β γ : ℚ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      α * qx a + β * qx b + γ * qx c = qx q ∧
      α * qy a + β * qy b + γ * qy c = qy q

  /-- Write D_ij = (p_i[0]-p_j[0])^2 + (p_i[1]-p_j[1])^2 for 1<=i<j<=4. Whenever the function returns Result.ok r, r is true if and only if there exists a positive integer s such that the multiset {D_12,D_13,D_14,D_23,D_24,D_34} has exactly four occurrences of s and exactly two occurrences of 2*s.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_1 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      (r = true ↔ ∃ s : ℤ, 0 < s ∧
        occ (dists p1 p2 p3 p4) s = 4 ∧ occ (dists p1 p2 p3 p4) (2 * s) = 2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), (r = true ↔ ∃ s : ℤ, 0 < s ∧
          occ (dists p1 p2 p3 p4) s = 4 ∧ occ (dists p1 p2 p3 p4) (2 * s) = 2)) := by
    sorry

  /-- Under the preconditions the function returns Result.ok r for some Boolean r; it does not fail (no panic, arithmetic overflow, or out-of-bounds access).
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_2 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4) :
      ∃ r : Bool, valid_square p1 p2 p3 p4 = .ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4), ∃ r : Bool, valid_square p1 p2 p3 p4 = Result.ok r) := by
    sorry

  /-- Let perm be any permutation of {1,2,3,4}, and set q_1=p_{perm(1)}, q_2=p_{perm(2)}, q_3=p_{perm(3)}, q_4=p_{perm(4)}. Whenever valid_square(p1,p2,p3,p4) returns Result.ok r and valid_square(q_1,q_2,q_3,q_4) returns Result.ok r', we have r=r'.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_3 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (σ : Equiv.Perm (Fin 4))
      (r r' : Bool)
      (hr : valid_square p1 p2 p3 p4 = .ok r)
      (hr' : valid_square (pts p1 p2 p3 p4 (σ 0)) (pts p1 p2 p3 p4 (σ 1))
        (pts p1 p2 p3 p4 (σ 2)) (pts p1 p2 p3 p4 (σ 3)) = .ok r') :
      r = r' := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (σ : Equiv.Perm (Fin 4))
        (r r' : Bool)
        (hr : valid_square p1 p2 p3 p4 = Result.ok r)
        (hr' : valid_square (pts p1 p2 p3 p4 (σ 0)) (pts p1 p2 p3 p4 (σ 1))
          (pts p1 p2 p3 p4 (σ 2)) (pts p1 p2 p3 p4 (σ 3)) = Result.ok r'), r = r') := by
    sorry

  /-- Whenever the function returns Result.ok r, if there are i<j in {1,2,3,4} with p_i[0]=p_j[0] and p_i[1]=p_j[1], then r=false.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_4 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      (SamePoint p1 p2 ∨ SamePoint p1 p3 ∨ SamePoint p1 p4 ∨
        SamePoint p2 p3 ∨ SamePoint p2 p4 ∨ SamePoint p3 p4) → r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), (SamePoint p1 p2 ∨ SamePoint p1 p3 ∨ SamePoint p1 p4 ∨
          SamePoint p2 p3 ∨ SamePoint p2 p4 ∨ SamePoint p3 p4) → r = false) := by
    sorry

  /-- Whenever the function returns Result.ok r, if all four points are collinear (there exist integers A,B,C with (A,B) != (0,0) and A*p_i[0]+B*p_i[1]+C=0 for i=1,2,3,4), then r=false.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_5 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      Collinear4 p1 p2 p3 p4 → r = false := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), Collinear4 p1 p2 p3 p4 → r = false) := by
    sorry

  /-- Whenever the function returns Result.ok r, if r=true then no three of the four points are collinear: for every choice of three distinct indices i,j,k, (p_j[0]-p_i[0])*(p_k[1]-p_i[1]) != (p_j[1]-p_i[1])*(p_k[0]-p_i[0]).
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_6 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        crossZ p1 p2 p3 ≠ 0 ∧ crossZ p1 p2 p4 ≠ 0 ∧
          crossZ p1 p3 p4 ≠ 0 ∧ crossZ p2 p3 p4 ≠ 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          crossZ p1 p2 p3 ≠ 0 ∧ crossZ p1 p2 p4 ≠ 0 ∧
            crossZ p1 p3 p4 ≠ 0 ∧ crossZ p2 p3 p4 ≠ 0) := by
    sorry

  /-- With D_ij as in spec_1, whenever the function returns Result.ok r, if r=true then for each i in {1,2,3,4} there exists a positive integer s_i such that among the three values D_ij with j != i, exactly two equal s_i and the remaining one equals 2*s_i.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_7 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        (∃ s : ℤ, 0 < s ∧
            TwoAndDouble (sqDist p1 p2) (sqDist p1 p3) (sqDist p1 p4) s) ∧
          (∃ s : ℤ, 0 < s ∧
            TwoAndDouble (sqDist p1 p2) (sqDist p2 p3) (sqDist p2 p4) s) ∧
          (∃ s : ℤ, 0 < s ∧
            TwoAndDouble (sqDist p1 p3) (sqDist p2 p3) (sqDist p3 p4) s) ∧
          (∃ s : ℤ, 0 < s ∧
            TwoAndDouble (sqDist p1 p4) (sqDist p2 p4) (sqDist p3 p4) s) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          (∃ s : ℤ, 0 < s ∧
              TwoAndDouble (sqDist p1 p2) (sqDist p1 p3) (sqDist p1 p4) s) ∧
            (∃ s : ℤ, 0 < s ∧
              TwoAndDouble (sqDist p1 p2) (sqDist p2 p3) (sqDist p2 p4) s) ∧
            (∃ s : ℤ, 0 < s ∧
              TwoAndDouble (sqDist p1 p3) (sqDist p2 p3) (sqDist p3 p4) s) ∧
            (∃ s : ℤ, 0 < s ∧
              TwoAndDouble (sqDist p1 p4) (sqDist p2 p4) (sqDist p3 p4) s)) := by
    sorry

  /-- With D_ij as in spec_1, whenever the function returns Result.ok r, if r=true then min{D_ij : 1<=i<j<=4} > 0 and max{D_ij : 1<=i<j<=4} = 2 * min{D_ij : 1<=i<j<=4}.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_8 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        0 < listMin (dists p1 p2 p3 p4) ∧
          listMax (dists p1 p2 p3 p4) = 2 * listMin (dists p1 p2 p3 p4) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          0 < listMin (dists p1 p2 p3 p4) ∧
            listMax (dists p1 p2 p3 p4) = 2 * listMin (dists p1 p2 p3 p4)) := by
    sorry

  /-- Whenever the function returns Result.ok r, if r=true then each of p1,p2,p3,p4 is a vertex of the convex hull of the set {p1,p2,p3,p4}; equivalently, no one of the four points lies in the convex hull of the other three.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_9 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        ¬ inHull3 p1 p2 p3 p4 ∧ ¬ inHull3 p2 p1 p3 p4 ∧
          ¬ inHull3 p3 p1 p2 p4 ∧ ¬ inHull3 p4 p1 p2 p3 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          ¬ inHull3 p1 p2 p3 p4 ∧ ¬ inHull3 p2 p1 p3 p4 ∧
            ¬ inHull3 p3 p1 p2 p4 ∧ ¬ inHull3 p4 p1 p2 p3) := by
    sorry

  /-- Let q_i be the point [p_i[0]+tx, p_i[1]+ty]. Whenever valid_square(p1,p2,p3,p4) returns Result.ok r and valid_square(q_1,q_2,q_3,q_4) returns Result.ok r', we have r=r'.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000; and tx,ty are integers such that for each i, -10000 <= p_i[0]+tx <= 10000 and -10000 <= p_i[1]+ty <= 10000. -/
  theorem spec_10 (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64) (tx ty : ℤ)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (hq1 : Shifted q1 p1 tx ty) (hq2 : Shifted q2 p2 tx ty)
      (hq3 : Shifted q3 p3 tx ty) (hq4 : Shifted q4 p4 tx ty)
      (hs1 : InRangeShifted p1 tx ty) (hs2 : InRangeShifted p2 tx ty)
      (hs3 : InRangeShifted p3 tx ty) (hs4 : InRangeShifted p4 tx ty)
      (r r' : Bool)
      (hr : valid_square p1 p2 p3 p4 = .ok r)
      (hr' : valid_square q1 q2 q3 q4 = .ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64) (tx ty : ℤ)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (hq1 : Shifted q1 p1 tx ty) (hq2 : Shifted q2 p2 tx ty)
        (hq3 : Shifted q3 p3 tx ty) (hq4 : Shifted q4 p4 tx ty)
        (hs1 : InRangeShifted p1 tx ty) (hs2 : InRangeShifted p2 tx ty)
        (hs3 : InRangeShifted p3 tx ty) (hs4 : InRangeShifted p4 tx ty)
        (r r' : Bool)
        (hr : valid_square p1 p2 p3 p4 = Result.ok r)
        (hr' : valid_square q1 q2 q3 q4 = Result.ok r'), r = r') := by
    sorry

  /-- Let q_i=[c*p_i[0], c*p_i[1]]. Whenever valid_square(p1,p2,p3,p4) returns Result.ok r and valid_square(q_1,q_2,q_3,q_4) returns Result.ok r', we have r=r'.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000; and c is a positive integer such that for each i, -10000 <= c*p_i[0] <= 10000 and -10000 <= c*p_i[1] <= 10000. -/
  theorem spec_11 (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64) (c : ℤ)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (hc : 0 < c)
      (hq1 : Scaled q1 p1 c) (hq2 : Scaled q2 p2 c)
      (hq3 : Scaled q3 p3 c) (hq4 : Scaled q4 p4 c)
      (hs1 : InRangeScaled p1 c) (hs2 : InRangeScaled p2 c)
      (hs3 : InRangeScaled p3 c) (hs4 : InRangeScaled p4 c)
      (r r' : Bool)
      (hr : valid_square p1 p2 p3 p4 = .ok r)
      (hr' : valid_square q1 q2 q3 q4 = .ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64) (c : ℤ)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (hc : 0 < c)
        (hq1 : Scaled q1 p1 c) (hq2 : Scaled q2 p2 c)
        (hq3 : Scaled q3 p3 c) (hq4 : Scaled q4 p4 c)
        (hs1 : InRangeScaled p1 c) (hs2 : InRangeScaled p2 c)
        (hs3 : InRangeScaled p3 c) (hs4 : InRangeScaled p4 c)
        (r r' : Bool)
        (hr : valid_square p1 p2 p3 p4 = Result.ok r)
        (hr' : valid_square q1 q2 q3 q4 = Result.ok r'), r = r') := by
    sorry

  /-- Let q_i=[p_i[1], p_i[0]] (reflection in the line y=x). Whenever valid_square(p1,p2,p3,p4) returns Result.ok r and valid_square(q_1,q_2,q_3,q_4) returns Result.ok r', we have r=r'.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_12 (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (hq1 : Transposed q1 p1) (hq2 : Transposed q2 p2)
      (hq3 : Transposed q3 p3) (hq4 : Transposed q4 p4)
      (r r' : Bool)
      (hr : valid_square p1 p2 p3 p4 = .ok r)
      (hr' : valid_square q1 q2 q3 q4 = .ok r') :
      r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (p1 p2 p3 p4 q1 q2 q3 q4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (hq1 : Transposed q1 p1) (hq2 : Transposed q2 p2)
        (hq3 : Transposed q3 p3) (hq4 : Transposed q4 p4)
        (r r' : Bool)
        (hr : valid_square p1 p2 p3 p4 = Result.ok r)
        (hr' : valid_square q1 q2 q3 q4 = Result.ok r'), r = r') := by
    sorry

  /-- Write D_ij as in spec_1. Whenever the function returns Result.ok r, if r=true then there is a pairing of {1,2,3,4} into two disjoint unordered pairs {a,c} and {b,d} whose union is {1,2,3,4} such that p_a[0]+p_c[0]=p_b[0]+p_d[0], p_a[1]+p_c[1]=p_b[1]+p_d[1], D_ac=D_bd=L for some L>0, and (p_c[0]-p_a[0])*(p_d[0]-p_b[0])+(p_c[1]-p_a[1])*(p_d[1]-p_b[1])=0.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_13 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        (PairWitness p1 p2 p3 p4 ∨ PairWitness p1 p3 p2 p4 ∨
          PairWitness p1 p4 p2 p3) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          (PairWitness p1 p2 p3 p4 ∨ PairWitness p1 p3 p2 p4 ∨
            PairWitness p1 p4 p2 p3)) := by
    sorry

  /-- With D_ij as in spec_1, let s = min{D_ij : 1<=i<j<=4}. Whenever the function returns Result.ok r, if r=true then the ordinary Euclidean area of the convex hull of {p1,p2,p3,p4} equals s.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_14 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true → hullArea p1 p2 p3 p4 = (listMin (dists p1 p2 p3 p4) : ℚ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true → hullArea p1 p2 p3 p4 = (listMin (dists p1 p2 p3 p4) : ℚ)) := by
    sorry

  /-- With D_ij as in spec_1, let s = min{D_ij : 1<=i<j<=4}. Whenever the function returns Result.ok r, if r=true then 1 <= s <= 400000000.
    Preconditions: len(p1)=len(p2)=len(p3)=len(p4)=2; write p_1=p1, p_2=p2, p_3=p3, p_4=p4; for each i in {1,2,3,4}, -10000 <= p_i[0] <= 10000 and -10000 <= p_i[1] <= 10000. -/
  theorem spec_15 (p1 p2 p3 p4 : Slice Std.I64)
      (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
      (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
      (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
      (r : Bool) (hr : valid_square p1 p2 p3 p4 = .ok r) :
      r = true →
        1 ≤ listMin (dists p1 p2 p3 p4) ∧ listMin (dists p1 p2 p3 p4) ≤ 400000000 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (p1 p2 p3 p4 : Slice Std.I64)
        (h1 : p1.val.length = 2) (h2 : p2.val.length = 2)
        (h3 : p3.val.length = 2) (h4 : p4.val.length = 2)
        (hp1 : InRange p1) (hp2 : InRange p2) (hp3 : InRange p3) (hp4 : InRange p4)
        (r : Bool) (hr : valid_square p1 p2 p3 p4 = Result.ok r), r = true →
          1 ≤ listMin (dists p1 p2 p3 p4) ∧ listMin (dists p1 p2 p3 p4) ≤ 400000000) := by
    sorry

  end AegisSpec.ValidSquare
