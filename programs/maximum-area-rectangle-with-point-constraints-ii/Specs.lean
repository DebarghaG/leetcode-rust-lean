import Aegis.MaxRectangleArea.Code.Funs

/-!
# Specifications of `Aegis.MaxRectangleArea.max_rectangle_area`

LeetCode problem `maximum-area-rectangle-with-point-constraints-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxRectangleArea

open Aegis.MaxRectangleArea

def Occurs (xs ys : Slice I64) (a c : Int) : Prop :=
  ∃ (i : Nat) (x y : I64),
    xs.val[i]? = some x ∧ ys.val[i]? = some y ∧ x.val = a ∧ y.val = c

def CornersOccur (xs ys : Slice I64) (a b c d : Int) : Prop :=
  Occurs xs ys a c ∧ Occurs xs ys a d ∧ Occurs xs ys b c ∧ Occurs xs ys b d

def IsEmptyRect (xs ys : Slice I64) (a b c d : Int) : Prop :=
  a < b ∧ c < d ∧ CornersOccur xs ys a b c d ∧
    (∀ (i : Nat) (x y : I64), xs.val[i]? = some x → ys.val[i]? = some y →
      a ≤ x.val → x.val ≤ b → c ≤ y.val → y.val ≤ d →
      (x.val = a ∨ x.val = b) ∧ (y.val = c ∨ y.val = d))

def IsFourCorners (xs ys : Slice I64) (a b c d : Int) : Prop :=
  a < b ∧ c < d ∧ CornersOccur xs ys a b c d ∧
    (∀ (i : Nat) (x y : I64), xs.val[i]? = some x → ys.val[i]? = some y →
      (x.val = a ∧ y.val = c) ∨ (x.val = a ∧ y.val = d) ∨
      (x.val = b ∧ y.val = c) ∨ (x.val = b ∧ y.val = d))

def listMax : List I64 → Int
  | [] => 0
  | v :: l => l.foldr (fun w acc => max w.val acc) v.val

def listMin : List I64 → Int
  | [] => 0
  | v :: l => l.foldr (fun w acc => min w.val acc) v.val

def TranslatedBy (xs xs' : Slice I64) (k : Int) : Prop :=
  xs'.val.length = xs.val.length ∧
    ∀ (i : Nat) (x x' : I64),
      xs.val[i]? = some x → xs'.val[i]? = some x' → x'.val = x.val + k

def ReflectedAround (xs xs' : Slice I64) (C : Int) : Prop :=
  xs'.val.length = xs.val.length ∧
    ∀ (i : Nat) (x x' : I64),
      xs.val[i]? = some x → xs'.val[i]? = some x' → x'.val = C - x.val

def Reindexed (xs ys xs' ys' : Slice I64) : Prop :=
  xs'.val.length = xs.val.length ∧ ys'.val.length = ys.val.length ∧
    List.Perm (xs'.val.zip ys'.val) (xs.val.zip ys.val)

/-- The function returns a result r, and: (a) if there exists a tuple of integers (a,b,c,d) with a < b and c < d such that the four points (a,c), (a,d), (b,c), (b,d) all appear among the input points (i.e., for each of these four coordinate pairs there is an index i with xCoord[i] equal to the x-coordinate and yCoord[i] equal to the y-coordinate) and no input point (x,y) with a ≤ x ≤ b and c ≤ y ≤ d is different from these four corners, then r is the maximum of (b-a)*(d-c) over all such tuples; (b) if no such tuple exists, then r = -1.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct (i.e., for i ≠ j, xCoord[i] ≠ xCoord[j] or yCoord[i] ≠ yCoord[j]). -/
theorem spec_1 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ((∃ a b c d : Int, IsEmptyRect xs ys a b c d) →
          (∀ a b c d : Int, IsEmptyRect xs ys a b c d → (b - a) * (d - c) ≤ r.val) ∧
            (∃ a b c d : Int, IsEmptyRect xs ys a b c d ∧ (b - a) * (d - c) = r.val)) ∧
        ((¬ ∃ a b c d : Int, IsEmptyRect xs ys a b c d) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ((∃ a b c d : Int, IsEmptyRect xs ys a b c d) →
          (∀ a b c d : Int, IsEmptyRect xs ys a b c d → (b - a) * (d - c) ≤ r.val) ∧
            (∃ a b c d : Int, IsEmptyRect xs ys a b c d ∧ (b - a) * (d - c) = r.val)) ∧
        ((¬ ∃ a b c d : Int, IsEmptyRect xs ys a b c d) → r.val = -1)) := by
  sorry

/-- The function returns a result r, and either r = -1 or 1 ≤ r ≤ (max_{0≤i<n} xCoord[i] - min_{0≤i<n} xCoord[i]) * (max_{0≤i<n} yCoord[i] - min_{0≤i<n} yCoord[i]).
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_2 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        (r.val = -1 ∨
          (1 ≤ r.val ∧
            r.val ≤ (listMax xs.val - listMin xs.val) * (listMax ys.val - listMin ys.val))) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        (r.val = -1 ∨
          (1 ≤ r.val ∧
            r.val ≤ (listMax xs.val - listMin xs.val) * (listMax ys.val - listMin ys.val)))) := by
  sorry

/-- If n < 4, then the function returns a result r and r = -1.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_3 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hsmall : xs.val.length < 4) :
    ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hsmall : xs.val.length < 4), ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1) := by
  sorry

/-- If all xCoord[i] are equal (i.e., there is a constant X with xCoord[i] = X for all 0 ≤ i < n) or all yCoord[i] are equal (i.e., there is a constant Y with yCoord[i] = Y for all 0 ≤ i < n), then the function returns a result r and r = -1.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_4 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hdeg : (∃ X : Int, ∀ (i : Nat) (x : I64), xs.val[i]? = some x → x.val = X) ∨
      (∃ Y : Int, ∀ (i : Nat) (y : I64), ys.val[i]? = some y → y.val = Y)) :
    ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hdeg : (∃ X : Int, ∀ (i : Nat) (x : I64), xs.val[i]? = some x → x.val = X) ∨
      (∃ Y : Int, ∀ (i : Nat) (y : I64), ys.val[i]? = some y → y.val = Y)), ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1) := by
  sorry

/-- If n = 4, then the function returns a result r, and: if there exist integers a < b and c < d such that the set of the four input points is exactly {(a,c), (a,d), (b,c), (b,d)}, then r = (b-a)*(d-c); otherwise r = -1.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_5 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hfour : xs.val.length = 4) :
    ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ((∃ a b c d : Int, IsFourCorners xs ys a b c d) →
          ∃ a b c d : Int, IsFourCorners xs ys a b c d ∧ (b - a) * (d - c) = r.val) ∧
        ((¬ ∃ a b c d : Int, IsFourCorners xs ys a b c d) → r.val = -1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hfour : xs.val.length = 4), ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ((∃ a b c d : Int, IsFourCorners xs ys a b c d) →
          ∃ a b c d : Int, IsFourCorners xs ys a b c d ∧ (b - a) * (d - c) = r.val) ∧
        ((¬ ∃ a b c d : Int, IsFourCorners xs ys a b c d) → r.val = -1)) := by
  sorry

/-- Whenever the function returns a result r with r ≠ -1, there exist indices i, j, k, l such that xCoord[i] = xCoord[j] < xCoord[k] = xCoord[l], yCoord[i] = yCoord[k] < yCoord[j] = yCoord[l], (xCoord[k]-xCoord[i])*(yCoord[j]-yCoord[i]) = r, and for every index m with 0 ≤ m < n, if xCoord[i] ≤ xCoord[m] ≤ xCoord[k] and yCoord[i] ≤ yCoord[m] ≤ yCoord[l], then m ∈ {i,j,k,l}.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_6 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∀ r : I64, max_rectangle_area xs ys = ok r → r.val ≠ -1 →
      ∃ (i j k l : Nat) (xi xj xk xl yi yj yk yl : I64),
        xs.val[i]? = some xi ∧ xs.val[j]? = some xj ∧
        xs.val[k]? = some xk ∧ xs.val[l]? = some xl ∧
        ys.val[i]? = some yi ∧ ys.val[j]? = some yj ∧
        ys.val[k]? = some yk ∧ ys.val[l]? = some yl ∧
        xi.val = xj.val ∧ xk.val = xl.val ∧ xi.val < xk.val ∧
        yi.val = yk.val ∧ yj.val = yl.val ∧ yi.val < yj.val ∧
        (xk.val - xi.val) * (yj.val - yi.val) = r.val ∧
        (∀ (m : Nat) (xm ym : I64),
          xs.val[m]? = some xm → ys.val[m]? = some ym →
          xi.val ≤ xm.val → xm.val ≤ xk.val → yi.val ≤ ym.val → ym.val ≤ yj.val →
          m = i ∨ m = j ∨ m = k ∨ m = l) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∀ r : I64, max_rectangle_area xs ys = ok r → r.val ≠ -1 →
      ∃ (i j k l : Nat) (xi xj xk xl yi yj yk yl : I64),
        xs.val[i]? = some xi ∧ xs.val[j]? = some xj ∧
        xs.val[k]? = some xk ∧ xs.val[l]? = some xl ∧
        ys.val[i]? = some yi ∧ ys.val[j]? = some yj ∧
        ys.val[k]? = some yk ∧ ys.val[l]? = some yl ∧
        xi.val = xj.val ∧ xk.val = xl.val ∧ xi.val < xk.val ∧
        yi.val = yk.val ∧ yj.val = yl.val ∧ yi.val < yj.val ∧
        (xk.val - xi.val) * (yj.val - yi.val) = r.val ∧
        (∀ (m : Nat) (xm ym : I64),
          xs.val[m]? = some xm → ys.val[m]? = some ym →
          xi.val ≤ xm.val → xm.val ≤ xk.val → yi.val ≤ ym.val → ym.val ≤ yj.val →
          m = i ∨ m = j ∨ m = k ∨ m = l)) := by
  sorry

/-- Whenever the function returns a result r with r = -1, for every quadruple of integers (a,b,c,d) with a < b and c < d such that the four points (a,c), (a,d), (b,c), (b,d) all appear among the input points, there exists an index m with 0 ≤ m < n such that a ≤ xCoord[m] ≤ b, c ≤ yCoord[m] ≤ d, and (xCoord[m], yCoord[m]) is not one of the four corners (a,c), (a,d), (b,c), (b,d).
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_7 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∀ r : I64, max_rectangle_area xs ys = ok r → r.val = -1 →
      ∀ a b c d : Int, a < b → c < d → CornersOccur xs ys a b c d →
        ∃ (m : Nat) (xm ym : I64),
          xs.val[m]? = some xm ∧ ys.val[m]? = some ym ∧
          a ≤ xm.val ∧ xm.val ≤ b ∧ c ≤ ym.val ∧ ym.val ≤ d ∧
          ¬ ((xm.val = a ∨ xm.val = b) ∧ (ym.val = c ∨ ym.val = d)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∀ r : I64, max_rectangle_area xs ys = ok r → r.val = -1 →
      ∀ a b c d : Int, a < b → c < d → CornersOccur xs ys a b c d →
        ∃ (m : Nat) (xm ym : I64),
          xs.val[m]? = some xm ∧ ys.val[m]? = some ym ∧
          a ≤ xm.val ∧ xm.val ≤ b ∧ c ≤ ym.val ∧ ym.val ≤ d ∧
          ¬ ((xm.val = a ∨ xm.val = b) ∧ (ym.val = c ∨ ym.val = d))) := by
  sorry

/-- The function returns a result r, and for every tuple of integers (a,b,c,d) with a < b and c < d such that the four points (a,c), (a,d), (b,c), (b,d) all appear among the input points and no input point (x,y) with a ≤ x ≤ b and c ≤ y ≤ d is different from these four corners, we have r ≥ (b-a)*(d-c).
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_8 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ∀ a b c d : Int, IsEmptyRect xs ys a b c d → (b - a) * (d - c) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∃ r : I64,
      max_rectangle_area xs ys = ok r ∧
        ∀ a b c d : Int, IsEmptyRect xs ys a b c d → (b - a) * (d - c) ≤ r.val) := by
  sorry

/-- The function returns a result r on (xCoord, yCoord), and it also returns a result r' on (yCoord, xCoord) (which satisfies the same preconditions after swapping the roles of the coordinate arrays), and r = r'.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_9 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∃ r r' : I64,
      max_rectangle_area xs ys = ok r ∧ max_rectangle_area ys xs = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∃ r r' : I64,
      max_rectangle_area xs ys = ok r ∧ max_rectangle_area ys xs = ok r' ∧ r.val = r'.val) := by
  sorry

/-- For every integer k such that 0 ≤ xCoord[i] + k ≤ 80000000 for all 0 ≤ i < n, let xCoord' be the slice with xCoord'[i] = xCoord[i] + k. Then the function returns a result r on (xCoord, yCoord), it returns a result r' on (xCoord', yCoord), and r = r'.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_10 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (k : Int)
    (hk : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val + k ∧ x.val + k ≤ 80000000) :
    ∃ xs' : Slice I64, TranslatedBy xs xs' k ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (k : Int)
    (hk : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val + k ∧ x.val + k ≤ 80000000), ∃ xs' : Slice I64, TranslatedBy xs xs' k ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys = ok r' ∧ r.val = r'.val) := by
  sorry

/-- For every integer k such that 0 ≤ yCoord[i] + k ≤ 80000000 for all 0 ≤ i < n, let yCoord' be the slice with yCoord'[i] = yCoord[i] + k. Then the function returns a result r on (xCoord, yCoord), it returns a result r' on (xCoord, yCoord'), and r = r'.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_11 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (k : Int)
    (hk : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val + k ∧ y.val + k ≤ 80000000) :
    ∃ ys' : Slice I64, TranslatedBy ys ys' k ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs ys' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (k : Int)
    (hk : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val + k ∧ y.val + k ≤ 80000000), ∃ ys' : Slice I64, TranslatedBy ys ys' k ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs ys' = ok r' ∧ r.val = r'.val) := by
  sorry

/-- For every integer C such that 0 ≤ C - xCoord[i] ≤ 80000000 for all 0 ≤ i < n, let xCoord' be the slice with xCoord'[i] = C - xCoord[i]. Then the function returns a result r on (xCoord, yCoord), it returns a result r' on (xCoord', yCoord), and r = r'.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_12 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (C : Int)
    (hC : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ C - x.val ∧ C - x.val ≤ 80000000) :
    ∃ xs' : Slice I64, ReflectedAround xs xs' C ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (C : Int)
    (hC : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ C - x.val ∧ C - x.val ≤ 80000000), ∃ xs' : Slice I64, ReflectedAround xs xs' C ∧
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys = ok r' ∧ r.val = r'.val) := by
  sorry

/-- If there do not exist integers a < b and c < d such that the four points (a,c), (a,d), (b,c), (b,d) all appear among the input points, then the function returns a result r and r = -1.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_13 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hnone : ¬ ∃ a b c d : Int, a < b ∧ c < d ∧ CornersOccur xs ys a b c d) :
    ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val)
    (hnone : ¬ ∃ a b c d : Int, a < b ∧ c < d ∧ CornersOccur xs ys a b c d), ∃ r : I64, max_rectangle_area xs ys = ok r ∧ r.val = -1) := by
  sorry

/-- For every permutation π of {0, ..., n-1}, let xCoord'[i] = xCoord[π(i)] and yCoord'[i] = yCoord[π(i)] for 0 ≤ i < n. Then the function returns a result r on (xCoord, yCoord), it returns a result r' on (xCoord', yCoord'), and r = r'.
  Preconditions: Let n = len(xCoord). Assume len(xCoord) = len(yCoord), 1 ≤ n ≤ 200000, 0 ≤ xCoord[i] ≤ 80000000 and 0 ≤ yCoord[i] ≤ 80000000 for every 0 ≤ i < n, and the points (xCoord[i], yCoord[i]) for 0 ≤ i < n are pairwise distinct. -/
theorem spec_14 (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val) :
    ∀ xs' ys' : Slice I64, Reindexed xs ys xs' ys' →
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys' = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (xs ys : Slice I64)
    (hlen : xs.val.length = ys.val.length)
    (hpos : 1 ≤ xs.val.length)
    (hsize : xs.val.length ≤ 200000)
    (hbx : ∀ (i : Nat) (x : I64), xs.val[i]? = some x → 0 ≤ x.val ∧ x.val ≤ 80000000)
    (hby : ∀ (i : Nat) (y : I64), ys.val[i]? = some y → 0 ≤ y.val ∧ y.val ≤ 80000000)
    (hdist : ∀ (i j : Nat) (x₁ x₂ y₁ y₂ : I64),
      xs.val[i]? = some x₁ → xs.val[j]? = some x₂ →
      ys.val[i]? = some y₁ → ys.val[j]? = some y₂ →
      i ≠ j → x₁.val ≠ x₂.val ∨ y₁.val ≠ y₂.val), ∀ xs' ys' : Slice I64, Reindexed xs ys xs' ys' →
      ∃ r r' : I64,
        max_rectangle_area xs ys = ok r ∧ max_rectangle_area xs' ys' = ok r' ∧ r.val = r'.val) := by
  sorry

end AegisSpec.MaxRectangleArea
