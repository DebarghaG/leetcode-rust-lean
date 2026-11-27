import Aegis.LargestSquareArea.Code.Funs

/-!
# Specifications of `Aegis.LargestSquareArea.largest_square_area`

LeetCode problem `find-the-largest-area-of-square-inside-two-rectangles`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.LargestSquareArea

  namespace AegisSpec.LargestSquareArea

  def coords (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun x => x.val)

  def coord (v : alloc.vec.Vec Std.I64) (k : Nat) : ℤ := (coords v)[k]?.getD 0

  def nthCoord (l : List (alloc.vec.Vec Std.I64)) (i k : Nat) : ℤ :=
    (l[i]?.map (fun v => coord v k)).getD 0

  def loX (bl : List (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ := nthCoord bl i 0

  def loY (bl : List (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ := nthCoord bl i 1

  def hiX (tr : List (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ := nthCoord tr i 0

  def hiY (tr : List (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ := nthCoord tr i 1

  def RectWF (bl tr : List (alloc.vec.Vec Std.I64)) (i : Nat) : Prop :=
    (bl[i]?).map coords = some [loX bl i, loY bl i] ∧
      (tr[i]?).map coords = some [hiX tr i, hiY tr i] ∧
        1 ≤ loX bl i ∧ loX bl i ≤ 10 ^ 7 ∧
          1 ≤ loY bl i ∧ loY bl i ≤ 10 ^ 7 ∧
            1 ≤ hiX tr i ∧ hiX tr i ≤ 10 ^ 7 ∧
              1 ≤ hiY tr i ∧ hiY tr i ≤ 10 ^ 7 ∧
                loX bl i < hiX tr i ∧ loY bl i < hiY tr i

  def Pre (bl tr : List (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    2 ≤ n ∧ n ≤ 10 ^ 3 ∧ bl.length = n ∧ tr.length = n ∧ ∀ i, i < n → RectWF bl tr i

  def width (bl tr : List (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
    min (hiX tr i) (hiX tr j) - max (loX bl i) (loX bl j)

  def height (bl tr : List (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
    min (hiY tr i) (hiY tr j) - max (loY bl i) (loY bl j)

  def side (bl tr : List (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
    max 0 (min (width bl tr i j) (height bl tr i j))

  def sqArea (bl tr : List (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
    side bl tr i j * side bl tr i j

  def maxArea (bl tr : List (alloc.vec.Vec Std.I64)) (n : Nat) : ℤ :=
    let s := ((Finset.range n).product (Finset.range n)).filter (fun p => p.1 < p.2)
    if h : s.Nonempty then s.sup' h (fun p => sqArea bl tr p.1 p.2) else 0

  def PermutedBy {α : Type} {n : Nat} (p : Equiv.Perm (Fin n)) (l l' : List α) : Prop :=
    l'.length = n ∧ ∀ i : Fin n, l'[(i : Nat)]? = l[((p i : Fin n) : Nat)]?

  def TranslatedBy (dx dy : ℤ) (bl tr bl' tr' : List (alloc.vec.Vec Std.I64)) : Prop :=
    bl'.length = bl.length ∧ tr'.length = tr.length ∧
      ∀ i, i < bl.length →
        (bl'[i]?).map coords = (bl[i]?).map (fun v => [coord v 0 + dx, coord v 1 + dy]) ∧
          (tr'[i]?).map coords = (tr[i]?).map (fun v => [coord v 0 + dx, coord v 1 + dy])

  /-- Whenever the function returns Ok r, r = max { s(i,j)^2 | 0 <= i < j < n }, where s(i,j) = max(0, min( min(c_i,c_j) - max(a_i,a_j), min(d_i,d_j) - max(b_i,b_j) )).
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_1 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r → r.val = maxArea bl.val tr.val n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r → r.val = maxArea bl.val tr.val n) := by
    sorry

  /-- The function returns Ok r for some value r; equivalently, it does not fail, panic, overflow, or access an out-of-bounds element on any input satisfying the preconditions.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_2 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∃ r, largest_square_area bl tr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∃ r, largest_square_area bl tr = ok r) := by
    sorry

  /-- Whenever the function returns Ok r, r >= 0.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_3 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns Ok r, r <= (10^7 - 1)^2.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_4 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r → r.val ≤ (10 ^ 7 - 1) ^ 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r → r.val ≤ (10 ^ 7 - 1) ^ 2) := by
    sorry

  /-- Whenever the function returns Ok r, there exists an integer s with 0 <= s <= 10^7 - 1 and r = s * s.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_5 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r →
        ∃ s : ℤ, 0 ≤ s ∧ s ≤ 10 ^ 7 - 1 ∧ r.val = s * s := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r →
          ∃ s : ℤ, 0 ≤ s ∧ s ≤ 10 ^ 7 - 1 ∧ r.val = s * s) := by
    sorry

  /-- Whenever the function returns Ok r, r = 0 if and only if for every pair of indices i,j with 0 <= i < j < n, either min(c_i,c_j) <= max(a_i,a_j) or min(d_i,d_j) <= max(b_i,b_j).
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_6 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r →
        (r.val = 0 ↔
          ∀ i j, i < j → j < n →
            width bl.val tr.val i j ≤ 0 ∨ height bl.val tr.val i j ≤ 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r →
          (r.val = 0 ↔
            ∀ i j, i < j → j < n →
              width bl.val tr.val i j ≤ 0 ∨ height bl.val tr.val i j ≤ 0)) := by
    sorry

  /-- Whenever the function returns Ok r and r > 0, there exist indices i,j with 0 <= i < j < n such that min(c_i,c_j) > max(a_i,a_j), min(d_i,d_j) > max(b_i,b_j), and r = ( min( min(c_i,c_j) - max(a_i,a_j), min(d_i,d_j) - max(b_i,b_j) ) )^2.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_7 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r → 0 < r.val →
        ∃ i j, i < j ∧ j < n ∧
          0 < width bl.val tr.val i j ∧ 0 < height bl.val tr.val i j ∧
            r.val = sqArea bl.val tr.val i j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r → 0 < r.val →
          ∃ i j, i < j ∧ j < n ∧
            0 < width bl.val tr.val i j ∧ 0 < height bl.val tr.val i j ∧
              r.val = sqArea bl.val tr.val i j) := by
    sorry

  /-- Whenever the function returns Ok r, for every pair i,j with 0 <= i < j < n, if w = min(c_i,c_j) - max(a_i,a_j) and h = min(d_i,d_j) - max(b_i,b_j), then max(0, min(w,h))^2 <= r.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_8 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r →
        ∀ i j, i < j → j < n → sqArea bl.val tr.val i j ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r →
          ∀ i j, i < j → j < n → sqArea bl.val tr.val i j ≤ r.val) := by
    sorry

  /-- Whenever the function returns Ok r, for every integer L with 1 <= L and L*L > r, and for every pair i,j with 0 <= i < j < n, either min(c_i,c_j) - max(a_i,a_j) < L or min(d_i,d_j) - max(b_i,b_j) < L.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_9 (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (hpre : Pre bl.val tr.val n) :
      ∀ r, largest_square_area bl tr = ok r →
        ∀ L : ℤ, 1 ≤ L → r.val < L * L →
          ∀ i j, i < j → j < n →
            width bl.val tr.val i j < L ∨ height bl.val tr.val i j < L := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (bl tr : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (hpre : Pre bl.val tr.val n), ∀ r, largest_square_area bl tr = ok r →
          ∀ L : ℤ, 1 ≤ L → r.val < L * L →
            ∀ i j, i < j → j < n →
              width bl.val tr.val i j < L ∨ height bl.val tr.val i j < L) := by
    sorry

  /-- For any bijection p of {0,...,n-1}, define permuted arrays by bottomLeft'[i] = bottomLeft[p(i)] and topRight'[i] = topRight[p(i)] for every i. Whenever the function returns Ok r on (bottomLeft, topRight), it returns Ok r on (bottomLeft', topRight').
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_10 (bl tr bl' tr' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
      (p : Equiv.Perm (Fin n))
      (hpre : Pre bl.val tr.val n)
      (hbl : PermutedBy p bl.val bl'.val) (htr : PermutedBy p tr.val tr'.val) :
      ∀ r, largest_square_area bl tr = ok r → largest_square_area bl' tr' = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (bl tr bl' tr' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
        (p : Equiv.Perm (Fin n))
        (hpre : Pre bl.val tr.val n)
        (hbl : PermutedBy p bl.val bl'.val) (htr : PermutedBy p tr.val tr'.val), ∀ r, largest_square_area bl tr = ok r → largest_square_area bl' tr' = ok r) := by
    sorry

  /-- For any integers dx and dy such that translating all x-coordinates by dx and all y-coordinates by dy keeps the preconditions true, define bottomLeft'[i] = [bottomLeft[i][0]+dx, bottomLeft[i][1]+dy] and topRight'[i] = [topRight[i][0]+dx, topRight[i][1]+dy]. Whenever the function returns Ok r on the original arrays, it returns Ok r on the translated arrays.
    Preconditions: Let n = len(bottomLeft) = len(topRight). Assume 2 <= n <= 10^3; for every i with 0 <= i < n, len(bottomLeft[i]) = 2 and len(topRight[i]) = 2; writing bottomLeft[i] = [a_i, b_i] and topRight[i] = [c_i, d_i], assume 1 <= a_i, b_i, c_i, d_i <= 10^7, a_i < c_i, and b_i < d_i. -/
  theorem spec_11 (bl tr bl' tr' : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (dx dy : ℤ)
      (hpre : Pre bl.val tr.val n)
      (hpre' : Pre bl'.val tr'.val n)
      (htrans : TranslatedBy dx dy bl.val tr.val bl'.val tr'.val) :
      ∀ r, largest_square_area bl tr = ok r → largest_square_area bl' tr' = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (bl tr bl' tr' : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (dx dy : ℤ)
        (hpre : Pre bl.val tr.val n)
        (hpre' : Pre bl'.val tr'.val n)
        (htrans : TranslatedBy dx dy bl.val tr.val bl'.val tr'.val), ∀ r, largest_square_area bl tr = ok r → largest_square_area bl' tr' = ok r) := by
    sorry

  end AegisSpec.LargestSquareArea
