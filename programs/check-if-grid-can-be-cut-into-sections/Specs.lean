import Aegis.CheckValidCuts.Code.Funs

/-!
# Specifications of `Aegis.CheckValidCuts.check_valid_cuts`

LeetCode problem `check-if-grid-can-be-cut-into-sections`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CheckValidCuts

  namespace AegisSpec.CheckValidCuts

  abbrev Rect : Type := alloc.vec.Vec I64

  def rowCoords (rectangles : List Rect) (i : Nat) : List Int :=
    match rectangles[i]? with
    | none => []
    | some row => row.val.map (fun x => x.val)

  def coord (rectangles : List Rect) (i k : Nat) : Int :=
    ((rowCoords rectangles i)[k]?).getD 0

  def sx (rectangles : List Rect) (i : Nat) : Int := coord rectangles i 0

  def sy (rectangles : List Rect) (i : Nat) : Int := coord rectangles i 1

  def ex (rectangles : List Rect) (i : Nat) : Int := coord rectangles i 2

  def ey (rectangles : List Rect) (i : Nat) : Int := coord rectangles i 3

  def ProblemConstraints (n : Int) (rectangles : List Rect) : Prop :=
    n ≥ 3 ∧
    rectangles.length ≥ 3 ∧
    (∀ i, i < rectangles.length → (rowCoords rectangles i).length = 4) ∧
    (∀ i, i < rectangles.length →
      0 ≤ sx rectangles i ∧ sx rectangles i < ex rectangles i ∧ ex rectangles i ≤ n ∧
      0 ≤ sy rectangles i ∧ sy rectangles i < ey rectangles i ∧ ey rectangles i ≤ n) ∧
    (∀ i j, i < rectangles.length → j < rectangles.length → i ≠ j →
      ¬ (sx rectangles i < ex rectangles j ∧ sx rectangles j < ex rectangles i ∧
         sy rectangles i < ey rectangles j ∧ sy rectangles j < ey rectangles i))

  def CutsX (rectangles : List Rect) (a b : Int) : Prop :=
    ∀ i, i < rectangles.length →
      ¬ (sx rectangles i < a ∧ a < ex rectangles i) ∧
      ¬ (sx rectangles i < b ∧ b < ex rectangles i)

  def CutsY (rectangles : List Rect) (c d : Int) : Prop :=
    ∀ i, i < rectangles.length →
      ¬ (sy rectangles i < c ∧ c < ey rectangles i) ∧
      ¬ (sy rectangles i < d ∧ d < ey rectangles i)

  def V (n : Int) (rectangles : List Rect) : Prop :=
    ∃ a b : Int, 0 ≤ a ∧ a < b ∧ b ≤ n ∧ CutsX rectangles a b ∧
      (∃ i, i < rectangles.length ∧ ex rectangles i ≤ a) ∧
      (∃ i, i < rectangles.length ∧ a ≤ sx rectangles i ∧ ex rectangles i ≤ b) ∧
      (∃ i, i < rectangles.length ∧ b ≤ sx rectangles i)

  def H (n : Int) (rectangles : List Rect) : Prop :=
    ∃ c d : Int, 0 ≤ c ∧ c < d ∧ d ≤ n ∧ CutsY rectangles c d ∧
      (∃ i, i < rectangles.length ∧ ey rectangles i ≤ c) ∧
      (∃ i, i < rectangles.length ∧ c ≤ sy rectangles i ∧ ey rectangles i ≤ d) ∧
      (∃ i, i < rectangles.length ∧ d ≤ sy rectangles i)

  def VStrict (n : Int) (rectangles : List Rect) : Prop :=
    ∃ a b : Int, 0 < a ∧ a < b ∧ b < n ∧ CutsX rectangles a b ∧
      (∃ i, i < rectangles.length ∧ ex rectangles i ≤ a) ∧
      (∃ i, i < rectangles.length ∧ a ≤ sx rectangles i ∧ ex rectangles i ≤ b) ∧
      (∃ i, i < rectangles.length ∧ b ≤ sx rectangles i)

  def HStrict (n : Int) (rectangles : List Rect) : Prop :=
    ∃ c d : Int, 0 < c ∧ c < d ∧ d < n ∧ CutsY rectangles c d ∧
      (∃ i, i < rectangles.length ∧ ey rectangles i ≤ c) ∧
      (∃ i, i < rectangles.length ∧ c ≤ sy rectangles i ∧ ey rectangles i ≤ d) ∧
      (∃ i, i < rectangles.length ∧ d ≤ sy rectangles i)

  def NonemptyRange (m : Nat) (p : Nat → Prop) : Prop :=
    ∃ i, i < m ∧ p i

  def UniqueRange (m : Nat) (p : Nat → Prop) : Prop :=
    ∃ i, i < m ∧ p i ∧ ∀ j, j < m → p j → j = i

  /-- Whenever check_valid_cuts(n, rectangles) returns a result r, r = true if and only if V(n, rectangles) or H(n, rectangles), where: V(n, rectangles) means there exist integers a,b with 0 <= a < b <= n such that (i) for every i with 0 <= i < m, not (sx_i < a < ex_i) and not (sx_i < b < ex_i); (ii) there exists i with ex_i <= a; (iii) there exists i with sx_i >= a and ex_i <= b; (iv) there exists i with sx_i >= b. H(n, rectangles) means there exist integers c,d with 0 <= c < d <= n such that (i) for every i, not (sy_i < c < ey_i) and not (sy_i < d < ey_i); (ii) there exists i with ey_i <= c; (iii) there exists i with sy_i >= c and ey_i <= d; (iv) there exists i with sy_i >= d.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_1 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧
        (r = true ↔ V n.val rectangles.val ∨ H n.val rectangles.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧
          (r = true ↔ V n.val rectangles.val ∨ H n.val rectangles.val)) := by
    sorry

  /-- For every n and rectangles satisfying the preconditions, the call check_valid_cuts(n, rectangles) returns a result r; it does not panic, get stuck, or overflow.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_2 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val), ∃ r : Bool, check_valid_cuts n rectangles = ok r) := by
    sorry

  /-- Let V(n, rectangles) mean that there exist integers a,b with 0 <= a < b <= n such that: (i) for every i with 0 <= i < m, not (sx_i < a < ex_i) and not (sx_i < b < ex_i); (ii) there exists i with ex_i <= a; (iii) there exists i with sx_i >= a and ex_i <= b; (iv) there exists i with sx_i >= b. If V(n, rectangles) holds, then check_valid_cuts(n, rectangles) returns true.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_3 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (hV : V n.val rectangles.val) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (hV : V n.val rectangles.val), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ r = true) := by
    sorry

  /-- Let H(n, rectangles) mean that there exist integers c,d with 0 <= c < d <= n such that: (i) for every i with 0 <= i < m, not (sy_i < c < ey_i) and not (sy_i < d < ey_i); (ii) there exists i with ey_i <= c; (iii) there exists i with sy_i >= c and ey_i <= d; (iv) there exists i with sy_i >= d. If H(n, rectangles) holds, then check_valid_cuts(n, rectangles) returns true.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_4 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (hH : H n.val rectangles.val) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (hH : H n.val rectangles.val), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ r = true) := by
    sorry

  /-- Whenever check_valid_cuts(n, rectangles) returns false, both of the following hold: (1) there do not exist integers a,b with 0 <= a < b <= n such that (i) for every i, not (sx_i < a < ex_i) and not (sx_i < b < ex_i); (ii) some i has ex_i <= a; (iii) some i has sx_i >= a and ex_i <= b; (iv) some i has sx_i >= b; (2) there do not exist integers c,d with 0 <= c < d <= n such that (i) for every i, not (sy_i < c < ey_i) and not (sy_i < d < ey_i); (ii) some i has ey_i <= c; (iii) some i has sy_i >= c and ey_i <= d; (iv) some i has sy_i >= d.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_5 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val) :
      ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = false →
        ¬ V n.val rectangles.val ∧ ¬ H n.val rectangles.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val), ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = false →
          ¬ V n.val rectangles.val ∧ ¬ H n.val rectangles.val) := by
    sorry

  /-- Whenever check_valid_cuts(n, rectangles) returns true, at least one of the following holds: (a) there exist integers a,b with 0 < a < b < n such that (i) for every i, not (sx_i < a < ex_i) and not (sx_i < b < ex_i); (ii) some i has ex_i <= a; (iii) some i has sx_i >= a and ex_i <= b; (iv) some i has sx_i >= b; (b) there exist integers c,d with 0 < c < d < n such that (i) for every i, not (sy_i < c < ey_i) and not (sy_i < d < ey_i); (ii) some i has ey_i <= c; (iii) some i has sy_i >= c and ey_i <= d; (iv) some i has sy_i >= d.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_6 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val) :
      ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
        VStrict n.val rectangles.val ∨ HStrict n.val rectangles.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val), ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
          VStrict n.val rectangles.val ∨ HStrict n.val rectangles.val) := by
    sorry

  /-- For every permutation pi of {0,...,m-1}, let R' be the list of length m with R'[i] = rectangles[pi(i)] for 0 <= i < m. Then check_valid_cuts(n, rectangles) returns the same Bool as check_valid_cuts(n, R').
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_7 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (pi : Equiv.Perm (Fin rectangles.val.length))
      (R' : Slice Rect)
      (hR' : R'.val = List.ofFn (fun i : Fin rectangles.val.length =>
        rectangles.val.get (pi i))) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (pi : Equiv.Perm (Fin rectangles.val.length))
        (R' : Slice Rect)
        (hR' : R'.val = List.ofFn (fun i : Fin rectangles.val.length =>
          rectangles.val.get (pi i))), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r) := by
    sorry

  /-- Let R^T be the list of length m with R^T[i] = [sy_i, sx_i, ey_i, ex_i] for 0 <= i < m, i.e., swap the x and y coordinates of every rectangle. Then check_valid_cuts(n, rectangles) returns the same Bool as check_valid_cuts(n, R^T).
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_8 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (R' : Slice Rect)
      (hlen : R'.val.length = rectangles.val.length)
      (hR' : ∀ i, i < rectangles.val.length →
        rowCoords R'.val i = [sy rectangles.val i, sx rectangles.val i,
          ey rectangles.val i, ex rectangles.val i]) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (R' : Slice Rect)
        (hlen : R'.val.length = rectangles.val.length)
        (hR' : ∀ i, i < rectangles.val.length →
          rowCoords R'.val i = [sy rectangles.val i, sx rectangles.val i,
            ey rectangles.val i, ex rectangles.val i]), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r) := by
    sorry

  /-- For every integer n' with n <= n' <= 2^63-1, the call check_valid_cuts(n', rectangles) returns the same Bool as check_valid_cuts(n, rectangles).
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_9 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (n' : I64) (hn' : n.val ≤ n'.val) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n' rectangles = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (n' : I64) (hn' : n.val ≤ n'.val), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n' rectangles = ok r) := by
    sorry

  /-- If check_valid_cuts(n, rectangles) returns true, then check_valid_cuts(n, R') returns true.
    Preconditions: The original n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). Let R' be another list of m rectangles satisfying the same problem constraints with n, and write R'[i] = [sx'_i, sy'_i, ex'_i, ey'_i]. Suppose that for every i, sx_i <= sx'_i < ex'_i <= ex_i and sy_i <= sy'_i < ey'_i <= ey_i. -/
  theorem spec_10 (n : I64) (rectangles : Slice Rect) (R' : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (h' : ProblemConstraints n.val R'.val)
      (hm : R'.val.length = rectangles.val.length)
      (hsub : ∀ i, i < rectangles.val.length →
        sx rectangles.val i ≤ sx R'.val i ∧
        sx R'.val i < ex R'.val i ∧
        ex R'.val i ≤ ex rectangles.val i ∧
        sy rectangles.val i ≤ sy R'.val i ∧
        sy R'.val i < ey R'.val i ∧
        ey R'.val i ≤ ey rectangles.val i) :
      ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
        ∃ r' : Bool, check_valid_cuts n R' = ok r' ∧ r' = true := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect) (R' : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (h' : ProblemConstraints n.val R'.val)
        (hm : R'.val.length = rectangles.val.length)
        (hsub : ∀ i, i < rectangles.val.length →
          sx rectangles.val i ≤ sx R'.val i ∧
          sx R'.val i < ex R'.val i ∧
          ex R'.val i ≤ ex rectangles.val i ∧
          sy rectangles.val i ≤ sy R'.val i ∧
          sy R'.val i < ey R'.val i ∧
          ey R'.val i ≤ ey rectangles.val i), ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
          ∃ r' : Bool, check_valid_cuts n R' = ok r' ∧ r' = true) := by
    sorry

  /-- If check_valid_cuts(n, rectangles) returns true, then there exist two vertical cuts or two horizontal cuts such that every rectangle lies entirely in one of the three sections and each of the three sections contains exactly one rectangle. In symbols, either there exist integers a,b with 0 <= a < b <= n satisfying (i) for every i, not (sx_i < a < ex_i) and not (sx_i < b < ex_i), and such that the three sets L = {i | ex_i <= a}, M = {i | sx_i >= a and ex_i <= b}, R = {i | sx_i >= b} each have cardinality 1, or the analogous statement holds for y-coordinates with c,d and sets {i | ey_i <= c}, {i | sy_i >= c and ey_i <= d}, {i | sy_i >= d}.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). Also m = 3. -/
  theorem spec_11 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (hm : rectangles.val.length = 3) :
      ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
        ((∃ a b : Int, 0 ≤ a ∧ a < b ∧ b ≤ n ∧ CutsX rectangles.val a b ∧
            UniqueRange rectangles.val.length (fun i => ex rectangles.val i ≤ a) ∧
            UniqueRange rectangles.val.length
              (fun i => a ≤ sx rectangles.val i ∧ ex rectangles.val i ≤ b) ∧
            UniqueRange rectangles.val.length (fun i => b ≤ sx rectangles.val i)) ∨
          (∃ c d : Int, 0 ≤ c ∧ c < d ∧ d ≤ n ∧ CutsY rectangles.val c d ∧
            UniqueRange rectangles.val.length (fun i => ey rectangles.val i ≤ c) ∧
            UniqueRange rectangles.val.length
              (fun i => c ≤ sy rectangles.val i ∧ ey rectangles.val i ≤ d) ∧
            UniqueRange rectangles.val.length (fun i => d ≤ sy rectangles.val i))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (hm : rectangles.val.length = 3), ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
          ((∃ a b : Int, 0 ≤ a ∧ a < b ∧ b ≤ n ∧ CutsX rectangles.val a b ∧
              UniqueRange rectangles.val.length (fun i => ex rectangles.val i ≤ a) ∧
              UniqueRange rectangles.val.length
                (fun i => a ≤ sx rectangles.val i ∧ ex rectangles.val i ≤ b) ∧
              UniqueRange rectangles.val.length (fun i => b ≤ sx rectangles.val i)) ∨
            (∃ c d : Int, 0 ≤ c ∧ c < d ∧ d ≤ n ∧ CutsY rectangles.val c d ∧
              UniqueRange rectangles.val.length (fun i => ey rectangles.val i ≤ c) ∧
              UniqueRange rectangles.val.length
                (fun i => c ≤ sy rectangles.val i ∧ ey rectangles.val i ≤ d) ∧
              UniqueRange rectangles.val.length (fun i => d ≤ sy rectangles.val i)))) := by
    sorry

  /-- Whenever check_valid_cuts(n, rectangles) returns true, at least one of the following holds: (a) there exist indices p,q and integers a,b with 0 <= a < b <= n such that a = ex_p, b = sx_q, for every i not (sx_i < a < ex_i) and not (sx_i < b < ex_i), and the three sets {i | ex_i <= a}, {i | sx_i >= a and ex_i <= b}, {i | sx_i >= b} are all nonempty; (b) there exist indices p,q and integers c,d with 0 <= c < d <= n such that c = ey_p, d = sy_q, for every i not (sy_i < c < ey_i) and not (sy_i < d < ey_i), and the three sets {i | ey_i <= c}, {i | sy_i >= c and ey_i <= d}, {i | sy_i >= d} are all nonempty.
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). -/
  theorem spec_12 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val) :
      ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
        ((∃ p q : Nat, p < rectangles.val.length ∧ q < rectangles.val.length ∧
            ∃ a b : Int, 0 ≤ a ∧ a < b ∧ b ≤ n.val ∧
              a = ex rectangles.val p ∧ b = sx rectangles.val q ∧
              CutsX rectangles.val a b ∧
              NonemptyRange rectangles.val.length (fun i => ex rectangles.val i ≤ a) ∧
              NonemptyRange rectangles.val.length
                (fun i => a ≤ sx rectangles.val i ∧ ex rectangles.val i ≤ b) ∧
              NonemptyRange rectangles.val.length (fun i => b ≤ sx rectangles.val i)) ∨
          (∃ p q : Nat, p < rectangles.val.length ∧ q < rectangles.val.length ∧
            ∃ c d : Int, 0 ≤ c ∧ c < d ∧ d ≤ n.val ∧
              c = ey rectangles.val p ∧ d = sy rectangles.val q ∧
              CutsY rectangles.val c d ∧
              NonemptyRange rectangles.val.length (fun i => ey rectangles.val i ≤ c) ∧
              NonemptyRange rectangles.val.length
                (fun i => c ≤ sy rectangles.val i ∧ ey rectangles.val i ≤ d) ∧
              NonemptyRange rectangles.val.length (fun i => d ≤ sy rectangles.val i))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val), ∀ r : Bool, check_valid_cuts n rectangles = ok r → r = true →
          ((∃ p q : Nat, p < rectangles.val.length ∧ q < rectangles.val.length ∧
              ∃ a b : Int, 0 ≤ a ∧ a < b ∧ b ≤ n.val ∧
                a = ex rectangles.val p ∧ b = sx rectangles.val q ∧
                CutsX rectangles.val a b ∧
                NonemptyRange rectangles.val.length (fun i => ex rectangles.val i ≤ a) ∧
                NonemptyRange rectangles.val.length
                  (fun i => a ≤ sx rectangles.val i ∧ ex rectangles.val i ≤ b) ∧
                NonemptyRange rectangles.val.length (fun i => b ≤ sx rectangles.val i)) ∨
            (∃ p q : Nat, p < rectangles.val.length ∧ q < rectangles.val.length ∧
              ∃ c d : Int, 0 ≤ c ∧ c < d ∧ d ≤ n.val ∧
                c = ey rectangles.val p ∧ d = sy rectangles.val q ∧
                CutsY rectangles.val c d ∧
                NonemptyRange rectangles.val.length (fun i => ey rectangles.val i ≤ c) ∧
                NonemptyRange rectangles.val.length
                  (fun i => c ≤ sy rectangles.val i ∧ ey rectangles.val i ≤ d) ∧
                NonemptyRange rectangles.val.length (fun i => d ≤ sy rectangles.val i)))) := by
    sorry

  /-- check_valid_cuts(n, rectangles) returns the same Bool as check_valid_cuts(n, R').
    Preconditions: n and rectangles satisfy the problem constraints: n >= 3; m = len(rectangles) >= 3; each rectangles[i] has length 4; writing sx_i = rectangles[i][0], sy_i = rectangles[i][1], ex_i = rectangles[i][2], ey_i = rectangles[i][3] for 0 <= i < m, we have 0 <= sx_i < ex_i <= n and 0 <= sy_i < ey_i <= n; and for i != j the interiors are disjoint: not (sx_i < ex_j and sx_j < ex_i and sy_i < ey_j and sy_j < ey_i). Let dx,dy be integers such that for every i, 0 <= sx_i+dx < ex_i+dx <= n and 0 <= sy_i+dy < ey_i+dy <= n, and let R'[i] = [sx_i+dx, sy_i+dy, ex_i+dx, ey_i+dy]. -/
  theorem spec_13 (n : I64) (rectangles : Slice Rect)
      (h : ProblemConstraints n.val rectangles.val)
      (dx dy : Int)
      (hshift : ∀ i, i < rectangles.val.length →
        0 ≤ sx rectangles.val i + dx ∧ sx rectangles.val i + dx < ex rectangles.val i + dx ∧
        ex rectangles.val i + dx ≤ n.val ∧
        0 ≤ sy rectangles.val i + dy ∧ sy rectangles.val i + dy < ey rectangles.val i + dy ∧
        ey rectangles.val i + dy ≤ n.val)
      (R' : Slice Rect)
      (hlen : R'.val.length = rectangles.val.length)
      (hR' : ∀ i, i < rectangles.val.length →
        rowCoords R'.val i = [sx rectangles.val i + dx, sy rectangles.val i + dy,
          ex rectangles.val i + dx, ey rectangles.val i + dy]) :
      ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (rectangles : Slice Rect)
        (h : ProblemConstraints n.val rectangles.val)
        (dx dy : Int)
        (hshift : ∀ i, i < rectangles.val.length →
          0 ≤ sx rectangles.val i + dx ∧ sx rectangles.val i + dx < ex rectangles.val i + dx ∧
          ex rectangles.val i + dx ≤ n.val ∧
          0 ≤ sy rectangles.val i + dy ∧ sy rectangles.val i + dy < ey rectangles.val i + dy ∧
          ey rectangles.val i + dy ≤ n.val)
        (R' : Slice Rect)
        (hlen : R'.val.length = rectangles.val.length)
        (hR' : ∀ i, i < rectangles.val.length →
          rowCoords R'.val i = [sx rectangles.val i + dx, sy rectangles.val i + dy,
            ex rectangles.val i + dx, ey rectangles.val i + dy]), ∃ r : Bool, check_valid_cuts n rectangles = ok r ∧ check_valid_cuts n R' = ok r) := by
    sorry

  end AegisSpec.CheckValidCuts
