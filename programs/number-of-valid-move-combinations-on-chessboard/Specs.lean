import Aegis.CountCombinations.Code.Funs

/-!
# Specifications of `Aegis.CountCombinations.count_combinations`

LeetCode problem `number-of-valid-move-combinations-on-chessboard`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountCombinations

def bytesNat (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def squareOf (p : alloc.vec.Vec Std.I64) : Option (Int × Int) :=
  match p.val.map (fun x => x.val) with
  | [r, c] => some (r, c)
  | _ => none

inductive PieceKind
  | rook
  | queen
  | bishop
  deriving DecidableEq, Repr

def PieceKind.asciiName : PieceKind → List Nat
  | .rook => [114, 111, 111, 107]
  | .queen => [113, 117, 101, 101, 110]
  | .bishop => [98, 105, 115, 104, 111, 112]

def pieceKindOf (v : alloc.vec.Vec Std.U8) : Option PieceKind :=
  if bytesNat v = PieceKind.asciiName .rook then some .rook
  else if bytesNat v = PieceKind.asciiName .queen then some .queen
  else if bytesNat v = PieceKind.asciiName .bishop then some .bishop
  else none

structure PieceView where
  kind : PieceKind
  start : Int × Int
  deriving DecidableEq, Repr

def pieceViewOf :
    List (alloc.vec.Vec Std.U8) → List (alloc.vec.Vec Std.I64) → Option (List PieceView)
  | [], [] => some []
  | v :: vs, w :: ws =>
      match pieceKindOf v, squareOf w with
      | some k, some s => (pieceViewOf vs ws).map (fun ps => ⟨k, s⟩ :: ps)
      | _, _ => none
  | _, _ => none

def pieceView (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) : Option (List PieceView) :=
  pieceViewOf pieces.val positions.val

def board : List (Int × Int) :=
  (List.range 8).flatMap (fun r => (List.range 8).map (fun c => ((r : Int) + 1, (c : Int) + 1)))

abbrev onBoard (d : Int × Int) : Prop := 1 ≤ d.1 ∧ d.1 ≤ 8 ∧ 1 ≤ d.2 ∧ d.2 ≤ 8

def reachB (k : PieceKind) (s d : Int × Int) : Bool :=
  match k with
  | .rook => (d.1 == s.1) || (d.2 == s.2)
  | .queen => (d.1 == s.1) || (d.2 == s.2) || ((d.1 - s.1).natAbs == (d.2 - s.2).natAbs)
  | .bishop => ((d.1 - s.1).natAbs == (d.2 - s.2).natAbs)

def moveB (k : PieceKind) (s d : Int × Int) : Bool :=
  decide (onBoard d) && reachB k s d

def moveSet (k : PieceKind) (s d : Int × Int) : Prop := moveB k s d = true

def moveList (k : PieceKind) (s : Int × Int) : List (Int × Int) :=
  board.filter (fun d => moveB k s d)

def moveCount (k : PieceKind) (s : Int × Int) : Nat := (moveList k s).length

def delta (s d : Int × Int) : Nat := max (d.1 - s.1).natAbs (d.2 - s.2).natAbs

def path (s d : Int × Int) (t : Int) : Int × Int :=
  if (delta s d : Int) ≤ t then d
  else
    ( s.1 + t * ((d.1 - s.1) / (delta s d : Int)),
      s.2 + t * ((d.2 - s.2) / (delta s d : Int)) )

def pathAt : List PieceView → List (Int × Int) → Int → List (Int × Int)
  | [], _, _ => []
  | _ :: _, [], _ => []
  | p :: ps, d :: ds, t => path p.start d t :: pathAt ps ds t

def allMovesB : List PieceView → List (Int × Int) → Bool
  | [], ds => ds.isEmpty
  | _ :: _, [] => false
  | p :: ps, d :: ds => moveB p.kind p.start d && allMovesB ps ds

def movesOK (ps : List PieceView) (ds : List (Int × Int)) : Prop := allMovesB ps ds = true

def choices : List PieceView → List (List (Int × Int))
  | [] => [[]]
  | p :: ps =>
      (moveList p.kind p.start).flatMap (fun d => (choices ps).map (fun ds => d :: ds))

def noCollision (ps : List PieceView) (ds : List (Int × Int)) (t : Int) : Prop :=
  (pathAt ps ds t).Nodup

def ValidCombo (ps : List PieceView) (ds : List (Int × Int)) : Prop :=
  movesOK ps ds ∧ ∀ t : Int, 0 ≤ t → noCollision ps ds t

def timesUpTo7 : List Int := [0, 1, 2, 3, 4, 5, 6, 7]

def ValidComboUpTo7 (ps : List PieceView) (ds : List (Int × Int)) : Prop :=
  movesOK ps ds ∧ ∀ t ∈ timesUpTo7, noCollision ps ds t

noncomputable def comboCount (ps : List PieceView) : Nat := by
  classical
  exact ((choices ps).filter (fun ds => ValidCombo ps ds)).length

noncomputable def comboCountUpTo7 (ps : List PieceView) : Nat := by
  classical
  exact ((choices ps).filter (fun ds => ValidComboUpTo7 ps ds)).length

def cardProduct (ps : List PieceView) : Nat :=
  (ps.map (fun p => moveCount p.kind p.start)).prod

def moveSetsDisjoint (ps : List PieceView) : Prop :=
  ∀ (i j : Nat) (hi : i < ps.length) (hj : j < ps.length), i ≠ j →
    ∀ d, moveSet (ps.get ⟨i, hi⟩).kind (ps.get ⟨i, hi⟩).start d →
      moveSet (ps.get ⟨j, hj⟩).kind (ps.get ⟨j, hj⟩).start d → False

inductive BoardMap
  | reflRows
  | reflCols
  | transpose
  deriving DecidableEq, Repr

def BoardMap.apply : BoardMap → Int × Int → Int × Int
  | .reflRows => fun d => (9 - d.1, d.2)
  | .reflCols => fun d => (d.1, 9 - d.2)
  | .transpose => fun d => (d.2, d.1)

def applyMaps : List BoardMap → Int × Int → Int × Int
  | [], d => d
  | g :: gs, d => applyMaps gs (g.apply d)

def queenCount (ps : List PieceView) : Nat :=
  (ps.filter (fun p => p.kind = PieceKind.queen)).length

def PreOn (ps : List PieceView) : Prop :=
  1 ≤ ps.length ∧ ps.length ≤ 4 ∧ (∀ p ∈ ps, onBoard p.start) ∧ queenCount ps ≤ 1 ∧
    (ps.map (fun p => p.start)).Nodup

/-- For each i, let s_i = (positions[i][0], positions[i][1]). Define the reachable set M_i subset of {1,...,8}^2 as follows: if pieces[i] is the ASCII byte sequence for "rook", M_i = { (r,c) in {1,...,8}^2 : r = s_i.0 or c = s_i.1 }; if pieces[i] is "queen", M_i = { (r,c) in {1,...,8}^2 : r = s_i.0 or c = s_i.1 or |r - s_i.0| = |c - s_i.1| }; if pieces[i] is "bishop", M_i = { (r,c) in {1,...,8}^2 : |r - s_i.0| = |c - s_i.1| }. A move combination is a tuple (d_0,...,d_{n-1}) with d_i in M_i for each i. For each i and integer t >= 0, define p_i(t) as follows. Let delta_i = max(|d_i.0 - s_i.0|, |d_i.1 - s_i.1|). If delta_i = 0, then p_i(t) = s_i for all t. If delta_i > 0, let u_i = ((d_i.0 - s_i.0)/delta_i, (d_i.1 - s_i.1)/delta_i); if t >= delta_i then p_i(t) = d_i, and if t < delta_i then p_i(t) = (s_i.0 + t * u_i.0, s_i.1 + t * u_i.1). Because d_i is in M_i, the non-zero entries of u_i are 0 or +/ -1 and the path is along an allowed rook/queen/bishop line. A move combination is valid iff for every integer t >= 0 and every pair i != j, p_i(t) != p_j(t). The function returns a result res and res is the number of valid move combinations. Pieces do not block one another; reachability is determined only by the geometric rule above.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_1 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (comboCount ps : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (comboCount ps : Int)) := by
  sorry

/-- The function returns a result (i.e., it does not fail, panic, or overflow).
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_2 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res) := by
  sorry

/-- The function returns a result res and res >= 1.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_3 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      1 ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      1 ≤ res.val) := by
  sorry

/-- The function returns a result res and res <= ∏_{i=0}^{n-1} |M_i|, where M_i is the set of squares reachable by piece i (as defined in spec_1), and |M_i| denotes its cardinality.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_4 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val ≤ (cardProduct ps : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val ≤ (cardProduct ps : Int)) := by
  sorry

/-- The function returns a result res and res = |M_0|, where M_0 is the set of squares reachable by the single piece (as defined in spec_1). In other words, every reachable destination is a valid move combination when there is only one piece.
  Preconditions: n = len(pieces) = len(positions) = 1; pieces[0] is the ASCII byte sequence for one of "rook", "queen", "bishop"; positions[0] is a vector of length 2 with positions[0][0] and positions[0][1] in {1,2,...,8}. -/
theorem spec_5 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p]) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (moveCount p.kind p.start : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p]), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (moveCount p.kind p.start : Int)) := by
  sorry

/-- The function returns a result res = 15.
  Preconditions: n = len(pieces) = len(positions) = 1; pieces[0] is the ASCII byte sequence for "rook"; positions[0] is a vector of length 2 with positions[0][0] and positions[0][1] in {1,2,...,8}. -/
theorem spec_6 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.rook) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 15 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.rook) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 15) := by
  sorry

/-- The function returns a result res = 15 + min(8-r, 8-c) + min(8-r, c-1) + min(r-1, 8-c) + min(r-1, c-1).
  Preconditions: n = len(pieces) = len(positions) = 1; pieces[0] is the ASCII byte sequence for "queen"; positions[0] = [r, c] with 1 <= r,c <= 8. -/
theorem spec_7 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.queen) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 15 + min (8 - r) (8 - c) + min (8 - r) (c - 1) + min (r - 1) (8 - c) +
        min (r - 1) (c - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.queen) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 15 + min (8 - r) (8 - c) + min (8 - r) (c - 1) + min (r - 1) (8 - c) +
        min (r - 1) (c - 1)) := by
  sorry

/-- The function returns a result res = 1 + min(8-r, 8-c) + min(8-r, c-1) + min(r-1, 8-c) + min(r-1, c-1).
  Preconditions: n = len(pieces) = len(positions) = 1; pieces[0] is the ASCII byte sequence for "bishop"; positions[0] = [r, c] with 1 <= r,c <= 8. -/
theorem spec_8 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.bishop) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 1 + min (8 - r) (8 - c) + min (8 - r) (c - 1) + min (r - 1) (8 - c) +
        min (r - 1) (c - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p : PieceView) (r c : Int)
    (hview : pieceView pieces positions = some [p]) (hpre : PreOn [p])
    (hk : p.kind = PieceKind.bishop) (hstart : p.start = (r, c))
    (hr : 1 ≤ r ∧ r ≤ 8) (hc : 1 ≤ c ∧ c ≤ 8), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 1 + min (8 - r) (8 - c) + min (8 - r) (c - 1) + min (r - 1) (8 - c) +
        min (r - 1) (c - 1)) := by
  sorry

/-- For any permutation π of {0,...,n-1}, let pieces' and positions' be defined by pieces'[i] = pieces[π(i)] and positions'[i] = positions[π(i)] for all i. The function returns a result res for (pieces, positions) and a result res' for (pieces', positions'), and res = res'.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_9 (pieces pieces' : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hview' : pieceView pieces' positions' = some ps') (hpre' : PreOn ps')
    (hperm : ps'.Perm ps) :
    ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces' positions' = ok res' ∧
          res.val = res'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (pieces pieces' : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hview' : pieceView pieces' positions' = some ps') (hpre' : PreOn ps')
    (hperm : ps'.Perm ps), ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces' positions' = ok res' ∧
          res.val = res'.val) := by
  sorry

/-- Let f be any symmetry of the 8x8 board, i.e., a composition of the reflections (r,c) -> (9-r,c) and (r,c) -> (r,9-c) and the transpose (r,c) -> (c,r). Let positions' be obtained from positions by applying f to each position: positions'[i] = [f(positions[i][0], positions[i][1])]. The function returns a result res for (pieces, positions) and a result res' for (pieces, positions'), and res = res'.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_10 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (f : List BoardMap)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hview' : pieceView pieces positions' = some ps')
    (hpos' : ps' = ps.map (fun p => ⟨p.kind, applyMaps f p.start⟩)) (hpre' : PreOn ps') :
    ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces positions' = ok res' ∧
          res.val = res'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (f : List BoardMap)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hview' : pieceView pieces positions' = some ps')
    (hpos' : ps' = ps.map (fun p => ⟨p.kind, applyMaps f p.start⟩)) (hpre' : PreOn ps'), ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces positions' = ok res' ∧
          res.val = res'.val) := by
  sorry

/-- The function returns a result res = ∏_{i=0}^{n-1} |M_i|.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. Additionally, for all i != j, M_i ∩ M_j = ∅, where M_i is the set of squares reachable by piece i (as defined in spec_1). -/
theorem spec_11 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hdisj : moveSetsDisjoint ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (cardProduct ps : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps)
    (hdisj : moveSetsDisjoint ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (cardProduct ps : Int)) := by
  sorry

/-- The function returns a result res' for (pieces', positions') and a result res for (pieces, positions), and res' = res * |M_new|.
  Preconditions: Let (pieces, positions) be any input satisfying the constraints with n pieces and n < 4. Let T be a piece type in {"rook", "queen", "bishop"} and P a position in [1,8]^2 such that: (a) if T = "queen", then no piece in pieces is "queen"; (b) P is distinct from all positions in positions; (c) the reachable set M_new of a piece of type T starting at P is disjoint from M_i for every i = 0..n-1, where M_i is the reachable set of piece i. Let pieces' = pieces concatenated with [T] and positions' = positions concatenated with [P]. -/
theorem spec_12 (pieces pieces' : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (p : PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) (hlen : ps.length < 4)
    (hview' : pieceView pieces' positions' = some ps') (hcat : ps' = ps ++ [p])
    (hpre' : PreOn ps')
    (hqueen : p.kind = PieceKind.queen → queenCount ps = 0)
    (hfresh : ∀ q ∈ ps, q.start ≠ p.start)
    (hdisj : ∀ q ∈ ps, ∀ d, moveSet p.kind p.start d → moveSet q.kind q.start d → False) :
    ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces' positions' = ok res' ∧
          res'.val = res.val * (moveCount p.kind p.start : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (pieces pieces' : Slice (alloc.vec.Vec Std.U8))
    (positions positions' : Slice (alloc.vec.Vec Std.I64)) (ps ps' : List PieceView)
    (p : PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) (hlen : ps.length < 4)
    (hview' : pieceView pieces' positions' = some ps') (hcat : ps' = ps ++ [p])
    (hpre' : PreOn ps')
    (hqueen : p.kind = PieceKind.queen → queenCount ps = 0)
    (hfresh : ∀ q ∈ ps, q.start ≠ p.start)
    (hdisj : ∀ q ∈ ps, ∀ d, moveSet p.kind p.start d → moveSet q.kind q.start d → False), ∃ res res' : Std.I64,
      Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
        Aegis.CountCombinations.count_combinations pieces' positions' = ok res' ∧
          res'.val = res.val * (moveCount p.kind p.start : Int)) := by
  sorry

/-- The function returns a result res and res <= 94500.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_13 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val ≤ 94500 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val ≤ 94500) := by
  sorry

/-- The function returns a result res and res equals the number of tuples (d_0,...,d_{n-1}) with d_i in M_i (as defined in spec_1) such that for every t in {0,1,...,7} and every i != j, p_i(t) != p_j(t), where p_i(t) is defined as in spec_1. It is sufficient to check t = 0,...,7 because every allowed destination is at distance at most 7 from the starting square, so after time 7 every piece has reached its destination and remains there.
  Preconditions: n = len(pieces) = len(positions); 1 <= n <= 4; for each i with 0 <= i < n, pieces[i] is the ASCII byte sequence for one of "rook", "queen", "bishop"; at most one pieces[i] is "queen"; positions[i] is a vector of length 2 with positions[i][0] and positions[i][1] in {1,2,...,8}; all positions[i] are pairwise distinct. -/
theorem spec_14 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (comboCountUpTo7 ps : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (ps : List PieceView)
    (hview : pieceView pieces positions = some ps) (hpre : PreOn ps), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = (comboCountUpTo7 ps : Int)) := by
  sorry

/-- The function returns a result res and res = 309.
  Preconditions: n = len(pieces) = len(positions) = 2; pieces[0] is the ASCII byte sequence for "queen"; pieces[1] is the ASCII byte sequence for "rook"; positions[0] = [1,1]; positions[1] = [2,2]. -/
theorem spec_15 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p q : PieceView)
    (hview : pieceView pieces positions = some [p, q]) (hpre : PreOn [p, q])
    (hpk : p.kind = PieceKind.queen) (hps : p.start = (1, 1))
    (hqk : q.kind = PieceKind.rook) (hqs : q.start = (2, 2)) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 309 := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p q : PieceView)
    (hview : pieceView pieces positions = some [p, q]) (hpre : PreOn [p, q])
    (hpk : p.kind = PieceKind.queen) (hps : p.start = (1, 1))
    (hqk : q.kind = PieceKind.rook) (hqs : q.start = (2, 2)), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 309) := by
  sorry

/-- The function returns a result res and res = 223.
  Preconditions: n = len(pieces) = len(positions) = 2; pieces[0] is the ASCII byte sequence for "rook"; pieces[1] is the ASCII byte sequence for "rook"; positions[0] = [1,1]; positions[1] = [8,8]. -/
theorem spec_16 (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p q : PieceView)
    (hview : pieceView pieces positions = some [p, q]) (hpre : PreOn [p, q])
    (hpk : p.kind = PieceKind.rook) (hps : p.start = (1, 1))
    (hqk : q.kind = PieceKind.rook) (hqs : q.start = (8, 8)) :
    ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 223 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (pieces : Slice (alloc.vec.Vec Std.U8))
    (positions : Slice (alloc.vec.Vec Std.I64)) (p q : PieceView)
    (hview : pieceView pieces positions = some [p, q]) (hpre : PreOn [p, q])
    (hpk : p.kind = PieceKind.rook) (hps : p.start = (1, 1))
    (hqk : q.kind = PieceKind.rook) (hqs : q.start = (8, 8)), ∃ res : Std.I64, Aegis.CountCombinations.count_combinations pieces positions = ok res ∧
      res.val = 223) := by
  sorry

end AegisSpec.CountCombinations
