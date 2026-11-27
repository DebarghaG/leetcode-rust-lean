import Aegis.IsPathCrossing.Code.Funs

/-!
# Specifications of `Aegis.IsPathCrossing.is_path_crossing`

LeetCode problem `path-crossing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsPathCrossing

  def byteN : Nat := 78

  def byteS : Nat := 83

  def byteE : Nat := 69

  def byteW : Nat := 87

  def IsDirByte (c : U8) : Prop :=
    c.val = byteN ∨ c.val = byteS ∨ c.val = byteE ∨ c.val = byteW

  def AllDirBytes (l : List U8) : Prop := ∀ c ∈ l, IsDirByte c

  def countByte (l : List U8) (b : Nat) (t : Nat) : Nat :=
    ((l.take t).filter (fun c => c.val = b)).length

  def posX (l : List U8) (t : Nat) : Int :=
    (countByte l byteE t : Int) - (countByte l byteW t : Int)

  def posY (l : List U8) (t : Nat) : Int :=
    (countByte l byteN t : Int) - (countByte l byteS t : Int)

  def pos (l : List U8) (t : Nat) : Int × Int := (posX l t, posY l t)

  def positions (l : List U8) : List (Int × Int) := (List.range (l.length + 1)).map (pos l)

  def PairwiseDistinctPositions (l : List U8) : Prop := (positions l).Nodup

  def Opposite (a b : U8) : Prop :=
    (a.val = byteN ∧ b.val = byteS) ∨ (a.val = byteS ∧ b.val = byteN) ∨
      (a.val = byteE ∧ b.val = byteW) ∨ (a.val = byteW ∧ b.val = byteE)

  def HasOppositeAdjacent (l : List U8) : Prop :=
    ∃ i : Nat,
      i + 1 < l.length ∧ ∃ a b : U8, l[i]? = some a ∧ l[i + 1]? = some b ∧ Opposite a b

  def IsReverseOf (l' l : List U8) : Prop := l' = l.reverse

  def flipNS (c : U8) : U8 :=
    if c.val = byteN then 83#u8 else if c.val = byteS then 78#u8 else c

  def IsNSMirrorOf (l' l : List U8) : Prop := l' = l.map flipNS

  theorem val_length_le (s : Slice U8) : s.val.length ≤ Usize.max := by
    have h : s.val.length = s.leng := by
      simpa [Slice.val] using Aeneas.Data.ListN.ListN_length s.list
    rw [h]
    exact s.bound

  def mkSlice (l : List U8) (h : l.length ≤ Usize.max) : Slice U8 :=
    { leng := l.length, list := Aeneas.Data.ListN.ListN.fromList l, bound := h }

  def reverseSlice (s : Slice U8) : Slice U8 :=
    mkSlice s.val.reverse (by rw [List.length_reverse]; exact val_length_le s)

  def mirrorSlice (s : Slice U8) : Slice U8 :=
    mkSlice (s.val.map flipNS) (by rw [List.length_map]; exact val_length_le s)

  theorem reverseSlice_val (s : Slice U8) : (reverseSlice s).val = s.val.reverse := by
    simp [reverseSlice, mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  theorem mirrorSlice_val (s : Slice U8) : (mirrorSlice s).val = s.val.map flipNS := by
    simp [mirrorSlice, mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

  theorem reverseSlice_isReverseOf (s : Slice U8) :
      IsReverseOf (reverseSlice s).val s.val :=
    reverseSlice_val s

  theorem mirrorSlice_isNSMirrorOf (s : Slice U8) :
      IsNSMirrorOf (mirrorSlice s).val s.val :=
    mirrorSlice_val s

  /-- Let P(0)=(0,0). For 1 <= t <= n let P(t)=(X(t),Y(t)), where X(t) is the number of indices i with 0 <= i < t and path[i]='E' minus the number of indices i with 0 <= i < t and path[i]='W', and Y(t) is the number of indices i with 0 <= i < t and path[i]='N' minus the number of indices i with 0 <= i < t and path[i]='S'. Whenever the function returns a result r, r=true if and only if there exist integers k,l with 0 <= k < l <= n and P(k)=P(l); equivalently r=false if and only if the n+1 positions P(0),...,P(n) are pairwise distinct.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_1 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r) :
      (r = true ↔
          ∃ k l : Nat, k < l ∧ l ≤ path.val.length ∧ pos path.val k = pos path.val l) ∧
        (r = false ↔ PairwiseDistinctPositions path.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r), (r = true ↔
            ∃ k l : Nat, k < l ∧ l ≤ path.val.length ∧ pos path.val k = pos path.val l) ∧
          (r = false ↔ PairwiseDistinctPositions path.val)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every path satisfying the preconditions; in particular, there is no out-of-bounds access to path and no 64-bit integer overflow during the computation.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_2 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) :
      ∃ r : Bool, Aegis.IsPathCrossing.is_path_crossing path = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val), ∃ r : Bool, Aegis.IsPathCrossing.is_path_crossing path = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index i with 0 <= i < n-1 such that path[i] and path[i+1] are opposite directions, then r is true.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_3 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
      (hwit : HasOppositeAdjacent path.val) : r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
        (hwit : HasOppositeAdjacent path.val), r = true) := by
    sorry

  /-- Let P(t) be the position after t moves, as defined by the prefix displacement counts from spec_1. Whenever the function returns a result r, if there exists an integer t with 1 <= t <= n such that P(t)=(0,0), then r is true.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_4 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
      (hwit : ∃ t : Nat, 1 ≤ t ∧ t ≤ path.val.length ∧ pos path.val t = (0, 0)) :
      r = true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
        (hwit : ∃ t : Nat, 1 ≤ t ∧ t ≤ path.val.length ∧ pos path.val t = (0, 0)), r = true) := by
    sorry

  /-- Let P(t) be the position after t moves, as defined by the prefix displacement counts from spec_1. Whenever the function returns a result r and r=true, there exists an integer l with 1 <= l <= n such that (a) P(l)=P(k) for some integer k with 0 <= k < l, and (b) for every integer t with 1 <= t < l, P(t) is not equal to P(j) for any integer j with 0 <= j < t. Thus l is the first time at which a previously visited location is reached.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_5 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r) (hrtrue : r = true) :
      ∃ l : Nat,
        1 ≤ l ∧ l ≤ path.val.length ∧
          (∃ k : Nat, k < l ∧ pos path.val k = pos path.val l) ∧
            (∀ t : Nat, 1 ≤ t → t < l → ∀ j : Nat, j < t →
              pos path.val t ≠ pos path.val j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r) (hrtrue : r = true), ∃ l : Nat,
          1 ≤ l ∧ l ≤ path.val.length ∧
            (∃ k : Nat, k < l ∧ pos path.val k = pos path.val l) ∧
              (∀ t : Nat, 1 ≤ t → t < l → ∀ j : Nat, j < t →
                pos path.val t ≠ pos path.val j)) := by
    sorry

  /-- Let rev(path) be the byte sequence of length n with rev(path)[i]=path[n-1-i] for 0 <= i < n. For every path satisfying the preconditions, whenever is_path_crossing(path) returns a result r and is_path_crossing(rev(path)) returns a result r', we have r=r'.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_6 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r r' : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
      (hr' : Aegis.IsPathCrossing.is_path_crossing (reverseSlice path) = ok r') :
      r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r r' : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
        (hr' : Aegis.IsPathCrossing.is_path_crossing (reverseSlice path) = ok r'), r = r') := by
    sorry

  /-- Let mirror(path) be obtained from path by replacing every byte 'N' with 'S' and every byte 'S' with 'N', leaving 'E' and 'W' unchanged. For every path satisfying the preconditions, whenever is_path_crossing(path) returns a result r and is_path_crossing(mirror(path)) returns a result r', we have r=r'.
    Preconditions: Let n = len(path). Assume 1 <= n <= 10000 and for every i with 0 <= i < n, path[i] is one of the ASCII bytes for 'N', 'S', 'E', 'W'. -/
  theorem spec_7 (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
      (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r r' : Bool)
      (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
      (hr' : Aegis.IsPathCrossing.is_path_crossing (mirrorSlice path) = ok r') :
      r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (path : Slice U8) (hlen_pos : 1 ≤ path.val.length)
        (hlen_ub : path.val.length ≤ 10000) (hdir : AllDirBytes path.val) (r r' : Bool)
        (hr : Aegis.IsPathCrossing.is_path_crossing path = ok r)
        (hr' : Aegis.IsPathCrossing.is_path_crossing (mirrorSlice path) = ok r'), r = r') := by
    sorry

  end AegisSpec.IsPathCrossing
