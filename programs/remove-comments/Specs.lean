import Aegis.RemoveComments.Code.Funs

/-!
# Specifications of `Aegis.RemoveComments.remove_comments`

LeetCode problem `remove-comments`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.RemoveComments

open Aegis.RemoveComments

def nlByte : U8 := 10#u8

def slashByte : U8 := 47#u8

def starByte : U8 := 42#u8

def isNl (b : U8) : Bool := b.val == 10

def isSlash (b : U8) : Bool := b.val == 47

def isStar (b : U8) : Bool := b.val == 42

def rows (source : Slice (alloc.vec.Vec U8)) : List (List U8) :=
  source.val.map (fun v => v.val)

def outRows (r : alloc.vec.Vec (alloc.vec.Vec U8)) : List (List U8) :=
  r.val.map (fun v => v.val)

def joinRows : List (List U8) → List U8
  | [] => []
  | [r] => r
  | r :: r' :: rs => r ++ nlByte :: joinRows (r' :: rs)

def SOf (source : Slice (alloc.vec.Vec U8)) : List U8 := joinRows (rows source)

def byteAt (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Option U8 := (SOf source)[p]?

inductive ScanState where
  | normal
  | line
  | block
  deriving DecidableEq, Repr

structure CopyEntry where
  pos : Nat
  byte : U8
  inNormal : Bool

structure ScanTrace where
  copies : List CopyEntry
  visited : List (Nat × ScanState)
  final : ScanState

def scanFuel (S : List U8) : Nat → Nat → ScanState → ScanTrace → ScanTrace
  | 0, _, st, acc => { acc with final := st }
  | fuel + 1, k, st, acc =>
    if k < S.length then
      let acc' : ScanTrace := { acc with visited := acc.visited ++ [(k, st)] }
      match st with
      | .normal =>
        match S[k]?, S[k + 1]? with
        | some a, some b =>
          if isSlash a && isSlash b then
            scanFuel S fuel (k + 2) .line acc'
          else if isSlash a && isStar b then
            scanFuel S fuel (k + 2) .block acc'
          else
            scanFuel S fuel (k + 1) .normal
              { acc' with copies := acc'.copies ++ [⟨k, a, true⟩] }
        | some a, none =>
          scanFuel S fuel (k + 1) .normal { acc' with copies := acc'.copies ++ [⟨k, a, true⟩] }
        | none, _ => { acc' with final := .normal }
      | .line =>
        match S[k]? with
        | some a =>
          if isNl a then
            scanFuel S fuel (k + 1) .normal
              { acc' with copies := acc'.copies ++ [⟨k, a, false⟩] }
          else scanFuel S fuel (k + 1) .line acc'
        | none => { acc' with final := .line }
      | .block =>
        match S[k]?, S[k + 1]? with
        | some a, some b =>
          if isStar a && isSlash b then scanFuel S fuel (k + 2) .normal acc'
          else scanFuel S fuel (k + 1) .block acc'
        | _, _ => scanFuel S fuel (k + 1) .block acc'
    else { acc with final := st }

def trace (source : Slice (alloc.vec.Vec U8)) : ScanTrace :=
  scanFuel (SOf source) ((SOf source).length + 1) 0 .normal
    { copies := [], visited := [], final := .normal }

def outC (source : Slice (alloc.vec.Vec U8)) : List U8 :=
  (trace source).copies.map (fun e => e.byte)

def finalState (source : Slice (alloc.vec.Vec U8)) : ScanState := (trace source).final

def scannedAt (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Option ScanState :=
  (trace source).visited.lookup p

def copiedPositions (source : Slice (alloc.vec.Vec U8)) : List Nat :=
  (trace source).copies.map (fun e => e.pos)

def CopiedAt (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Prop := p ∈ copiedPositions source

def splitOnGo {α : Type} (p : α → Bool) : List α → List α → List (List α) → List (List α)
  | [], cur, segs => cur.reverse :: segs
  | x :: rest, cur, segs =>
    if p x then splitOnGo p rest [] (cur.reverse :: segs)
    else splitOnGo p rest (x :: cur) segs

def splitOnP {α : Type} (p : α → Bool) (l : List α) : List (List α) :=
  (splitOnGo p l [] []).reverse

def splitLines (C : List U8) : List (List U8) :=
  (splitOnP isNl C).filter (fun s => !s.isEmpty)

def entryLines (source : Slice (alloc.vec.Vec U8)) : List (List CopyEntry) :=
  (splitOnP (fun e : CopyEntry => isNl e.byte) (trace source).copies).filter
    (fun s => !s.isEmpty)

def refLines (source : Slice (alloc.vec.Vec U8)) : List (List U8) := splitLines (outC source)

def lineIndexOfPosAux (p : Nat) : Nat → List (List CopyEntry) → Option Nat
  | _, [] => none
  | i, seg :: rest => if seg.any (fun e => e.pos == p) then some i
    else lineIndexOfPosAux p (i + 1) rest

def lineIndexOfPos (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Option Nat :=
  lineIndexOfPosAux p 0 (entryLines source)

def posToRowColAux (p : Nat) : List (List U8) → Nat → Nat → Option (Nat × Nat)
  | [], _, _ => none
  | r :: rs, k, off =>
    if p < off + r.length then some (k, p - off)
    else posToRowColAux p rs (k + 1) (off + r.length + 1)

def posToRowCol (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Option (Nat × Nat) :=
  posToRowColAux p (rows source) 0 0

def OpensBlockAt (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Prop :=
  scannedAt source p = some .normal ∧ byteAt source p = some slashByte ∧
    byteAt source (p + 1) = some starByte

def OpensLineAt (source : Slice (alloc.vec.Vec U8)) (p : Nat) : Prop :=
  scannedAt source p = some .normal ∧ byteAt source p = some slashByte ∧
    byteAt source (p + 1) = some slashByte

def IsBlockClose (source : Slice (alloc.vec.Vec U8)) (p q : Nat) : Prop :=
  p + 2 ≤ q ∧ byteAt source q = some starByte ∧ byteAt source (q + 1) = some slashByte ∧
    ∀ r, p + 2 ≤ r → r < q →
      ¬ (byteAt source r = some starByte ∧ byteAt source (r + 1) = some slashByte)

def LineCommentEnd (source : Slice (alloc.vec.Vec U8)) (p q : Nat) : Prop :=
  (p + 1 < q ∧ byteAt source q = some nlByte ∧
      ∀ r, p + 1 < r → r < q → byteAt source r ≠ some nlByte) ∨
    (q = (SOf source).length ∧ ∀ r, p + 1 < r → r < q → byteAt source r ≠ some nlByte)

def ConsecutiveCopies (source : Slice (alloc.vec.Vec U8)) (a b : Nat) : Prop :=
  ∃ (ea eb : CopyEntry) (pre suf : List CopyEntry),
    (trace source).copies = pre ++ ea :: eb :: suf ∧ ea.pos = a ∧ eb.pos = b

def NoInnerNewline (source : Slice (alloc.vec.Vec U8)) : Prop :=
  ∀ (k : Nat) (rowk : List U8), (rows source)[k]? = some rowk → ∀ b ∈ rowk, b.val ≠ 10

def PreSource (source : Slice (alloc.vec.Vec U8)) : Prop :=
  1 ≤ (rows source).length ∧ (rows source).length ≤ 100 ∧
    (∀ row ∈ rows source, row.length ≤ 80) ∧ finalState source ≠ ScanState.block

def PreSourceStrict (source : Slice (alloc.vec.Vec U8)) : Prop :=
  PreSource source ∧ NoInnerNewline source

/-- Let S be the byte string obtained by concatenating source[0], a newline byte, source[1], a newline byte, ..., a newline byte, source[len(source)-1]. Scan S from left to right starting in state NORMAL and building a byte string C initially empty. In NORMAL: if the next two bytes are '/' '/' then consume them and switch to LINE; otherwise if the next two bytes are '/' '*' then consume them and switch to BLOCK; otherwise append the next byte to C and advance one byte. In LINE: if the next byte is a newline then append it to C, advance, and switch to NORMAL; otherwise consume the next byte without appending. In BLOCK: if the next two bytes are '*' '/' then consume them and switch to NORMAL; otherwise consume the next byte without appending (including a newline byte). A two-byte test fails if fewer than two bytes remain. The scan stops when all of S is consumed (it never stops in BLOCK by the precondition). Let r be the list of byte strings obtained by splitting C at every newline byte and then deleting all empty byte strings, preserving order. The function returns r.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_1 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec U8),
      remove_comments source = ok r ∧ outRows r = refLines source := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∃ r : alloc.vec.Vec (alloc.vec.Vec U8),
      remove_comments source = ok r ∧ outRows r = refLines source) := by
  sorry

/-- The function returns a result r and does not fail (no panic, overflow, or out-of-bounds access).
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_2 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∃ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r) := by
  sorry

/-- Let r be the result of remove_comments(source). Then for every i with 0 <= i < len(r), len(r[i]) >= 1.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_3 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, 1 ≤ line.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, 1 ≤ line.val.length) := by
  sorry

/-- Let r be the result of remove_comments(source). Then len(r) <= len(source).
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_4 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      r.val.length ≤ (rows source).length := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      r.val.length ≤ (rows source).length) := by
  sorry

/-- Let r be the result of remove_comments(source). Then sum_{i=0}^{len(r)-1} len(r[i]) <= sum_{i=0}^{len(source)-1} len(source[i]).
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_5 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      (r.val.map (fun line => line.val.length)).sum ≤
        (source.val.map (fun v => v.val.length)).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      (r.val.map (fun line => line.val.length)).sum ≤
        (source.val.map (fun v => v.val.length)).sum) := by
  sorry

/-- Let r be the result of remove_comments(source). Then len(r) <= the number of indices i with 0 <= i < len(source) and len(source[i]) > 0.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_6 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      r.val.length ≤ ((rows source).filter (fun row => !row.isEmpty)).length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      r.val.length ≤ ((rows source).filter (fun row => !row.isEmpty)).length) := by
  sorry

/-- Let r be the result of remove_comments(source). For every i with 0 <= i < len(r), there is no j with 0 <= j < len(r[i]) - 1 such that r[i][j] = '/' and r[i][j+1] = '/'.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_7 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j + 1 < line.val.length →
        ¬ (line.val[j]? = some slashByte ∧ line.val[(j + 1)]? = some slashByte) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j + 1 < line.val.length →
        ¬ (line.val[j]? = some slashByte ∧ line.val[(j + 1)]? = some slashByte)) := by
  sorry

/-- Let r be the result of remove_comments(source). For every i with 0 <= i < len(r), there is no j with 0 <= j < len(r[i]) - 1 such that r[i][j] = '/' and r[i][j+1] = '*'.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_8 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j + 1 < line.val.length →
        ¬ (line.val[j]? = some slashByte ∧ line.val[(j + 1)]? = some starByte) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j + 1 < line.val.length →
        ¬ (line.val[j]? = some slashByte ∧ line.val[(j + 1)]? = some starByte)) := by
  sorry

/-- Let r be the result of remove_comments(source). Then remove_comments(r) returns r.
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_9 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∃ r' : alloc.vec.Vec (alloc.vec.Vec U8),
        remove_comments r.slice = ok r' ∧ r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∃ r' : alloc.vec.Vec (alloc.vec.Vec U8),
        remove_comments r.slice = ok r' ∧ r'.val = r.val) := by
  sorry

/-- Let r be the result of remove_comments(source). For every i with 0 <= i < len(r) and every j with 0 <= j < len(r[i]), r[i][j] != 10 (the newline byte).
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_10 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j < line.val.length → line.val[j]? ≠ some nlByte := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      ∀ line ∈ r.val, ∀ j : Nat, j < line.val.length → line.val[j]? ≠ some nlByte) := by
  sorry

/-- Let S be the byte string obtained by concatenating source[0], a newline byte, source[1], ..., a newline byte, source[len(source)-1], and let r be the result of remove_comments(source). If the scan of S never enters LINE or BLOCK, then r is exactly the list [source[i] | 0 <= i < len(source) and len(source[i]) > 0].
  Preconditions: 1 <= len(source) <= 100; for every i with 0 <= i < len(source), len(source[i]) <= 80; every block comment opened during the scan of source is eventually closed (equivalently, the scan never ends in the block-comment state). -/
theorem spec_11 (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      (∀ (p : Nat) (s : ScanState), scannedAt source p = some s → s = ScanState.normal) →
        outRows r = (rows source).filter (fun row => !row.isEmpty) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (source : Slice (alloc.vec.Vec U8)) (hpre : PreSource source), ∀ r : alloc.vec.Vec (alloc.vec.Vec U8), remove_comments source = ok r →
      (∀ (p : Nat) (s : ScanState), scannedAt source p = some s → s = ScanState.normal) →
        outRows r = (rows source).filter (fun row => !row.isEmpty)) := by
  sorry

end AegisSpec.RemoveComments
