import Aegis.FullJustify.Code.Funs

/-!
# Specifications of `Aegis.FullJustify.full_justify`

LeetCode problem `text-justification`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FullJustify

def spaceByte : Nat := 32

def vecBytes (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def inputWords (words : Slice (alloc.vec.Vec Std.U8)) : List (List Nat) :=
  words.val.map vecBytes

def outputLines (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Nat) :=
  r.val.map vecBytes

def spaces (k : Nat) : List Nat := List.replicate k spaceByte

def delSpaces (l : List Nat) : List Nat := l.filter (fun b => b ≠ spaceByte)

def numSpaces (l : List Nat) : Nat := (l.filter (fun b => b = spaceByte)).length

def cat (b : List (List Nat)) : List Nat := b.flatten

def sumLen (b : List (List Nat)) : Nat := (b.map List.length).sum

def minWidth (b : List (List Nat)) : Nat := sumLen b + (b.length - 1)

def widthNat (maxWidth : Std.I64) : Nat := maxWidth.val.toNat

def gapBudget (maxWidth : Std.I64) (S : Nat) : Nat := (maxWidth.val - (S : Int)).toNat

def justifiedGap (maxWidth : Std.I64) (S k d : Nat) : Nat :=
  let G := gapBudget maxWidth S
  if d < G % (k - 1) then G / (k - 1) + 1 else G / (k - 1)

def blk (ws : List (List Nat)) (p : Nat → Nat) (t : Nat) : List (List Nat) :=
  (ws.drop (p t)).take (p (t + 1) - p t)

def wordAt (ws : List (List Nat)) (j : Nat) : List Nat := (ws[j]?).getD []

def wordLenAt (ws : List (List Nat)) (j : Nat) : Nat := (ws[j]?).map List.length |>.getD 0

def insertGaps : List (List Nat) → (Nat → Nat) → List Nat
  | [], _ => []
  | [w], _ => w
  | w :: w' :: rest, g => w ++ spaces (g 0) ++ insertGaps (w' :: rest) (fun d => g (d + 1))

def buildLine (b : List (List Nat)) (g : Nat → Nat) (h : Nat) : List Nat :=
  insertGaps b g ++ spaces h

def CutFrom (ws : List (List Nat)) (lines : List (List Nat)) (p : Nat → Nat) : Prop :=
  p 0 = 0 ∧ p lines.length = ws.length ∧
    (∀ t, t < lines.length → p t < p (t + 1)) ∧
    (∀ t, t < lines.length → (lines[t]?).map delSpaces = some (cat (blk ws p t)))

def EveryLine (lines : List (List Nat)) (P : List Nat → Prop) : Prop :=
  ∀ i, i < lines.length → ∀ line, lines[i]? = some line → P line

def WordsOK (ws : List (List Nat)) : Prop :=
  1 ≤ ws.length ∧ ws.length ≤ 300 ∧
    ∀ w ∈ ws, 1 ≤ w.length ∧ w.length ≤ 100 ∧ ∀ b ∈ w, b ≠ spaceByte

def WidthOK (maxWidth : Std.I64) : Prop := 1 ≤ maxWidth.val ∧ maxWidth.val ≤ 100

def LineOK (ws : List (List Nat)) (maxWidth : Std.I64) (lines : List (List Nat))
    (p : Nat → Nat) (g : Nat → Nat → Nat) (h : Nat → Nat) (t : Nat) : Prop :=
  let k := p (t + 1) - p t
  let S := sumLen (blk ws p t)

  lines[t]? = some (buildLine (blk ws p t) (g t) (h t)) ∧

    (∀ d, d < k - 1 → 1 ≤ g t d) ∧

    (t < lines.length - 1 → 2 ≤ k →
      S + (k - 1) ≤ widthNat maxWidth ∧ h t = 0 ∧
        ∀ d, d < k - 1 → g t d = justifiedGap maxWidth S k d) ∧

    ((t = lines.length - 1 ∨ k = 1) →
      (∀ d, d < k - 1 → g t d = 1) ∧ h t = widthNat maxWidth - (S + (k - 1))) ∧

    (2 ≤ k → S + (k - 1) ≤ widthNat maxWidth) ∧

    (t < lines.length - 1 →
      widthNat maxWidth < S + (k - 1) + 1 + wordLenAt ws (p (t + 1)))

/-- Let n = len(words). The function returns a result r and there exist an integer m >= 1 and indices 0 = p_0 < p_1 < ... < p_m = n such that len(r) = m and for every t with 0 <= t < m, writing k = p_{t+1} - p_t and S = sum_{j=p_t}^{p_{t+1}-1} len(words[j]), the following hold. (a) r[t] is exactly the byte array obtained from words[p_t], words[p_t+1], ..., words[p_{t+1}-1] by inserting g_d >= 1 space bytes (byte 32) between words[p_t+d] and words[p_t+d+1] for each d with 0 <= d < k-1, and then h >= 0 trailing space bytes after the last word, with no other bytes. (b) If t < m-1 and k >= 2, then S + (k-1) <= maxWidth, G = maxWidth - S, q = floor(G/(k-1)), rem = G mod (k-1), g_d = q+1 for 0 <= d < rem, g_d = q for rem <= d < k-1, and h = 0. (c) If t = m-1 or k = 1, then g_d = 1 for every d with 0 <= d < k-1, and h = max(0, maxWidth - (S + (k-1))). (d) For every t with k >= 2, S + (k-1) <= maxWidth. (e) If t < m-1, then S + (k-1) + 1 + len(words[p_{t+1}]) > maxWidth.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_1 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∃ r, Aegis.FullJustify.full_justify words maxWidth = ok r ∧
      ∃ (p : Nat → Nat) (g : Nat → Nat → Nat) (h : Nat → Nat),
        1 ≤ (outputLines r).length ∧
          CutFrom (inputWords words) (outputLines r) p ∧
          ∀ t, t < (outputLines r).length →
            LineOK (inputWords words) maxWidth (outputLines r) p g h t := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∃ r, Aegis.FullJustify.full_justify words maxWidth = ok r ∧
      ∃ (p : Nat → Nat) (g : Nat → Nat → Nat) (h : Nat → Nat),
        1 ≤ (outputLines r).length ∧
          CutFrom (inputWords words) (outputLines r) p ∧
          ∀ t, t < (outputLines r).length →
            LineOK (inputWords words) maxWidth (outputLines r) p g h t) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, overflow, or out-of-bounds) on any input satisfying the preconditions.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_2 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∃ r, Aegis.FullJustify.full_justify words maxWidth = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∃ r, Aegis.FullJustify.full_justify words maxWidth = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1 and for every i with 0 <= i < len(r), len(r[i]) >= 1 (there is at least one line and no empty line).
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_3 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      1 ≤ (outputLines r).length ∧
        EveryLine (outputLines r) (fun line => 0 < line.length) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      1 ≤ (outputLines r).length ∧
        EveryLine (outputLines r) (fun line => 0 < line.length)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), let k_i be the number of input words that form line r[i] (the contiguous block from which r[i] is constructed). If k_i = 1 and the single word has length greater than maxWidth, then len(r[i]) equals that word's length; in every other case (including k_i >= 2, or k_i = 1 with word length <= maxWidth), len(r[i]) = maxWidth.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_4 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ i, i < lines.length → ∀ line, lines[i]? = some line →
          let k := p (i + 1) - p i
          let w := wordAt ws (p i)
          ((k = 1 ∧ widthNat maxWidth < w.length) → line.length = w.length) ∧
            (¬(k = 1 ∧ widthNat maxWidth < w.length) → line.length = widthNat maxWidth) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ i, i < lines.length → ∀ line, lines[i]? = some line →
          let k := p (i + 1) - p i
          let w := wordAt ws (p i)
          ((k = 1 ∧ widthNat maxWidth < w.length) → line.length = w.length) ∧
            (¬(k = 1 ∧ widthNat maxWidth < w.length) → line.length = widthNat maxWidth)) := by
  sorry

/-- Whenever the function returns a result r, if from each line r[i] all space bytes (32) are deleted and the resulting byte arrays are concatenated in increasing line order, the resulting byte array equals the concatenation words[0] ++ words[1] ++ ... ++ words[n-1].
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_5 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      ((outputLines r).map delSpaces).flatten = (inputWords words).flatten := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      ((outputLines r).map delSpaces).flatten = (inputWords words).flatten) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), r[i][0] is not the space byte 32; that is, no output line begins with a space.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_6 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      EveryLine (outputLines r)
        (fun line => 0 < line.length ∧ line[0]? ≠ some spaceByte) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      EveryLine (outputLines r)
        (fun line => 0 < line.length ∧ line[0]? ≠ some spaceByte)) := by
  sorry

/-- Whenever the function returns a result r, let t = len(r)-1 be the last line. If the last line is formed from k >= 2 input words, then between each pair of consecutive words on that line there is exactly one space byte, and any additional space bytes occur only as a trailing suffix after the last word; equivalently, no two words on the last line are separated by more than one space.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_7 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        2 ≤ p lines.length - p (lines.length - 1) →
          ∃ h, lines[lines.length - 1]? =
            some (buildLine (blk ws p (lines.length - 1)) (fun _ => 1) h) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        2 ≤ p lines.length - p (lines.length - 1) →
          ∃ h, lines[lines.length - 1]? =
            some (buildLine (blk ws p (lines.length - 1)) (fun _ => 1) h)) := by
  sorry

/-- Whenever the function returns a result r, for every non-last line t with t < len(r)-1 that is formed from k >= 2 input words, let S be the sum of the lengths of those k words and let G = maxWidth - S. Then G >= k-1, and if the k-1 gaps between consecutive words are listed from left to right, the first (G mod (k-1)) gaps contain floor(G/(k-1))+1 space bytes and the remaining gaps contain floor(G/(k-1)) space bytes; there are no trailing spaces on this line.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_8 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length - 1 →
          let k := p (t + 1) - p t
          let S := sumLen (blk ws p t)
          2 ≤ k →
            k - 1 ≤ gapBudget maxWidth S ∧
              lines[t]? = some (buildLine (blk ws p t) (justifiedGap maxWidth S k) 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length - 1 →
          let k := p (t + 1) - p t
          let S := sumLen (blk ws p t)
          2 ≤ k →
            k - 1 ≤ gapBudget maxWidth S ∧
              lines[t]? = some (buildLine (blk ws p t) (justifiedGap maxWidth S k) 0)) := by
  sorry

/-- Whenever the function returns a result r, for every line t that is formed from exactly one input word w (whether or not it is the last line), r[t] is w followed by exactly max(0, maxWidth - len(w)) space bytes and then ends; there are no other bytes. Consequently, if len(w) <= maxWidth then len(r[t]) = maxWidth, and if len(w) > maxWidth then r[t] = w.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_9 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length → p (t + 1) - p t = 1 →
          let w := wordAt ws (p t)
          ∀ line, lines[t]? = some line →
            line = w ++ spaces (widthNat maxWidth - w.length) ∧
              (w.length ≤ widthNat maxWidth → line.length = widthNat maxWidth) ∧
                (widthNat maxWidth < w.length → line = w) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length → p (t + 1) - p t = 1 →
          let w := wordAt ws (p t)
          ∀ line, lines[t]? = some line →
            line = w ++ spaces (widthNat maxWidth - w.length) ∧
              (w.length ≤ widthNat maxWidth → line.length = widthNat maxWidth) ∧
                (widthNat maxWidth < w.length → line = w)) := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < len(r)-1, let B_t be the contiguous nonempty block of input words forming line t, and let j be the index of the first word of line t+1 (so words[j] immediately follows the last word of B_t). Then (sum of lengths of words in B_t) + (|B_t| - 1) + 1 + len(words[j]) > maxWidth. That is, adding the next word to line t with one separating space would exceed maxWidth even before any extra justification spaces.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_10 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length - 1 →
          widthNat maxWidth < minWidth (blk ws p t) + 1 + wordLenAt ws (p (t + 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length - 1 →
          widthNat maxWidth < minWidth (blk ws p t) + 1 + wordLenAt ws (p (t + 1))) := by
  sorry

/-- Whenever the function returns a result r, for every line t formed from k >= 2 input words, the sum of the lengths of those k words plus (k-1) is at most maxWidth. Equivalently, every multiword line could fit with exactly one space between adjacent words.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_11 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length → 2 ≤ p (t + 1) - p t →
          minWidth (blk ws p t) ≤ widthNat maxWidth := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ p, CutFrom ws lines p →
        ∀ t, t < lines.length → 2 ≤ p (t + 1) - p t →
          minWidth (blk ws p t) ≤ widthNat maxWidth) := by
  sorry

/-- Whenever the function returns a result r, every byte of every line r[i] is either the space byte 32 or one of the bytes of the input words; moreover, the subsequence of non-space bytes of r[i] is exactly the concatenation of the input words that form that line, in their original order and without modification.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_12 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∃ p, CutFrom ws lines p ∧
        EveryLine lines
          (fun line => ∀ b ∈ line, b = spaceByte ∨ ∃ w ∈ ws, b ∈ w) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∃ p, CutFrom ws lines p ∧
        EveryLine lines
          (fun line => ∀ b ∈ line, b = spaceByte ∨ ∃ w ∈ ws, b ∈ w)) := by
  sorry

/-- Whenever the function returns a result r, let L = len(r). For every integer M with 1 <= M < L and every strictly increasing sequence 0 = q_0 < q_1 < ... < q_M = n, there exists s with 0 <= s < M such that (sum_{j=q_s}^{q_{s+1}-1} len(words[j])) + (q_{s+1}-q_s-1) > maxWidth. Equivalently, no partition of the words into fewer than L consecutive nonempty lines can have every line's minimum width (word lengths plus one space per gap) at most maxWidth.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). Additionally, for every i with 0 <= i < n, len(words[i]) <= maxWidth. -/
theorem spec_13 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth)
    (hsmall : ∀ w ∈ inputWords words, w.length ≤ widthNat maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ (M : Nat) (q : Nat → Nat), 1 ≤ M → M < lines.length → q 0 = 0 → q M = ws.length →
        (∀ s, s < M → q s < q (s + 1)) →
          ∃ s, s < M ∧ widthNat maxWidth < minWidth (blk ws q s) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth)
    (hsmall : ∀ w ∈ inputWords words, w.length ≤ widthNat maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∀ (M : Nat) (q : Nat → Nat), 1 ≤ M → M < lines.length → q 0 = 0 → q M = ws.length →
        (∀ s, s < M → q s < q (s + 1)) →
          ∃ s, s < M ∧ widthNat maxWidth < minWidth (blk ws q s)) := by
  sorry

/-- Whenever the function returns a result r, let B_0, ..., B_{L-1} be the contiguous blocks of input words that form the lines of r in order, where L = len(r). Then B_0 starts with words[0]; for every t with 0 <= t < L-1, B_{t+1} starts with the word immediately after the last word of B_t; B_{L-1} ends with words[n-1]; and every B_t is nonempty. Thus the lines partition words into consecutive nonempty blocks covering every input word exactly once in order.
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). -/
theorem spec_14 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∃ p, p 0 = 0 ∧ p lines.length = ws.length ∧
        (∀ t, t < lines.length → p t < p (t + 1)) ∧
        (∀ t, t < lines.length → (lines[t]?).map delSpaces = some (cat (blk ws p t))) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      ∃ p, p 0 = 0 ∧ p lines.length = ws.length ∧
        (∀ t, t < lines.length → p t < p (t + 1)) ∧
        (∀ t, t < lines.length → (lines[t]?).map delSpaces = some (cat (blk ws p t)))) := by
  sorry

/-- Whenever the function returns a result r, under the additional guarantee that every input word has length at most maxWidth, the total number of space bytes (byte 32) in all lines of r is exactly len(r) * maxWidth - sum_{i=0}^{n-1} len(words[i]).
  Preconditions: Let n = len(words). 1 <= n <= 300; 1 <= maxWidth <= 100; for every i with 0 <= i < n, 1 <= len(words[i]) <= 100 and every byte of words[i] is an ASCII non-space byte (not 32). Additionally, for every i with 0 <= i < n, len(words[i]) <= maxWidth. -/
theorem spec_15 (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth)
    (hsmall : ∀ w ∈ inputWords words, w.length ≤ widthNat maxWidth) :
    ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      (lines.map numSpaces).sum = lines.length * widthNat maxWidth - sumLen ws := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (words : Slice (alloc.vec.Vec Std.U8)) (maxWidth : Std.I64)
    (hwords : WordsOK (inputWords words)) (hwidth : WidthOK maxWidth)
    (hsmall : ∀ w ∈ inputWords words, w.length ≤ widthNat maxWidth), ∀ r, Aegis.FullJustify.full_justify words maxWidth = ok r →
      let ws := inputWords words
      let lines := outputLines r
      (lines.map numSpaces).sum = lines.length * widthNat maxWidth - sumLen ws) := by
  sorry

end AegisSpec.FullJustify
