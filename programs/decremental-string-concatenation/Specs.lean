import Aegis.MinimizeConcatenatedLength.Code.Funs

/-!
# Specifications of `Aegis.MinimizeConcatenatedLength.minimize_concatenated_length`

LeetCode problem `decremental-string-concatenation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimizeConcatenatedLength

  namespace AegisSpec.MinimizeConcatenatedLength

  abbrev Words := Slice (alloc.vec.Vec U8)

  def numWords (ws : Words) : ℕ := ws.val.length

  def wordAt (ws : Words) (i : ℕ) : Option (alloc.vec.Vec U8) := ws.val[i]?

  def byteOf (w : alloc.vec.Vec U8) (j : ℕ) : Option U8 := w.val[j]?

  def wordLen (w : alloc.vec.Vec U8) : ℕ := w.val.length

  def wordLenAt (ws : Words) (i : ℕ) : ℕ := (wordAt ws i).map wordLen |>.getD 0

  def firstByte (w : alloc.vec.Vec U8) : Option U8 := w.val.head?

  def lastByte (w : alloc.vec.Vec U8) : Option U8 := w.val.getLast?

  def firstByteAt (ws : Words) (i : ℕ) : Option U8 := (wordAt ws i).bind firstByte

  def lastByteAt (ws : Words) (i : ℕ) : Option U8 := (wordAt ws i).bind lastByte

  def byteAt (ws : Words) (i j : ℕ) : Option U8 := (wordAt ws i).bind fun w => byteOf w j

  def IsLowercaseByte (b : U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def totalLen (ws : Words) : ℤ := (ws.val.map (fun w => (w.val.length : ℤ))).sum

  def ValidWords (ws : Words) : Prop :=
    1 ≤ ws.val.length ∧ ws.val.length ≤ 1000 ∧
      ∀ w ∈ ws.val, 1 ≤ w.val.length ∧ w.val.length ≤ 50 ∧
        ∀ b ∈ w.val, IsLowercaseByte b

  def appendMatches (ws : Words) : ℕ :=
    ((List.range ws.val.length).filter (fun i =>
        decide (1 ≤ i) && decide (lastByteAt ws (i - 1) = firstByteAt ws i))).length

  def prependMatches (ws : Words) : ℕ :=
    ((List.range ws.val.length).filter (fun i =>
        decide (1 ≤ i) && decide (lastByteAt ws i = firstByteAt ws (i - 1)))).length

  structure ConcatState where

    first : Option U8

    last : Option U8

    len : ℤ

  def appendReduction (l : Option U8) (w : alloc.vec.Vec U8) : ℤ :=
    match l, firstByte w with
    | some x, some y => if x = y then 1 else 0
    | _, _ => 0

  def prependReduction (f : Option U8) (w : alloc.vec.Vec U8) : ℤ :=
    match lastByte w, f with
    | some y, some x => if x = y then 1 else 0
    | _, _ => 0

  def stepAppend (st : ConcatState) (w : alloc.vec.Vec U8) : ConcatState :=
    { first := st.first
      last := lastByte w
      len := st.len + (w.val.length : ℤ) - appendReduction st.last w }

  def stepPrepend (st : ConcatState) (w : alloc.vec.Vec U8) : ConcatState :=
    { first := firstByte w
      last := st.last
      len := st.len + (w.val.length : ℤ) - prependReduction st.first w }

  def dpStep (isAppend : Bool) (st : ConcatState) (w : alloc.vec.Vec U8) : ConcatState :=
    if isAppend then stepAppend st w else stepPrepend st w

  def runChoices (cs : List Bool) (ws : List (alloc.vec.Vec U8)) (st : ConcatState) : ConcatState :=
    match cs, ws with
    | [], _ => st
    | _ :: _, [] => st
    | c :: cs', w :: ws' => runChoices cs' ws' (dpStep c st w)

  def initState (ws : Words) : ConcatState :=
    match ws.val with
    | [] => { first := none, last := none, len := 0 }
    | w :: _ => { first := firstByte w, last := lastByte w, len := (w.val.length : ℤ) }

  def strategyLengths (ws : Words) : Set ℤ :=
    { L | ∃ cs : List Bool, cs.length = ws.val.length - 1 ∧
        (runChoices cs ws.val.tail (initState ws)).len = L }

  /-- Let n = len(words). For each i with 0 <= i < n, let L_i = len(words[i]), A_i = words[i][0], B_i = words[i][L_i - 1]. A strategy is a sequence of choices c_1, c_2, ..., c_{n-1} where each c_k is either `append` or `prepend`. For a strategy, define f_0 = A_0, l_0 = B_0, and len_0 = L_0. For k = 1 to n-1: if c_k = `append`, then reduction_k = 1 if l_{k-1} == A_k else 0, f_k = f_{k-1}, l_k = B_k, len_k = len_{k-1} + L_k - reduction_k; if c_k = `prepend`, then reduction_k = 1 if B_k == f_{k-1} else 0, f_k = A_k, l_k = l_{k-1}, len_k = len_{k-1} + L_k - reduction_k. The function returns a result r such that r = min { len_{n-1} | c is a strategy }. (If n = 1, the minimum is L_0.)
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter (ASCII code 97..122). -/
  theorem spec_1 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        IsLeast (strategyLengths words) (r.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          IsLeast (strategyLengths words) (r.val : ℤ)) := by
    sorry

  /-- The function returns a result r and sum_{i=0}^{n-1} len(words[i]) - (n - 1) <= r <= sum_{i=0}^{n-1} len(words[i]), where n = len(words).
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter (ASCII code 97..122). -/
  theorem spec_2 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        totalLen words - ((numWords words : ℤ) - 1) ≤ (r.val : ℤ) ∧
        (r.val : ℤ) ≤ totalLen words := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          totalLen words - ((numWords words : ℤ) - 1) ≤ (r.val : ℤ) ∧
          (r.val : ℤ) ≤ totalLen words) := by
    sorry

  /-- Let r1 be the result of the function on words1, and r2 be the result on words2. Then r1 = r2 (and both are results, i.e., neither fails).
    Preconditions: words1 and words2 are two slices of vectors of bytes, each satisfying the constraints of S1 (i.e., 1 <= len <= 1000, word lengths 1..50, English lowercase). They have the same length n = len(words1) = len(words2). For every i with 0 <= i < n, len(words1[i]) = len(words2[i]), words1[i][0] = words2[i][0], and words1[i][len(words1[i])-1] = words2[i][len(words2[i])-1]. -/
  theorem spec_3 (words1 words2 : Words) (h1 : ValidWords words1) (h2 : ValidWords words2)
      (hlen : numWords words1 = numWords words2)
      (hdata : ∀ i : ℕ, i < numWords words1 →
        wordLenAt words2 i = wordLenAt words1 i ∧
        firstByteAt words2 i = firstByteAt words1 i ∧
        lastByteAt words2 i = lastByteAt words1 i) :
      ∃ r1 r2 : I64, minimize_concatenated_length words1 = ok r1 ∧
        minimize_concatenated_length words2 = ok r2 ∧ r1 = r2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (words1 words2 : Words) (h1 : ValidWords words1) (h2 : ValidWords words2)
        (hlen : numWords words1 = numWords words2)
        (hdata : ∀ i : ℕ, i < numWords words1 →
          wordLenAt words2 i = wordLenAt words1 i ∧
          firstByteAt words2 i = firstByteAt words1 i ∧
          lastByteAt words2 i = lastByteAt words1 i), ∃ r1 r2 : I64, minimize_concatenated_length words1 = ok r1 ∧
          minimize_concatenated_length words2 = ok r2 ∧ r1 = r2) := by
    sorry

  /-- Let r be the result on words and r' be the result on words'. Then r' = r + d.
    Preconditions: words and words' are two slices of vectors of bytes satisfying the constraints of spec_1. They have the same length n. There exists an index i (0 <= i < n) such that for all j != i, words'[j] = words[j]. For the index i, words'[i] has length len(words[i]) + d for some integer d >= 0, and words'[i][0] = words[i][0], words'[i][len(words'[i])-1] = words[i][len(words[i])-1]. -/
  theorem spec_4 (words words' : Words) (d : ℕ) (hw : ValidWords words) (hw' : ValidWords words')
      (hlen : numWords words' = numWords words)
      (hdiff : ∃ i : ℕ, i < numWords words ∧
        wordLenAt words' i = wordLenAt words i + d ∧
        firstByteAt words' i = firstByteAt words i ∧
        lastByteAt words' i = lastByteAt words i ∧
        ∀ j : ℕ, j < numWords words → j ≠ i → wordAt words' j = wordAt words j) :
      ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
        minimize_concatenated_length words' = ok r' ∧
        (r'.val : ℤ) = (r.val : ℤ) + (d : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (words words' : Words) (d : ℕ) (hw : ValidWords words) (hw' : ValidWords words')
        (hlen : numWords words' = numWords words)
        (hdiff : ∃ i : ℕ, i < numWords words ∧
          wordLenAt words' i = wordLenAt words i + d ∧
          firstByteAt words' i = firstByteAt words i ∧
          lastByteAt words' i = lastByteAt words i ∧
          ∀ j : ℕ, j < numWords words → j ≠ i → wordAt words' j = wordAt words j), ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
          minimize_concatenated_length words' = ok r' ∧
          (r'.val : ℤ) = (r.val : ℤ) + (d : ℤ)) := by
    sorry

  /-- Let K_append = the number of indices i with 1 <= i < n such that words[i-1][len(words[i-1])-1] == words[i][0], where n = len(words). Then the function returns a result r and r <= sum_{i=0}^{n-1} len(words[i]) - K_append.
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter. -/
  theorem spec_5 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        (r.val : ℤ) ≤ totalLen words - (appendMatches words : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          (r.val : ℤ) ≤ totalLen words - (appendMatches words : ℤ)) := by
    sorry

  /-- Let K_prepend = the number of indices i with 1 <= i < n such that words[i][len(words[i])-1] == words[i-1][0], where n = len(words). Then the function returns a result r and r <= sum_{i=0}^{n-1} len(words[i]) - K_prepend.
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter. -/
  theorem spec_6 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        (r.val : ℤ) ≤ totalLen words - (prependMatches words : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          (r.val : ℤ) ≤ totalLen words - (prependMatches words : ℤ)) := by
    sorry

  /-- The function returns a result (i.e., it does not return an error or panic) for every input satisfying the preconditions.
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter. -/
  theorem spec_7 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r) := by
    sorry

  /-- Let n = len(words) and S = sum_{i=0}^{n-1} len(words[i]), and let r be the result of the function. Then r = S if and only if for all pairs (i, j) with 0 <= i < j < n, it is not the case that words[i][len(words[i])-1] == words[j][0] and it is not the case that words[j][len(words[j])-1] == words[i][0]. Equivalently, r < S if and only if there exist i < j such that words[i][len(words[i])-1] == words[j][0] or words[j][len(words[j])-1] == words[i][0].
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter (ASCII code 97..122). -/
  theorem spec_8 (words : Words) (hw : ValidWords words) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        ((r.val : ℤ) = totalLen words ↔
          ∀ i j : ℕ, i < j → j < numWords words →
            lastByteAt words i ≠ firstByteAt words j ∧
            lastByteAt words j ≠ firstByteAt words i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          ((r.val : ℤ) = totalLen words ↔
            ∀ i j : ℕ, i < j → j < numWords words →
              lastByteAt words i ≠ firstByteAt words j ∧
              lastByteAt words j ≠ firstByteAt words i)) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{n-1} len(words[i]) - (n - 1), where n = len(words).
    Preconditions: words is a slice of vectors of bytes such that 1 <= len(words) <= 1000. For every i with 0 <= i < len(words), 1 <= len(words[i]) <= 50, and every byte in words[i] is an English lowercase letter (ASCII code 97..122). There exists a byte c such that for every i with 0 <= i < len(words), words[i][0] = c and words[i][len(words[i])-1] = c. -/
  theorem spec_9 (words : Words) (hw : ValidWords words)
      (hc : ∃ c : U8, ∀ i : ℕ, i < numWords words →
        firstByteAt words i = some c ∧ lastByteAt words i = some c) :
      ∃ r : I64, minimize_concatenated_length words = ok r ∧
        (r.val : ℤ) = totalLen words - ((numWords words : ℤ) - 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (words : Words) (hw : ValidWords words)
        (hc : ∃ c : U8, ∀ i : ℕ, i < numWords words →
          firstByteAt words i = some c ∧ lastByteAt words i = some c), ∃ r : I64, minimize_concatenated_length words = ok r ∧
          (r.val : ℤ) = totalLen words - ((numWords words : ℤ) - 1)) := by
    sorry

  /-- Let r be the result of the function on words, and r' the result on words'. Then r' = r + len(w) - 1 or r' = r + len(w).
    Preconditions: words satisfies the constraints of spec_1. Let n = len(words). Assume n <= 999. w is a vector of bytes with 1 <= len(w) <= 50 and all bytes are English lowercase letters. Let words' be the concatenation of words and w (so words' has length n+1, with words'[i] = words[i] for 0 <= i < n, and words'[n] = w). -/
  theorem spec_10 (words words' : Words) (w : alloc.vec.Vec U8)
      (hw : ValidWords words) (hn : numWords words ≤ 999)
      (hw1 : 1 ≤ wordLen w) (hw2 : wordLen w ≤ 50)
      (hw3 : ∀ b ∈ w.val, IsLowercaseByte b)
      (hcat : words'.val = words.val ++ [w]) :
      ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
        minimize_concatenated_length words' = ok r' ∧
        ((r'.val : ℤ) = (r.val : ℤ) + (wordLen w : ℤ) - 1 ∨
         (r'.val : ℤ) = (r.val : ℤ) + (wordLen w : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (words words' : Words) (w : alloc.vec.Vec U8)
        (hw : ValidWords words) (hn : numWords words ≤ 999)
        (hw1 : 1 ≤ wordLen w) (hw2 : wordLen w ≤ 50)
        (hw3 : ∀ b ∈ w.val, IsLowercaseByte b)
        (hcat : words'.val = words.val ++ [w]), ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
          minimize_concatenated_length words' = ok r' ∧
          ((r'.val : ℤ) = (r.val : ℤ) + (wordLen w : ℤ) - 1 ∨
           (r'.val : ℤ) = (r.val : ℤ) + (wordLen w : ℤ))) := by
    sorry

  /-- Let r be the result on words and r' the result on words'. Then r = r'.
    Preconditions: words satisfies the constraints of spec_1. Let n = len(words). Define words' by reversing each word: for each i with 0 <= i < n, words'[i] has the same length as words[i], and words'[i][j] = words[i][len(words[i])-1-j] for all 0 <= j < len(words[i]). -/
  theorem spec_11 (words words' : Words) (hw : ValidWords words)
      (hlen : numWords words' = numWords words)
      (hrev : ∀ i : ℕ, i < numWords words →
        wordLenAt words' i = wordLenAt words i ∧
        ∀ j : ℕ, j < wordLenAt words i →
          byteAt words' i j = byteAt words i (wordLenAt words i - 1 - j)) :
      ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
        minimize_concatenated_length words' = ok r' ∧ r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (words words' : Words) (hw : ValidWords words)
        (hlen : numWords words' = numWords words)
        (hrev : ∀ i : ℕ, i < numWords words →
          wordLenAt words' i = wordLenAt words i ∧
          ∀ j : ℕ, j < wordLenAt words i →
            byteAt words' i j = byteAt words i (wordLenAt words i - 1 - j)), ∃ r r' : I64, minimize_concatenated_length words = ok r ∧
          minimize_concatenated_length words' = ok r' ∧ r = r') := by
    sorry

  end AegisSpec.MinimizeConcatenatedLength
