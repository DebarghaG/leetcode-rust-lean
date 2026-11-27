import Aegis.CanWin.Code.Funs

/-!
# Specifications of `Aegis.CanWin.can_win`

LeetCode problem `flip-game-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CanWin

namespace AegisSpec.CanWin

abbrev plusByte : Std.U8 := 43#u8

abbrev minusByte : Std.U8 := 45#u8

def IsPlusAt (l : List Std.U8) (i : Nat) : Prop := l[i]? = some plusByte

def AdjacentPlus (l : List Std.U8) (i : Nat) : Prop := IsPlusAt l i ∧ IsPlusAt l (i + 1)

def IsPlusOrMinus (b : Std.U8) : Prop := b.val = 43 ∨ b.val = 45

def plusCount (l : List Std.U8) : Nat := l.countP (fun b => decide (b = plusByte))

def replacePair (l : List Std.U8) (i : Nat) : List Std.U8 :=
  l.take i ++ minusByte :: minusByte :: l.drop (i + 2)

theorem plusCount_append (a b : List Std.U8) :
    plusCount (a ++ b) = plusCount a + plusCount b := by
  simp [plusCount, List.countP_append]

theorem plusCount_cons_minus (r : List Std.U8) :
    plusCount (minusByte :: r) = plusCount r := by
  simp [plusCount, minusByte, plusByte, List.countP_cons_of_neg]

theorem plusCount_cons_plus (r : List Std.U8) :
    plusCount (plusByte :: r) = plusCount r + 1 := by
  simp [plusCount, plusByte, List.countP_cons_of_pos]

theorem length_replacePair_of_lt (l : List Std.U8) (i : Nat) (h : i + 1 < l.length) :
    (replacePair l i).length = l.length := by
  have hi : i ≤ l.length := by omega
  simp only [replacePair, List.length_append, List.length_cons, List.length_take,
    List.length_drop, Nat.min_eq_left hi]
  omega

theorem plusCount_replacePair_lt (l : List Std.U8) (i : Nat)
    (h1 : l[i]? = some plusByte) (h2 : l[i + 1]? = some plusByte) :
    plusCount (replacePair l i) < plusCount l := by
  obtain ⟨hlt1, hget1⟩ := List.getElem?_eq_some_iff.mp h1
  obtain ⟨hlt2, hget2⟩ := List.getElem?_eq_some_iff.mp h2

  have hgcd1 : plusByte :: l.drop (i + 1) = l.drop i := by
    simpa [hget1] using List.getElem_cons_drop (i := i) hlt1
  have hstep1 : l.take i ++ plusByte :: l.drop (i + 1) = l := by
    rw [hgcd1]; exact List.take_append_drop i l

  have hd0 : (l.drop (i + 1))[0]? = some plusByte := by
    rw [List.getElem?_drop]; simpa using h2
  obtain ⟨hlt0, hget0⟩ := List.getElem?_eq_some_iff.mp hd0
  have hgcd0 : (l.drop (i + 1))[0] :: List.drop 1 (l.drop (i + 1)) = l.drop (i + 1) :=
    List.getElem_cons_drop (i := 0) hlt0
  have hdrop1 : l.drop (i + 1) = plusByte :: l.drop (i + 2) := by
    rw [← hgcd0, hget0]
    simp [List.drop_drop]

  have hl : l = l.take i ++ plusByte :: plusByte :: l.drop (i + 2) := by
    conv_lhs => rw [← hstep1]
    rw [hdrop1]
  have hleft : plusCount (replacePair l i) = plusCount (l.take i) + plusCount (l.drop (i + 2)) := by
    simp [replacePair, plusCount, minusByte, plusByte, List.countP_append,
      List.countP_cons_of_neg]
  have hright :
      plusCount l = plusCount (l.take i) + plusCount (l.drop (i + 2)) + 2 := by
    conv_lhs => rw [hl]
    simp [plusCount, plusByte, List.countP_append, List.countP_cons_of_pos]
    omega
  omega

def Win (l : List Std.U8) : Prop :=
  ∃ (i : Nat) (h : AdjacentPlus l i), ¬ Win (replacePair l i)
termination_by plusCount l
decreasing_by
  obtain ⟨h1, h2⟩ := h
  exact plusCount_replacePair_lt l i h1 h2

theorem Win.unfold (l : List Std.U8) :
    Win l ↔ ∃ i, AdjacentPlus l i ∧ ¬ Win (replacePair l i) := by
  rw [Win.eq_def]
  constructor
  · rintro ⟨i, h, hnot⟩
    exact ⟨i, h, hnot⟩
  · rintro ⟨i, h, hnot⟩
    exact ⟨i, h, hnot⟩

def mkSlice (l : List Std.U8) (h : l.length ≤ Aeneas.Std.Usize.max) : Slice Std.U8 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

@[simp]
theorem mkSlice_val (l : List Std.U8) (h : l.length ≤ Aeneas.Std.Usize.max) :
    (mkSlice l h).val = l := by
  simp [mkSlice, Slice.val, Aeneas.Data.ListN.ListN.from_to_inverse]

@[simp]
theorem slice_length_val (s : Slice Std.U8) : s.val.length = s.leng := by
  obtain ⟨leng, list, bound⟩ := s
  simp [Slice.val, Aeneas.Data.ListN.ListN_length]

theorem sixty_le_usize_max : 60 ≤ Aeneas.Std.Usize.max := by
  have h : Aeneas.Std.Usize.max = 2 ^ System.Platform.numBits - 1 := by
    simp [Aeneas.Std.Usize.max, Aeneas.Std.Usize.numBits]
  rw [h]
  rcases System.Platform.numBits_eq with h' | h' <;> rw [h'] <;> norm_num

def replacePairSlice (s : Slice Std.U8) (i : Nat) : Slice Std.U8 :=
  if h : i + 1 < s.val.length then
    mkSlice (replacePair s.val i) (by
      rw [length_replacePair_of_lt _ _ h, slice_length_val]
      exact s.bound)
  else s

theorem replacePairSlice_val (s : Slice Std.U8) (i : Nat) (h : AdjacentPlus s.val i) :
    (replacePairSlice s i).val = replacePair s.val i := by
  have hlt : i + 1 < s.leng := by
    obtain ⟨h1, h2⟩ := h
    have := (List.getElem?_eq_some_iff.mp h2).1
    simpa [slice_length_val] using this
  simp [replacePairSlice, hlt]

def prependMinus (s : Slice Std.U8) (h : s.val.length ≤ 59) : Slice Std.U8 :=
  mkSlice (minusByte :: s.val) (by
    have hU : 60 ≤ Aeneas.Std.Usize.max := sixty_le_usize_max
    simp only [List.length_cons]
    omega)

@[simp]
theorem prependMinus_val (s : Slice Std.U8) (h : s.val.length ≤ 59) :
    (prependMinus s h).val = minusByte :: s.val := by
  simp [prependMinus]

@[simp]
theorem prependMinus_length (s : Slice Std.U8) (h : s.val.length ≤ 59) :
    (prependMinus s h).val.length = s.val.length + 1 := by
  simp [prependMinus]

/-- Let a position be any byte slice of length between 1 and 60 whose bytes are all 43 or 45. Define the predicate Win(p) on positions by well-founded recursion on the number of '+' bytes in p: Win(p) is true if and only if there exists an index i with 0 <= i < len(p)-1 such that p[i] = p[i+1] = 43, and letting p' be the position obtained from p by replacing p[i] and p[i+1] with 45, we have Win(p') = false. (If no such i exists, Win(p) is false.) Whenever can_win(currentState) returns a result r, r is true if and only if Win(currentState) is true.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_1 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    ∀ r, can_win currentState = ok r → (r = true ↔ Win currentState.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), ∀ r, can_win currentState = ok r → (r = true ↔ Win currentState.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function can_win returns a result (it does not panic, overflow, or go out of bounds).
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_2 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    ∃ r, can_win currentState = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), ∃ r, can_win currentState = ok r) := by
  sorry

/-- If there is no index i with 0 <= i < len(currentState)-1 such that currentState[i] = currentState[i+1] = 43, then whenever can_win(currentState) returns a result r, r = false.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_3 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b)
    (h_none : ∀ i, ¬ AdjacentPlus currentState.val i) :
    ∀ r, can_win currentState = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b)
    (h_none : ∀ i, ¬ AdjacentPlus currentState.val i), ∀ r, can_win currentState = ok r → r = false) := by
  sorry

/-- Whenever can_win(currentState) returns true, there exists an index i with 0 <= i < len(currentState)-1 such that currentState[i] = currentState[i+1] = 43, and if p' is the slice obtained from currentState by replacing positions i and i+1 with 45, then can_win(p') returns false.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_4 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    can_win currentState = ok true →
      ∃ i, AdjacentPlus currentState.val i ∧ can_win (replacePairSlice currentState i) = ok false := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), can_win currentState = ok true →
      ∃ i, AdjacentPlus currentState.val i ∧ can_win (replacePairSlice currentState i) = ok false) := by
  sorry

/-- Whenever can_win(currentState) returns false, for every index i with 0 <= i < len(currentState)-1 such that currentState[i] = currentState[i+1] = 43, if p' is the slice obtained from currentState by replacing positions i and i+1 with 45, then can_win(p') returns true.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_5 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    can_win currentState = ok false →
      ∀ i, AdjacentPlus currentState.val i → can_win (replacePairSlice currentState i) = ok true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), can_win currentState = ok false →
      ∀ i, AdjacentPlus currentState.val i → can_win (replacePairSlice currentState i) = ok true) := by
  sorry

/-- If there exists an index i with 0 <= i < len(currentState)-1 such that currentState[i] = currentState[i+1] = 43, and if p' is the slice obtained from currentState by replacing positions i and i+1 with 45, and can_win(p') returns false, then can_win(currentState) returns true.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_6 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    (∃ i, AdjacentPlus currentState.val i ∧
        can_win (replacePairSlice currentState i) = ok false) →
      can_win currentState = ok true := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), (∃ i, AdjacentPlus currentState.val i ∧
        can_win (replacePairSlice currentState i) = ok false) →
      can_win currentState = ok true) := by
  sorry

/-- If for every index i with 0 <= i < len(currentState)-1 such that currentState[i] = currentState[i+1] = 43, letting p' be the slice obtained from currentState by replacing positions i and i+1 with 45, we have that can_win(p') returns true, then can_win(currentState) returns false.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_7 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b) :
    (∀ i, AdjacentPlus currentState.val i →
        can_win (replacePairSlice currentState i) = ok true) →
      can_win currentState = ok false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b), (∀ i, AdjacentPlus currentState.val i →
        can_win (replacePairSlice currentState i) = ok true) →
      can_win currentState = ok false) := by
  sorry

/-- Whenever both can_win(s) and can_win(s') return results, those results are equal.
  Preconditions: Let s be any byte slice of length between 1 and 59 inclusive, with every byte being 43 or 45. Let s' be the slice of length len(s)+1 obtained by prepending the byte 45 to s. -/
theorem spec_8 (s : Slice Std.U8)
    (h_len_pos : 1 ≤ s.val.length)
    (h_len_le : s.val.length ≤ 59)
    (h_bytes : ∀ b ∈ s.val, IsPlusOrMinus b) :
    ∀ r r', can_win s = ok r → can_win (prependMinus s h_len_le) = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (h_len_pos : 1 ≤ s.val.length)
    (h_len_le : s.val.length ≤ 59)
    (h_bytes : ∀ b ∈ s.val, IsPlusOrMinus b), ∀ r r', can_win s = ok r → can_win (prependMinus s h_len_le) = ok r' → r = r') := by
  sorry

/-- Let s_rev be the slice of the same length as currentState such that s_rev[i] = currentState[len(currentState)-1-i] for all i. Whenever can_win(currentState) and can_win(s_rev) return results, those results are equal.
  Preconditions: The slice currentState has length between 1 and 60 inclusive. Every byte is either 43 (the ASCII code for '+') or 45 (the ASCII code for '-'). -/
theorem spec_9 (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b)
    (s_rev : Slice Std.U8)
    (h_rev_len : s_rev.val.length = currentState.val.length)
    (h_rev : ∀ i, i < s_rev.val.length →
      s_rev.val[i]? = currentState.val[currentState.val.length - 1 - i]?) :
    ∀ r r', can_win currentState = ok r → can_win s_rev = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (currentState : Slice Std.U8)
    (h_len_pos : 1 ≤ currentState.val.length)
    (h_len_le : currentState.val.length ≤ 60)
    (h_bytes : ∀ b ∈ currentState.val, IsPlusOrMinus b)
    (s_rev : Slice Std.U8)
    (h_rev_len : s_rev.val.length = currentState.val.length)
    (h_rev : ∀ i, i < s_rev.val.length →
      s_rev.val[i]? = currentState.val[currentState.val.length - 1 - i]?), ∀ r r', can_win currentState = ok r → can_win s_rev = ok r' → r = r') := by
  sorry

end AegisSpec.CanWin
