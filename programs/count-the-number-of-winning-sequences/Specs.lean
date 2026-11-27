import Aegis.CountWinningSequences.Code.Funs

/-!
# Specifications of `Aegis.CountWinningSequences.count_winning_sequences`

LeetCode problem `count-the-number-of-winning-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountWinningSequences

abbrev U8Slice := Aeneas.Std.Slice Aeneas.Std.U8

def isSymbol (c : Nat) : Prop := c = 70 ∨ c = 87 ∨ c = 69

def beats (x y : Nat) : Prop :=
  (x = 87 ∧ y = 70) ∨ (x = 69 ∧ y = 87) ∨ (x = 70 ∧ y = 69)

def rotCode (c : Nat) : Nat := if c = 70 then 87 else if c = 87 then 69 else 70

def counterCode (c : Nat) : Nat := if c = 70 then 87 else if c = 87 then 69 else 70

def rotByte (c : Aeneas.Std.U8) : Aeneas.Std.U8 :=
  if c.val = 70 then 87#u8 else if c.val = 87 then 69#u8 else 70#u8

def rotSlice (s : U8Slice) : U8Slice :=
  Aeneas.Std.Slice.mk (s.val.map rotByte).length
    (Aeneas.Data.ListN.ListN.fromList (s.val.map rotByte))
    (by
      have h := Aeneas.Data.ListN.ListN_length s.list
      have hb := s.bound
      simp only [Aeneas.Std.Slice.val, List.length_map] at *
      omega)

def revSlice (s : U8Slice) : U8Slice :=
  Aeneas.Std.Slice.mk s.val.reverse.length (Aeneas.Data.ListN.ListN.fromList s.val.reverse)
    (by
      have h := Aeneas.Data.ListN.ListN_length s.list
      have hb := s.bound
      simp only [Aeneas.Std.Slice.val, List.length_reverse] at *
      omega)

def codes (s : U8Slice) : List Nat := s.val.map (fun c => c.val)

noncomputable def bobScore (b sL : List Nat) : Nat := by
  classical
  exact (b.zipWith (fun x y => if beats x y then 1 else 0) sL).sum

def codeOf (i : Fin 3) : Nat := if i.val = 0 then 70 else if i.val = 1 then 87 else 69

noncomputable def N (s : U8Slice) : Nat := by
  classical
  exact
    ((Finset.univ : Finset (Fin (codes s).length → Fin 3)).filter (fun b =>
        (∀ (i : Nat) (h : i + 1 < (codes s).length),
            b ⟨i, Nat.lt_of_succ_lt h⟩ ≠ b ⟨i + 1, h⟩) ∧
          bobScore (List.ofFn fun i => codeOf (b i)) (codes s) >
            bobScore (codes s) (List.ofFn fun i => codeOf (b i)))).card

def counterSeq (sL : List Nat) : List Nat := sL.map counterCode

/-- The function returns a result r (it does not fail), and r is the unique integer with 0 <= r < 1000000007 that is congruent modulo 1000000007 to the number N of sequences b of length n over the symbols {'F','W','E'} satisfying: (i) for every i with 0 <= i < n-1, b[i] != b[i+1]; and (ii) the number of indices i with beats(b[i], s[i]) is strictly greater than the number of indices i with beats(s[i], b[i]), where beats(x, y) holds exactly when (x = 'W' and y = 'F') or (x = 'E' and y = 'W') or (x = 'F' and y = 'E'). Thus r = N mod 1000000007.
  Preconditions: Let n = len(s). 1 <= n <= 1000. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_1 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val) :
    ∃ r : Aeneas.Std.I64,
      Aegis.CountWinningSequences.count_winning_sequences s = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧ r.val = (N s : Int) % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val), ∃ r : Aeneas.Std.I64,
      Aegis.CountWinningSequences.count_winning_sequences s = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧ r.val = (N s : Int) % 1000000007) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r and does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let n = len(s). 1 <= n <= 1000. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_2 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val) :
    ∃ r : Aeneas.Std.I64, Aegis.CountWinningSequences.count_winning_sequences s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val), ∃ r : Aeneas.Std.I64, Aegis.CountWinningSequences.count_winning_sequences s = ok r) := by
  sorry

/-- Whenever the function returns r for such an s, the result satisfies 0 <= r < 1000000007.
  Preconditions: Let n = len(s). 1 <= n <= 1000. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_3 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r) :
    0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Let N be the unmodded number of winning Bob sequences described in spec_1. The function returns r = N, not merely N mod 1000000007; in other words, no modular reduction occurs for these lengths.
  Preconditions: Let n = len(s). 1 <= n <= 29. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_4 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 29)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r) :
    r.val = (N s : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 29)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r), r.val = (N s : Int)) := by
  sorry

/-- Define rot(s) by rot(s)[i] = 'W' if s[i] = 'F', rot(s)[i] = 'E' if s[i] = 'W', and rot(s)[i] = 'F' if s[i] = 'E', for every 0 <= i < n. If r is the function's result on s and r' is its result on rot(s), then r = r'.
  Preconditions: Let n = len(s). 1 <= n <= 1000. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_5 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r)
    (hr' : Aegis.CountWinningSequences.count_winning_sequences (rotSlice s) = ok r') :
    r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r)
    (hr' : Aegis.CountWinningSequences.count_winning_sequences (rotSlice s) = ok r'), r = r') := by
  sorry

/-- Define rev(s)[i] = s[n-1-i] for every 0 <= i < n. If r is the function's result on s and r' is its result on rev(s), then r = r'.
  Preconditions: Let n = len(s). 1 <= n <= 1000. For every i with 0 <= i < n, s[i] is the ASCII code of one of 'F' (70), 'W' (87), or 'E' (69). -/
theorem spec_6 (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r)
    (hr' : Aegis.CountWinningSequences.count_winning_sequences (revSlice s) = ok r') :
    r = r' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : U8Slice)
    (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
    (hsym : ∀ i (hi : i < s.val.length), isSymbol (s.val[i]).val)
    (r r' : Aeneas.Std.I64)
    (hr : Aegis.CountWinningSequences.count_winning_sequences s = ok r)
    (hr' : Aegis.CountWinningSequences.count_winning_sequences (revSlice s) = ok r'), r = r') := by
  sorry

end AegisSpec.CountWinningSequences
