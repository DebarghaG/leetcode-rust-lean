import Aegis.FindRepeatedDnaSequences.Code.Funs

/-!
# Specifications of `Aegis.FindRepeatedDnaSequences.find_repeated_dna_sequences`

LeetCode problem `repeated-dna-sequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindRepeatedDnaSequences

def IsDNAByte (b : Std.U8) : Prop :=
  b.val = 65 ∨ b.val = 67 ∨ b.val = 71 ∨ b.val = 84

def IsDNASeq (s : Slice Std.U8) : Prop :=
  ∀ (i : Nat) (h : i < (Slice.len s).val), IsDNAByte (s.val[i]'h)

def window (s : List Std.U8) (i : Nat) : List Std.U8 :=
  (s.drop i).take 10

@[reducible] def OccursAt (s w : List Std.U8) (i : Nat) : Prop :=
  i + 10 ≤ s.length ∧ w = window s i

def Occ (s w : List Std.U8) : Nat :=
  ((List.range (s.length + 1)).filter (fun i => decide (OccursAt s w i))).length

/-- Whenever find_repeated_dna_sequences(s) returns r, every element of r has length 10, and for every byte vector w with len(w) = 10, let Occ(w) be the number of indices i such that 0 <= i, i+10 <= len(s), and w[k] = s[i+k] for every k with 0 <= k < 10. Then the number of indices q with 0 <= q < len(r) and r[q] = w is exactly 1 if Occ(w) >= 2, and exactly 0 otherwise. Equivalently, r contains exactly the distinct 10-byte contiguous substrings of s that occur at at least two distinct starting indices, each once, in arbitrary order.
  Preconditions: s is a DNA sequence: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] is 65, 67, 71, or 84 (the ASCII codes of A, C, G, T). Lists and byte arrays are 0-indexed; len(s) and len(r) are numbers of bytes/elements. -/
theorem spec_1
    (s : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hlen_lo : 1 ≤ (Slice.len s).val) (hlen_hi : (Slice.len s).val ≤ 100000)
    (hdna : IsDNASeq s) :
    Aegis.FindRepeatedDnaSequences.find_repeated_dna_sequences s = ok r →
      (∀ (q : Nat) (hq : q < r.val.length), (r.val[q]).val.length = 10) ∧
      (∀ w : List Std.U8, w.length = 10 →
        (r.val.filter (fun x => x.val = w)).length
          = if 2 ≤ Occ s.val w then 1 else 0) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hlen_lo : 1 ≤ (Slice.len s).val) (hlen_hi : (Slice.len s).val ≤ 100000)
    (hdna : IsDNASeq s), Aegis.FindRepeatedDnaSequences.find_repeated_dna_sequences s = ok r →
      (∀ (q : Nat) (hq : q < r.val.length), (r.val[q]).val.length = 10) ∧
      (∀ w : List Std.U8, w.length = 10 →
        (r.val.filter (fun x => x.val = w)).length
          = if 2 ≤ Occ s.val w then 1 else 0)) := by
  sorry

/-- For every s satisfying the preconditions, find_repeated_dna_sequences(s) returns a result r; it does not fail by panic, out-of-bounds access, or machine-integer overflow.
  Preconditions: s is a DNA sequence: 1 <= len(s) <= 100000 and for every i with 0 <= i < len(s), s[i] is 65, 67, 71, or 84 (the ASCII codes of A, C, G, T). Lists and byte arrays are 0-indexed; len(s) and len(r) are numbers of bytes/elements. -/
theorem spec_2
    (s : Slice Std.U8)
    (hlen_lo : 1 ≤ (Slice.len s).val) (hlen_hi : (Slice.len s).val ≤ 100000)
    (hdna : IsDNASeq s) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.FindRepeatedDnaSequences.find_repeated_dna_sequences s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ (Slice.len s).val) (hlen_hi : (Slice.len s).val ≤ 100000)
    (hdna : IsDNASeq s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.FindRepeatedDnaSequences.find_repeated_dna_sequences s = ok r) := by
  sorry

end AegisSpec.FindRepeatedDnaSequences
