import Aegis.MinMutation.Code.Funs

/-!
# Specifications of `Aegis.MinMutation.min_mutation`

LeetCode problem `minimum-genetic-mutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std

namespace AegisSpec.MinMutation

open Aeneas.Std.Result
open Aegis.MinMutation (min_mutation)

abbrev Gene := List U8

def DNAByte (b : U8) : Prop := b.val = 65 ∨ b.val = 67 ∨ b.val = 71 ∨ b.val = 84

def DNAGene (g : Gene) : Prop := ∀ b ∈ g, DNAByte b

def Present (bank : List (alloc.vec.Vec U8)) (g : Gene) : Prop :=
  ∃ j : Fin bank.length, (bank.get j).val = g

def DiffOne (a b : Gene) : Prop :=
  a.length = 8 ∧ b.length = 8 ∧
    ∃ p : ℕ, p < 8 ∧ a[p]? ≠ b[p]? ∧ ∀ q : ℕ, q < 8 → q ≠ p → a[q]? = b[q]?

def ChainDiffOne : List Gene → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => DiffOne a b ∧ ChainDiffOne (b :: rest)

def ValidMutationSeq (bank : List (alloc.vec.Vec U8)) (src dst : Gene)
    (gs : List Gene) : Prop :=
  gs.head? = some src ∧ gs.getLast? = some dst ∧ ChainDiffOne gs ∧
    ∀ i : ℕ, 1 ≤ i → ∀ hi : i < gs.length, Present bank (gs[i]'hi)

def HasValidSeqOfLength (bank : List (alloc.vec.Vec U8)) (src dst : Gene) (k : ℕ) : Prop :=
  ∃ gs : List Gene, gs.length = k + 1 ∧ ValidMutationSeq bank src dst gs

def GeneOK (g : Slice U8) : Prop := g.val.length = 8 ∧ DNAGene g.val

def BankOK (bank : Slice (alloc.vec.Vec U8)) : Prop :=
  bank.val.length ≤ 10 ∧
    (∀ i : ℕ, ∀ hi : i < bank.val.length, (bank.val[i]'hi).val.length = 8) ∧
    (∀ i : ℕ, ∀ hi : i < bank.val.length, DNAGene (bank.val[i]'hi).val)

def Hyp (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8)) : Prop :=
  GeneOK startGene ∧ GeneOK endGene ∧ BankOK bank

/-- Whenever the function returns a result r, the following holds. Call a finite sequence (g_0,...,g_k) of byte strings a valid mutation sequence of length k from startGene to endGene if: g_0 = startGene and g_k = endGene; for every i with 0 <= i < k, g_i and g_{i+1} both have length 8 and there is exactly one index p with 0 <= p < 8 such that g_i[p] != g_{i+1}[p] (all other positions are equal); and for every i with 1 <= i <= k, there exists j with 0 <= j < len(bank) such that bank[j] equals g_i byte for byte. Then if some valid mutation sequence of length k with k >= 0 exists, r is the least such k; otherwise r = -1.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_1 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) :
    (∃ k : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k ∧ r.val = (k : ℤ) ∧
        ∀ k' : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k' → k ≤ k')
      ∨ ((¬ ∃ k : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k) ∧ r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r), (∃ k : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k ∧ r.val = (k : ℤ) ∧
        ∀ k' : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k' → k ≤ k')
      ∨ ((¬ ∃ k : ℕ, HasValidSeqOfLength bank.val startGene.val endGene.val k) ∧ r.val = -1)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, overflow, or access out of bounds) for every input satisfying the preconditions.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_2 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) :
    ∃ r : I64, min_mutation startGene endGene bank = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank), ∃ r : I64, min_mutation startGene endGene bank = ok r) := by
  sorry

/-- Whenever the function returns r, either r = -1, or 0 <= r <= len(bank).
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_3 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) :
    r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (bank.val.length : ℤ)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (bank.val.length : ℤ))) := by
  sorry

/-- Whenever the function returns r, r = 0 if and only if startGene = endGene (same bytes at all 8 positions).
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_4 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) :
    r.val = 0 ↔ startGene.val = endGene.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r), r.val = 0 ↔ startGene.val = endGene.val) := by
  sorry

/-- Whenever the function returns r, if r > 0 then endGene is present in bank: there exists j with 0 <= j < len(bank) such that bank[j] equals endGene byte for byte.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_5 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val) :
    Present bank.val endGene.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val), Present bank.val endGene.val) := by
  sorry

/-- Whenever the function returns r, if endGene is not present in bank (there is no j with 0 <= j < len(bank) and bank[j] = endGene byte for byte), then r = 0 when startGene = endGene, and r = -1 when startGene != endGene.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_6 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r)
    (hnot : ¬ Present bank.val endGene.val) :
    (startGene.val = endGene.val → r.val = 0) ∧
      (startGene.val ≠ endGene.val → r.val = -1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r)
    (hnot : ¬ Present bank.val endGene.val), (startGene.val = endGene.val → r.val = 0) ∧
      (startGene.val ≠ endGene.val → r.val = -1)) := by
  sorry

/-- Whenever the function returns r, r = 1 if and only if startGene and endGene differ in exactly one position p with 0 <= p < 8 (all other positions are equal), and endGene is present in bank.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_7 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) :
    r.val = 1 ↔ DiffOne startGene.val endGene.val ∧ Present bank.val endGene.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r), r.val = 1 ↔ DiffOne startGene.val endGene.val ∧ Present bank.val endGene.val) := by
  sorry

/-- Whenever the function returns r, if r > 0 then there exists an index j with 0 <= j < len(bank) such that startGene and bank[j] differ in exactly one of the 8 positions, and there exists a valid mutation sequence of length r - 1 from bank[j] to endGene using bank, meaning a sequence (h_0,...,h_{r-1}) with h_0 = bank[j], h_{r-1} = endGene, every consecutive pair differs in exactly one of the 8 positions, and every h_i with 1 <= i <= r - 1 is present in bank.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_8 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val) :
    ∃ j : Fin bank.val.length,
      DiffOne startGene.val (bank.val.get j).val ∧
        ∃ gs : List Gene, gs.length = r.val.toNat ∧
          ValidMutationSeq bank.val (bank.val.get j).val endGene.val gs := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val), ∃ j : Fin bank.val.length,
      DiffOne startGene.val (bank.val.get j).val ∧
        ∃ gs : List Gene, gs.length = r.val.toNat ∧
          ValidMutationSeq bank.val (bank.val.get j).val endGene.val gs) := by
  sorry

/-- Whenever the function returns r with r >= 0, there exists a valid mutation sequence (g_0,...,g_r) of length r from startGene to endGene using bank such that g_0,g_1,...,g_r are pairwise distinct byte strings.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_9 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hnn : 0 ≤ r.val) :
    ∃ gs : List Gene, gs.length = r.val.toNat + 1 ∧
      ValidMutationSeq bank.val startGene.val endGene.val gs ∧ gs.Nodup := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hnn : 0 ≤ r.val), ∃ gs : List Gene, gs.length = r.val.toNat + 1 ∧
      ValidMutationSeq bank.val startGene.val endGene.val gs ∧ gs.Nodup) := by
  sorry

/-- Whenever the function returns r for (startGene,endGene,bank), the function returns r for (startGene,endGene,bank2) as well.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). Let bank2 be any slice of Vec<U8> satisfying the same length, alphabet, and at-most-10 preconditions, and such that for every 8-byte gene string g over {A,C,G,T}, g is present in bank exactly when g is present in bank2. -/
theorem spec_10 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (bank2 : Slice (alloc.vec.Vec U8))
    (h2 : Hyp startGene endGene bank2)
    (hset : ∀ g : Gene, DNAGene g → g.length = 8 → (Present bank.val g ↔ Present bank2.val g))
    (r : I64) (hr : min_mutation startGene endGene bank = ok r) :
    min_mutation startGene endGene bank2 = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (bank2 : Slice (alloc.vec.Vec U8))
    (h2 : Hyp startGene endGene bank2)
    (hset : ∀ g : Gene, DNAGene g → g.length = 8 → (Present bank.val g ↔ Present bank2.val g))
    (r : I64) (hr : min_mutation startGene endGene bank = ok r), min_mutation startGene endGene bank2 = ok r) := by
  sorry

/-- Whenever the function returns r for (startGene,endGene,bank), if startGene is present in bank, then for the bank2 obtained from bank by deleting every entry equal to startGene byte for byte, the function returns r for (startGene,endGene,bank2).
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_11 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (hstart : Present bank.val startGene.val)
    (bank2 : Slice (alloc.vec.Vec U8))
    (h2 : bank2.val = bank.val.filter (fun v => v.val ≠ startGene.val))
    (r : I64) (hr : min_mutation startGene endGene bank = ok r) :
    min_mutation startGene endGene bank2 = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (hstart : Present bank.val startGene.val)
    (bank2 : Slice (alloc.vec.Vec U8))
    (h2 : bank2.val = bank.val.filter (fun v => v.val ≠ startGene.val))
    (r : I64) (hr : min_mutation startGene endGene bank = ok r), min_mutation startGene endGene bank2 = ok r) := by
  sorry

/-- Whenever the function returns r1 for (startGene,endGene,bank1) and r2 for (startGene,endGene,bank2), either r1 = -1, or (r2 >= 0 and r2 <= r1).
  Preconditions: len(startGene) = 8, len(endGene) = 8, and every byte of startGene and endGene is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). Let bank1 and bank2 be slices of Vec<U8> both satisfying len <= 10, every entry has length 8 and uses only A,C,G,T, and suppose every gene string present in bank1 is also present in bank2. -/
theorem spec_12 (startGene endGene : Slice U8)
    (hgene : GeneOK startGene ∧ GeneOK endGene)
    (bank1 bank2 : Slice (alloc.vec.Vec U8)) (h1 : BankOK bank1) (h2 : BankOK bank2)
    (hsub : ∀ g : Gene, Present bank1.val g → Present bank2.val g)
    (r1 r2 : I64) (hr1 : min_mutation startGene endGene bank1 = ok r1)
    (hr2 : min_mutation startGene endGene bank2 = ok r2) :
    r1.val = -1 ∨ (0 ≤ r2.val ∧ r2.val ≤ r1.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (startGene endGene : Slice U8)
    (hgene : GeneOK startGene ∧ GeneOK endGene)
    (bank1 bank2 : Slice (alloc.vec.Vec U8)) (h1 : BankOK bank1) (h2 : BankOK bank2)
    (hsub : ∀ g : Gene, Present bank1.val g → Present bank2.val g)
    (r1 r2 : I64) (hr1 : min_mutation startGene endGene bank1 = ok r1)
    (hr2 : min_mutation startGene endGene bank2 = ok r2), r1.val = -1 ∨ (0 ≤ r2.val ∧ r2.val ≤ r1.val)) := by
  sorry

/-- Whenever the function returns r, if startGene != endGene and there is no index j with 0 <= j < len(bank) such that startGene and bank[j] differ in exactly one of the 8 positions, then r = -1.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_13 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hne : startGene.val ≠ endGene.val)
    (hno : ∀ j : Fin bank.val.length, ¬ DiffOne startGene.val (bank.val.get j).val) :
    r.val = -1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hne : startGene.val ≠ endGene.val)
    (hno : ∀ j : Fin bank.val.length, ¬ DiffOne startGene.val (bank.val.get j).val), r.val = -1) := by
  sorry

/-- Whenever the function returns r with r > 0, bank contains at least r pairwise distinct byte strings: there exist indices j_1,...,j_r with 0 <= j_m < len(bank) such that bank[j_1],...,bank[j_r] are pairwise unequal as byte sequences.
  Preconditions: len(startGene) = 8, len(endGene) = 8, len(bank) <= 10, and for every i with 0 <= i < len(bank), len(bank[i]) = 8. Every byte of startGene, endGene, and every bank[i] is one of 65 ('A'), 67 ('C'), 71 ('G'), 84 ('T'). -/
theorem spec_14 (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val) :
    ∃ js : List (Fin bank.val.length), js.length = r.val.toNat ∧
      (js.map (fun j => (bank.val.get j).val)).Nodup := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (startGene endGene : Slice U8) (bank : Slice (alloc.vec.Vec U8))
    (h : Hyp startGene endGene bank) (r : I64)
    (hr : min_mutation startGene endGene bank = ok r) (hpos : 0 < r.val), ∃ js : List (Fin bank.val.length), js.length = r.val.toNat ∧
      (js.map (fun j => (bank.val.get j).val)).Nodup) := by
  sorry

end AegisSpec.MinMutation
