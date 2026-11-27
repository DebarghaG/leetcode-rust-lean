import Aegis.NumberOfBeams.Code.Funs

/-!
# Specifications of `Aegis.NumberOfBeams.number_of_beams`

LeetCode problem `number-of-laser-beams-in-a-bank`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfBeams

def row (bank : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : List Std.U8 :=
  match bank.val[i]? with
  | some r => r.val
  | none => []

def rowLen (bank : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Nat :=
  (row bank i).length

def entry (bank : Slice (alloc.vec.Vec Std.U8)) (i j : Nat) : Nat :=
  ((row bank i)[j]?).elim 0 (fun b => b.val)

def rowCount (bank : Slice (alloc.vec.Vec Std.U8)) (i : Nat) : Nat :=
  (row bank i).countP (fun b => decide (b.val = 49))

def activeRows (bank : Slice (alloc.vec.Vec Std.U8)) (m : Nat) : List Nat :=
  (List.range m).filter (fun i => decide (rowCount bank i > 0))

def activeCounts (bank : Slice (alloc.vec.Vec Std.U8)) (m : Nat) : List Nat :=
  (activeRows bank m).map (fun i => rowCount bank i)

def beamTotal (counts : List Nat) : Nat :=
  ((counts.zip counts.tail).map (fun p : Nat × Nat => p.1 * p.2)).sum

def singleOneRows (bank : Slice (alloc.vec.Vec Std.U8)) (m : Nat) : Nat :=
  ((List.range m).filter (fun i => decide (rowCount bank i = 1))).length

def pairWeight (bank : Slice (alloc.vec.Vec Std.U8)) (m i j : Nat) : Nat :=
  ((activeRows bank m).zip (activeRows bank m).tail).countP
    (fun p => p.1 == i && p.2 == j)

def pairContribution (bank : Slice (alloc.vec.Vec Std.U8)) (m i j : Nat) : Nat :=
  pairWeight bank m i j * rowCount bank i * rowCount bank j

def consecutiveTotal (bank : Slice (alloc.vec.Vec Std.U8)) (m : Nat) : Nat :=
  ((List.range (m - 1)).map (fun i => rowCount bank i * rowCount bank (i + 1))).sum

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. Let i_1 < i_2 < ... < i_k be exactly the row indices with row_count(i_t) > 0. The function returns a result r and: if k <= 1 then r = 0; if k >= 2 then r = sum_{t=1}^{k-1} row_count(i_t) * row_count(i_{t+1}).
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_1 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∃ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r ∧
      r.val = ((beamTotal (activeCounts bank m) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∃ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r ∧
      r.val = ((beamTotal (activeCounts bank m) : Nat) : Int)) := by
  sorry

/-- For every bank satisfying the preconditions, number_of_beams returns a result r (an Ok value); it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_2 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∃ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∃ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r) := by
  sorry

/-- Whenever number_of_beams returns a result r, we have r >= 0.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_3 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever number_of_beams returns a result r, we have r <= (m-1)*n*n.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_4 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val ≤ ((m : Int) - 1) * (n : Int) * (n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val ≤ ((m : Int) - 1) * (n : Int) * (n : Int)) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. Whenever number_of_beams returns a result r, we have r = 0 if and only if at most one row index i satisfies row_count(i) > 0.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_5 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      (r.val = 0 ↔ (activeRows bank m).length ≤ 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      (r.val = 0 ↔ (activeRows bank m).length ≤ 1)) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. If exactly two row indices i1 < i2 satisfy row_count(i1) > 0 and row_count(i2) > 0, then whenever number_of_beams returns a result r, we have r = row_count(i1) * row_count(i2).
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_6 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (i1 i2 : Nat) (hi12 : i1 < i2) (hi2m : i2 < m)
    (hc1 : 0 < rowCount bank i1) (hc2 : 0 < rowCount bank i2)
    (hexactly : ∀ i, i < m → 0 < rowCount bank i → i = i1 ∨ i = i2) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = (rowCount bank i1 : Int) * (rowCount bank i2 : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (i1 i2 : Nat) (hi12 : i1 < i2) (hi2m : i2 < m)
    (hc1 : 0 < rowCount bank i1) (hc2 : 0 < rowCount bank i2)
    (hexactly : ∀ i, i < m → 0 < rowCount bank i → i = i1 ∨ i = i2), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = (rowCount bank i1 : Int) * (rowCount bank i2 : Int)) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. If row_count(i) > 0 for every i with 0 <= i < m, then whenever number_of_beams returns a result r, we have r = sum_{i=0}^{m-2} row_count(i) * row_count(i+1), with the empty sum equal to 0 when m = 1.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_7 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hpositive : ∀ i, i < m → 0 < rowCount bank i) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = ((consecutiveTotal bank m : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hpositive : ∀ i, i < m → 0 < rowCount bank i), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = ((consecutiveTotal bank m : Nat) : Int)) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. If row_count(i) <= 1 for every i, let k be the number of indices i with row_count(i) = 1. Then whenever number_of_beams returns a result r, we have r = max(k-1, 0).
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_8 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hatMostOne : ∀ i, i < m → rowCount bank i ≤ 1) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = max ((singleOneRows bank m : Int) - 1) 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hatMostOne : ∀ i, i < m → rowCount bank i ≤ 1), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      r.val = max ((singleOneRows bank m : Int) - 1) 0) := by
  sorry

/-- Whenever number_of_beams bank returns r and number_of_beams bank' returns r', we have r = r'.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). Let bank' be the row-reversal of bank: len(bank') = m, len(bank'[i]) = n for every i, and bank'[i][j] = bank[m-1-i][j] for every i,j. -/
theorem spec_9 (bank bank' : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hm' : bank'.val.length = m)
    (hlen' : ∀ i, i < m → rowLen bank' i = n)
    (hrev : ∀ i j, i < m → j < n → entry bank' i j = entry bank (m - 1 - i) j) :
    ∀ r r', Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      Aegis.NumberOfBeams.number_of_beams bank' = Result.ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bank bank' : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hm' : bank'.val.length = m)
    (hlen' : ∀ i, i < m → rowLen bank' i = n)
    (hrev : ∀ i j, i < m → j < n → entry bank' i j = entry bank (m - 1 - i) j), ∀ r r', Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      Aegis.NumberOfBeams.number_of_beams bank' = Result.ok r' → r.val = r'.val) := by
  sorry

/-- Define row_count_bank(i) as the number of j with bank[i][j] = 49, and row_count_bank'(i) as the number of j with bank'[i][j] = 49. If row_count_bank(i) = row_count_bank'(i) for every i with 0 <= i < m, then whenever number_of_beams bank returns r and number_of_beams bank' returns r', we have r = r'.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). Let bank' be any other input satisfying the same constraints and having len(bank') = m. -/
theorem spec_10 (bank bank' : Slice (alloc.vec.Vec Std.U8)) (m n n' : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hm' : bank'.val.length = m)
    (hn'_lower : 1 ≤ n') (hn'_upper : n' ≤ 500)
    (hlen' : ∀ i, i < m → rowLen bank' i = n')
    (hbits' : ∀ i j, i < m → j < n' → entry bank' i j = 48 ∨ entry bank' i j = 49)
    (hcounts : ∀ i, i < m → rowCount bank' i = rowCount bank i) :
    ∀ r r', Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      Aegis.NumberOfBeams.number_of_beams bank' = Result.ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bank bank' : Slice (alloc.vec.Vec Std.U8)) (m n n' : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49)
    (hm' : bank'.val.length = m)
    (hn'_lower : 1 ≤ n') (hn'_upper : n' ≤ 500)
    (hlen' : ∀ i, i < m → rowLen bank' i = n')
    (hbits' : ∀ i j, i < m → j < n' → entry bank' i j = 48 ∨ entry bank' i j = 49)
    (hcounts : ∀ i, i < m → rowCount bank' i = rowCount bank i), ∀ r r', Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      Aegis.NumberOfBeams.number_of_beams bank' = Result.ok r' → r.val = r'.val) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. Whenever number_of_beams returns a result r with r > 0, there exist indices i < j and columns c,d such that 0 <= c < len(bank[i]), 0 <= d < len(bank[j]), bank[i][c] = 49, bank[j][d] = 49, and row_count(k) = 0 for every k with i < k < j.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_11 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r → 0 < r.val →
      ∃ i j c d, i < j ∧ j < m ∧ c < rowLen bank i ∧ d < rowLen bank j ∧
        entry bank i c = 49 ∧ entry bank j d = 49 ∧
        ∀ k, i < k → k < j → rowCount bank k = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r → 0 < r.val →
      ∃ i j c d, i < j ∧ j < m ∧ c < rowLen bank i ∧ d < rowLen bank j ∧
        entry bank i c = 49 ∧ entry bank j d = 49 ∧
        ∀ k, i < k → k < j → rowCount bank k = 0) := by
  sorry

/-- Let row_count(i) be the number of j with 0 <= j < len(bank[i]) and bank[i][j] = 49. Whenever number_of_beams returns a result r, for every i < j with row_count(i) > 0 and row_count(j) > 0, if there exists k with i < k < j and row_count(k) > 0, then no laser beam has one endpoint in row i and one endpoint in row j; equivalently, the ordered row pair (i,j) contributes 0 to r.
  Preconditions: Let m = len(bank). Assume 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that len(bank[i]) = n for every i with 0 <= i < m; and for every i,j with 0 <= i < m and 0 <= j < n, bank[i][j] is either 48 (ASCII '0') or 49 (ASCII '1'). -/
theorem spec_12 (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49) :
    ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      ∀ i j, i < j → 0 < rowCount bank i → 0 < rowCount bank j →
        (∃ k, i < k ∧ k < j ∧ 0 < rowCount bank k) →
        pairContribution bank m i j = 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (bank : Slice (alloc.vec.Vec Std.U8)) (m n : Nat)
    (hm : bank.val.length = m)
    (hm_lower : 1 ≤ m) (hm_upper : m ≤ 500)
    (hn_lower : 1 ≤ n) (hn_upper : n ≤ 500)
    (hlen : ∀ i, i < m → rowLen bank i = n)
    (hbits : ∀ i j, i < m → j < n → entry bank i j = 48 ∨ entry bank i j = 49), ∀ r, Aegis.NumberOfBeams.number_of_beams bank = Result.ok r →
      ∀ i j, i < j → 0 < rowCount bank i → 0 < rowCount bank j →
        (∃ k, i < k ∧ k < j ∧ 0 < rowCount bank k) →
        pairContribution bank m i j = 0) := by
  sorry

end AegisSpec.NumberOfBeams
