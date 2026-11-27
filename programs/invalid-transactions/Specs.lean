import Aegis.InvalidTransactions.Code.Funs

/-!
# Specifications of `Aegis.InvalidTransactions.invalid_transactions`

LeetCode problem `invalid-transactions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.InvalidTransactions

abbrev Byte : Type := Aeneas.Std.U8

abbrev ByteVec : Type := Aeneas.Std.alloc.vec.Vec Byte

abbrev ByteVecVec : Type := Aeneas.Std.alloc.vec.Vec ByteVec

abbrev ByteVecSlice : Type := Aeneas.Std.Slice ByteVec

def commaValue : Nat := 44

def isLowerByte (b : Byte) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

def isDigitByte (b : Byte) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

def lowerWord (l : List Byte) : Prop := 1 ≤ l.length ∧ l.length ≤ 10 ∧ ∀ b ∈ l, isLowerByte b

def digitString (l : List Byte) : Prop := 1 ≤ l.length ∧ ∀ b ∈ l, isDigitByte b

def digitsVal (l : List Byte) : Nat := l.foldl (fun acc b => acc * 10 + (b.val - 48)) 0

def splitFirstComma : List Byte → Option (List Byte × List Byte)
  | [] => none
  | b :: bs =>
    if b.val = commaValue then some ([], bs)
    else Option.map (fun p => (b :: p.1, p.2)) (splitFirstComma bs)

def parseTx (l : List Byte) : Option (List Byte × List Byte × List Byte × List Byte) :=
  match splitFirstComma l with
  | none => none
  | some (nm, rest1) =>
    match splitFirstComma rest1 with
    | none => none
    | some (timeStr, rest2) =>
      match splitFirstComma rest2 with
      | none => none
      | some (amountStr, city) => some (nm, timeStr, amountStr, city)

def txName (l : List Byte) : List Byte := ((parseTx l).map (fun p => p.1)).getD []

def txTimeStr (l : List Byte) : List Byte := ((parseTx l).map (fun p => p.2.1)).getD []

def txAmountStr (l : List Byte) : List Byte := ((parseTx l).map (fun p => p.2.2.1)).getD []

def txCity (l : List Byte) : List Byte := ((parseTx l).map (fun p => p.2.2.2)).getD []

def vName (v : ByteVec) : List Byte := txName v.val

def vTime (v : ByteVec) : Nat := digitsVal (txTimeStr v.val)

def vAmount (v : ByteVec) : Nat := digitsVal (txAmountStr v.val)

def vCity (v : ByteVec) : List Byte := txCity v.val

def IsTxString (l : List Byte) : Prop :=
  ∃ nm timeStr amountStr city,
    parseTx l = some (nm, timeStr, amountStr, city) ∧
      lowerWord nm ∧ lowerWord city ∧ digitString timeStr ∧ digitString amountStr ∧
      digitsVal timeStr ≤ 1000 ∧ digitsVal amountStr ≤ 2000

def IsTxInput (transactions : ByteVecSlice) : Prop :=
  transactions.val.length ≤ 1000 ∧ ∀ t ∈ transactions.val, IsTxString t.val

@[reducible] def timeClose (t1 t2 : Nat) : Prop := ((t1 : Int) - (t2 : Int)).natAbs ≤ 60

@[reducible] def invalidAt (transactions : List ByteVec) (i : Fin transactions.length) : Prop :=
  vAmount (transactions.get i) > 1000 ∨
    ∃ j : Fin transactions.length,
      j ≠ i ∧ vName (transactions.get j) = vName (transactions.get i) ∧
        vCity (transactions.get j) ≠ vCity (transactions.get i) ∧
        timeClose (vTime (transactions.get i)) (vTime (transactions.get j))

def invalidTransactions (transactions : List ByteVec) : List ByteVec :=
  ((List.finRange transactions.length).filter (fun i => decide (invalidAt transactions i))).map
    (fun i => transactions.get i)

def countInvalid (transactions : List ByteVec) : Nat :=
  (List.finRange transactions.length).countP (fun i => decide (invalidAt transactions i))

def countOcc (v : ByteVec) (l : List ByteVec) : Nat := l.countP (fun w => decide (w.val = v.val))

/-- Let n = len(transactions). For 0 <= i < n, let name_i, time_i, amount_i, city_i be the components of transactions[i] as described in the preconditions. Define invalid(i) as: amount_i > 1000, or there exists j with 0 <= j < n, j != i, such that name_j = name_i, city_j != city_i, and |time_i - time_j| <= 60. Whenever the function returns a result r, r is a permutation of the list [transactions[i] | 0 <= i < n and invalid(i)]. Equivalently, for every byte vector v, the number of occurrences of v in r equals the number of indices i with invalid(i) and transactions[i] = v.
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_1 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r) :
    r.val.Perm (invalidTransactions transactions.val) ∧
      ∀ v : ByteVec, countOcc v r.val = countOcc v (invalidTransactions transactions.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r), r.val.Perm (invalidTransactions transactions.val) ∧
      ∀ v : ByteVec, countOcc v r.val = countOcc v (invalidTransactions transactions.val)) := by
  sorry

/-- The function returns a result r (it does not panic or fail due to overflow or out-of-bounds access).
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_2 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) :
    ∃ r : ByteVecVec, Aegis.InvalidTransactions.invalid_transactions transactions = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions), ∃ r : ByteVecVec, Aegis.InvalidTransactions.invalid_transactions transactions = ok r) := by
  sorry

/-- Let n = len(transactions). For 0 <= i < n, let name_i, time_i, amount_i, city_i be the components of transactions[i]. Define invalid(i) as: amount_i > 1000, or there exists j with 0 <= j < n, j != i, such that name_j = name_i, city_j != city_i, and |time_i - time_j| <= 60. Whenever the function returns a result r, for every i with 0 <= i < n, if invalid(i) then transactions[i] appears at least once in r.
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_3 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r) :
    ∀ i : Fin transactions.val.length,
      invalidAt transactions.val i → 1 ≤ countOcc (transactions.val.get i) r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r), ∀ i : Fin transactions.val.length,
      invalidAt transactions.val i → 1 ≤ countOcc (transactions.val.get i) r.val) := by
  sorry

/-- Let n = len(transactions). For 0 <= i < n, let name_i, time_i, amount_i, city_i be the components of transactions[i]. Define invalid(i) as: amount_i > 1000, or there exists j with 0 <= j < n, j != i, such that name_j = name_i, city_j != city_i, and |time_i - time_j| <= 60. Whenever the function returns a result r, for every element v of r, there exists i with 0 <= i < n such that v = transactions[i] and invalid(i).
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_4 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r) :
    ∀ v : ByteVec,
      v ∈ r.val →
        ∃ i : Fin transactions.val.length,
          v = transactions.val.get i ∧ invalidAt transactions.val i := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r), ∀ v : ByteVec,
      v ∈ r.val →
        ∃ i : Fin transactions.val.length,
          v = transactions.val.get i ∧ invalidAt transactions.val i) := by
  sorry

/-- Let n = len(transactions). For 0 <= i < n, let name_i, time_i, amount_i, city_i be the components of transactions[i]. Define invalid(i) as: amount_i > 1000, or there exists j with 0 <= j < n, j != i, such that name_j = name_i, city_j != city_i, and |time_i - time_j| <= 60. Whenever the function returns a result r, len(r) = the number of indices i with 0 <= i < n such that invalid(i).
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_5 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r) :
    r.val.length = countInvalid transactions.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r), r.val.length = countInvalid transactions.val) := by
  sorry

/-- Let n = len(transactions). Whenever the function returns a result r, for every byte vector v, the number of occurrences of v in r is at most the number of occurrences of v in transactions.
  Preconditions: transactions is a slice of byte vectors with len(transactions) <= 1000. For every i with 0 <= i < len(transactions), transactions[i] is an ASCII string of the form name_i + ',' + time_i + ',' + amount_i + ',' + city_i, where name_i and city_i are strings of lowercase English letters of length 1 to 10, time_i is a decimal integer with 0 <= time_i <= 1000, and amount_i is a decimal integer with 0 <= amount_i <= 2000. -/
theorem spec_6 (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r) :
    ∀ v : ByteVec, countOcc v r.val ≤ countOcc v transactions.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (transactions : ByteVecSlice) (hinput : IsTxInput transactions) (r : ByteVecVec)
    (hres : Aegis.InvalidTransactions.invalid_transactions transactions = ok r), ∀ v : ByteVec, countOcc v r.val ≤ countOcc v transactions.val) := by
  sorry

/-- For any two input arrays transactions1 and transactions2 that are permutations of each other (i.e., for every byte vector v, the number of occurrences of v in transactions1 equals the number of occurrences of v in transactions2), if the function returns r1 on transactions1 and r2 on transactions2, then r1 and r2 are permutations of each other (i.e., for every byte vector v, the number of occurrences of v in r1 equals the number of occurrences of v in r2).
  Preconditions: Both transactions1 and transactions2 are slices of byte vectors with len <= 1000. For every transaction in either slice, it is an ASCII string of the form name + ',' + time + ',' + amount + ',' + city, where name and city are strings of lowercase English letters of length 1 to 10, time is a decimal integer with 0 <= time <= 1000, and amount is a decimal integer with 0 <= amount <= 2000. -/
theorem spec_7 (transactions1 transactions2 : ByteVecSlice) (hinput1 : IsTxInput transactions1)
    (hinput2 : IsTxInput transactions2)
    (hperm : ∀ v : ByteVec, countOcc v transactions1.val = countOcc v transactions2.val)
    (r1 r2 : ByteVecVec)
    (hres1 : Aegis.InvalidTransactions.invalid_transactions transactions1 = ok r1)
    (hres2 : Aegis.InvalidTransactions.invalid_transactions transactions2 = ok r2) :
    ∀ v : ByteVec, countOcc v r1.val = countOcc v r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (transactions1 transactions2 : ByteVecSlice) (hinput1 : IsTxInput transactions1)
    (hinput2 : IsTxInput transactions2)
    (hperm : ∀ v : ByteVec, countOcc v transactions1.val = countOcc v transactions2.val)
    (r1 r2 : ByteVecVec)
    (hres1 : Aegis.InvalidTransactions.invalid_transactions transactions1 = ok r1)
    (hres2 : Aegis.InvalidTransactions.invalid_transactions transactions2 = ok r2), ∀ v : ByteVec, countOcc v r1.val = countOcc v r2.val) := by
  sorry

end AegisSpec.InvalidTransactions
