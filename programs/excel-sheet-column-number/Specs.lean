import Aegis.TitleToNumber.Code.Funs

/-!
# Specifications of `Aegis.TitleToNumber.title_to_number`

LeetCode problem `excel-sheet-column-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.TitleToNumber

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat :=
    if h : i < s.val.length then (s.val[i]).val else 0

  def excelNumber (s : Slice Std.U8) : Int :=
    Finset.sum (Finset.range s.val.length)
      (fun i => ((byteAt s i : Int) - 64) * 26 ^ (s.val.length - 1 - i))

  def allUpper (s : Slice Std.U8) : Prop :=
    ∀ i, i < s.val.length → 65 ≤ byteAt s i ∧ byteAt s i ≤ 90

  def lexLt (s t : Slice Std.U8) : Prop :=
    ∃ j, j < s.val.length ∧ byteAt s j < byteAt t j ∧ ∀ k, k < j → byteAt s k = byteAt t k

  /-- The function returns a result r and r = sum_{i=0}^{n-1} (columnTitle[i] - 64) * 26^{n-1-i}, with 26^0 = 1. This is the usual Excel column number: A = 1, B = 2, ..., Z = 26, AA = 27, AB = 28, etc.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90 (so columnTitle[i] is an uppercase ASCII letter); and the Excel column number of columnTitle, as defined in the statement, is at most 2,147,483,647. -/
  theorem spec_1 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647) :
      ∃ r : Std.I64,
        Aegis.TitleToNumber.title_to_number columnTitle = ok r ∧ r.val = excelNumber columnTitle := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647), ∃ r : Std.I64,
          Aegis.TitleToNumber.title_to_number columnTitle = ok r ∧ r.val = excelNumber columnTitle) := by
    sorry

  /-- The function returns a result r (an I64 value) and does not fail: it does not panic, overflow, or access memory out of bounds.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_2 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647) :
      ∃ r : Std.I64, Aegis.TitleToNumber.title_to_number columnTitle = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647), ∃ r : Std.I64, Aegis.TitleToNumber.title_to_number columnTitle = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= (26^n - 1)/25, where the division is exact.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_3 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r) :
      r.val ≥ (26 ^ columnTitle.val.length - 1) / 25 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r), r.val ≥ (26 ^ columnTitle.val.length - 1) / 25) := by
    sorry

  /-- Whenever the function returns a result r, r <= 26*(26^n - 1)/25.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_4 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r) :
      r.val ≤ 26 * (26 ^ columnTitle.val.length - 1) / 25 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r), r.val ≤ 26 * (26 ^ columnTitle.val.length - 1) / 25) := by
    sorry

  /-- Whenever the function returns a result r, the non-negative remainder of r modulo 26 equals the non-negative remainder of (columnTitle[n-1] - 64) modulo 26.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_5 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r) :
      r.val % 26 = ((byteAt columnTitle (columnTitle.val.length - 1) : Int) - 64) % 26 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r), r.val % 26 = ((byteAt columnTitle (columnTitle.val.length - 1) : Int) - 64) % 26) := by
    sorry

  /-- Whenever the function returns a result r, r >= (columnTitle[0] - 64) * 26^{n-1} + (26^{n-1} - 1)/25.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_6 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r) :
      r.val ≥ ((byteAt columnTitle 0 : Int) - 64) * 26 ^ (columnTitle.val.length - 1) +
        (26 ^ (columnTitle.val.length - 1) - 1) / 25 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r), r.val ≥ ((byteAt columnTitle 0 : Int) - 64) * 26 ^ (columnTitle.val.length - 1) +
          (26 ^ (columnTitle.val.length - 1) - 1) / 25) := by
    sorry

  /-- Whenever the function returns a result r, r <= (columnTitle[0] - 64) * 26^{n-1} + 26*(26^{n-1} - 1)/25.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_7 (columnTitle : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r) :
      r.val ≤ ((byteAt columnTitle 0 : Int) - 64) * 26 ^ (columnTitle.val.length - 1) +
        26 * (26 ^ (columnTitle.val.length - 1) - 1) / 25 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (columnTitle : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        {r : Std.I64} (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r), r.val ≤ ((byteAt columnTitle 0 : Int) - 64) * 26 ^ (columnTitle.val.length - 1) +
          26 * (26 ^ (columnTitle.val.length - 1) - 1) / 25) := by
    sorry

  /-- For any byte slice t satisfying the same preconditions (len(t)=n, all bytes in 65..90, and Excel column number at most 2,147,483,647) and any index i with 0 <= i < n, if t[j] = columnTitle[j] for every j with 0 <= j < n and j != i, then whenever title_to_number(columnTitle) returns r and title_to_number(t) returns r_t, we have r_t = r + (t[i] - columnTitle[i]) * 26^{n-1-i}.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_8 (columnTitle t : Slice Std.U8) (i : Nat)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      (htlen : t.val.length = columnTitle.val.length)
      (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
      (hi : i < columnTitle.val.length)
      (hagree : ∀ j, j < columnTitle.val.length → j ≠ i → byteAt t j = byteAt columnTitle j)
      {r r_t : Std.I64}
      (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
      (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t) :
      r_t.val = r.val +
        ((byteAt t i : Int) - (byteAt columnTitle i : Int)) *
          26 ^ (columnTitle.val.length - 1 - i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (columnTitle t : Slice Std.U8) (i : Nat)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        (htlen : t.val.length = columnTitle.val.length)
        (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
        (hi : i < columnTitle.val.length)
        (hagree : ∀ j, j < columnTitle.val.length → j ≠ i → byteAt t j = byteAt columnTitle j)
        {r r_t : Std.I64}
        (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
        (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t), r_t.val = r.val +
          ((byteAt t i : Int) - (byteAt columnTitle i : Int)) *
            26 ^ (columnTitle.val.length - 1 - i)) := by
    sorry

  /-- For any byte slice t satisfying the same preconditions (len(t)=n, all bytes in 65..90, and Excel column number at most 2,147,483,647), if columnTitle is lexicographically smaller than t (there is an index j with 0 <= j < n such that columnTitle[j] < t[j] and columnTitle[k] = t[k] for all 0 <= k < j), then whenever title_to_number(columnTitle) returns r and title_to_number(t) returns r_t, we have r < r_t.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_9 (columnTitle t : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      (htlen : t.val.length = columnTitle.val.length)
      (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
      (hlt : lexLt columnTitle t)
      {r r_t : Std.I64}
      (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
      (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t) :
      r.val < r_t.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (columnTitle t : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        (htlen : t.val.length = columnTitle.val.length)
        (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
        (hlt : lexLt columnTitle t)
        {r r_t : Std.I64}
        (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
        (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t), r.val < r_t.val) := by
    sorry

  /-- For any byte slice t satisfying the same preconditions (all bytes in 65..90 and Excel column number at most 2,147,483,647), if len(t) = n + 1 (which requires n <= 6), then whenever title_to_number(columnTitle) returns r and title_to_number(t) returns r_t, we have r < r_t.
    Preconditions: Let n = len(columnTitle). Assume 1 <= n <= 7; for every i with 0 <= i < n, 65 <= columnTitle[i] <= 90; and the Excel column number of columnTitle is at most 2,147,483,647. -/
  theorem spec_10 (columnTitle t : Slice Std.U8)
      (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
      (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
      (htlen : t.val.length = columnTitle.val.length + 1)
      (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
      {r r_t : Std.I64}
      (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
      (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t) :
      r.val < r_t.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (columnTitle t : Slice Std.U8)
        (hn1 : 1 ≤ columnTitle.val.length) (hn7 : columnTitle.val.length ≤ 7)
        (hup : allUpper columnTitle) (hbound : excelNumber columnTitle ≤ 2147483647)
        (htlen : t.val.length = columnTitle.val.length + 1)
        (htup : allUpper t) (htbound : excelNumber t ≤ 2147483647)
        {r r_t : Std.I64}
        (hr : Aegis.TitleToNumber.title_to_number columnTitle = ok r)
        (hrt : Aegis.TitleToNumber.title_to_number t = ok r_t), r.val < r_t.val) := by
    sorry

  end AegisSpec.TitleToNumber
