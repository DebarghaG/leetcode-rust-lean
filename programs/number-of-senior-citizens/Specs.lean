import Aegis.CountSeniors.Code.Funs

/-!
# Specifications of `Aegis.CountSeniors.count_seniors`

LeetCode problem `number-of-senior-citizens`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountSeniors

  abbrev Row := Aeneas.Std.alloc.vec.Vec Aeneas.Std.U8

  def byteAt (row : List Aeneas.Std.U8) (j : Nat) : Nat :=
    match row[j]? with
    | some b => b.val
    | none => 0

  def isDigitCode (b : Nat) : Prop := 48 ≤ b ∧ b ≤ 57

  def isGenderCode (b : Nat) : Prop := b = 77 ∨ b = 70 ∨ b = 79

  def ageOf (row : List Aeneas.Std.U8) : Int :=
    10 * ((byteAt row 11 : Int) - 48) + ((byteAt row 12 : Int) - 48)

  def phoneOf (row : List Aeneas.Std.U8) : List Nat := (List.range 10).map (byteAt row)

  def seatOf (row : List Aeneas.Std.U8) : List Nat := [byteAt row 13, byteAt row 14]

  def RowFormat (row : List Aeneas.Std.U8) : Prop :=
    row.length = 15 ∧
      (∀ j, j < 15 → j ≠ 10 → isDigitCode (byteAt row j)) ∧
      isGenderCode (byteAt row 10)

  def RowAgeDigits (row : List Aeneas.Std.U8) : Prop :=
    row.length = 15 ∧ isDigitCode (byteAt row 11) ∧ isDigitCode (byteAt row 12)

  def AllRowsFormatted (rows : List Row) : Prop := ∀ row ∈ rows, RowFormat row.val

  def DistinctIds (rows : List Row) : Prop :=
    rows.Pairwise (fun a b => (phoneOf a.val, seatOf a.val) ≠ (phoneOf b.val, seatOf b.val))

  def seniorCount (rows : List Row) : Nat :=
    (rows.filter (fun row => decide (60 < ageOf row.val))).length

  def juniorCount (rows : List Row) : Nat :=
    (rows.filter (fun row => decide (ageOf row.val ≤ 60))).length

  /-- The function returns a result r, and r = |{ i | 0 <= i < len(details) and age_i > 60 }|.
    Preconditions: 1 <= len(details) <= 100. For every i with 0 <= i < len(details): len(details[i]) = 15; for every j with 0 <= j < 15 and j != 10, details[i][j] is an ASCII decimal digit code (48 <= details[i][j] <= 57); details[i][10] is 77 (M), 70 (F), or 79 (O). The phone numbers details[i][0..9] and seat numbers details[i][13..14] are pairwise distinct. For each i define age_i = 10*(details[i][11]-48) + (details[i][12]-48). -/
  theorem spec_1 (details : Slice Row)
      (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
      (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val) :
      ∃ r, Aegis.CountSeniors.count_seniors details = ok r ∧
        r.val = (seniorCount details.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (details : Slice Row)
        (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
        (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val), ∃ r, Aegis.CountSeniors.count_seniors details = ok r ∧
          r.val = (seniorCount details.val : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail) for every such details.
    Preconditions: len(details) <= 100. For every i with 0 <= i < len(details): len(details[i]) = 15, and details[i][11] and details[i][12] are ASCII decimal digit codes (48 <= details[i][11] <= 57 and 48 <= details[i][12] <= 57). No other format, gender, or distinctness condition is imposed. -/
  theorem spec_2 (details : Slice Row)
      (hlen_le : details.val.length ≤ 100)
      (hfmt : ∀ row ∈ details.val, RowAgeDigits row.val) :
      ∃ r, Aegis.CountSeniors.count_seniors details = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (details : Slice Row)
        (hlen_le : details.val.length ≤ 100)
        (hfmt : ∀ row ∈ details.val, RowAgeDigits row.val), ∃ r, Aegis.CountSeniors.count_seniors details = ok r) := by
    sorry

  /-- Whenever the function returns a result r for such details, 0 <= r <= len(details).
    Preconditions: len(details) <= 100. For every i with 0 <= i < len(details): len(details[i]) = 15, and details[i][11] and details[i][12] are ASCII decimal digit codes (48 <= details[i][11] <= 57 and 48 <= details[i][12] <= 57). No other format, gender, or distinctness condition is imposed. -/
  theorem spec_3 (details : Slice Row)
      (hlen_le : details.val.length ≤ 100)
      (hfmt : ∀ row ∈ details.val, RowAgeDigits row.val) :
      ∀ r, Aegis.CountSeniors.count_seniors details = ok r →
        0 ≤ r.val ∧ r.val ≤ (details.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (details : Slice Row)
        (hlen_le : details.val.length ≤ 100)
        (hfmt : ∀ row ∈ details.val, RowAgeDigits row.val), ∀ r, Aegis.CountSeniors.count_seniors details = ok r →
          0 ≤ r.val ∧ r.val ≤ (details.val.length : Int)) := by
    sorry

  /-- The function returns a result r, and r + |{ i | 0 <= i < len(details) and age_i <= 60 }| = len(details).
    Preconditions: The full well-formedness conditions hold: 1 <= len(details) <= 100; each details[i] has length 15; positions other than 10 are ASCII decimal digits (48..57); position 10 is 77, 70, or 79; phone and seat numbers are pairwise distinct. For each i define age_i = 10*(details[i][11]-48) + (details[i][12]-48). -/
  theorem spec_4 (details : Slice Row)
      (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
      (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val) :
      ∃ r, Aegis.CountSeniors.count_seniors details = ok r ∧
        r.val + (juniorCount details.val : Int) = (details.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (details : Slice Row)
        (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
        (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val), ∃ r, Aegis.CountSeniors.count_seniors details = ok r ∧
          r.val + (juniorCount details.val : Int) = (details.val.length : Int)) := by
    sorry

  /-- Whenever the function returns r for details, rA for detailsA, and rB for detailsB, r = rA + rB.
    Preconditions: details, detailsA, and detailsB are slices of byte vectors. details is the concatenation of detailsA and detailsB: len(details) = len(detailsA)+len(detailsB), details[i] = detailsA[i] for 0 <= i < len(detailsA), and details[len(detailsA)+i] = detailsB[i] for 0 <= i < len(detailsB). len(details) <= 100, and detailsA and detailsB are nonempty. Every element of all three slices has length 15, positions other than 10 are ASCII decimal digits (48..57), and position 10 is 77, 70, or 79. For each string define its age by 10*(byte[11]-48)+(byte[12]-48). -/
  theorem spec_5 (details detailsA detailsB : Slice Row)
      (hlen : details.val.length = detailsA.val.length + detailsB.val.length)
      (hcatA : ∀ i, i < detailsA.val.length → details.val[i]? = detailsA.val[i]?)
      (hcatB : ∀ i, i < detailsB.val.length →
        details.val[detailsA.val.length + i]? = detailsB.val[i]?)
      (hlen_le : details.val.length ≤ 100)
      (hneA : 0 < detailsA.val.length) (hneB : 0 < detailsB.val.length)
      (hfmt : ∀ row ∈ details.val, RowFormat row.val)
      (hfmtA : ∀ row ∈ detailsA.val, RowFormat row.val)
      (hfmtB : ∀ row ∈ detailsB.val, RowFormat row.val) :
      ∀ r rA rB, Aegis.CountSeniors.count_seniors details = ok r →
        Aegis.CountSeniors.count_seniors detailsA = ok rA →
        Aegis.CountSeniors.count_seniors detailsB = ok rB → r.val = rA.val + rB.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (details detailsA detailsB : Slice Row)
        (hlen : details.val.length = detailsA.val.length + detailsB.val.length)
        (hcatA : ∀ i, i < detailsA.val.length → details.val[i]? = detailsA.val[i]?)
        (hcatB : ∀ i, i < detailsB.val.length →
          details.val[detailsA.val.length + i]? = detailsB.val[i]?)
        (hlen_le : details.val.length ≤ 100)
        (hneA : 0 < detailsA.val.length) (hneB : 0 < detailsB.val.length)
        (hfmt : ∀ row ∈ details.val, RowFormat row.val)
        (hfmtA : ∀ row ∈ detailsA.val, RowFormat row.val)
        (hfmtB : ∀ row ∈ detailsB.val, RowFormat row.val), ∀ r rA rB, Aegis.CountSeniors.count_seniors details = ok r →
          Aegis.CountSeniors.count_seniors detailsA = ok rA →
          Aegis.CountSeniors.count_seniors detailsB = ok rB → r.val = rA.val + rB.val) := by
    sorry

  /-- Whenever the function returns r for details and r_prime for details_prime, r = r_prime.
    Preconditions: details and details_prime are slices of byte vectors. Both satisfy the full well-formedness conditions: lengths between 1 and 100; every element has length 15; positions other than 10 are ASCII decimal digits (48..57); position 10 is 77, 70, or 79; phone and seat numbers are pairwise distinct. details_prime is a permutation of details: there is a bijection pi from {0,...,len(details)-1} to {0,...,len(details_prime)-1} such that details_prime[pi(i)] = details[i] for every i. -/
  theorem spec_6 (details details_prime : Slice Row)
      (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
      (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val)
      (hlen_ge' : 1 ≤ details_prime.val.length) (hlen_le' : details_prime.val.length ≤ 100)
      (hfmt' : AllRowsFormatted details_prime.val) (hids' : DistinctIds details_prime.val)
      (hperm : details_prime.val.Perm details.val) :
      ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
        Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
        r.val = r_prime.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (details details_prime : Slice Row)
        (hlen_ge : 1 ≤ details.val.length) (hlen_le : details.val.length ≤ 100)
        (hfmt : AllRowsFormatted details.val) (hids : DistinctIds details.val)
        (hlen_ge' : 1 ≤ details_prime.val.length) (hlen_le' : details_prime.val.length ≤ 100)
        (hfmt' : AllRowsFormatted details_prime.val) (hids' : DistinctIds details_prime.val)
        (hperm : details_prime.val.Perm details.val), ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
          Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
          r.val = r_prime.val) := by
    sorry

  /-- Whenever the function returns r for details and r_prime for details_prime, r_prime >= r.
    Preconditions: details and details_prime are slices of byte vectors with len(details) = len(details_prime) <= 100. For every i with 0 <= i < len(details): len(details[i]) = len(details_prime[i]) = 15; positions other than 10 are ASCII decimal digits (48..57); position 10 is 77, 70, or 79. Define age_i = 10*(details[i][11]-48)+(details[i][12]-48) and age_prime_i = 10*(details_prime[i][11]-48)+(details_prime[i][12]-48). Assume for every i, age_prime_i >= age_i. -/
  theorem spec_7 (details details_prime : Slice Row)
      (hlen_eq : details.val.length = details_prime.val.length)
      (hlen_le : details.val.length ≤ 100)
      (hfmt : ∀ i (hi : i < details.val.length),
        RowFormat (details.val[i]'hi).val ∧
          RowFormat (details_prime.val[i]'(hlen_eq ▸ hi)).val)
      (hmono : ∀ i (hi : i < details.val.length),
        ageOf (details.val[i]'hi).val ≤ ageOf (details_prime.val[i]'(hlen_eq ▸ hi)).val) :
      ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
        Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
        r.val ≤ r_prime.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (details details_prime : Slice Row)
        (hlen_eq : details.val.length = details_prime.val.length)
        (hlen_le : details.val.length ≤ 100)
        (hfmt : ∀ i (hi : i < details.val.length),
          RowFormat (details.val[i]'hi).val ∧
            RowFormat (details_prime.val[i]'(hlen_eq ▸ hi)).val)
        (hmono : ∀ i (hi : i < details.val.length),
          ageOf (details.val[i]'hi).val ≤ ageOf (details_prime.val[i]'(hlen_eq ▸ hi)).val), ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
          Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
          r.val ≤ r_prime.val) := by
    sorry

  /-- Whenever the function returns r for details and r_prime for details_prime, r_prime = r + 1.
    Preconditions: details and details_prime are slices of byte vectors with len(details) = len(details_prime) <= 100. For every i with 0 <= i < len(details): len(details[i]) = len(details_prime[i]) = 15; positions other than 10 are ASCII decimal digits (48..57); position 10 is 77, 70, or 79. Define age_i = 10*(details[i][11]-48)+(details[i][12]-48) and age_prime_i = 10*(details_prime[i][11]-48)+(details_prime[i][12]-48). There is exactly one index k with 0 <= k < len(details) such that age_k <= 60 and age_prime_k > 60; for every i with 0 <= i < len(details) and i != k, age_prime_i = age_i. -/
  theorem spec_8 (details details_prime : Slice Row)
      (hlen_eq : details.val.length = details_prime.val.length)
      (hlen_le : details.val.length ≤ 100)
      (hfmt : ∀ i (hi : i < details.val.length),
        RowFormat (details.val[i]'hi).val ∧
          RowFormat (details_prime.val[i]'(hlen_eq ▸ hi)).val)
      (hstep : ∃ (k : Nat) (hk : k < details.val.length),
        ageOf (details.val[k]'hk).val ≤ 60 ∧
          60 < ageOf (details_prime.val[k]'(hlen_eq ▸ hk)).val ∧
          (∀ i (hi : i < details.val.length), i ≠ k →
            ageOf (details.val[i]'hi).val =
              ageOf (details_prime.val[i]'(hlen_eq ▸ hi)).val)) :
      ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
        Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
        r_prime.val = r.val + 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (details details_prime : Slice Row)
        (hlen_eq : details.val.length = details_prime.val.length)
        (hlen_le : details.val.length ≤ 100)
        (hfmt : ∀ i (hi : i < details.val.length),
          RowFormat (details.val[i]'hi).val ∧
            RowFormat (details_prime.val[i]'(hlen_eq ▸ hi)).val)
        (hstep : ∃ (k : Nat) (hk : k < details.val.length),
          ageOf (details.val[k]'hk).val ≤ 60 ∧
            60 < ageOf (details_prime.val[k]'(hlen_eq ▸ hk)).val ∧
            (∀ i (hi : i < details.val.length), i ≠ k →
              ageOf (details.val[i]'hi).val =
                ageOf (details_prime.val[i]'(hlen_eq ▸ hi)).val)), ∀ r r_prime, Aegis.CountSeniors.count_seniors details = ok r →
          Aegis.CountSeniors.count_seniors details_prime = ok r_prime →
          r_prime.val = r.val + 1) := by
    sorry

  end AegisSpec.CountSeniors
