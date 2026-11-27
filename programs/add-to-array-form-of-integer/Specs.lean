import Aegis.AddToArrayForm.Code.Funs

/-!
# Specifications of `Aegis.AddToArrayForm.add_to_array_form`

LeetCode problem `add-to-array-form-of-integer`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.AddToArrayForm (add_to_array_form)

  namespace AegisSpec.AddToArrayForm

  def arrayVal (a : List Std.I64) : Int :=
    a.foldl (fun acc d => acc * 10 + d.val) 0

  def IsDigitList (a : List Std.I64) : Prop :=
    ∀ (i : Nat) (h : i < a.length), 0 ≤ (a[i]).val ∧ (a[i]).val ≤ 9

  def firstDigit (a : List Std.I64) : Int := (a.headD default).val

  def lastDigit (a : List Std.I64) : Int := (a.getLastD default).val

  def digitAt (a : List Std.I64) (i : Nat) : Int := (a.getD i default).val

  def digitSum (a : List Std.I64) : Int := (a.map (fun d => d.val)).sum

  def IsValidNum (num : Aeneas.Std.Slice Std.I64) : Prop :=
    1 ≤ num.val.length ∧ num.val.length ≤ 10000 ∧ IsDigitList num.val ∧
      (1 < num.val.length → firstDigit num.val ≠ 0)

  def IsValidK (k : Std.I64) : Prop := 1 ≤ k.val ∧ k.val ≤ 10000

  /-- Whenever the function returns a result r, r is the array-form of the integer val(num) + k. That is: (a) len(r) >= 1; (b) for every i with 0 <= i < len(r), 0 <= r[i] <= 9; (c) r[0] != 0; (d) val(r) = val(num) + k, where val(a) = sum_{i=0}^{len(a)-1} a[i] * 10^{len(a)-1-i} for any digit array a.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_1 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r →
        1 ≤ r.val.length ∧
          IsDigitList r.val ∧
          firstDigit r.val ≠ 0 ∧
          arrayVal r.val = arrayVal num.val + k.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r →
          1 ≤ r.val.length ∧
            IsDigitList r.val ∧
            firstDigit r.val ≠ 0 ∧
            arrayVal r.val = arrayVal num.val + k.val) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_2 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∃ r, add_to_array_form num k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∃ r, add_to_array_form num k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) >= len(num).
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_3 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r → num.val.length ≤ r.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r → num.val.length ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r, len(r) <= max(len(num), 5) + 1.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_4 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r →
        r.val.length ≤ max num.val.length 5 + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r →
          r.val.length ≤ max num.val.length 5 + 1) := by
    sorry

  /-- Whenever the function returns a result r, r[len(r)-1] = (num[len(num)-1] + k) mod 10.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_5 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r →
        lastDigit r.val = (lastDigit num.val + k.val) % 10 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r →
          lastDigit r.val = (lastDigit num.val + k.val) % 10) := by
    sorry

  /-- Whenever the function returns a result r, (sum_{i=0}^{len(r)-1} r[i]) mod 9 = (sum_{i=0}^{len(num)-1} num[i] + k) mod 9.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_6 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r →
        digitSum r.val % 9 = (digitSum num.val + k.val) % 9 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r →
          digitSum r.val % 9 = (digitSum num.val + k.val) % 9) := by
    sorry

  /-- Whenever the function returns a result r and len(r) > len(num), then r[0] = 1.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_7 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r → num.val.length < r.val.length →
        firstDigit r.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r → num.val.length < r.val.length →
          firstDigit r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, if k < 10 and num[len(num)-1] + k < 10, then len(r) = len(num), r[len(num)-1] = num[len(num)-1] + k, and for every i with 0 <= i < len(num)-1, r[i] = num[i].
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_8 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r → k.val < 10 → lastDigit num.val + k.val < 10 →
        r.val.length = num.val.length ∧
          lastDigit r.val = lastDigit num.val + k.val ∧
          (∀ i, i < num.val.length - 1 → digitAt r.val i = digitAt num.val i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r → k.val < 10 → lastDigit num.val + k.val < 10 →
          r.val.length = num.val.length ∧
            lastDigit r.val = lastDigit num.val + k.val ∧
            (∀ i, i < num.val.length - 1 → digitAt r.val i = digitAt num.val i)) := by
    sorry

  /-- Whenever the function returns a result r and len(num) >= 5, len(r) is either len(num) or len(num) + 1.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_9 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r → 5 ≤ num.val.length →
        r.val.length = num.val.length ∨ r.val.length = num.val.length + 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r → 5 ≤ num.val.length →
          r.val.length = num.val.length ∨ r.val.length = num.val.length + 1) := by
    sorry

  /-- Whenever the function returns a result r and len(num) < 5, len(r) <= 5.
    Preconditions: 1 <= len(num) <= 10000; for every i with 0 <= i < len(num), 0 <= num[i] <= 9; if len(num) > 1 then num[0] != 0 (no leading zeros except for the single zero); 1 <= k <= 10000. -/
  theorem spec_10 (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
      (hnum : IsValidNum num) (hk : IsValidK k) :
      ∀ r, add_to_array_form num k = ok r → num.val.length < 5 → r.val.length ≤ 5 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Aeneas.Std.Slice Std.I64) (k : Std.I64)
        (hnum : IsValidNum num) (hk : IsValidK k), ∀ r, add_to_array_form num k = ok r → num.val.length < 5 → r.val.length ≤ 5) := by
    sorry

  end AegisSpec.AddToArrayForm
