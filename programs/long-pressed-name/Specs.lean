import Aegis.IsLongPressedName.Code.Funs

/-!
# Specifications of `Aegis.IsLongPressedName.is_long_pressed_name`

LeetCode problem `long-pressed-name`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsLongPressedName

def IsLowerAsciiByte (b : Std.U8) : Prop :=
  97 ≤ b.val ∧ b.val ≤ 122

def AllLowerAscii (s : Slice Std.U8) : Prop :=
  ∀ b, b ∈ s.val → IsLowerAsciiByte b

def bytesOf (s : Slice Std.U8) : List ℕ :=
  s.val.map (fun b => b.val)

def rleStep (acc : List (ℕ × ℕ)) (b : ℕ) : List (ℕ × ℕ) :=
  match acc with
  | [] => [(b, 1)]
  | (c, n) :: rest => if c = b then (c, n + 1) :: rest else (b, 1) :: acc

def rle (l : List ℕ) : List (ℕ × ℕ) :=
  (l.foldl rleStep []).reverse

def compressed (l : List ℕ) : List ℕ :=
  (rle l).map (fun p => p.1)

def IsSubsequence (a b : List ℕ) : Prop :=
  ∃ js : List ℕ,
    js.length = a.length ∧
    js.Pairwise (· < ·) ∧
    (∀ j, j ∈ js → j < b.length) ∧
    js.map (fun j => b.getD j 0) = a

def occurrences (l : List ℕ) (c : ℕ) : ℕ :=
  l.count c

/-- Whenever is_long_pressed_name(name, typed) returns a result r, we have r = true if and only if the following condition holds. Decompose name into its maximal nonempty contiguous runs of equal bytes, written as (c_0,a_0),...,(c_{k-1},a_{k-1}), where c_i is the byte of the i-th run and a_i is its length, and adjacent runs have different bytes. Decompose typed similarly as (d_0,b_0),...,(d_{m-1},b_{m-1}). Then k = m, and for every i with 0 <= i < k, c_i = d_i and b_i >= a_i.
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_1 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔
        (rle (bytesOf «name»)).length = (rle (bytesOf typed)).length ∧
        ∀ i, i < (rle (bytesOf «name»)).length →
          ∃ c a b, (rle (bytesOf «name»))[i]? = some (c, a) ∧
                   (rle (bytesOf typed))[i]? = some (c, b) ∧
                   a ≤ b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔
        (rle (bytesOf «name»)).length = (rle (bytesOf typed)).length ∧
        ∀ i, i < (rle (bytesOf «name»)).length →
          ∃ c a b, (rle (bytesOf «name»))[i]? = some (c, a) ∧
                   (rle (bytesOf typed))[i]? = some (c, b) ∧
                   a ≤ b)) := by
  sorry

/-- For every name and typed satisfying the preconditions, is_long_pressed_name(name, typed) returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_2 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∃ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∃ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, we have len(name) <= len(typed).
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_3 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      «name».val.length ≤ typed.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      «name».val.length ≤ typed.val.length) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, we have name[0] = typed[0].
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_4 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      (bytesOf «name»)[0]? = (bytesOf typed)[0]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      (bytesOf «name»)[0]? = (bytesOf typed)[0]?) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, we have name[len(name)-1] = typed[len(typed)-1].
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_5 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      (bytesOf «name»)[«name».val.length - 1]? =
        (bytesOf typed)[typed.val.length - 1]? := by
  sorry

theorem spec_5_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      (bytesOf «name»)[«name».val.length - 1]? =
        (bytesOf typed)[typed.val.length - 1]?) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r, we have r = true if and only if for every i with 0 <= i < len(name), name[i] = typed[i].
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, every byte of both lies in the lowercase ASCII range 97 through 122 inclusive, and len(name) = len(typed). -/
theorem spec_6 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hlen : «name».val.length = typed.val.length) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔ ∀ i, i < «name».val.length →
        (bytesOf «name»)[i]? = (bytesOf typed)[i]?) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hlen : «name».val.length = typed.val.length), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔ ∀ i, i < «name».val.length →
        (bytesOf «name»)[i]? = (bytesOf typed)[i]?)) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, name is a subsequence of typed: there exist indices j_0 < j_1 < ... < j_{len(name)-1} with 0 <= j_0 and j_{len(name)-1} < len(typed), such that typed[j_i] = name[i] for every i with 0 <= i < len(name).
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_7 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      IsSubsequence (bytesOf «name») (bytesOf typed) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      IsSubsequence (bytesOf «name») (bytesOf typed)) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, for every byte c with 0 <= c < 256, the number of indices i with 0 <= i < len(typed) and typed[i] = c is at least the number of indices i with 0 <= i < len(name) and name[i] = c.
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_8 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      ∀ c, c < 256 → occurrences (bytesOf «name») c ≤ occurrences (bytesOf typed) c := by
  sorry

theorem spec_8_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      ∀ c, c < 256 → occurrences (bytesOf «name») c ≤ occurrences (bytesOf typed) c) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r and r = true, the sequence obtained by replacing each maximal nonempty run of equal bytes in name by that single byte is equal, element for element, to the sequence obtained the same way from typed.
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, and every byte of both lies in the lowercase ASCII range 97 through 122 inclusive. -/
theorem spec_9 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      compressed (bytesOf «name») = compressed (bytesOf typed) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      compressed (bytesOf «name») = compressed (bytesOf typed)) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r, we have r = false.
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, every byte of both lies in the lowercase ASCII range 97 through 122 inclusive, and there exists a byte c with 97 <= c <= 122 such that c occurs in typed but c does not occur in name. -/
theorem spec_10 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hwitness : ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ c ∈ bytesOf typed ∧ c ∉ bytesOf «name») :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = false := by
  sorry

theorem spec_10_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hwitness : ∃ c, 97 ≤ c ∧ c ≤ 122 ∧ c ∈ bytesOf typed ∧ c ∉ bytesOf «name»), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = false) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r, we have r = true.
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, every byte of both lies in the lowercase ASCII range 97 through 122 inclusive, and there exists an index i with 0 <= i < len(name) such that len(typed) = len(name) + 1, typed[j] = name[j] for every j with 0 <= j <= i, typed[i+1] = name[i], and typed[j+1] = name[j] for every j with i+1 <= j < len(name). -/
theorem spec_11 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hwitness : ∃ i, i < «name».val.length ∧
      typed.val.length = «name».val.length + 1 ∧
      (∀ j, j ≤ i → (bytesOf typed)[j]? = (bytesOf «name»)[j]?) ∧
      (bytesOf typed)[i + 1]? = (bytesOf «name»)[i]? ∧
      (∀ j, i + 1 ≤ j → j < «name».val.length →
        (bytesOf typed)[j + 1]? = (bytesOf «name»)[j]?)) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true := by
  sorry

theorem spec_11_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hwitness : ∃ i, i < «name».val.length ∧
      typed.val.length = «name».val.length + 1 ∧
      (∀ j, j ≤ i → (bytesOf typed)[j]? = (bytesOf «name»)[j]?) ∧
      (bytesOf typed)[i + 1]? = (bytesOf «name»)[i]? ∧
      (∀ j, i + 1 ≤ j → j < «name».val.length →
        (bytesOf typed)[j + 1]? = (bytesOf «name»)[j]?)), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r with r = true and is_long_pressed_name(name, typed2) returns a result r2, we have r2 = true.
  Preconditions: name, typed, and typed2 are nonempty byte slices with lengths between 1 and 1000, every byte of all three lies in the lowercase ASCII range 97 through 122 inclusive, and typed2 is obtained from typed by increasing the length of exactly one maximal nonempty run: there exist indices l,u with 0 <= l < u <= len(typed), a byte c, and an integer d >= 1 such that typed[j] = c for every j with l <= j < u; l = 0 or typed[l-1] != c; u = len(typed) or typed[u] != c; len(typed2) = len(typed) + d; typed2[j] = typed[j] for every j with 0 <= j < l; typed2[j] = c for every j with l <= j < u + d; and typed2[j+d] = typed[j] for every j with u <= j < len(typed). -/
theorem spec_12 («name» typed typed2 : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (htyped2_len : 1 ≤ typed2.val.length) (htyped2_ub : typed2.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (htyped2_lower : AllLowerAscii typed2)
    (hlengthen : ∃ (l u c d : ℕ), l < u ∧ u ≤ typed.val.length ∧ 1 ≤ d ∧
      (∀ j, l ≤ j → j < u → (bytesOf typed)[j]? = some c) ∧
      (l = 0 ∨ (bytesOf typed)[l - 1]? ≠ some c) ∧
      (u = typed.val.length ∨ (bytesOf typed)[u]? ≠ some c) ∧
      typed2.val.length = typed.val.length + d ∧
      (∀ j, j < l → (bytesOf typed2)[j]? = (bytesOf typed)[j]?) ∧
      (∀ j, l ≤ j → j < u + d → (bytesOf typed2)[j]? = some c) ∧
      (∀ j, u ≤ j → j < typed.val.length →
        (bytesOf typed2)[j + d]? = (bytesOf typed)[j]?)) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      ∀ r2, Aegis.IsLongPressedName.is_long_pressed_name «name» typed2 = ok r2 → r2 = true := by
  sorry

theorem spec_12_neg :
    ¬ (∀ («name» typed typed2 : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (htyped2_len : 1 ≤ typed2.val.length) (htyped2_ub : typed2.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (htyped2_lower : AllLowerAscii typed2)
    (hlengthen : ∃ (l u c d : ℕ), l < u ∧ u ≤ typed.val.length ∧ 1 ≤ d ∧
      (∀ j, l ≤ j → j < u → (bytesOf typed)[j]? = some c) ∧
      (l = 0 ∨ (bytesOf typed)[l - 1]? ≠ some c) ∧
      (u = typed.val.length ∨ (bytesOf typed)[u]? ≠ some c) ∧
      typed2.val.length = typed.val.length + d ∧
      (∀ j, j < l → (bytesOf typed2)[j]? = (bytesOf typed)[j]?) ∧
      (∀ j, l ≤ j → j < u + d → (bytesOf typed2)[j]? = some c) ∧
      (∀ j, u ≤ j → j < typed.val.length →
        (bytesOf typed2)[j + d]? = (bytesOf typed)[j]?)), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r → r = true →
      ∀ r2, Aegis.IsLongPressedName.is_long_pressed_name «name» typed2 = ok r2 → r2 = true) := by
  sorry

/-- Whenever is_long_pressed_name(name, typed) returns a result r, we have r = true if and only if for every i with 0 <= i < len(typed), typed[i] = name[0].
  Preconditions: name and typed are nonempty byte slices with 1 <= len(name), len(typed) <= 1000, every byte of both lies in the lowercase ASCII range 97 through 122 inclusive, and len(name) = 1. -/
theorem spec_13 («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hname_one : «name».val.length = 1) :
    ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔ ∀ i, i < typed.val.length →
        (bytesOf typed)[i]? = (bytesOf «name»)[0]?) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ («name» typed : Slice Std.U8)
    (hname_len : 1 ≤ «name».val.length) (hname_ub : «name».val.length ≤ 1000)
    (htyped_len : 1 ≤ typed.val.length) (htyped_ub : typed.val.length ≤ 1000)
    (hname_lower : AllLowerAscii «name») (htyped_lower : AllLowerAscii typed)
    (hname_one : «name».val.length = 1), ∀ r, Aegis.IsLongPressedName.is_long_pressed_name «name» typed = ok r →
      (r = true ↔ ∀ i, i < typed.val.length →
        (bytesOf typed)[i]? = (bytesOf «name»)[0]?)) := by
  sorry

end AegisSpec.IsLongPressedName
