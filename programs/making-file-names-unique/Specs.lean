import Aegis.GetFolderNames.Code.Funs

/-!
# Specifications of `Aegis.GetFolderNames.get_folder_names`

LeetCode problem `making-file-names-unique`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetFolderNames

def byteOfNat (n : ℕ) : U8 := ⟨BitVec.ofNat 8 n⟩

def decimalDigits (k : ℕ) : List U8 :=
  match k with
  | 0 => []
  | n + 1 => decimalDigits ((n + 1) / 10) ++ [byteOfNat ((n + 1) % 10 + 48)]
termination_by k
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def numbered (s : List U8) (k : ℕ) : List U8 :=
  s ++ [byteOfNat 40] ++ decimalDigits k ++ [byteOfNat 41]

def AllowedByte (b : U8) : Prop :=
  (97 ≤ b.val ∧ b.val ≤ 122) ∨ (48 ≤ b.val ∧ b.val ≤ 57) ∨ b.val = 40 ∨ b.val = 41

def ValidInput (names : Slice (alloc.vec.Vec U8)) : Prop :=
  1 ≤ names.val.length ∧ names.val.length ≤ 50000 ∧
    ∀ (i : ℕ) (_ : i < names.val.length),
      1 ≤ (names.val[i]).val.length ∧ (names.val[i]).val.length ≤ 20 ∧
        ∀ (b : U8), b ∈ (names.val[i]).val → AllowedByte b

/-- Whenever get_folder_names returns a result r, len(r) = len(names), and for every i with 0 <= i < len(names): if there is no j with 0 <= j < i and r[j] = names[i], then r[i] = names[i]; otherwise r[i] = names[i] ++ '(' ++ decimal(k) ++ ')' where k is the least positive integer such that names[i] ++ '(' ++ decimal(k) ++ ')' is not equal to r[j] for every j with 0 <= j < i. Here decimal(k) is the canonical base-10 representation of positive integer k without leading zeros, and ++ denotes concatenation of byte strings.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_1 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r),
      r.val.length = names.val.length ∧
        ∀ (i : ℕ) (hi : i < names.val.length) (_ : i < r.val.length),
          ((∀ (j : ℕ) (_ : j < i), (r.val[j]).val ≠ (names.val[i]).val) →
              (r.val[i]).val = (names.val[i]).val) ∧
            ((∃ (j : ℕ) (_ : j < i), (r.val[j]).val = (names.val[i]).val) →
              ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k ∧
                ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m < k),
                  ∃ (j : ℕ) (_ : j < i),
                    (r.val[j]).val = numbered (names.val[i]).val m) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r),
      r.val.length = names.val.length ∧
        ∀ (i : ℕ) (hi : i < names.val.length) (_ : i < r.val.length),
          ((∀ (j : ℕ) (_ : j < i), (r.val[j]).val ≠ (names.val[i]).val) →
              (r.val[i]).val = (names.val[i]).val) ∧
            ((∃ (j : ℕ) (_ : j < i), (r.val[j]).val = (names.val[i]).val) →
              ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k ∧
                ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m < k),
                  ∃ (j : ℕ) (_ : j < i),
                    (r.val[j]).val = numbered (names.val[i]).val m)) := by
  sorry

/-- The function get_folder_names returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_2 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∃ r, Aegis.GetFolderNames.get_folder_names names = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∃ r, Aegis.GetFolderNames.get_folder_names names = ok r) := by
  sorry

/-- Whenever get_folder_names returns a result r, len(r) = len(names).
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_3 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r),
      r.val.length = names.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r),
      r.val.length = names.val.length) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i and j with 0 <= i < j < len(names), r[i] != r[j].
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_4 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i j : ℕ) (_ : i < j) (_ : j < names.val.length),
      (r.val[i]).val ≠ (r.val[j]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i j : ℕ) (_ : i < j) (_ : j < names.val.length),
      (r.val[i]).val ≠ (r.val[j]).val) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names), either r[i] = names[i], or there exists a positive integer k such that r[i] = names[i] ++ '(' ++ decimal(k) ++ ')', where decimal(k) is the canonical base-10 representation of k without leading zeros.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_5 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (r.val[i]).val = (names.val[i]).val ∨
        ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (r.val[i]).val = (names.val[i]).val ∨
        ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names), if names[i] is not equal to r[j] for every j with 0 <= j < i, then r[i] = names[i].
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_6 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (∀ (j : ℕ) (_ : j < i), (r.val[j]).val ≠ (names.val[i]).val) →
        (r.val[i]).val = (names.val[i]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (∀ (j : ℕ) (_ : j < i), (r.val[j]).val ≠ (names.val[i]).val) →
        (r.val[i]).val = (names.val[i]).val) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names), if there exists j with 0 <= j < i and r[j] = names[i], then there exists a positive integer k such that r[i] = names[i] ++ '(' ++ decimal(k) ++ ')', where decimal(k) is the canonical base-10 representation of k without leading zeros.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_7 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (∃ (j : ℕ) (_ : j < i), (r.val[j]).val = (names.val[i]).val) →
        ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (∃ (j : ℕ) (_ : j < i), (r.val[j]).val = (names.val[i]).val) →
        ∃ k, 1 ≤ k ∧ (r.val[i]).val = numbered (names.val[i]).val k) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names) and every positive integer k, if r[i] = names[i] ++ '(' ++ decimal(k) ++ ')', then for every positive integer m with 1 <= m < k there exists j with 0 <= j < i and r[j] = names[i] ++ '(' ++ decimal(m) ++ ')'. Here decimal is the canonical base-10 representation without leading zeros.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_8 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (k : ℕ)
      (_ : 1 ≤ k) (_ : (r.val[i]).val = numbered (names.val[i]).val k),
      ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m < k),
        ∃ (j : ℕ) (_ : j < i), (r.val[j]).val = numbered (names.val[i]).val m := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (k : ℕ)
      (_ : 1 ≤ k) (_ : (r.val[i]).val = numbered (names.val[i]).val k),
      ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m < k),
        ∃ (j : ℕ) (_ : j < i), (r.val[j]).val = numbered (names.val[i]).val m) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names) and every j with 0 <= j <= i, there exists t with 0 <= t <= i such that r[t] = names[j].
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_9 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (j : ℕ)
      (_ : j ≤ i),
      ∃ (t : ℕ) (_ : t ≤ i), (r.val[t]).val = (names.val[j]).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (j : ℕ)
      (_ : j ≤ i),
      ∃ (t : ℕ) (_ : t ≤ i), (r.val[t]).val = (names.val[j]).val) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i and j with 0 <= j < i < len(names), r[i] != names[j].
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_10 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i j : ℕ) (_ : j < i) (_ : i < names.val.length),
      (r.val[i]).val ≠ (names.val[j]).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i j : ℕ) (_ : j < i) (_ : i < names.val.length),
      (r.val[i]).val ≠ (names.val[j]).val) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names), len(names[i]) <= len(r[i]) <= len(names[i]) + 7.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_11 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (names.val[i]).val.length ≤ (r.val[i]).val.length ∧
        (r.val[i]).val.length ≤ (names.val[i]).val.length + 7 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length),
      (names.val[i]).val.length ≤ (r.val[i]).val.length ∧
        (r.val[i]).val.length ≤ (names.val[i]).val.length + 7) := by
  sorry

/-- Whenever get_folder_names returns a result r, for every i with 0 <= i < len(names) and every positive integer k, if r[i] = names[i] ++ '(' ++ decimal(k) ++ ')', then k <= i + 1. Here decimal is the canonical base-10 representation without leading zeros.
  Preconditions: names is a slice of byte-vector strings with 1 <= len(names) <= 50000. For every i with 0 <= i < len(names), 1 <= len(names[i]) <= 20, and every byte of names[i] is the ASCII code of a lowercase English letter, a digit, an opening round bracket, or a closing round bracket. -/
theorem spec_12 (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names) :
    ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (k : ℕ)
      (_ : 1 ≤ k) (_ : (r.val[i]).val = numbered (names.val[i]).val k),
      k ≤ i + 1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (names : Slice (alloc.vec.Vec U8)) (h : ValidInput names), ∀ (r : alloc.vec.Vec (alloc.vec.Vec U8)) (_ : Aegis.GetFolderNames.get_folder_names names = ok r)
      (_ : r.val.length = names.val.length) (i : ℕ) (hi : i < names.val.length) (k : ℕ)
      (_ : 1 ≤ k) (_ : (r.val[i]).val = numbered (names.val[i]).val k),
      k ≤ i + 1) := by
  sorry

end AegisSpec.GetFolderNames
