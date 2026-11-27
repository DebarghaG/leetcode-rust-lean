import Aegis.SplitIntoFibonacci.Code.Funs

/-!
# Specifications of `Aegis.SplitIntoFibonacci.split_into_fibonacci`

LeetCode problem `split-array-into-fibonacci-sequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SplitIntoFibonacci

  open Aeneas.Std Aeneas.Std.Result Aegis.SplitIntoFibonacci

  def dec (x : Int) : List U8 :=
    (Nat.repr x.toNat).toList.map (fun c => UScalar.mk (BitVec.ofNat 8 c.toNat))

  def substr {α : Type} (l : List α) (i j : Nat) : List α := (l.drop i).take (j - i)

  def IsFibSplit (num : List U8) (g : List I64) : Prop :=
    3 ≤ g.length ∧
      (∀ i, (h : i < g.length) → 0 ≤ g[i].val ∧ g[i].val < (2 : Int) ^ 31) ∧
        (∀ i, (h : i + 2 < g.length) → g[i].val + g[i + 1].val = g[i + 2].val) ∧
          num = (g.map fun x => dec x.val).flatten

  /-- Let dec(x), for an integer x with 0 <= x < 2^31, be the unique nonempty ASCII decimal digit string with no leading '0' except that dec(0) is the one-character string '0'. Call a vector g of i64 a valid Fibonacci split of num if: (1) len(g) >= 3; (2) for every i with 0 <= i < len(g), 0 <= g[i] < 2^31; (3) for every i with 0 <= i < len(g)-2, g[i] + g[i+1] = g[i+2] as ordinary integers; and (4) the byte string num is exactly the concatenation dec(g[0]) dec(g[1]) ... dec(g[len(g)-1]) encoded as ASCII, byte-for-byte. The function returns a result r and: if there exists at least one valid Fibonacci split of num, then r is a valid Fibonacci split of num; if no valid Fibonacci split of num exists, then r = [].
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_1 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : alloc.vec.Vec I64,
        split_into_fibonacci num = ok r ∧
          ((∃ g : List I64, IsFibSplit num.val g) → IsFibSplit num.val r.val) ∧
            ((¬ ∃ g : List I64, IsFibSplit num.val g) → r.val = []) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : alloc.vec.Vec I64,
          split_into_fibonacci num = ok r ∧
            ((∃ g : List I64, IsFibSplit num.val g) → IsFibSplit num.val r.val) ∧
              ((¬ ∃ g : List I64, IsFibSplit num.val g) → r.val = [])) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or panic, regardless of whether num admits a valid Fibonacci split.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_2 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : alloc.vec.Vec I64, split_into_fibonacci num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : alloc.vec.Vec I64, split_into_fibonacci num = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r != [], the length of r is at least 3.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_3 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      3 ≤ r.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), 3 ≤ r.val.length) := by
    sorry

  /-- Whenever the function returns a result r with r != [], len(r) <= len(num).
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_4 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      r.val.length ≤ num.val.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), r.val.length ≤ num.val.length) := by
    sorry

  /-- Whenever the function returns a result r with r != [], for every i with 0 <= i < len(r), 0 <= r[i] < 2^31.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_5 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      ∀ i, (h : i < r.val.length) → 0 ≤ r.val[i].val ∧ r.val[i].val < (2 : Int) ^ 31 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), ∀ i, (h : i < r.val.length) → 0 ≤ r.val[i].val ∧ r.val[i].val < (2 : Int) ^ 31) := by
    sorry

  /-- Whenever the function returns a result r with r != [], for every i with 0 <= i < len(r)-2, r[i] + r[i+1] = r[i+2] as ordinary integers, with no wrap-around.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_6 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      ∀ i, (h : i + 2 < r.val.length) → r.val[i].val + r.val[i + 1].val = r.val[i + 2].val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), ∀ i, (h : i + 2 < r.val.length) → r.val[i].val + r.val[i + 1].val = r.val[i + 2].val) := by
    sorry

  /-- Whenever the function returns a result r with r != [], let dec(x) be the canonical decimal representation of x (no leading '0', except dec(0) is the one-character string '0'). Then the byte string num is exactly the concatenation of dec(r[0]), dec(r[1]), ..., dec(r[len(r)-1]), encoded as ASCII, with no extra bytes, separators, or leading zeroes beyond the canonical representations.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_7 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      num.val = (r.val.map fun x => dec x.val).flatten := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), num.val = (r.val.map fun x => dec x.val).flatten) := by
    sorry

  /-- If the function returns the empty vector r = [], then there does not exist any valid Fibonacci split g of num, where a valid split has len(g) >= 3, every g[i] in [0, 2^31), the recurrence g[i] + g[i+1] = g[i+2] for all 0 <= i < len(g)-2, and canonical decimal concatenation equal to num.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_8 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_empty : r.val = []) :
      ¬ ∃ g : List I64, IsFibSplit num.val g := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_empty : r.val = []), ¬ ∃ g : List I64, IsFibSplit num.val g) := by
    sorry

  /-- Whenever the function returns a result r, for every vector g of i64, if g is a valid Fibonacci split of num (len(g) >= 3, every g[i] in [0, 2^31), g[i] + g[i+1] = g[i+2] for all 0 <= i < len(g)-2, and canonical decimal concatenation equal to num), then r is also a valid Fibonacci split of num.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_9 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) :
      ∀ g : List I64, IsFibSplit num.val g → IsFibSplit num.val r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r), ∀ g : List I64, IsFibSplit num.val g → IsFibSplit num.val r.val) := by
    sorry

  /-- If len(num) < 3, then the function returns r = [].
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_10 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_short : num.val.length < 3) :
      ∃ r : alloc.vec.Vec I64, split_into_fibonacci num = ok r ∧ r.val = [] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_short : num.val.length < 3), ∃ r : alloc.vec.Vec I64, split_into_fibonacci num = ok r ∧ r.val = []) := by
    sorry

  /-- Suppose num consists of k bytes, all equal to the ASCII digit '0', so k = len(num), and k >= 3. Then the function returns r = [0, 0, ..., 0] with exactly k entries.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_11 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (h_len_three : 3 ≤ num.val.length) (h_all_zero : ∀ b ∈ num.val, b = 48#u8) :
      ∃ r : alloc.vec.Vec I64,
        split_into_fibonacci num = ok r ∧ r.val = List.replicate num.val.length 0#i64 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (h_len_three : 3 ≤ num.val.length) (h_all_zero : ∀ b ∈ num.val, b = 48#u8), ∃ r : alloc.vec.Vec I64,
          split_into_fibonacci num = ok r ∧ r.val = List.replicate num.val.length 0#i64) := by
    sorry

  /-- Whenever the function returns a nonempty result r and num[0] is the ASCII digit byte '0', then r[0] = 0.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_12 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ [])
      (h_zero : num.val[0]? = some 48#u8) :
      r.val[0]? = some 0#i64 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ [])
        (h_zero : num.val[0]? = some 48#u8), r.val[0]? = some 0#i64) := by
    sorry

  /-- Whenever the function returns a nonempty result r, there exist non-negative indices 0 = c[0] < c[1] < ... < c[k] = len(num), where k = len(r), such that for every i with 0 <= i < k, the byte substring num[c[i] .. c[i+1]) is the canonical decimal representation of r[i], with no leading '0' unless r[i] = 0.
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_13 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      ∃ c : Nat → Nat,
        c 0 = 0 ∧
          c r.val.length = num.val.length ∧
            (∀ i, (h : i < r.val.length) → c i < c (i + 1)) ∧
              (∀ i, (h : i < r.val.length) →
                substr num.val (c i) (c (i + 1)) = dec (r.val[i]).val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), ∃ c : Nat → Nat,
          c 0 = 0 ∧
            c r.val.length = num.val.length ∧
              (∀ i, (h : i < r.val.length) → c i < c (i + 1)) ∧
                (∀ i, (h : i < r.val.length) →
                  substr num.val (c i) (c (i + 1)) = dec (r.val[i]).val)) := by
    sorry

  /-- Whenever the function returns a nonempty result r, for every i with 1 <= i < len(r)-1, r[i] <= r[i+1].
    Preconditions: 1 <= len(num) <= 200, and every byte of num is an ASCII digit byte ('0' = 48 through '9' = 57). -/
  theorem spec_14 (num : Slice U8)
      (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
      (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []) :
      ∀ i, (h_ge : 1 ≤ i) → (h_lt : i + 1 < r.val.length) → r.val[i].val ≤ r.val[i + 1].val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : Slice U8)
        (h_len_ge : 1 ≤ num.val.length) (h_len_le : num.val.length ≤ 200)
        (h_digits : ∀ b ∈ num.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (r : alloc.vec.Vec I64) (h_res : split_into_fibonacci num = ok r) (h_ne : r.val ≠ []), ∀ i, (h_ge : 1 ≤ i) → (h_lt : i + 1 < r.val.length) → r.val[i].val ≤ r.val[i + 1].val) := by
    sorry

  end AegisSpec.SplitIntoFibonacci
