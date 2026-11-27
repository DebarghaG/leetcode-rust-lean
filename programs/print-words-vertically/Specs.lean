import Aegis.PrintVertically.Code.Funs

/-!
# Specifications of `Aegis.PrintVertically.print_vertically`

LeetCode problem `print-words-vertically`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PrintVertically

def IsSpace (b : Std.U8) : Prop := b.val = 32

def IsUpper (b : Std.U8) : Prop := 65 ≤ b.val ∧ b.val ≤ 90

def IsWord (w : List Std.U8) : Prop := w ≠ [] ∧ ∀ b, b ∈ w → IsUpper b

def Decomp (s : List Std.U8) (k : Nat) (w : Nat → List Std.U8) : Prop :=
  ∃ sep : Std.U8, IsSpace sep ∧ s = List.intercalate [sep] (List.ofFn (fun j : Fin k => w j))

def maxLen (k : Nat) (w : Nat → List Std.U8) : Nat :=
  ((List.range k).map (fun j => (w j).length)).foldr max 0

def indicesAt (k : Nat) (w : Nat → List Std.U8) (i : Nat) : List Nat :=
  (List.range k).filter (fun j => decide (i < (w j).length))

def lastIndexAt (k : Nat) (w : Nat → List Std.U8) (i : Nat) : Nat :=
  (indicesAt k w i).foldr max 0

def column (k : Nat) (w : Nat → List Std.U8) (i : Nat) : List Std.U8 :=
  (List.range k).filterMap (fun j => (w j)[i]?)

/-- The function returns a result r and does not fail. Then len(r) = m, and for every i with 0 <= i < m, len(r[i]) = 1 + max{ j | 0 <= j < k and i < len(w_j) } (the set is nonempty), and for every j with 0 <= j < len(r[i]), r[i][j] = w_j[i] if i < len(w_j), otherwise r[i][j] = 32.
  Preconditions: Let s be a nonempty byte array of length at most 200. It consists of k >= 1 nonempty words w_0,...,w_{k-1} in that order, where each word is a maximal contiguous block of bytes in 65..90 (uppercase English letters), and consecutive words are separated by exactly one byte 32 (space). Thus there are no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_1 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.PrintVertically.print_vertically s = ok r ∧
      r.val.length = m ∧
      (∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
        r.val[i]? = some row ∧
        row.val.length = 1 + lastIndexAt k w i ∧
        indicesAt k w i ≠ [] ∧
        ∀ (j : Nat) (hj : j < row.val.length),
          (row.val[j]).val =
            if h : i < (w j).length then ((w j)[i]).val else 32) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.PrintVertically.print_vertically s = ok r ∧
      r.val.length = m ∧
      (∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
        r.val[i]? = some row ∧
        row.val.length = 1 + lastIndexAt k w i ∧
        indicesAt k w i ≠ [] ∧
        ∀ (j : Nat) (hj : j < row.val.length),
          (row.val[j]).val =
            if h : i < (w j).length then ((w j)[i]).val else 32)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns some result r. It does not fail, panic, overflow, or access any index out of bounds.
  Preconditions: Let s be a nonempty byte array of length at most 200. It consists of k >= 1 nonempty words w_0,...,w_{k-1} in that order, where each word is a maximal contiguous block of bytes in 65..90, and consecutive words are separated by exactly one byte 32. Thus there are no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_2 (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.PrintVertically.print_vertically s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      Aegis.PrintVertically.print_vertically s = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = m and, for every i with 0 <= i < m, 1 <= len(r[i]) <= k.
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_3 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    r.val.length = m ∧
      (∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
        r.val[i]? = some row ∧ 1 ≤ row.val.length ∧ row.val.length ≤ k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), r.val.length = m ∧
      (∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
        r.val[i]? = some row ∧ 1 ≤ row.val.length ∧ row.val.length ≤ k)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if j_i = max{ j | 0 <= j < k and i < len(w_j) }, then len(r[i]) = j_i + 1.
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_4 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧ row.val.length = lastIndexAt k w i + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧ row.val.length = lastIndexAt k w i + 1) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < m, 0 <= j < k, i < len(w_j), and j < len(r[i]), we have r[i][j] = w_j[i].
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_5 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i j : Nat) (hi : i < m) (hj : j < k) (hij : i < (w j).length)
      (row : alloc.vec.Vec Std.U8) (hrow : r.val[i]? = some row)
      (hjrow : j < row.val.length),
      (row.val[j]).val = ((w j)[i]).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i j : Nat) (hi : i < m) (hj : j < k) (hij : i < (w j).length)
      (row : alloc.vec.Vec Std.U8) (hrow : r.val[i]? = some row)
      (hjrow : j < row.val.length),
      (row.val[j]).val = ((w j)[i]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < m, 0 <= j < k, j < len(r[i]), and i >= len(w_j), we have r[i][j] = 32.
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_6 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i j : Nat) (hi : i < m) (hj : j < k) (row : alloc.vec.Vec Std.U8)
      (hrow : r.val[i]? = some row) (hjrow : j < row.val.length)
      (hge : (w j).length ≤ i),
      (row.val[j]).val = 32 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i j : Nat) (hi : i < m) (hj : j < k) (row : alloc.vec.Vec Std.U8)
      (hrow : r.val[i]? = some row) (hjrow : j < row.val.length)
      (hge : (w j).length ≤ i),
      (row.val[j]).val = 32) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), len(r[i]) > 0 and r[i][len(r[i]) - 1] != 32. In particular, no output row ends with a space.
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_7 (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length),
      0 < (r.val[i]).val.length ∧
        ∀ (b : Std.U8), (r.val[i]).val.getLast? = some b → b.val ≠ 32 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < r.val.length),
      0 < (r.val[i]).val.length ∧
        ∀ (b : Std.U8), (r.val[i]).val.getLast? = some b → b.val ≠ 32) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, the sequence obtained from r[i] by deleting every byte equal to 32 is exactly the sequence of bytes w_j[i], taken over j = 0,1,...,k-1 in increasing order with i < len(w_j).
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_8 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧
      row.val.filter (fun b => decide (b.val ≠ 32)) = column k w i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧
      row.val.filter (fun b => decide (b.val ≠ 32)) = column k w i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, the number of positions p with 0 <= p < len(r[i]) and r[i][p] != 32 equals the number of j with 0 <= j < k and i < len(w_j).
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_9 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧
      (row.val.filter (fun b => decide (b.val ≠ 32))).length = (indicesAt k w i).length := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧
      (row.val.filter (fun b => decide (b.val ≠ 32))).length = (indicesAt k w i).length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, let j_i = max{ j | 0 <= j < k and i < len(w_j) }; then len(r[i]) > 0 and r[i][len(r[i]) - 1] = w_{j_i}[i].
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_10 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧ 0 < row.val.length ∧
      ∀ (b : Std.U8), row.val.getLast? = some b →
        (w (lastIndexAt k w i))[i]? = some b := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < m), ∃ row : alloc.vec.Vec Std.U8,
      r.val[i]? = some row ∧ 0 < row.val.length ∧
      ∀ (b : Std.U8), row.val.getLast? = some b →
        (w (lastIndexAt k w i))[i]? = some b) := by
  sorry

/-- Whenever the function returns a result r, for every i and p with 0 <= i < len(r) and 0 <= p < len(r[i]), the byte r[i][p] is either 32 or satisfies 65 <= r[i][p] <= 90.
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_11 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < r.val.length) (p : Nat) (hp : p < (r.val[i]).val.length),
      ((r.val[i]).val[p]).val = 32 ∨
        (65 ≤ ((r.val[i]).val[p]).val ∧ ((r.val[i]).val[p]).val ≤ 90) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < r.val.length) (p : Nat) (hp : p < (r.val[i]).val.length),
      ((r.val[i]).val[p]).val = 32 ∨
        (65 ≤ ((r.val[i]).val[p]).val ∧ ((r.val[i]).val[p]).val ≤ 90)) := by
  sorry

/-- Whenever the function returns a result r, len(r) >= 1, len(r[0]) = k, and for every j with 0 <= j < k, r[0][j] = w_j[0].
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_12 (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    1 ≤ r.val.length ∧
      (∀ (row : alloc.vec.Vec Std.U8), r.val[0]? = some row →
        row.val.length = k ∧ ∀ (j : Nat), j < k → (w j)[0]? = row.val[j]?) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), 1 ≤ r.val.length ∧
      (∀ (row : alloc.vec.Vec Std.U8), r.val[0]? = some row →
        row.val.length = k ∧ ∀ (j : Nat), j < k → (w j)[0]? = row.val[j]?)) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i < m and 0 <= j < k, if i < len(w_j), then j < len(r[i]).
  Preconditions: Let s be a nonempty byte array of length at most 200, consisting of k >= 1 nonempty uppercase words w_0,...,w_{k-1} separated by single spaces, with no leading, trailing, or consecutive spaces. Let m = max_{0 <= j < k} len(w_j). -/
theorem spec_13 (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r) :
    ∀ (i : Nat) (hi : i < m) (j : Nat) (hj : j < k), i < (w j).length →
      ∃ row : alloc.vec.Vec Std.U8, r.val[i]? = some row ∧ j < row.val.length := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (k m : Nat) (w : Nat → List Std.U8)
    (hne : s.val ≠ []) (hlen : s.val.length ≤ 200) (hk : 1 ≤ k)
    (hw : ∀ j, j < k → IsWord (w j)) (hdec : Decomp s.val k w) (hm : m = maxLen k w)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : Aegis.PrintVertically.print_vertically s = ok r), ∀ (i : Nat) (hi : i < m) (j : Nat) (hj : j < k), i < (w j).length →
      ∃ row : alloc.vec.Vec Std.U8, r.val[i]? = some row ∧ j < row.val.length) := by
  sorry

end AegisSpec.PrintVertically
