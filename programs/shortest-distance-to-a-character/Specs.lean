import Aegis.ShortestToChar.Code.Funs

/-!
# Specifications of `Aegis.ShortestToChar.shortest_to_char`

LeetCode problem `shortest-distance-to-a-character`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ShortestToChar

abbrev Byte := Aeneas.Std.U8

abbrev ByteSlice := Aeneas.Std.Slice Aeneas.Std.U8

abbrev I64Vec := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

def slen (s : ByteSlice) : ℕ := (s : List Byte).length

def byteAt (s : ByteSlice) (i : ℕ) : Byte := (s : List Byte).getD i 0#u8

def vecAt (r : I64Vec) (i : ℕ) : ℤ := (r.val.getD i 0#i64).val

def occs (s : ByteSlice) (t : Byte) : List ℕ :=
  (List.range (slen s)).filter (fun j => byteAt s j = t)

def minOpt (l : List ℕ) : Option ℕ :=
  l.foldr (fun a acc => some (match acc with | none => a | some b => min a b)) none

def maxOpt (l : List ℕ) : Option ℕ :=
  l.foldr (fun a acc => some (match acc with | none => a | some b => max a b)) none

def firstOcc (s : ByteSlice) (t : Byte) : ℕ := (minOpt (occs s t)).getD 0

def lastOcc (s : ByteSlice) (t : Byte) : ℕ := (maxOpt (occs s t)).getD 0

def minDist (s : ByteSlice) (t : Byte) (i : ℕ) : ℕ :=
  (minOpt ((occs s t).map (fun j => ((i : ℤ) - (j : ℤ)).natAbs))).getD 0

/-- The function returns a result r and len(r) = len(s), and for every i with 0 <= i < len(s), r[i] = min{ |i - j| : 0 <= j < len(s) and s[j] = c[0] }, where the minimum is taken over the nonempty set of occurrence indices of c[0] in s and |i - j| denotes the absolute difference of the integers i and j.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_1 (s c : ByteSlice)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0) :
    ∃ r : I64Vec,
      Aegis.ShortestToChar.shortest_to_char s c = Result.ok r ∧
        r.val.length = slen s ∧
          ∀ i, i < slen s → vecAt r i = (minDist s (byteAt c 0) i : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s c : ByteSlice)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0), ∃ r : I64Vec,
      Aegis.ShortestToChar.shortest_to_char s c = Result.ok r ∧
        r.val.length = slen s ∧
          ∀ i, i < slen s → vecAt r i = (minDist s (byteAt c 0) i : ℤ)) := by
  sorry

/-- The function returns a result r; in particular, it does not fail, overflow, panic, or access memory out of bounds on any input satisfying the preconditions.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_2 (s c : ByteSlice)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0) :
    ∃ r : I64Vec, Aegis.ShortestToChar.shortest_to_char s c = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s c : ByteSlice)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0), ∃ r : I64Vec, Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(s).
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_3 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    r.val.length = slen s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), r.val.length = slen s) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), 0 <= r[i] <= len(s) - 1.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_4 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i < slen s → 0 ≤ vecAt r i ∧ vecAt r i ≤ (slen s : ℤ) - 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i < slen s → 0 ≤ vecAt r i ∧ vecAt r i ≤ (slen s : ℤ) - 1) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), r[i] = 0 if and only if s[i] = c[0].
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_5 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i < slen s → (vecAt r i = 0 ↔ byteAt s i = byteAt c 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i < slen s → (vecAt r i = 0 ↔ byteAt s i = byteAt c 0)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s), there exists j with 0 <= j < len(s) such that s[j] = c[0] and r[i] = |i - j|.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_6 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i < slen s →
      ∃ j, j < slen s ∧ byteAt s j = byteAt c 0 ∧ vecAt r i = |(i : ℤ) - (j : ℤ)| := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i < slen s →
      ∃ j, j < slen s ∧ byteAt s j = byteAt c 0 ∧ vecAt r i = |(i : ℤ) - (j : ℤ)|) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s) and every j with 0 <= j < len(s), if s[j] = c[0] then r[i] <= |i - j|.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_7 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i < slen s → ∀ j, j < slen s → byteAt s j = byteAt c 0 →
      vecAt r i ≤ |(i : ℤ) - (j : ℤ)| := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i < slen s → ∀ j, j < slen s → byteAt s j = byteAt c 0 →
      vecAt r i ≤ |(i : ℤ) - (j : ℤ)|) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(s) - 1, |r[i+1] - r[i]| <= 1, where the outer absolute value is the absolute difference of the integers r[i+1] and r[i].
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_8 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i < slen s - 1 → |vecAt r (i + 1) - vecAt r i| ≤ 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i < slen s - 1 → |vecAt r (i + 1) - vecAt r i| ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, let p be the least index with 0 <= p < len(s) and s[p] = c[0]; then for every i with 0 <= i <= p, r[i] = p - i.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_9 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, i ≤ firstOcc s (byteAt c 0) →
      vecAt r i = (firstOcc s (byteAt c 0) : ℤ) - (i : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, i ≤ firstOcc s (byteAt c 0) →
      vecAt r i = (firstOcc s (byteAt c 0) : ℤ) - (i : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let q be the greatest index with 0 <= q < len(s) and s[q] = c[0]; then for every i with q <= i < len(s), r[i] = i - q.
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_10 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ i, lastOcc s (byteAt c 0) ≤ i → i < slen s →
      vecAt r i = (i : ℤ) - (lastOcc s (byteAt c 0) : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ i, lastOcc s (byteAt c 0) ≤ i → i < slen s →
      vecAt r i = (i : ℤ) - (lastOcc s (byteAt c 0) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every p and q with 0 <= p < q < len(s) such that s[p] = c[0], s[q] = c[0], and no k with p < k < q has s[k] = c[0], and for every i with p <= i <= q, r[i] = min(i - p, q - i).
  Preconditions: len(s) >= 1 and len(s) <= 10000; for every i with 0 <= i < len(s), 97 <= s[i] <= 122; len(c) = 1; 97 <= c[0] <= 122; and there exists j with 0 <= j < len(s) such that s[j] = c[0]. -/
theorem spec_11 (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r) :
    ∀ p q, p < q → q < slen s → byteAt s p = byteAt c 0 → byteAt s q = byteAt c 0 →
      (∀ k, p < k → k < q → byteAt s k ≠ byteAt c 0) →
        ∀ i, p ≤ i → i ≤ q →
          vecAt r i = min ((i : ℤ) - (p : ℤ)) ((q : ℤ) - (i : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s c : ByteSlice) (r : I64Vec)
    (hlen_pos : 1 ≤ slen s) (hlen_le : slen s ≤ 10000)
    (hbytes : ∀ i, i < slen s → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
    (hclen : slen c = 1)
    (hc_byte : 97 ≤ (byteAt c 0).val ∧ (byteAt c 0).val ≤ 122)
    (hocc : ∃ j, j < slen s ∧ byteAt s j = byteAt c 0)
    (hr : Aegis.ShortestToChar.shortest_to_char s c = Result.ok r), ∀ p q, p < q → q < slen s → byteAt s p = byteAt c 0 → byteAt s q = byteAt c 0 →
      (∀ k, p < k → k < q → byteAt s k ≠ byteAt c 0) →
        ∀ i, p ≤ i → i ≤ q →
          vecAt r i = min ((i : ℤ) - (p : ℤ)) ((q : ℤ) - (i : ℤ))) := by
  sorry

end AegisSpec.ShortestToChar
