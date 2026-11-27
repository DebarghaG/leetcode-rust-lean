import Aegis.CountBinarySubstrings.Code.Funs

/-!
# Specifications of `Aegis.CountBinarySubstrings.count_binary_substrings`

LeetCode problem `count-binary-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountBinarySubstrings

  open Aegis.CountBinarySubstrings

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def len (s : Slice Std.U8) : ℕ := (bytes s).length

  def IsBinary (s : Slice Std.U8) : Prop :=
    ∀ i : ℕ, i < len s → (bytes s)[i]? = some 48 ∨ (bytes s)[i]? = some 49

  def IsConst (s : Slice Std.U8) (b : ℕ) : Prop :=
    ∀ i : ℕ, i < len s → (bytes s)[i]? = some b

  def otherByte (b : ℕ) : ℕ := if b = 48 then 49 else 48

  def blockOk (L : List ℕ) (l a : ℕ) : Bool :=
    0 < a &&
    decide (l + 2 * a ≤ L.length) &&
    ((((List.range a).all fun i => decide (L[l + i]? = some 48)) &&
        ((List.range a).all fun i => decide (L[l + a + i]? = some 49))) ||
      (((List.range a).all fun i => decide (L[l + i]? = some 49)) &&
        ((List.range a).all fun i => decide (L[l + a + i]? = some 48))))

  def countPairs (L : List ℕ) : ℕ :=
    (((List.range (L.length + 1)).flatMap fun l =>
        (List.range (L.length + 1)).map fun a => (l, a))).countP
      (fun p => blockOk L p.1 p.2)

  def countStarts (L : List ℕ) : ℕ :=
    (List.range (L.length + 1)).countP
      (fun l => (List.range (L.length + 1)).any fun a => blockOk L l a)

  def runLengthsAux (b c : ℕ) : List ℕ → List ℕ
    | [] => [c]
    | x :: xs => if x = b then runLengthsAux b (c + 1) xs else c :: runLengthsAux x 1 xs

  def runLengths : List ℕ → List ℕ
    | [] => []
    | x :: xs => runLengthsAux x 1 xs

  def adjacentMinSum : List ℕ → ℕ
    | [] => 0
    | [_] => 0
    | a :: b :: rest => min a b + adjacentMinSum (b :: rest)

  def countDescents (L : List ℕ) : ℕ :=
    (List.range (L.length - 1)).countP (fun i => decide (L[i]? ≠ L[i + 1]?))

  /-- The function returns a result r, and interpreting r as an integer, r is equal to the number of pairs (l,a) of integers such that 0 <= l, 1 <= a, l + 2*a <= len(s), and either (s[l] = 48, s[i] = 48 for every i with l <= i < l+a, and s[i] = 49 for every i with l+a <= i < l+2*a) or (s[l] = 49, s[i] = 49 for every i with l <= i < l+a, and s[i] = 48 for every i with l+a <= i < l+2*a). Each such pair corresponds to the substring occurrence s[l .. l+2*a) of length 2*a, and occurrences at different positions are counted separately.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 (the byte for '0') or 49 (the byte for '1'). -/
  theorem spec_1 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∃ r : Std.I64, count_binary_substrings s = ok r ∧ r.val = (countPairs (bytes s) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∃ r : Std.I64, count_binary_substrings s = ok r ∧ r.val = (countPairs (bytes s) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let 0 = p_0 < p_1 < ... < p_k = len(s) be the unique maximal decomposition of s into k runs of equal bytes, so for each j with 1 <= j <= k all bytes s[p_{j-1} .. p_j) are equal, and for each j with 1 <= j < k the byte of run j differs from the byte of run j+1. Put c_j = p_j - p_{j-1}. Then r = sum_{j=1}^{k-1} min(c_j, c_{j+1}), with the empty sum equal to 0 when k = 1.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_2 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        r.val = (adjacentMinSum (runLengths (bytes s)) : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          r.val = (adjacentMinSum (runLengths (bytes s)) : ℤ)) := by
    sorry

  /-- Under these preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_3 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∃ r : Std.I64, count_binary_substrings s = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∃ r : Std.I64, count_binary_substrings s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s) - 1.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_4 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        0 ≤ r.val ∧ r.val ≤ (len s : ℤ) - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          0 ≤ r.val ∧ r.val ≤ (len s : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if either s[i] = 48 for every i with 0 <= i < len(s), or s[i] = 49 for every i with 0 <= i < len(s).
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_5 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        (r.val = 0 ↔ (IsConst s 48 ∨ IsConst s 49)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          (r.val = 0 ↔ (IsConst s 48 ∨ IsConst s 49))) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if s[0] != s[1], and r = 0 if s[0] = s[1].
    Preconditions: len(s) = 2, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_6 (s : Slice Std.U8) (hlen : len s = 2) (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        ((bytes s)[0]? ≠ (bytes s)[1]? → r.val = 1) ∧
        ((bytes s)[0]? = (bytes s)[1]? → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : len s = 2) (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          ((bytes s)[0]? ≠ (bytes s)[1]? → r.val = 1) ∧
          ((bytes s)[0]? = (bytes s)[1]? → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r >= T, where T is the number of indices i with 0 <= i < len(s) - 1 and s[i] != s[i+1].
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_7 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        (countDescents (bytes s) : ℤ) ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          (countDescents (bytes s) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s) - 1.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, for every i with 0 <= i < len(s), s[i] is either 48 or 49, and for every i with 0 <= i < len(s) - 1, s[i] != s[i+1]. -/
  theorem spec_8 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) (halt : ∀ i : ℕ, i < len s - 1 → (bytes s)[i]? ≠ (bytes s)[i + 1]?) :
      ∀ r : Std.I64, count_binary_substrings s = ok r → r.val = (len s : ℤ) - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s) (halt : ∀ i : ℕ, i < len s - 1 → (bytes s)[i]? ≠ (bytes s)[i + 1]?), ∀ r : Std.I64, count_binary_substrings s = ok r → r.val = (len s : ℤ) - 1) := by
    sorry

  /-- Whenever the function returns a result r, if i is the unique index with s[i] != s[i+1], then r = min(i + 1, len(s) - i - 1).
    Preconditions: len(s) >= 2, for every i with 0 <= i < len(s), s[i] is either 48 or 49, and there is exactly one index i with 0 <= i < len(s) - 1 and s[i] != s[i+1]. -/
  theorem spec_9 (s : Slice Std.U8) (hlen : 2 ≤ len s) (hbin : IsBinary s) (i : ℕ)
      (hi : i < len s - 1) (hne : (bytes s)[i]? ≠ (bytes s)[i + 1]?)
      (huniq : ∀ j : ℕ, j < len s - 1 → j ≠ i → (bytes s)[j]? = (bytes s)[j + 1]?) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        r.val = ((min (i + 1) (len s - i - 1) : ℕ) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : 2 ≤ len s) (hbin : IsBinary s) (i : ℕ)
        (hi : i < len s - 1) (hne : (bytes s)[i]? ≠ (bytes s)[i + 1]?)
        (huniq : ∀ j : ℕ, j < len s - 1 → j ≠ i → (bytes s)[j]? = (bytes s)[j + 1]?), ∀ r : Std.I64, count_binary_substrings s = ok r →
          r.val = ((min (i + 1) (len s - i - 1) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns r on s and also returns r' on the slice t defined by t[i] = s[len(s) - 1 - i] for every i with 0 <= i < len(s), we have r = r'.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_10 (s t : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) (ht : bytes t = (bytes s).reverse) :
      ∀ r r' : Std.I64, count_binary_substrings s = ok r → count_binary_substrings t = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s) (ht : bytes t = (bytes s).reverse), ∀ r r' : Std.I64, count_binary_substrings s = ok r → count_binary_substrings t = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Define t by t[i] = 49 if s[i] = 48, and t[i] = 48 if s[i] = 49. Whenever the function returns r on s and also returns r' on t, we have r = r'.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_11 (s t : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) (ht : bytes t = (bytes s).map otherByte) :
      ∀ r r' : Std.I64, count_binary_substrings s = ok r → count_binary_substrings t = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s) (ht : bytes t = (bytes s).map otherByte), ∀ r r' : Std.I64, count_binary_substrings s = ok r → count_binary_substrings t = ok r' →
          r.val = r'.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist integers l and a and a byte b in {48,49} such that 0 <= l, 1 <= a, l + 2*a <= len(s), s[i] = b for every i with l <= i < l+a, and s[i] is the other byte (49 if b = 48, and 48 if b = 49) for every i with l+a <= i < l+2*a.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_12 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r → 0 < r.val →
        ∃ l a b : ℕ, 1 ≤ a ∧ l + 2 * a ≤ len s ∧ (b = 48 ∨ b = 49) ∧
          (∀ i : ℕ, l ≤ i → i < l + a → (bytes s)[i]? = some b) ∧
          (∀ i : ℕ, l + a ≤ i → i < l + 2 * a → (bytes s)[i]? = some (otherByte b)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r → 0 < r.val →
          ∃ l a b : ℕ, 1 ≤ a ∧ l + 2 * a ≤ len s ∧ (b = 48 ∨ b = 49) ∧
            (∀ i : ℕ, l ≤ i → i < l + a → (bytes s)[i]? = some b) ∧
            (∀ i : ℕ, l + a ≤ i → i < l + 2 * a → (bytes s)[i]? = some (otherByte b))) := by
    sorry

  /-- Whenever the function returns a result r, for every starting index l with 0 <= l < len(s) there is at most one integer a >= 1 such that l + 2*a <= len(s) and s[l .. l+2*a) consists of a copies of one byte b in {48,49} followed by a copies of the other byte. Consequently, r is exactly the number of indices l for which such an a exists.
    Preconditions: len(s) satisfies 1 <= len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is either 48 or 49. -/
  theorem spec_13 (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
      (hbin : IsBinary s) :
      ∀ r : Std.I64, count_binary_substrings s = ok r →
        (∀ l a₁ a₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ → l + 2 * a₁ ≤ len s → l + 2 * a₂ ≤ len s →
            blockOk (bytes s) l a₁ = true → blockOk (bytes s) l a₂ = true → a₁ = a₂) ∧
        r.val = (countStarts (bytes s) : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen_lo : 1 ≤ len s) (hlen_hi : len s ≤ 100000)
        (hbin : IsBinary s), ∀ r : Std.I64, count_binary_substrings s = ok r →
          (∀ l a₁ a₂ : ℕ, 1 ≤ a₁ → 1 ≤ a₂ → l + 2 * a₁ ≤ len s → l + 2 * a₂ ≤ len s →
              blockOk (bytes s) l a₁ = true → blockOk (bytes s) l a₂ = true → a₁ = a₂) ∧
          r.val = (countStarts (bytes s) : ℤ)) := by
    sorry

  end AegisSpec.CountBinarySubstrings
