import Aegis.MaxUniqueSplit.Code.Funs

/-!
# Specifications of `Aegis.MaxUniqueSplit.max_unique_split`

LeetCode problem `split-a-string-into-the-max-number-of-unique-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxUniqueSplit

  def bytesOfSlice (s : Slice Std.U8) : List ℕ :=
    s.val.map (fun b => b.val)

  def IsUniqueSplit (w : List ℕ) (pieces : List (List ℕ)) : Prop :=
    pieces.flatten = w ∧ (∀ p ∈ pieces, p ≠ []) ∧ pieces.Nodup

  def IsMaxUniqueSplitLen (w : List ℕ) (k : ℕ) : Prop :=
    (∃ pieces, IsUniqueSplit w pieces ∧ pieces.length = k) ∧
      ∀ pieces, IsUniqueSplit w pieces → pieces.length ≤ k

  def PairwiseDistinctBytes (w : List ℕ) : Prop := w.Nodup

  def IsConstantBytes (w : List ℕ) : Prop := ∃ c, ∀ b ∈ w, b = c

  def FirstTwoBytesDiffer (w : List ℕ) : Prop := ∃ a b t, w = a :: b :: t ∧ a ≠ b

  def IsTriangularMax (n k : ℕ) : Prop :=
    k * (k + 1) / 2 ≤ n ∧ ∀ j, j * (j + 1) / 2 ≤ n → j ≤ k

  def distinctByteCount (w : List ℕ) : ℕ := w.dedup.length

  /-- A valid unique split of s is a sequence of indices 0 = i0 < i1 < ... < ik = len(s) with k >= 1 such that the k nonempty contiguous pieces s[i0..i1), s[i1..i2), ..., s[i(k-1)..ik) are pairwise distinct byte strings (two pieces are equal exactly when they have the same length and the same bytes at every corresponding position). The function returns a result r and r is the maximum k for which such a valid unique split of s exists. Equivalently, r is the largest number of pairwise distinct nonempty contiguous substrings into which s can be partitioned, in order, with concatenation exactly s.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∃ k : ℕ, r.val = (k : ℤ) ∧ IsMaxUniqueSplitLen (bytesOfSlice s) k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∃ k : ℕ, r.val = (k : ℤ) ∧ IsMaxUniqueSplitLen (bytesOfSlice s) k) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; in particular it does not panic, go out of bounds, or overflow.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r) := by
    sorry

  /-- The function returns a result r and 1 <= r <= len(s).
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (s.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (s.length : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a valid unique split of s into exactly r pieces: there are indices 0 = i0 < i1 < ... < ir = len(s) such that the r nonempty contiguous pieces s[i0..i1), ..., s[i(r-1)..ir) are pairwise distinct.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∃ pieces : List (List ℕ), IsUniqueSplit (bytesOfSlice s) pieces ∧
          r.val = (pieces.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∃ pieces : List (List ℕ), IsUniqueSplit (bytesOfSlice s) pieces ∧
            r.val = (pieces.length : ℤ)) := by
    sorry

  /-- The function returns a result r and, for every valid unique split of s into k pieces (a partition into k pairwise distinct nonempty contiguous substrings whose concatenation is s), k <= r. Thus no partition of s into more than r pairwise distinct nonempty contiguous substrings exists.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∀ pieces : List (List ℕ), IsUniqueSplit (bytesOfSlice s) pieces →
          (pieces.length : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∀ pieces : List (List ℕ), IsUniqueSplit (bytesOfSlice s) pieces →
            (pieces.length : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = len(s) if and only if the bytes of s are pairwise distinct: for all i,j with 0 <= i < j < len(s), s[i] != s[j].
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        (r.val = (s.length : ℤ) ↔ PairwiseDistinctBytes (bytesOfSlice s)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          (r.val = (s.length : ℤ) ↔ PairwiseDistinctBytes (bytesOfSlice s))) := by
    sorry

  /-- The function returns a result r and r is the largest integer k with k*(k+1)/2 <= len(s).
    Preconditions: len(s) is between 1 and 16 inclusive, for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122), and for every i with 0 <= i < len(s), s[i] = s[0]. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (hconst : IsConstantBytes (bytesOfSlice s)) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∃ k : ℕ, IsTriangularMax s.length k ∧ r.val = (k : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (hconst : IsConstantBytes (bytesOfSlice s)), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∃ k : ℕ, IsTriangularMax s.length k ∧ r.val = (k : ℤ)) := by
    sorry

  /-- Let revs be the byte string of length len(s) with revs[i] = s[len(s)-1-i] for 0 <= i < len(s). The function returns a result r, and r is also the maximum number of pieces in a valid unique split of revs (a partition into pairwise distinct nonempty contiguous substrings whose concatenation is revs).
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∃ k : ℕ, r.val = (k : ℤ) ∧
          IsMaxUniqueSplitLen (bytesOfSlice s) k ∧
          IsMaxUniqueSplitLen (bytesOfSlice s).reverse k := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∃ k : ℕ, r.val = (k : ℤ) ∧
            IsMaxUniqueSplitLen (bytesOfSlice s) k ∧
            IsMaxUniqueSplitLen (bytesOfSlice s).reverse k) := by
    sorry

  /-- For every injective map f from the set of byte values occurring in s to the lowercase English letter bytes, let t be the byte string with len(t) = len(s) and t[i] = f(s[i]) for 0 <= i < len(s). The function returns a result r for s, and r is also the maximum number of pieces in a valid unique split of t (a partition into pairwise distinct nonempty contiguous substrings whose concatenation is t).
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
      (f : ℕ → ℕ)
      (hf_inj : ∀ a ∈ bytesOfSlice s, ∀ b ∈ bytesOfSlice s, f a = f b → a = b)
      (hf_lower : ∀ a ∈ bytesOfSlice s, 97 ≤ f a)
      (hf_upper : ∀ a ∈ bytesOfSlice s, f a ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∃ k : ℕ, r.val = (k : ℤ) ∧
          IsMaxUniqueSplitLen (bytesOfSlice s) k ∧
          IsMaxUniqueSplitLen ((bytesOfSlice s).map f) k := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122)
        (f : ℕ → ℕ)
        (hf_inj : ∀ a ∈ bytesOfSlice s, ∀ b ∈ bytesOfSlice s, f a = f b → a = b)
        (hf_lower : ∀ a ∈ bytesOfSlice s, 97 ≤ f a)
        (hf_upper : ∀ a ∈ bytesOfSlice s, f a ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∃ k : ℕ, r.val = (k : ℤ) ∧
            IsMaxUniqueSplitLen (bytesOfSlice s) k ∧
            IsMaxUniqueSplitLen ((bytesOfSlice s).map f) k) := by
    sorry

  /-- Let n = len(s) and let k be the largest integer with k*(k+1)/2 <= n. The function returns a result r and r >= k.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        ∀ k : ℕ, IsTriangularMax s.length k → (k : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          ∀ k : ℕ, IsTriangularMax s.length k → (k : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and the condition r >= 2 holds if and only if either len(s) >= 3, or len(s) = 2 and s[0] != s[1].
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        (2 ≤ r.val ↔ 3 ≤ s.length ∨ (s.length = 2 ∧ FirstTwoBytesDiffer (bytesOfSlice s))) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          (2 ≤ r.val ↔ 3 ≤ s.length ∨ (s.length = 2 ∧ FirstTwoBytesDiffer (bytesOfSlice s)))) := by
    sorry

  /-- Let d be the number of distinct byte values occurring in s. The function returns a result r and r >= d.
    Preconditions: len(s) is between 1 and 16 inclusive, and for every i with 0 <= i < len(s), s[i] is a lowercase English letter byte (97 <= s[i] <= 122). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
      (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) :
      ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
        (distinctByteCount (bytesOfSlice s) : ℤ) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lower : 1 ≤ s.length) (hlen_upper : s.length ≤ 16)
        (hbytes : ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122), ∃ r : Std.I64, Aegis.MaxUniqueSplit.max_unique_split s = ok r ∧
          (distinctByteCount (bytesOfSlice s) : ℤ) ≤ r.val) := by
    sorry

  end AegisSpec.MaxUniqueSplit
