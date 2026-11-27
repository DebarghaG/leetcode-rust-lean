import Aegis.MinChanges.Code.Funs

/-!
# Specifications of `Aegis.MinChanges.min_changes`

LeetCode problem `minimum-number-of-changes-to-make-binary-string-beautiful`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinChanges

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ := (bytes s).getD i 0

  def flipByte (b : ℕ) : ℕ := if b = 48 then 49 else if b = 49 then 48 else b

  def partner (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

  def IsBlock (b : List ℕ) : Prop :=
    b ≠ [] ∧ b.length % 2 = 0 ∧ ((∀ x ∈ b, x = 48) ∨ (∀ x ∈ b, x = 49))

  def Beautiful (t : List ℕ) : Prop :=
    ∃ blocks : List (List ℕ),
      blocks ≠ [] ∧ t = blocks.flatten ∧ ∀ b ∈ blocks, IsBlock b

  def hamming (xs ys : List ℕ) : ℕ :=
    (List.zipWith (fun a b => if a = b then 0 else 1) xs ys).sum

  def mismatchPairs (s : Slice Std.U8) : ℕ :=
    ((Finset.range (s.val.length / 2)).filter
      (fun i => byteAt s (2 * i) ≠ byteAt s (2 * i + 1))).card

  /-- The function returns a result r, and r = |{ i | 0 <= i < len(s)/2 and s[2*i] != s[2*i+1] }|. Equivalently, r is the minimum number of byte changes needed to turn s into a beautiful byte string t of the same length, where a byte string t is beautiful iff it can be partitioned into one or more contiguous nonempty substrings, each of even length and each consisting entirely of byte 48 or entirely of byte 49.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_1 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∃ r : Std.I64, Aegis.MinChanges.min_changes s = ok r ∧ r.val = (mismatchPairs s : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r : Std.I64, Aegis.MinChanges.min_changes s = ok r ∧ r.val = (mismatchPairs s : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_2 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∃ r : Std.I64, Aegis.MinChanges.min_changes s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∃ r : Std.I64, Aegis.MinChanges.min_changes s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(s)/2.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_3 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
        0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
          0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(s)/2, s[2*i] = s[2*i+1].
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_4 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
        (r.val = 0 ↔ ∀ i, i < s.val.length / 2 → byteAt s (2 * i) = byteAt s (2 * i + 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
          (r.val = 0 ↔ ∀ i, i < s.val.length / 2 → byteAt s (2 * i) = byteAt s (2 * i + 1))) := by
    sorry

  /-- Whenever the function returns a result r, r = len(s)/2 if and only if for every i with 0 <= i < len(s)/2, s[2*i] != s[2*i+1].
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; for every i with 0 <= i < len(s), s[i] = 48 or s[i] = 49. -/
  theorem spec_5 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
        (r.val = ((s.val.length / 2 : ℕ) : ℤ) ↔
          ∀ i, i < s.val.length / 2 → byteAt s (2 * i) ≠ byteAt s (2 * i + 1)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
          (r.val = ((s.val.length / 2 : ℕ) : ℤ) ↔
            ∀ i, i < s.val.length / 2 → byteAt s (2 * i) ≠ byteAt s (2 * i + 1))) := by
    sorry

  /-- Whenever min_changes(s) returns r and min_changes(t) returns r', we have r = r'.
    Preconditions: s and t are byte strings with 2 <= len(s) = len(t) <= 100000, len(s) is even, and every byte of s and t is 48 or 49; for every i with 0 <= i < len(s)/2, s[2*i] = s[2*i+1] if and only if t[2*i] = t[2*i+1]. -/
  theorem spec_6 (s t : Slice Std.U8)
      (h_len_eq : s.val.length = t.val.length)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_s_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (h_t_bytes : ∀ i, i < t.val.length → byteAt t i = 48 ∨ byteAt t i = 49)
      (h_pairs : ∀ i, i < s.val.length / 2 →
        (byteAt s (2 * i) = byteAt s (2 * i + 1) ↔
          byteAt t (2 * i) = byteAt t (2 * i + 1))) :
      ∀ r r' : Std.I64,
        Aegis.MinChanges.min_changes s = ok r →
        Aegis.MinChanges.min_changes t = ok r' → r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (h_len_eq : s.val.length = t.val.length)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_s_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (h_t_bytes : ∀ i, i < t.val.length → byteAt t i = 48 ∨ byteAt t i = 49)
        (h_pairs : ∀ i, i < s.val.length / 2 →
          (byteAt s (2 * i) = byteAt s (2 * i + 1) ↔
            byteAt t (2 * i) = byteAt t (2 * i + 1))), ∀ r r' : Std.I64,
          Aegis.MinChanges.min_changes s = ok r →
          Aegis.MinChanges.min_changes t = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever min_changes(s) returns r, min_changes(u) returns r_u, and min_changes(v) returns r_v, we have r = r_u + r_v.
    Preconditions: s is a byte string with 4 <= len(s) <= 100000, len(s) is even, and every byte is 48 or 49; k is an even integer with 2 <= k <= len(s)-2; u is the prefix of s of length k; v is the suffix of s of length len(s)-k. -/
  theorem spec_7 (s u v : Slice Std.U8) (k : ℕ)
      (h_len_lo : 4 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (h_k_even : k % 2 = 0) (h_k_lo : 2 ≤ k) (h_k_hi : k ≤ s.val.length - 2)
      (hu : u.val = s.val.take k) (hv : v.val = s.val.drop k) :
      ∀ r r_u r_v : Std.I64,
        Aegis.MinChanges.min_changes s = ok r →
        Aegis.MinChanges.min_changes u = ok r_u →
        Aegis.MinChanges.min_changes v = ok r_v → r.val = r_u.val + r_v.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s u v : Slice Std.U8) (k : ℕ)
        (h_len_lo : 4 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (h_k_even : k % 2 = 0) (h_k_lo : 2 ≤ k) (h_k_hi : k ≤ s.val.length - 2)
        (hu : u.val = s.val.take k) (hv : v.val = s.val.drop k), ∀ r r_u r_v : Std.I64,
          Aegis.MinChanges.min_changes s = ok r →
          Aegis.MinChanges.min_changes u = ok r_u →
          Aegis.MinChanges.min_changes v = ok r_v → r.val = r_u.val + r_v.val) := by
    sorry

  /-- Whenever min_changes(s) returns r and min_changes(t) returns r', if s[j] = s[j'] then r' = r + 1, and if s[j] != s[j'] then r' = r - 1.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; every byte of s is 48 or 49; 0 <= j < len(s); let j' = j+1 when j is even and j' = j-1 when j is odd; t is s with byte j flipped, i.e. t[j] = 49 when s[j] = 48 and t[j] = 48 when s[j] = 49, and t[i] = s[i] for all i != j. -/
  theorem spec_8 (s t : Slice Std.U8) (j : ℕ)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
      (h_j : j < s.val.length)
      (h_t_len : t.val.length = s.val.length)
      (h_t_bytes : ∀ i, i < s.val.length →
        byteAt t i = if i = j then flipByte (byteAt s j) else byteAt s i) :
      ∀ r r' : Std.I64,
        Aegis.MinChanges.min_changes s = ok r →
        Aegis.MinChanges.min_changes t = ok r' →
        (byteAt s j = byteAt s (partner j) → r'.val = r.val + 1) ∧
        (byteAt s j ≠ byteAt s (partner j) → r'.val = r.val - 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice Std.U8) (j : ℕ)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49)
        (h_j : j < s.val.length)
        (h_t_len : t.val.length = s.val.length)
        (h_t_bytes : ∀ i, i < s.val.length →
          byteAt t i = if i = j then flipByte (byteAt s j) else byteAt s i), ∀ r r' : Std.I64,
          Aegis.MinChanges.min_changes s = ok r →
          Aegis.MinChanges.min_changes t = ok r' →
          (byteAt s j = byteAt s (partner j) → r'.val = r.val + 1) ∧
          (byteAt s j ≠ byteAt s (partner j) → r'.val = r.val - 1)) := by
    sorry

  /-- Whenever the function returns a result r, for every byte string t of the same length as s, with every byte equal to 48 or 49 and beautiful (that is, partitionable into one or more contiguous nonempty substrings, each of even length and each consisting entirely of byte 48 or entirely of byte 49), the Hamming distance |{ i | 0 <= i < len(s) and s[i] != t[i] }| is at least r.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; every byte of s is 48 or 49. -/
  theorem spec_9 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
        ∀ t : List ℕ, t.length = s.val.length →
          (∀ x ∈ t, x = 48 ∨ x = 49) → Beautiful t →
            r.val ≤ (hamming (bytes s) t : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
          ∀ t : List ℕ, t.length = s.val.length →
            (∀ x ∈ t, x = 48 ∨ x = 49) → Beautiful t →
              r.val ≤ (hamming (bytes s) t : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a byte string t of the same length as s, with every byte equal to 48 or 49 and beautiful (that is, partitionable into one or more contiguous nonempty substrings, each of even length and each consisting entirely of byte 48 or entirely of byte 49), such that |{ i | 0 <= i < len(s) and s[i] != t[i] }| = r.
    Preconditions: 2 <= len(s) <= 100000; len(s) is even; every byte of s is 48 or 49. -/
  theorem spec_10 (s : Slice Std.U8)
      (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
      (h_even : s.val.length % 2 = 0)
      (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49) :
      ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
        ∃ t : List ℕ, t.length = s.val.length ∧ (∀ x ∈ t, x = 48 ∨ x = 49) ∧
          Beautiful t ∧ r.val = (hamming (bytes s) t : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_lo : 2 ≤ s.val.length) (h_len_hi : s.val.length ≤ 100000)
        (h_even : s.val.length % 2 = 0)
        (h_bytes : ∀ i, i < s.val.length → byteAt s i = 48 ∨ byteAt s i = 49), ∀ r : Std.I64, Aegis.MinChanges.min_changes s = ok r →
          ∃ t : List ℕ, t.length = s.val.length ∧ (∀ x ∈ t, x = 48 ∨ x = 49) ∧
            Beautiful t ∧ r.val = (hamming (bytes s) t : ℤ)) := by
    sorry

  end AegisSpec.MinChanges
