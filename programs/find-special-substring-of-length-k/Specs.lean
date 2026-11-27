import Aegis.HasSpecialSubstring.Code.Funs

/-!
# Specifications of `Aegis.HasSpecialSubstring.has_special_substring`

LeetCode problem `find-special-substring-of-length-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.HasSpecialSubstring

  def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

  def size (s : Slice Std.U8) : Nat := (bytes s).length

  def byteAt (s : Slice Std.U8) (i : Nat) : Nat := (bytes s).getD i 0

  def kToNat (k : Std.I64) : Nat := k.val.toNat

  def IsMaximalRun (s : Slice Std.U8) (i j : Nat) : Prop :=
    0 ≤ i ∧ i < j ∧ j ≤ size s ∧
      (∀ t, i ≤ t → t < j → byteAt s t = byteAt s i) ∧
      (i = 0 ∨ byteAt s (i - 1) ≠ byteAt s i) ∧
      (j = size s ∨ byteAt s j ≠ byteAt s i)

  def AllRunsShorterThan (s : Slice Std.U8) (k : Nat) : Prop :=
    ∀ i j, IsMaximalRun s i j → j - i < k

  def AllRunsLongerThan (s : Slice Std.U8) (k : Nat) : Prop :=
    ∀ i j, IsMaximalRun s i j → k < j - i

  def IsSpecialStart (s : Slice Std.U8) (k : Nat) (i : Nat) : Prop :=
    0 ≤ i ∧ i + k ≤ size s ∧
      (∀ j, i ≤ j → j < i + k → byteAt s j = byteAt s i) ∧
      (i = 0 ∨ byteAt s (i - 1) ≠ byteAt s i) ∧
      (i + k = size s ∨ byteAt s (i + k) ≠ byteAt s i)

  /-- Whenever has_special_substring s k returns a result r, r = true if and only if there exists an integer i such that 0 ≤ i, i + k ≤ n, for every j with i ≤ j < i + k we have s[j] = s[i], (i = 0 or s[i-1] ≠ s[i]), and (i + k = n or s[i+k] ≠ s[i]).
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; and for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122. -/
  theorem spec_1 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r) :
      (r = true ↔ ∃ i, IsSpecialStart s (kToNat k) i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r), (r = true ↔ ∃ i, IsSpecialStart s (kToNat k) i)) := by
    sorry

  /-- For every s and k satisfying the preconditions, the evaluation of has_special_substring s k returns a result of the form Result.ok r for some Boolean r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; and for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122. -/
  theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : Bool, Aegis.HasSpecialSubstring.has_special_substring s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : Bool, Aegis.HasSpecialSubstring.has_special_substring s k = ok r) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, r = true if and only if there exists an integer i such that 0 ≤ i < n, (i = 0 or s[i-1] ≠ s[i]), and (i + 1 = n or s[i+1] ≠ s[i]).
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122; and k = 1. -/
  theorem spec_3 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hk1 : k.val = 1)
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r) :
      (r = true ↔ ∃ i, 0 ≤ i ∧ i < size s ∧
        (i = 0 ∨ byteAt s (i - 1) ≠ byteAt s i) ∧
        (i + 1 = size s ∨ byteAt s (i + 1) ≠ byteAt s i)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hk1 : k.val = 1)
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r), (r = true ↔ ∃ i, 0 ≤ i ∧ i < size s ∧
          (i = 0 ∨ byteAt s (i - 1) ≠ byteAt s i) ∧
          (i + 1 = size s ∨ byteAt s (i + 1) ≠ byteAt s i))) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, r = true if and only if for every i with 0 ≤ i < n, s[i] = s[0].
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122; and k = n. -/
  theorem spec_4 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hkn : k.val = (size s : Int))
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r) :
      (r = true ↔ ∀ i, 0 ≤ i → i < size s → byteAt s i = byteAt s 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hkn : k.val = (size s : Int))
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r), (r = true ↔ ∀ i, 0 ≤ i → i < size s → byteAt s i = byteAt s 0)) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, r = true if and only if k = 1.
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122; and for every i with 0 ≤ i < n - 1, s[i] ≠ s[i+1]. -/
  theorem spec_5 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hadj : ∀ i, 0 ≤ i → i < size s - 1 → byteAt s i ≠ byteAt s (i + 1))
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r) :
      (r = true ↔ k.val = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hadj : ∀ i, 0 ≤ i → i < size s - 1 → byteAt s i ≠ byteAt s (i + 1))
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r), (r = true ↔ k.val = 1)) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, r = true if and only if k = n.
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122; and for every i with 0 ≤ i < n, s[i] = s[0]. -/
  theorem spec_6 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hconst : ∀ i, 0 ≤ i → i < size s → byteAt s i = byteAt s 0)
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r) :
      (r = true ↔ k.val = (size s : Int)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hconst : ∀ i, 0 ≤ i → i < size s → byteAt s i = byteAt s 0)
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r), (r = true ↔ k.val = (size s : Int))) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, if every maximal run of equal bytes in s has length strictly less than k, then r = false. Here a maximal run is an interval [i,j) with 0 ≤ i < j ≤ n such that all s[t] for i ≤ t < j are equal, (i = 0 or s[i-1] ≠ s[i]), and (j = n or s[j] ≠ s[i]); its length is j - i.
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; and for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122. -/
  theorem spec_7 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r)
      (hruns : AllRunsShorterThan s (kToNat k)) :
      r = false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r)
        (hruns : AllRunsShorterThan s (kToNat k)), r = false) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r, if every maximal run of equal bytes in s has length strictly greater than k, then r = false. Here a maximal run is an interval [i,j) with 0 ≤ i < j ≤ n such that all s[t] for i ≤ t < j are equal, (i = 0 or s[i-1] ≠ s[i]), and (j = n or s[j] ≠ s[i]); its length is j - i.
    Preconditions: Let n = len(s). The slice s has 1 ≤ n ≤ 100; the integer k (the i64 argument) satisfies 1 ≤ k ≤ n; and for every i with 0 ≤ i < n, s[i] is an ASCII lowercase English letter, i.e. 97 ≤ s[i] ≤ 122. -/
  theorem spec_8 (s : Slice Std.U8) (k : Std.I64) (r : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r)
      (hruns : AllRunsLongerThan s (kToNat k)) :
      r = false := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64) (r : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hres : Aegis.HasSpecialSubstring.has_special_substring s k = ok r)
        (hruns : AllRunsLongerThan s (kToNat k)), r = false) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r1 and has_special_substring t k returns a result r2, we have r1 = r2.
    Preconditions: Let n = len(s). The common preconditions hold for (s,k): 1 ≤ n ≤ 100, 1 ≤ k ≤ n, and s has only ASCII lowercase letters. Let t be any byte slice of length n that also has only ASCII lowercase letters, and assume for all i,j with 0 ≤ i,j < n, s[i] = s[j] if and only if t[i] = t[j]. -/
  theorem spec_9 (s t : Slice Std.U8) (k : Std.I64) (r1 r2 : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (htlen : size t = size s)
      (htalpha : ∀ i, i < size t → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
      (hpattern : ∀ i j, 0 ≤ i → i < size s → 0 ≤ j → j < size s →
        (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
      (hres1 : Aegis.HasSpecialSubstring.has_special_substring s k = ok r1)
      (hres2 : Aegis.HasSpecialSubstring.has_special_substring t k = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64) (r1 r2 : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (htlen : size t = size s)
        (htalpha : ∀ i, i < size t → 97 ≤ byteAt t i ∧ byteAt t i ≤ 122)
        (hpattern : ∀ i j, 0 ≤ i → i < size s → 0 ≤ j → j < size s →
          (byteAt s i = byteAt s j ↔ byteAt t i = byteAt t j))
        (hres1 : Aegis.HasSpecialSubstring.has_special_substring s k = ok r1)
        (hres2 : Aegis.HasSpecialSubstring.has_special_substring t k = ok r2), r1 = r2) := by
    sorry

  /-- Whenever has_special_substring s k returns a result r1 and has_special_substring rev k returns a result r2, we have r1 = r2.
    Preconditions: Let n = len(s). The common preconditions hold for (s,k): 1 ≤ n ≤ 100, 1 ≤ k ≤ n, and s has only ASCII lowercase letters. Let rev be the byte slice of length n defined by rev[i] = s[n - 1 - i] for 0 ≤ i < n. -/
  theorem spec_10 (s rev : Slice Std.U8) (k : Std.I64) (r1 r2 : Bool)
      (hlen : 1 ≤ size s ∧ size s ≤ 100)
      (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
      (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (hrev : bytes rev = (bytes s).reverse)
      (hres1 : Aegis.HasSpecialSubstring.has_special_substring s k = ok r1)
      (hres2 : Aegis.HasSpecialSubstring.has_special_substring rev k = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s rev : Slice Std.U8) (k : Std.I64) (r1 r2 : Bool)
        (hlen : 1 ≤ size s ∧ size s ≤ 100)
        (hk : 1 ≤ k.val ∧ k.val ≤ (size s : Int))
        (halpha : ∀ i, i < size s → 97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (hrev : bytes rev = (bytes s).reverse)
        (hres1 : Aegis.HasSpecialSubstring.has_special_substring s k = ok r1)
        (hres2 : Aegis.HasSpecialSubstring.has_special_substring rev k = ok r2), r1 = r2) := by
    sorry

  end AegisSpec.HasSpecialSubstring
