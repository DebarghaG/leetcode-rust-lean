import Aegis.CheckInclusion.Code.Funs

/-!
# Specifications of `Aegis.CheckInclusion.check_inclusion`

LeetCode problem `permutation-in-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckInclusion

  def countByte (bs : List Std.U8) (c : Std.U8) : ℕ :=
    bs.countP fun b => decide (b = c)

  def window (bs : List Std.U8) (k n : ℕ) : List Std.U8 :=
    (bs.drop k).take n

  def sameMultisetAt (s1 s2 : List Std.U8) (k : ℕ) : Prop :=
    ∀ c : Std.U8, countByte (window s2 k s1.length) c = countByte s1 c

  def occursIn (sub bs : List Std.U8) : Prop :=
    ∃ p : ℕ, p + sub.length ≤ bs.length ∧ ∀ i : ℕ, i < sub.length → bs[p + i]? = sub[i]?

  def listNMapBytes (g : Std.U8 → Std.U8) {n : ℕ}
      (l : Aeneas.Data.ListN.ListN Std.U8 n) : Aeneas.Data.ListN.ListN Std.U8 n :=
    match n, l with
    | _, .nil => .nil
    | _, .cons a rest => .cons (g a) (listNMapBytes g rest)

  def listNSnocBytes (a : Std.U8) {n : ℕ}
      (l : Aeneas.Data.ListN.ListN Std.U8 n) : Aeneas.Data.ListN.ListN Std.U8 n.succ :=
    match n, l with
    | _, .nil => .cons a .nil
    | _, .cons b rest => .cons b (listNSnocBytes a rest)

  def listNReverseBytes {n : ℕ}
      (l : Aeneas.Data.ListN.ListN Std.U8 n) : Aeneas.Data.ListN.ListN Std.U8 n :=
    match n, l with
    | _, .nil => .nil
    | _, .cons a rest => listNSnocBytes a (listNReverseBytes rest)

  def sliceMapBytes (g : Std.U8 → Std.U8) (s : Slice Std.U8) : Slice Std.U8 where
    leng := s.leng
    list := listNMapBytes g s.list
    bound := s.bound

  def sliceReverse (s : Slice Std.U8) : Slice Std.U8 where
    leng := s.leng
    list := listNReverseBytes s.list
    bound := s.bound

  theorem listNMapBytes_toList (g : Std.U8 → Std.U8) {n : ℕ}
      (l : Aeneas.Data.ListN.ListN Std.U8 n) :
      (listNMapBytes g l).toList = l.toList.map g := by
    induction l with
    | nil => rfl
    | cons a rest ih => simp [listNMapBytes, Aeneas.Data.ListN.ListN.toList, ih]

  theorem listNSnocBytes_toList (a : Std.U8) {n : ℕ}
      (l : Aeneas.Data.ListN.ListN Std.U8 n) :
      (listNSnocBytes a l).toList = l.toList ++ [a] := by
    induction l with
    | nil => rfl
    | cons b rest ih => simp [listNSnocBytes, Aeneas.Data.ListN.ListN.toList, ih]

  theorem listNReverseBytes_toList {n : ℕ} (l : Aeneas.Data.ListN.ListN Std.U8 n) :
      (listNReverseBytes l).toList = l.toList.reverse := by
    induction l with
    | nil => rfl
    | cons a rest ih =>
      simp [listNReverseBytes, Aeneas.Data.ListN.ListN.toList, ih, listNSnocBytes_toList]

  theorem sliceMapBytes_val (g : Std.U8 → Std.U8) (s : Slice Std.U8) :
      (sliceMapBytes g s).val = s.val.map g := by
    simp [sliceMapBytes, Slice.val, listNMapBytes_toList]

  theorem sliceReverse_val (s : Slice Std.U8) :
      (sliceReverse s).val = s.val.reverse := by
    simp [sliceReverse, Slice.val, listNReverseBytes_toList]

  /-- The function returns a result r, and r = true if and only if there exists an integer k such that 0 <= k, k + len(s1) <= len(s2), and for every byte c, the number of indices j with 0 <= j < len(s1) and s2[k+j] = c equals the number of indices i with 0 <= i < len(s1) and s1[i] = c. In words: s2 has a contiguous substring of length len(s1) whose multiset of bytes is exactly the multiset of bytes of s1.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_1 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          (r = true ↔
            ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧ sameMultisetAt s1.val s2.val k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            (r = true ↔
              ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧ sameMultisetAt s1.val s2.val k)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or index out of bounds) for every s1 and s2 satisfying the constraints.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_2 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ r : Bool, Aegis.CheckInclusion.check_inclusion s1 s2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Bool, Aegis.CheckInclusion.check_inclusion s1 s2 = ok r) := by
    sorry

  /-- The function returns a result r, and r = false.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and len(s1) > len(s2). -/
  theorem spec_3 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hgt : s2.val.length < s1.val.length) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧ r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hgt : s2.val.length < s1.val.length), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧ r = false) := by
    sorry

  /-- The function returns a result r, and r = true if and only if for every byte c, the number of indices i with 0 <= i < len(s2) and s2[i] = c equals the number of indices i with 0 <= i < len(s1) and s1[i] = c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and len(s1) = len(s2). -/
  theorem spec_4 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hlen : s1.val.length = s2.val.length) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          (r = true ↔ ∀ c : Std.U8, countByte s2.val c = countByte s1.val c) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hlen : s1.val.length = s2.val.length), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            (r = true ↔ ∀ c : Std.U8, countByte s2.val c = countByte s1.val c)) := by
    sorry

  /-- The function returns a result r, and r = true if and only if there exists an index i with 0 <= i < len(s2) and s2[i] = s1[0].
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and len(s1) = 1. -/
  theorem spec_5 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hlen1 : s1.val.length = 1) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          (r = true ↔ ∃ i : ℕ, i < s2.val.length ∧ s2.val[i]? = s1.val[0]?) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hlen1 : s1.val.length = 1), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            (r = true ↔ ∃ i : ℕ, i < s2.val.length ∧ s2.val[i]? = s1.val[0]?)) := by
    sorry

  /-- Whenever the function returns a result r with r = true, for every byte c the number of indices i with 0 <= i < len(s1) and s1[i] = c is at most the number of indices i with 0 <= i < len(s2) and s2[i] = c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_6 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
      (htrue : r = true) :
      ∀ c : Std.U8, countByte s1.val c ≤ countByte s2.val c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
        (htrue : r = true), ∀ c : Std.U8, countByte s1.val c ≤ countByte s2.val c) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exists an integer k such that 0 <= k, k + len(s1) <= len(s2), and for every byte c, the number of indices j with 0 <= j < len(s1) and s2[k+j] = c equals the number of indices i with 0 <= i < len(s1) and s1[i] = c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_7 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
      (htrue : r = true) :
      ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧ sameMultisetAt s1.val s2.val k := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
        (htrue : r = true), ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧ sameMultisetAt s1.val s2.val k) := by
    sorry

  /-- Whenever the function returns a result r with r = false, for every integer k with 0 <= k and k + len(s1) <= len(s2), there exists a byte c such that the number of indices j with 0 <= j < len(s1) and s2[k+j] = c differs from the number of indices i with 0 <= i < len(s1) and s1[i] = c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_8 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
      (hfalse : r = false) :
      ∀ k : ℕ, k + s1.val.length ≤ s2.val.length →
        ∃ c : Std.U8, countByte (window s2.val k s1.val.length) c ≠ countByte s1.val c := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (r : Bool) (hres : Aegis.CheckInclusion.check_inclusion s1 s2 = ok r)
        (hfalse : r = false), ∀ k : ℕ, k + s1.val.length ≤ s2.val.length →
          ∃ c : Std.U8, countByte (window s2.val k s1.val.length) c ≠ countByte s1.val c) := by
    sorry

  /-- The function returns a result r for (s1,s2) and a result r' for (s1',s2), and r = r'.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), s1' is a slice of bytes with len(s1') >= 1, len(s1') <= 10000, every byte of s1' is an ASCII lowercase letter, len(s1') = len(s1), and for every byte c the number of indices i with 0 <= i < len(s1') and s1'[i] = c equals the number of indices i with 0 <= i < len(s1) and s1[i] = c. -/
  theorem spec_9 (s1 s2 s1' : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h1'pos : 1 ≤ s1'.val.length) (h1'max : s1'.val.length ≤ 10000)
      (h1'ascii : ∀ c ∈ s1'.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hlen : s1'.val.length = s1.val.length)
      (hcount : ∀ c : Std.U8, countByte s1'.val c = countByte s1.val c) :
      ∃ r r' : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          Aegis.CheckInclusion.check_inclusion s1' s2 = ok r' ∧ r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s1 s2 s1' : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h1'pos : 1 ≤ s1'.val.length) (h1'max : s1'.val.length ≤ 10000)
        (h1'ascii : ∀ c ∈ s1'.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hlen : s1'.val.length = s1.val.length)
        (hcount : ∀ c : Std.U8, countByte s1'.val c = countByte s1.val c), ∃ r r' : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            Aegis.CheckInclusion.check_inclusion s1' s2 = ok r' ∧ r = r') := by
    sorry

  /-- Let rev_s2 be the slice of length len(s2) defined by rev_s2[i] = s2[len(s2)-1-i] for every i with 0 <= i < len(s2). The function returns a result r for (s1,s2) and a result r' for (s1,rev_s2), and r = r'.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, and every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122). -/
  theorem spec_10 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ r r' : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          Aegis.CheckInclusion.check_inclusion s1 (sliceReverse s2) = ok r' ∧ r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ r r' : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            Aegis.CheckInclusion.check_inclusion s1 (sliceReverse s2) = ok r' ∧ r = r') := by
    sorry

  /-- The function returns a result r for (s1,s2) and a result r' for (s2,s1), and r = r'.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and len(s1) = len(s2). -/
  theorem spec_11 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hlen : s1.val.length = s2.val.length) :
      ∃ r r' : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          Aegis.CheckInclusion.check_inclusion s2 s1 = ok r' ∧ r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hlen : s1.val.length = s2.val.length), ∃ r r' : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            Aegis.CheckInclusion.check_inclusion s2 s1 = ok r' ∧ r = r') := by
    sorry

  /-- The function returns a result r for (s1,s2) and a result r_t for (s1,t), and if r = true then r_t = true.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), t is a slice of bytes with len(t) >= 1, len(t) <= 10000, every byte of t is an ASCII lowercase letter, and s2 occurs as a contiguous substring of t: there exists p with 0 <= p, p + len(s2) <= len(t), and for every i with 0 <= i < len(s2), t[p+i] = s2[i]. -/
  theorem spec_12 (s1 s2 t : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (htpos : 1 ≤ t.val.length) (htmax : t.val.length ≤ 10000)
      (htascii : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hocc : occursIn s2.val t.val) :
      ∃ r r_t : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          Aegis.CheckInclusion.check_inclusion s1 t = ok r_t ∧ (r = true → r_t = true) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s1 s2 t : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (htpos : 1 ≤ t.val.length) (htmax : t.val.length ≤ 10000)
        (htascii : ∀ c ∈ t.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hocc : occursIn s2.val t.val), ∃ r r_t : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            Aegis.CheckInclusion.check_inclusion s1 t = ok r_t ∧ (r = true → r_t = true)) := by
    sorry

  /-- The function returns a result r, and r = true if and only if len(s1) <= len(s2) and every byte of s1 equals c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and there exists a byte c such that every byte of s2 equals c. -/
  theorem spec_13 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (c : Std.U8) (hc : ∀ b ∈ s2.val, b = c) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          (r = true ↔ s1.val.length ≤ s2.val.length ∧ ∀ b ∈ s1.val, b = c) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (c : Std.U8) (hc : ∀ b ∈ s2.val, b = c), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            (r = true ↔ s1.val.length ≤ s2.val.length ∧ ∀ b ∈ s1.val, b = c)) := by
    sorry

  /-- The function returns a result r, and r = true if and only if there exists an integer k with 0 <= k, k + len(s1) <= len(s2), and for every j with 0 <= j < len(s1), s2[k+j] = c.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), and there exists a byte c such that every byte of s1 equals c. -/
  theorem spec_14 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (c : Std.U8) (hc : ∀ b ∈ s1.val, b = c) :
      ∃ r : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          (r = true ↔
            ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧
              ∀ j : ℕ, j < s1.val.length → s2.val[k + j]? = some c) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (c : Std.U8) (hc : ∀ b ∈ s1.val, b = c), ∃ r : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            (r = true ↔
              ∃ k : ℕ, k + s1.val.length ≤ s2.val.length ∧
                ∀ j : ℕ, j < s1.val.length → s2.val[k + j]? = some c)) := by
    sorry

  /-- The function returns a result r for (s1,s2) and a result r' for (f(s1),f(s2)), and r = r'.
    Preconditions: len(s1) >= 1, len(s2) >= 1, len(s1) <= 10000, len(s2) <= 10000, every byte of s1 and s2 is an ASCII lowercase letter (97 <= byte <= 122), f is a total function from bytes to bytes that maps every ASCII lowercase letter to an ASCII lowercase letter and is injective on the set of bytes that occur in s1 or s2; f(s1) is the slice of length len(s1) with f(s1)[i] = f(s1[i]) for 0 <= i < len(s1), and f(s2) is defined similarly. -/
  theorem spec_15 (s1 s2 : Slice Std.U8)
      (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
      (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
      (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (g : Std.U8 → Std.U8)
      (hg : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ (g c).val ∧ (g c).val ≤ 122)
      (hinj : ∀ a b : Std.U8, (a ∈ s1.val ∨ a ∈ s2.val) → (b ∈ s1.val ∨ b ∈ s2.val) →
        g a = g b → a = b) :
      ∃ r r' : Bool,
        Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
          Aegis.CheckInclusion.check_inclusion (sliceMapBytes g s1) (sliceMapBytes g s2) = ok r' ∧
            r = r' := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s1 s2 : Slice Std.U8)
        (h1pos : 1 ≤ s1.val.length) (h2pos : 1 ≤ s2.val.length)
        (h1max : s1.val.length ≤ 10000) (h2max : s2.val.length ≤ 10000)
        (h1ascii : ∀ c ∈ s1.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (h2ascii : ∀ c ∈ s2.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (g : Std.U8 → Std.U8)
        (hg : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ (g c).val ∧ (g c).val ≤ 122)
        (hinj : ∀ a b : Std.U8, (a ∈ s1.val ∨ a ∈ s2.val) → (b ∈ s1.val ∨ b ∈ s2.val) →
          g a = g b → a = b), ∃ r r' : Bool,
          Aegis.CheckInclusion.check_inclusion s1 s2 = ok r ∧
            Aegis.CheckInclusion.check_inclusion (sliceMapBytes g s1) (sliceMapBytes g s2) = ok r' ∧
              r = r') := by
    sorry

  end AegisSpec.CheckInclusion
