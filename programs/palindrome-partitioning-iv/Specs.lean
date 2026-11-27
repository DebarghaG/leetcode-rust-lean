import Aegis.CheckPartitioning.Code.Funs

/-!
# Specifications of `Aegis.CheckPartitioning.check_partitioning`

LeetCode problem `palindrome-partitioning-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CheckPartitioning

  namespace AegisSpec.CheckPartitioning

  def byteAt (s : Slice Std.U8) (i : Nat) : Std.U8 :=
    (s.val[i]?).getD default

  def PalSeg (s : Slice Std.U8) (a b : Nat) : Prop :=
    ∀ k, k < b - a → byteAt s (a + k) = byteAt s (b - 1 - k)

  def HasPartition (s : Slice Std.U8) : Prop :=
    ∃ i j : Nat, 0 < i ∧ i < j ∧ j < s.val.length ∧
      PalSeg s 0 i ∧ PalSeg s i j ∧ PalSeg s j s.val.length

  def thirdCeil (s : Slice Std.U8) : Nat :=
    (s.val.length + 2) / 3

  /-- The function returns a result r (it does not fail), and r = true exactly when there exist integers i and j with 0 < i < j < len(s) such that the three contiguous segments s[0:i], s[i:j], and s[j:len(s)] are all palindromic. A segment s[a:b] with 0 <= a <= b <= len(s) is palindromic iff for every k with 0 <= k < b-a, s[a+k] = s[b-1-k]. These conditions make the three segments non-empty, in order, and covering all of s.
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122 (s consists of lowercase ASCII letters). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition s)) := by
    sorry

  /-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∃ r : Bool, check_partitioning s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∃ r : Bool, check_partitioning s = ok r) := by
    sorry

  /-- The function returns a result r with r = true.
    Preconditions: len(s) = 3, and for every i with 0 <= i < 3, 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : s.val.length = 3)
      (hletters : ∀ i, i < 3 → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∃ r : Bool, check_partitioning s = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : s.val.length = 3)
        (hletters : ∀ i, i < 3 → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∃ r : Bool, check_partitioning s = ok r ∧ r = true) := by
    sorry

  /-- The function returns a result r, and r = true if and only if s[0] = s[1] or s[1] = s[2] or s[2] = s[3].
    Preconditions: len(s) = 4, and for every i with 0 <= i < 4, 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : s.val.length = 4)
      (hletters : ∀ i, i < 4 → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∃ r : Bool, check_partitioning s = ok r ∧
        (r = true ↔ (byteAt s 0 = byteAt s 1 ∨ byteAt s 1 = byteAt s 2 ∨
          byteAt s 2 = byteAt s 3)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : s.val.length = 4)
        (hletters : ∀ i, i < 4 → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∃ r : Bool, check_partitioning s = ok r ∧
          (r = true ↔ (byteAt s 0 = byteAt s 1 ∨ byteAt s 1 = byteAt s 2 ∨
            byteAt s 2 = byteAt s 3))) := by
    sorry

  /-- Let t be the reversed byte sequence of s: len(t) = len(s) and t[k] = s[len(s)-1-k] for every 0 <= k < len(s). The function returns a result r, and r = true if and only if the same partition property holds for t: there exist integers i and j with 0 < i < j < len(t) such that t[0:i], t[i:j], and t[j:len(t)] are all palindromic. Consequently, a string and its reverse have the same answer.
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s t : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
      (htlen : t.val.length = s.val.length)
      (hrev : ∀ k, k < s.val.length → byteAt t k = byteAt s (s.val.length - 1 - k)) :
      ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition t) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
        (htlen : t.val.length = s.val.length)
        (hrev : ∀ k, k < s.val.length → byteAt t k = byteAt s (s.val.length - 1 - k)), ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition t)) := by
    sorry

  /-- The function returns a result r for s, and r = true if and only if the partition property holds for u: there exist integers i and j with 0 < i < j < len(u) such that u[0:i], u[i:j], and u[j:len(u)] are all palindromic. Equivalently, any bijective renaming of the lowercase alphabet preserves splittability.
    Preconditions: len(s) >= 3, len(s) <= 2000, every byte of s is in 97..122, and pi is any bijection of the set {97,...,122} to itself. Let u be the sequence with len(u) = len(s) and u[k] = pi(s[k]) for every k. -/
  theorem spec_6 (s u : Slice Std.U8) (pi : Nat → Nat)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
      (hpi_maps : ∀ x, 97 ≤ x → x ≤ 122 → 97 ≤ pi x ∧ pi x ≤ 122)
      (hpi_inj : ∀ x y, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → pi x = pi y → x = y)
      (hulen : u.val.length = s.val.length)
      (hu : ∀ k, k < s.val.length → (byteAt u k).val = pi (byteAt s k).val) :
      ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition u) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s u : Slice Std.U8) (pi : Nat → Nat)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122)
        (hpi_maps : ∀ x, 97 ≤ x → x ≤ 122 → 97 ≤ pi x ∧ pi x ≤ 122)
        (hpi_inj : ∀ x y, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → pi x = pi y → x = y)
        (hulen : u.val.length = s.val.length)
        (hu : ∀ k, k < s.val.length → (byteAt u k).val = pi (byteAt s k).val), ∃ r : Bool, check_partitioning s = ok r ∧ (r = true ↔ HasPartition u)) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exist integers a and b with 0 <= a < b <= len(s) such that b - a >= ceil(len(s)/3) and the segment s[a:b] is palindromic: for every k with 0 <= k < b-a, s[a+k] = s[b-1-k].
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∀ r : Bool, check_partitioning s = ok r → r = true →
        ∃ a b : Nat, a < b ∧ b ≤ s.val.length ∧ thirdCeil s ≤ b - a ∧ PalSeg s a b := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∀ r : Bool, check_partitioning s = ok r → r = true →
          ∃ a b : Nat, a < b ∧ b ≤ s.val.length ∧ thirdCeil s ≤ b - a ∧ PalSeg s a b) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exists an integer i with 1 <= i <= len(s)-2 such that the prefix s[0:i] is palindromic: for every k with 0 <= k < i, s[k] = s[i-1-k].
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∀ r : Bool, check_partitioning s = ok r → r = true →
        ∃ i : Nat, 1 ≤ i ∧ i ≤ s.val.length - 2 ∧ PalSeg s 0 i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∀ r : Bool, check_partitioning s = ok r → r = true →
          ∃ i : Nat, 1 ≤ i ∧ i ≤ s.val.length - 2 ∧ PalSeg s 0 i) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exists an integer j with 2 <= j <= len(s)-1 such that the suffix s[j:len(s)] is palindromic: for every k with 0 <= k < len(s)-j, s[j+k] = s[len(s)-1-k].
    Preconditions: len(s) >= 3, len(s) <= 2000, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
      (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122) :
      ∀ r : Bool, check_partitioning s = ok r → r = true →
        ∃ j : Nat, 2 ≤ j ∧ j ≤ s.val.length - 1 ∧ PalSeg s j s.val.length := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 3 ≤ s.val.length) (hlen_le : s.val.length ≤ 2000)
        (hletters : ∀ i, i < s.val.length → 97 ≤ (byteAt s i).val ∧ (byteAt s i).val ≤ 122), ∀ r : Bool, check_partitioning s = ok r → r = true →
          ∃ j : Nat, 2 ≤ j ∧ j ≤ s.val.length - 1 ∧ PalSeg s j s.val.length) := by
    sorry

  end AegisSpec.CheckPartitioning
