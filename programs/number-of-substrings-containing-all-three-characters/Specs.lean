import Aegis.NumberOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubstrings.number_of_substrings`

LeetCode problem `number-of-substrings-containing-all-three-characters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfSubstrings

  open Aegis.NumberOfSubstrings (number_of_substrings)

  @[reducible] def Occurs (b : ℕ) (l : List Std.U8) : Prop := ∃ x, x ∈ l ∧ x.val = b

  @[reducible] def HasAllThree (l : List Std.U8) : Prop :=
    Occurs 97 l ∧ Occurs 98 l ∧ Occurs 99 l

  def substring (l : List Std.U8) (i j : ℕ) : List Std.U8 := (l.drop i).take (j + 1 - i)

  def BytesABC (b : Std.U8) : Prop := b.val = 97 ∨ b.val = 98 ∨ b.val = 99

  def OnlyABC (l : List Std.U8) : Prop := ∀ (i : ℕ) (h : i < l.length), BytesABC (l[i]'h)

  def goodPairSet (l : List Std.U8) (lo hi : ℕ) : Finset (ℕ × ℕ) :=
    (Finset.range l.length ×ˢ Finset.range l.length).filter
      (fun p : ℕ × ℕ =>
        lo ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 < hi ∧ HasAllThree (substring l p.1 p.2))

  def goodPairCount (l : List Std.U8) : ℕ := (goodPairSet l 0 l.length).card

  def badPairCount (l : List Std.U8) : ℕ :=
    ((Finset.range l.length ×ˢ Finset.range l.length).filter
      (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ ¬ HasAllThree (substring l p.1 p.2))).card

  def IsPermABC (σ : Std.U8 → Std.U8) : Prop :=
    (∀ b : Std.U8, BytesABC b → BytesABC (σ b)) ∧
      (∀ b : Std.U8, BytesABC b → ∃ a : Std.U8, BytesABC a ∧ σ a = b)

  /-- The function returns a result r, and r equals the number of pairs (i,j) with 0 <= i <= j < len(s) such that the contiguous substring s[i], s[i+1], ..., s[j] contains at least one occurrence of byte 97 ('a'), at least one occurrence of byte 98 ('b'), and at least one occurrence of byte 99 ('c').
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∃ r : Std.I64, number_of_substrings s = ok r ∧ r.val = (goodPairCount s.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∃ r : Std.I64, number_of_substrings s = ok r ∧ r.val = (goodPairCount s.val : ℤ)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) on every input satisfying the preconditions.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∃ r : Std.I64, number_of_substrings s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∃ r : Std.I64, number_of_substrings s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(s) * (len(s) + 1) / 2.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          r.val ≤ ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= (len(s) - 1) * (len(s) - 2) / 2.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        r.val ≤ (((s.val.length - 1) * (s.val.length - 2) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          r.val ≤ (((s.val.length - 1) * (s.val.length - 2) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if s contains all three of the bytes 97, 98, and 99 (equivalently, the three bytes of s are a permutation of 'a','b','c'), and r = 0 otherwise.
    Preconditions: len(s) = 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen3 : s.val.length = 3) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        (HasAllThree s.val → r.val = 1) ∧ (¬ HasAllThree s.val → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : s.val.length = 3) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          (HasAllThree s.val → r.val = 1) ∧ (¬ HasAllThree s.val → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if at least one of the bytes 97, 98, or 99 does not occur anywhere in s, then r = 0.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        (¬ HasAllThree s.val → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          (¬ HasAllThree s.val → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if each of the bytes 97, 98, and 99 occurs at least once in s, then r >= 1.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_8 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r → (HasAllThree s.val → 1 ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r → (HasAllThree s.val → 1 ≤ r.val)) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exist indices i and j with 0 <= i <= j < len(s) such that s[i], s[i+1], ..., s[j] contains at least one occurrence of each of the bytes 97, 98, and 99.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        (0 < r.val ↔
          ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ HasAllThree (substring s.val i j)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          (0 < r.val ↔
            ∃ i j : ℕ, i ≤ j ∧ j < s.val.length ∧ HasAllThree (substring s.val i j))) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k <= len(s), the number of pairs (i,j) with 0 <= i <= j < k such that s[i], s[i+1], ..., s[j] contains at least one occurrence of each of 97, 98, and 99 is at most r.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        ∀ k : ℕ, k ≤ s.val.length → ((goodPairSet s.val 0 k).card : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          ∀ k : ℕ, k ≤ s.val.length → ((goodPairSet s.val 0 k).card : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every k with 0 <= k <= len(s), the number of pairs (i,j) with k <= i <= j < len(s) such that s[i], s[i+1], ..., s[j] contains at least one occurrence of each of 97, 98, and 99 is at most r.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        ∀ k : ℕ, k ≤ s.val.length →
          ((goodPairSet s.val k s.val.length).card : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          ∀ k : ℕ, k ≤ s.val.length →
            ((goodPairSet s.val k s.val.length).card : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r plus the number of pairs (i,j) with 0 <= i <= j < len(s) whose substring s[i], s[i+1], ..., s[j] misses at least one of the bytes 97, 98, or 99 equals len(s)*(len(s)+1)/2.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        r.val + (badPairCount s.val : ℤ) =
          ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          r.val + (badPairCount s.val : ℤ) =
            ((s.val.length * (s.val.length + 1) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r for s, if t is the byte slice of length len(s) defined by t[i] = s[len(s)-1-i] for every 0 <= i < len(s), then the number of pairs (u,v) with 0 <= u <= v < len(t) such that t[u], t[u+1], ..., t[v] contains at least one occurrence of each of 97, 98, and 99 is also r.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_13 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        ∀ t : Slice Std.U8, t.val = s.val.reverse → (goodPairCount t.val : ℤ) = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          ∀ t : Slice Std.U8, t.val = s.val.reverse → (goodPairCount t.val : ℤ) = r.val) := by
    sorry

  /-- Whenever the function returns a result r for s, for every bijection p from the set {97, 98, 99} to itself, if t is the byte slice defined by t[i] = p(s[i]) for every 0 <= i < len(s), then the number of pairs (u,v) with 0 <= u <= v < len(t) such that t[u], t[u+1], ..., t[v] contains at least one occurrence of each of 97, 98, and 99 is also r.
    Preconditions: len(s) >= 3, len(s) <= 50000, and for every i with 0 <= i < len(s), s[i] is one of the byte values 97 ('a'), 98 ('b'), 99 ('c'). -/
  theorem spec_14 (s : Slice Std.U8)
      (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
      (hbytes : OnlyABC s.val) :
      ∀ r : Std.I64, number_of_substrings s = ok r →
        ∀ (σ : Std.U8 → Std.U8), IsPermABC σ →
          ∀ t : Slice Std.U8, t.val = s.val.map σ → (goodPairCount t.val : ℤ) = r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen3 : 3 ≤ s.val.length) (hlen_max : s.val.length ≤ 50000)
        (hbytes : OnlyABC s.val), ∀ r : Std.I64, number_of_substrings s = ok r →
          ∀ (σ : Std.U8 → Std.U8), IsPermABC σ →
            ∀ t : Slice Std.U8, t.val = s.val.map σ → (goodPairCount t.val : ℤ) = r.val) := by
    sorry

  end AegisSpec.NumberOfSubstrings
