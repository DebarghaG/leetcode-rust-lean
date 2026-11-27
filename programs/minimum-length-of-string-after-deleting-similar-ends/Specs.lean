import Aegis.MinimumLength.Code.Funs

/-!
# Specifications of `Aegis.MinimumLength.minimum_length`

LeetCode problem `minimum-length-of-string-after-deleting-similar-ends`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumLength

  def IsABC (b : U8) : Prop := b.val = 97 ∨ b.val = 98 ∨ b.val = 99

  def AllABC (x : List U8) : Prop := ∀ (i : ℕ) (_h : i < x.length), IsABC x[i]

  def mid (x : List U8) (p q : ℕ) : List U8 := (x.drop p).take (x.length - (p + q))

  def sub (x : List U8) (l h : ℕ) : List U8 := (x.drop l).take (h - l)

  def Step (x y : List U8) : Prop :=
    ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ p + q ≤ x.length ∧
      ∃ c : U8, y = mid x p q ∧
        (∀ i : ℕ, i < p → x[i]? = some c) ∧
        (∀ j : ℕ, x.length - q ≤ j → j < x.length → x[j]? = some c)

  def Reach (x y : List U8) : Prop := Relation.ReflTransGen Step x y

  def ReachPos (x y : List U8) : Prop := Relation.TransGen Step x y

  def IsMinLength (x : List U8) (m : ℕ) : Prop :=
    (∀ y : List U8, Reach x y → m ≤ y.length) ∧ ∃ y : List U8, Reach x y ∧ y.length = m

  def prefixRun (x : List U8) (c : U8) : ℕ := (x.takeWhile (fun b => b == c)).length

  def suffixRun (x : List U8) (c : U8) : ℕ := (x.reverse.takeWhile (fun b => b == c)).length

  /-- For every s satisfying the preconditions, if minimum_length(s) returns a result r, then the integer value of r is exactly m(s), defined as follows. A one-step operation on a byte sequence x produces a byte sequence y when there exist integers p >= 1 and q >= 1 with p + q <= len(x) and a byte c such that y = x[p : len(x)-q], x[i] = c for every i with 0 <= i < p, and x[j] = c for every j with len(x)-q <= j < len(x); here x[p : len(x)-q] is the contiguous middle part after deleting the first p and last q bytes, and is empty when p + q = len(x). Let Reach(s) be the set of all byte sequences obtainable from s by zero or more one-step operations. Then m(s) = min { len(y) | y in Reach(s) }, and r = m(s).
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_1 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        ∃ m : ℕ, IsMinLength s.val m ∧ r.val = (m : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          ∃ m : ℕ, IsMinLength s.val m ∧ r.val = (m : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, minimum_length(s) returns a result r; in particular it does not fail because of overflow, panic, or an out-of-bounds access.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_2 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∃ r : I64, Aegis.MinimumLength.minimum_length s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∃ r : I64, Aegis.MinimumLength.minimum_length s = ok r) := by
    sorry

  /-- For every s satisfying the preconditions, whenever minimum_length(s) returns a result r, the integer r satisfies 0 <= r and r <= len(s).
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_3 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          0 ≤ r.val ∧ r.val ≤ (s.val.length : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, if len(s) = 1 or s[0] != s[len(s)-1], then whenever minimum_length(s) returns a result r, r = len(s).
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_4 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (hedge : s.val.length = 1 ∨ s.val[0] ≠ s.val[s.val.length - 1]) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        r.val = (s.val.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (hedge : s.val.length = 1 ∨ s.val[0] ≠ s.val[s.val.length - 1]), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          r.val = (s.val.length : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, if len(s) >= 2 and all bytes of s are equal, that is, there exists c in {97,98,99} such that s[i] = c for every i with 0 <= i < len(s), then whenever minimum_length(s) returns a result r, r = 0.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_5 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (hlen : 2 ≤ s.val.length)
      (hconst : ∃ c : U8, IsABC c ∧ ∀ (i : ℕ) (_h : i < s.val.length), s.val[i] = c) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (hlen : 2 ≤ s.val.length)
        (hconst : ∃ c : U8, IsABC c ∧ ∀ (i : ℕ) (_h : i < s.val.length), s.val[i] = c), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r → r.val = 0) := by
    sorry

  /-- For every s satisfying the preconditions, if len(s) >= 2 and s[0] = s[len(s)-1], then whenever minimum_length(s) returns a result r, r <= len(s) - 2.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_6 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (hlen : 2 ≤ s.val.length) (heq : s.val[0] = s.val[s.val.length - 1]) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        r.val ≤ (s.val.length : ℤ) - 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (hlen : 2 ≤ s.val.length) (heq : s.val[0] = s.val[s.val.length - 1]), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          r.val ≤ (s.val.length : ℤ) - 2) := by
    sorry

  /-- For every s satisfying the preconditions, suppose len(s) >= 2, s[0] = s[len(s)-1] = c for some byte c, and not every byte of s equals c. Let a be the largest integer such that 1 <= a <= len(s) and s[i] = c for every i with 0 <= i < a. Let b be the largest integer such that 1 <= b <= len(s) and s[j] = c for every j with len(s)-b <= j < len(s). If minimum_length(s) returns r and minimum_length(s[a : len(s)-b]) returns r_mid, then r = r_mid.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_7 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (hlen : 2 ≤ s.val.length) (c : U8) (hc : IsABC c)
      (hfirst : s.val[0] = c) (hlast : s.val[s.val.length - 1] = c)
      (hnotall : ¬ ∀ (i : ℕ) (_h : i < s.val.length), s.val[i] = c)
      (a : ℕ) (ha_pos : 1 ≤ a) (ha_le : a ≤ s.val.length)
      (ha_pre : ∀ i : ℕ, i < a → s.val[i]? = some c)
      (ha_max : ∀ a' : ℕ, 1 ≤ a' → a' ≤ s.val.length →
        (∀ i : ℕ, i < a' → s.val[i]? = some c) → a' ≤ a)
      (b : ℕ) (hb_pos : 1 ≤ b) (hb_le : b ≤ s.val.length)
      (hb_suf : ∀ j : ℕ, s.val.length - b ≤ j → j < s.val.length → s.val[j]? = some c)
      (hb_max : ∀ b' : ℕ, 1 ≤ b' → b' ≤ s.val.length →
        (∀ j : ℕ, s.val.length - b' ≤ j → j < s.val.length → s.val[j]? = some c) → b' ≤ b)
      (r : I64) (hr : Aegis.MinimumLength.minimum_length s = ok r) :
      ∀ (t : Slice U8) (r_mid : I64), t.val = sub s.val a (s.val.length - b) →
        Aegis.MinimumLength.minimum_length t = ok r_mid → r = r_mid := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (hlen : 2 ≤ s.val.length) (c : U8) (hc : IsABC c)
        (hfirst : s.val[0] = c) (hlast : s.val[s.val.length - 1] = c)
        (hnotall : ¬ ∀ (i : ℕ) (_h : i < s.val.length), s.val[i] = c)
        (a : ℕ) (ha_pos : 1 ≤ a) (ha_le : a ≤ s.val.length)
        (ha_pre : ∀ i : ℕ, i < a → s.val[i]? = some c)
        (ha_max : ∀ a' : ℕ, 1 ≤ a' → a' ≤ s.val.length →
          (∀ i : ℕ, i < a' → s.val[i]? = some c) → a' ≤ a)
        (b : ℕ) (hb_pos : 1 ≤ b) (hb_le : b ≤ s.val.length)
        (hb_suf : ∀ j : ℕ, s.val.length - b ≤ j → j < s.val.length → s.val[j]? = some c)
        (hb_max : ∀ b' : ℕ, 1 ≤ b' → b' ≤ s.val.length →
          (∀ j : ℕ, s.val.length - b' ≤ j → j < s.val.length → s.val[j]? = some c) → b' ≤ b)
        (r : I64) (hr : Aegis.MinimumLength.minimum_length s = ok r), ∀ (t : Slice U8) (r_mid : I64), t.val = sub s.val a (s.val.length - b) →
          Aegis.MinimumLength.minimum_length t = ok r_mid → r = r_mid) := by
    sorry

  /-- For every s satisfying the preconditions, let t be the reversal of s: len(t) = len(s) and t[i] = s[len(s)-1-i] for every i with 0 <= i < len(s). If minimum_length(s) returns r and minimum_length(t) returns r_rev, then r = r_rev.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_8 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (t : Slice U8) (ht : t.val = s.val.reverse) :
      ∀ (r r_rev : I64), Aegis.MinimumLength.minimum_length s = ok r →
        Aegis.MinimumLength.minimum_length t = ok r_rev → r = r_rev := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (t : Slice U8) (ht : t.val = s.val.reverse), ∀ (r r_rev : I64), Aegis.MinimumLength.minimum_length s = ok r →
          Aegis.MinimumLength.minimum_length t = ok r_rev → r = r_rev) := by
    sorry

  /-- For every s satisfying the preconditions and every bijection f from the set {97,98,99} to itself, let t be the byte sequence with len(t)=len(s) and t[i]=f(s[i]) for every i with 0 <= i < len(s). If minimum_length(s) returns r and minimum_length(t) returns r', then r = r'.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_9 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (f : U8 → U8) (hf_maps : ∀ b : U8, IsABC b → IsABC (f b))
      (hf_inj : ∀ b₁ b₂ : U8, IsABC b₁ → IsABC b₂ → f b₁ = f b₂ → b₁ = b₂)
      (t : Slice U8) (ht : t.val = s.val.map f) :
      ∀ (r r' : I64), Aegis.MinimumLength.minimum_length s = ok r →
        Aegis.MinimumLength.minimum_length t = ok r' → r = r' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (f : U8 → U8) (hf_maps : ∀ b : U8, IsABC b → IsABC (f b))
        (hf_inj : ∀ b₁ b₂ : U8, IsABC b₁ → IsABC b₂ → f b₁ = f b₂ → b₁ = b₂)
        (t : Slice U8) (ht : t.val = s.val.map f), ∀ (r r' : I64), Aegis.MinimumLength.minimum_length s = ok r →
          Aegis.MinimumLength.minimum_length t = ok r' → r = r') := by
    sorry

  /-- For every s satisfying the preconditions, if minimum_length(s) returns a result r and r = len(s), then len(s) = 1 or s[0] != s[len(s)-1].
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_10 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        r.val = (s.val.length : ℤ) →
          s.val.length = 1 ∨ s.val[0] ≠ s.val[s.val.length - 1] := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          r.val = (s.val.length : ℤ) →
            s.val.length = 1 ∨ s.val[0] ≠ s.val[s.val.length - 1]) := by
    sorry

  /-- For every s satisfying the preconditions, whenever minimum_length(s) returns a result r, there exists a byte sequence t obtainable from s by zero or more operations of the following form: replace x by x[p : len(x)-q] for some p >= 1 and q >= 1 with p+q <= len(x) and some byte c such that the first p bytes of x and the last q bytes of x are all c. Moreover, len(t) = r, and if r > 0 then either len(t) = 1 or t[0] != t[len(t)-1].
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_11 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        ∃ t : List U8, Reach s.val t ∧ (t.length : ℤ) = r.val ∧
          (0 < r.val → t.length = 1 ∨ t[0]? ≠ t[t.length - 1]?) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          ∃ t : List U8, Reach s.val t ∧ (t.length : ℤ) = r.val ∧
            (0 < r.val → t.length = 1 ∨ t[0]? ≠ t[t.length - 1]?)) := by
    sorry

  /-- For every s satisfying the preconditions, whenever minimum_length(s) returns a result r, there exist integers l and h with 0 <= l <= h <= len(s) such that the contiguous slice s[l : h] is obtainable from s by zero or more operations of deleting a non-empty equal-character prefix and a non-overlapping equal-character suffix of the same character, and the integer r equals h - l.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). -/
  theorem spec_12 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val) :
      ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
        ∃ l h : ℕ, l ≤ h ∧ h ≤ s.val.length ∧ Reach s.val (sub s.val l h) ∧
          r.val = ((h - l : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val), ∀ r : I64, Aegis.MinimumLength.minimum_length s = ok r →
          ∃ l h : ℕ, l ≤ h ∧ h ≤ s.val.length ∧ Reach s.val (sub s.val l h) ∧
            r.val = ((h - l : ℕ) : ℤ)) := by
    sorry

  /-- For every s and y satisfying the preconditions, if minimum_length(s) returns a result r and minimum_length(y) returns a result r_y, then r <= r_y.
    Preconditions: len(s) >= 1 and len(s) <= 100000, and for every i with 0 <= i < len(s), s[i] is one of the ASCII bytes 97 ('a'), 98 ('b'), or 99 ('c'). Also, y is a byte sequence obtainable from s by one or more one-step operations as defined in spec_1, and len(y) >= 1. -/
  theorem spec_13 (s : Slice U8)
      (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
      (hbytes : AllABC s.val)
      (y : Slice U8) (hy : ReachPos s.val y.val) (hy_pos : 1 ≤ y.val.length) :
      ∀ (r r_y : I64), Aegis.MinimumLength.minimum_length s = ok r →
        Aegis.MinimumLength.minimum_length y = ok r_y → r.val ≤ r_y.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8)
        (hlen_pos : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 100000)
        (hbytes : AllABC s.val)
        (y : Slice U8) (hy : ReachPos s.val y.val) (hy_pos : 1 ≤ y.val.length), ∀ (r r_y : I64), Aegis.MinimumLength.minimum_length s = ok r →
          Aegis.MinimumLength.minimum_length y = ok r_y → r.val ≤ r_y.val) := by
    sorry

  end AegisSpec.MinimumLength
