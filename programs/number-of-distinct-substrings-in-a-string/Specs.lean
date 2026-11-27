import Aegis.CountDistinct.Code.Funs

/-!
# Specifications of `Aegis.CountDistinct.count_distinct`

LeetCode problem `number-of-distinct-substrings-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountDistinct

  namespace AegisSpec.CountDistinct

  open Aeneas Aeneas.Std Result

  def byteValues (l : List U8) : Finset ℕ := (l.map (fun b => b.val)).toFinset

  def distinctByteCount (l : List U8) : ℕ := (byteValues l).card

  def SubstringOf (l t : List U8) : Prop :=
    ∃ i L : ℕ, 1 ≤ L ∧ i + L ≤ l.length ∧ t.length = L ∧
      ∀ (k : ℕ), k < L → t[k]? = l[i + k]?

  def D (l : List U8) : Set (List U8) := {t | SubstringOf l t}

  def OccursAt (t s : List U8) (p : ℕ) : Prop :=
    p + s.length ≤ t.length ∧ ∀ (i : ℕ), i < s.length → s[i]? = t[p + i]?

  def OccursIn (t s : List U8) : Prop := ∃ p : ℕ, OccursAt t s p

  def distinctSubstringBound (n k : ℕ) : ℕ :=
    Finset.sum (Finset.Icc 1 n) (fun L => min (n - L + 1) (k ^ L))

  /-- Whenever count_distinct(s) returns a result r, r equals the cardinality of the set D(s) of all finite non-empty byte sequences t for which there exist integers i and L with 0 <= i, L >= 1, i + L <= n, len(t) = L, and t[k] = s[i+k] for every k with 0 <= k < L. Equivalently, r is the number of distinct non-empty contiguous substrings of s, each distinct substring counted once regardless of how many positions at which it occurs.
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
      ∀ r : I64, count_distinct s = ok r → r.val = ((D s.val).ncard : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∀ r : I64, count_distinct s = ok r → r.val = ((D s.val).ncard : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, count_distinct(s) returns a result r; that is, it does not fail, overflow, or panic.
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
      ∃ r : I64, count_distinct s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∃ r : I64, count_distinct s = ok r) := by
    sorry

  /-- Whenever count_distinct(s) returns a result r, r >= n, where n = len(s).
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
      ∀ r : I64, count_distinct s = ok r → (n : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∀ r : I64, count_distinct s = ok r → (n : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever count_distinct(s) returns a result r, r <= n*(n+1)/2, where n = len(s).
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
      ∀ r : I64,
        count_distinct s = ok r → r.val ≤ ((n : ℤ) * ((n : ℤ) + 1)) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∀ r : I64,
          count_distinct s = ok r → r.val ≤ ((n : ℤ) * ((n : ℤ) + 1)) / 2) := by
    sorry

  /-- Let k be the number of distinct byte values among s[0],...,s[n-1]. Whenever count_distinct(s) returns a result r, r <= sum_{L=1}^{n} min(n - L + 1, k^L).
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122) :
      ∀ r : I64,
        count_distinct s = ok r →
          r.val ≤ ((distinctSubstringBound n (distinctByteCount s.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122), ∀ r : I64,
          count_distinct s = ok r →
            r.val ≤ ((distinctSubstringBound n (distinctByteCount s.val) : ℕ) : ℤ)) := by
    sorry

  /-- Let t be the byte slice of length n with t[i] = s[n-1-i] for every 0 <= i < n. Whenever count_distinct(s) returns r_s and count_distinct(t) returns r_t, r_s = r_t.
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_6 (s t : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
      (ht : t.val = s.val.reverse) :
      ∀ r_s r_t : I64,
        count_distinct s = ok r_s → count_distinct t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
        (ht : t.val = s.val.reverse), ∀ r_s r_t : I64,
          count_distinct s = ok r_s → count_distinct t = ok r_t → r_s = r_t) := by
    sorry

  /-- Let f be any injective function from the set {97,...,122} of lowercase ASCII codes to itself, and let t be the byte slice of length n with t[i] = f(s[i]) for every 0 <= i < n. Whenever count_distinct(s) returns r_s and count_distinct(t) returns r_t, r_s = r_t.
    Preconditions: s is a byte slice, n = len(s), 1 <= n <= 500, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
  theorem spec_7 (s t : Slice U8) (n : ℕ) (hn : n = s.val.length)
      (hpos : 1 ≤ n) (hmax : n ≤ 500)
      (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
      (f : ℕ → ℕ)
      (hf_range : ∀ x : ℕ, 97 ≤ x → x ≤ 122 → 97 ≤ f x ∧ f x ≤ 122)
      (hf_inj : ∀ x y : ℕ, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → f x = f y → x = y)
      (ht : t.val.map (fun b => b.val) = s.val.map (fun b => f b.val)) :
      ∀ r_s r_t : I64,
        count_distinct s = ok r_s → count_distinct t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice U8) (n : ℕ) (hn : n = s.val.length)
        (hpos : 1 ≤ n) (hmax : n ≤ 500)
        (hbytes : ∀ (i : ℕ) (_ : i < n), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
        (f : ℕ → ℕ)
        (hf_range : ∀ x : ℕ, 97 ≤ x → x ≤ 122 → 97 ≤ f x ∧ f x ≤ 122)
        (hf_inj : ∀ x y : ℕ, 97 ≤ x → x ≤ 122 → 97 ≤ y → y ≤ 122 → f x = f y → x = y)
        (ht : t.val.map (fun b => b.val) = s.val.map (fun b => f b.val)), ∀ r_s r_t : I64,
          count_distinct s = ok r_s → count_distinct t = ok r_t → r_s = r_t) := by
    sorry

  /-- If s occurs as a contiguous substring of t, meaning there exists an integer p with 0 <= p and p + len(s) <= len(t) such that for every i with 0 <= i < len(s), s[i] = t[p+i], then whenever count_distinct(s) returns r_s and count_distinct(t) returns r_t, r_s <= r_t.
    Preconditions: s and t are byte slices, each with length between 1 and 500 inclusive, and every byte of each slice is in the range 97 through 122 inclusive. -/
  theorem spec_8 (s t : Slice U8) (ns nt : ℕ)
      (hns : ns = s.val.length) (hnt : nt = t.val.length)
      (hs_pos : 1 ≤ ns) (hs_max : ns ≤ 500) (ht_pos : 1 ≤ nt) (ht_max : nt ≤ 500)
      (hbytes_s : ∀ (i : ℕ) (_ : i < ns), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
      (hbytes_t : ∀ (i : ℕ) (_ : i < nt), 97 ≤ t.val[i].val ∧ t.val[i].val ≤ 122)
      (hocc : OccursIn t.val s.val) :
      ∀ r_s r_t : I64,
        count_distinct s = ok r_s → count_distinct t = ok r_t → r_s.val ≤ r_t.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice U8) (ns nt : ℕ)
        (hns : ns = s.val.length) (hnt : nt = t.val.length)
        (hs_pos : 1 ≤ ns) (hs_max : ns ≤ 500) (ht_pos : 1 ≤ nt) (ht_max : nt ≤ 500)
        (hbytes_s : ∀ (i : ℕ) (_ : i < ns), 97 ≤ s.val[i].val ∧ s.val[i].val ≤ 122)
        (hbytes_t : ∀ (i : ℕ) (_ : i < nt), 97 ≤ t.val[i].val ∧ t.val[i].val ≤ 122)
        (hocc : OccursIn t.val s.val), ∀ r_s r_t : I64,
          count_distinct s = ok r_s → count_distinct t = ok r_t → r_s.val ≤ r_t.val) := by
    sorry

  end AegisSpec.CountDistinct
