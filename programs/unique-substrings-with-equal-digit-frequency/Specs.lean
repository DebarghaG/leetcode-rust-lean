import Aegis.EqualDigitFrequency.Code.Funs

/-!
# Specifications of `Aegis.EqualDigitFrequency.equal_digit_frequency`

LeetCode problem `unique-substrings-with-equal-digit-frequency`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.EqualDigitFrequency

  def bytesOf (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def AllDigits (l : List ℕ) : Prop := ∀ c ∈ l, 48 ≤ c ∧ c ≤ 57

  def cnt (x : List ℕ) (d : ℕ) : ℕ := x.count (48 + d)

  def Balanced (x : List ℕ) : Prop :=
    ∀ d e : ℕ, d ≤ 9 → e ≤ 9 → 0 < cnt x d → 0 < cnt x e → cnt x d = cnt x e

  def IsContiguousSubstring (x : List ℕ) (s : List ℕ) : Prop :=
    ∃ i j : ℕ, i ≤ j ∧ j < s.length ∧ x.length = j - i + 1 ∧
      ∀ t : ℕ, t < x.length → x[t]? = s[i + t]?

  def substrSet (s : List ℕ) : Finset (List ℕ) :=
    ((Finset.range (s.length + 1)).product (Finset.range (s.length + 1))).biUnion
      (fun p : ℕ × ℕ =>
        if p.1 ≤ p.2 ∧ p.2 < s.length then {(s.drop p.1).take (p.2 - p.1 + 1)} else ∅)

  noncomputable def balancedSubstrSet (s : List ℕ) : Finset (List ℕ) := by
    classical
    exact (substrSet s).filter (fun x => x ≠ [] ∧ Balanced x)

  def digitSet (s : List ℕ) : Finset ℕ := (Finset.range 10).filter (fun d => 0 < cnt s d)

  def pairSet (s : List ℕ) : Finset (ℕ × ℕ) := (s.zip (s.drop 1)).toFinset

  def relabel (pi : ℕ → ℕ) (s : List ℕ) : List ℕ := s.map (fun c => 48 + pi (c - 48))

  def IsDigitPerm (pi : ℕ → ℕ) : Prop :=
    (∀ d : ℕ, d ≤ 9 → pi d ≤ 9) ∧ (∀ d e : ℕ, d ≤ 9 → e ≤ 9 → pi d = pi e → d = e)

  /-- The function returns a result r and r is the number of elements of the set { x | x is a nonempty contiguous substring of s and x is balanced }. Here x is a nonempty contiguous substring of s when there exist i,j with 0 <= i <= j < len(s), len(x) = j - i + 1, and x[t] = s[i+t] for every 0 <= t < len(x); the set is taken with list equality, so identical byte sequences occurring at different positions count once.
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. For a nonempty digit byte list x and d in {0,...,9}, let cnt(x,d) be the number of indices j with 0 <= j < len(x) and x[j] = 48 + d. Call x balanced when for all d,e in {0,...,9}, if cnt(x,d) > 0 and cnt(x,e) > 0 then cnt(x,d) = cnt(x,e). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s)) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        r.val = (((balancedSubstrSet (bytesOf s)).card : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s)), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          r.val = (((balancedSubstrSet (bytesOf s)).card : ℕ) : ℤ)) := by
    sorry

  /-- For every input s satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s)) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s)), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r) := by
    sorry

  /-- The function returns a result r and r >= |D| + |P|, where D = { d in {0,...,9} | there exists i with 0 <= i < len(s) and s[i] = 48+d } and P = { (s[i], s[i+1]) | 0 <= i < len(s)-1 } (P is a set of ordered pairs of byte values).
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s)) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        ((digitSet (bytesOf s)).card : ℤ) + ((pairSet (bytesOf s)).card : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s)), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          ((digitSet (bytesOf s)).card : ℤ) + ((pairSet (bytesOf s)).card : ℤ) ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= len(s)*(len(s)+1)/2.
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s)) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        r.val ≤ (((s.val.length * (s.val.length + 1)) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s)), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          r.val ≤ (((s.val.length * (s.val.length + 1)) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: len(s) = 1 and 48 <= s[0] <= 57. -/
  theorem spec_5 (s : Slice Std.U8) (hlen : s.val.length = 1)
      (h0_ge : 48 ≤ (s.val[0]'(by omega)).val)
      (h0_le : (s.val[0]'(by omega)).val ≤ 57) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length = 1)
        (h0_ge : 48 ≤ (s.val[0]'(by omega)).val)
        (h0_le : (s.val[0]'(by omega)).val ≤ 57), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = 2 when s[0] = s[1], and r = 3 when s[0] != s[1].
    Preconditions: len(s) = 2 and 48 <= s[0] <= 57 and 48 <= s[1] <= 57. -/
  theorem spec_6 (s : Slice Std.U8) (hlen : s.val.length = 2)
      (h0_ge : 48 ≤ (s.val[0]'(by omega)).val) (h0_le : (s.val[0]'(by omega)).val ≤ 57)
      (h1_ge : 48 ≤ (s.val[1]'(by omega)).val) (h1_le : (s.val[1]'(by omega)).val ≤ 57) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        ((s.val[0]'(by omega)).val = (s.val[1]'(by omega)).val → r.val = 2) ∧
        ((s.val[0]'(by omega)).val ≠ (s.val[1]'(by omega)).val → r.val = 3) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length = 2)
        (h0_ge : 48 ≤ (s.val[0]'(by omega)).val) (h0_le : (s.val[0]'(by omega)).val ≤ 57)
        (h1_ge : 48 ≤ (s.val[1]'(by omega)).val) (h1_le : (s.val[1]'(by omega)).val ≤ 57), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          ((s.val[0]'(by omega)).val = (s.val[1]'(by omega)).val → r.val = 2) ∧
          ((s.val[0]'(by omega)).val ≠ (s.val[1]'(by omega)).val → r.val = 3)) := by
    sorry

  /-- The function returns a result r and r = n.
    Preconditions: len(s) = n with 1 <= n <= 1000; there is a byte c with 48 <= c <= 57 such that s[i] = c for every 0 <= i < n. -/
  theorem spec_7 (s : Slice Std.U8) (n : ℕ) (hlen : s.val.length = n)
      (hn_ge : 1 ≤ n) (hn_le : n ≤ 1000)
      (hconst : ∃ c : Std.U8, 48 ≤ c.val ∧ c.val ≤ 57 ∧ ∀ x ∈ bytesOf s, x = c.val) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        r.val = ((n : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hlen : s.val.length = n)
        (hn_ge : 1 ≤ n) (hn_le : n ≤ 1000)
        (hconst : ∃ c : Std.U8, 48 ≤ c.val ∧ c.val ≤ 57 ∧ ∀ x ∈ bytesOf s, x = c.val), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          r.val = ((n : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and r = n*(n+1)/2.
    Preconditions: len(s) = n with 1 <= n <= 1000; for every i with 0 <= i < n, 48 <= s[i] <= 57; and for all i,j with 0 <= i < j < n, s[i] != s[j]. -/
  theorem spec_8 (s : Slice Std.U8) (n : ℕ) (hlen : s.val.length = n)
      (hn_ge : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdigit : AllDigits (bytesOf s))
      (hnd : (bytesOf s).Nodup) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        r.val = (((n * (n + 1)) / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hlen : s.val.length = n)
        (hn_ge : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdigit : AllDigits (bytesOf s))
        (hnd : (bytesOf s).Nodup), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          r.val = (((n * (n + 1)) / 2 : ℕ) : ℤ)) := by
    sorry

  /-- Let rev(s) be the byte list of length n = len(s) with rev(s)[i] = s[n-1-i] for 0 <= i < n. The function returns a result r on s and a result r_rev on rev(s), and r = r_rev.
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_9 (s t : Slice Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s))
      (hrev : t.val = s.val.reverse) :
      ∃ r r_rev : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r_rev ∧ r = r_rev := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s))
        (hrev : t.val = s.val.reverse), ∃ r r_rev : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r_rev ∧ r = r_rev) := by
    sorry

  /-- The function returns a result r on s and a result r_perm on t, and r = r_perm.
    Preconditions: len(s) >= 1 and len(s) <= 1000, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. Let pi be any permutation of {0,...,9}, and define t by t[i] = 48 + pi(s[i]-48) for 0 <= i < len(s). -/
  theorem spec_10 (s t : Slice Std.U8) (pi : ℕ → ℕ) (hpi : IsDigitPerm pi)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
      (hdigit : AllDigits (bytesOf s))
      (hperm : bytesOf t = relabel pi (bytesOf s)) :
      ∃ r r_perm : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r_perm ∧ r = r_perm := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice Std.U8) (pi : ℕ → ℕ) (hpi : IsDigitPerm pi)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 1000)
        (hdigit : AllDigits (bytesOf s))
        (hperm : bytesOf t = relabel pi (bytesOf s)), ∃ r r_perm : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r_perm ∧ r = r_perm) := by
    sorry

  /-- Let r be the result returned on s and r' the result returned on t. Then r <= r'.
    Preconditions: len(s) >= 1 and len(s) <= 999, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. Let c be a byte with 48 <= c <= 57, and let t be the byte list of length len(s)+1 with t[i]=s[i] for 0 <= i < len(s) and t[len(s)]=c. -/
  theorem spec_11 (s t : Slice Std.U8) (c : Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
      (hdigit : AllDigits (bytesOf s))
      (hc_ge : 48 ≤ c.val) (hc_le : c.val ≤ 57)
      (ht : t.val = s.val ++ [c]) :
      ∃ r r' : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice Std.U8) (c : Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
        (hdigit : AllDigits (bytesOf s))
        (hc_ge : 48 ≤ c.val) (hc_le : c.val ≤ 57)
        (ht : t.val = s.val ++ [c]), ∃ r r' : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  /-- Let r be the result returned on s and r' the result returned on t. Then r' <= r + len(t).
    Preconditions: len(s) >= 1 and len(s) <= 999, and for every i with 0 <= i < len(s), 48 <= s[i] <= 57. Let c be a byte with 48 <= c <= 57, and let t be the byte list of length len(s)+1 with t[i]=s[i] for 0 <= i < len(s) and t[len(s)]=c. -/
  theorem spec_12 (s t : Slice Std.U8) (c : Std.U8)
      (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
      (hdigit : AllDigits (bytesOf s))
      (hc_ge : 48 ≤ c.val) (hc_le : c.val ≤ 57)
      (ht : t.val = s.val ++ [c]) :
      ∃ r r' : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r' ∧
        r'.val ≤ r.val + ((t.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice Std.U8) (c : Std.U8)
        (hlen_ge : 1 ≤ s.val.length) (hlen_le : s.val.length ≤ 999)
        (hdigit : AllDigits (bytesOf s))
        (hc_ge : 48 ≤ c.val) (hc_le : c.val ≤ 57)
        (ht : t.val = s.val ++ [c]), ∃ r r' : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          Aegis.EqualDigitFrequency.equal_digit_frequency t = ok r' ∧
          r'.val ≤ r.val + ((t.val.length : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and: r = 3 if s[0] = s[1] = s[2]; r = 6 if s[0], s[1], s[2] are pairwise distinct; otherwise (exactly two of the three bytes are equal) r = 4.
    Preconditions: len(s) = 3 and 48 <= s[0] <= 57 and 48 <= s[1] <= 57 and 48 <= s[2] <= 57. -/
  theorem spec_13 (s : Slice Std.U8) (hlen : s.val.length = 3)
      (h0_ge : 48 ≤ (s.val[0]'(by omega)).val) (h0_le : (s.val[0]'(by omega)).val ≤ 57)
      (h1_ge : 48 ≤ (s.val[1]'(by omega)).val) (h1_le : (s.val[1]'(by omega)).val ≤ 57)
      (h2_ge : 48 ≤ (s.val[2]'(by omega)).val) (h2_le : (s.val[2]'(by omega)).val ≤ 57) :
      ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
        (let a : ℕ := (s.val[0]'(by omega)).val
         let b : ℕ := (s.val[1]'(by omega)).val
         let c : ℕ := (s.val[2]'(by omega)).val
         (a = b ∧ b = c → r.val = 3) ∧
         (a ≠ b ∧ a ≠ c ∧ b ≠ c → r.val = 6) ∧
         (¬(a = b ∧ b = c) ∧ ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c) → r.val = 4)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8) (hlen : s.val.length = 3)
        (h0_ge : 48 ≤ (s.val[0]'(by omega)).val) (h0_le : (s.val[0]'(by omega)).val ≤ 57)
        (h1_ge : 48 ≤ (s.val[1]'(by omega)).val) (h1_le : (s.val[1]'(by omega)).val ≤ 57)
        (h2_ge : 48 ≤ (s.val[2]'(by omega)).val) (h2_le : (s.val[2]'(by omega)).val ≤ 57), ∃ r : Std.I64, Aegis.EqualDigitFrequency.equal_digit_frequency s = ok r ∧
          (let a : ℕ := (s.val[0]'(by omega)).val
           let b : ℕ := (s.val[1]'(by omega)).val
           let c : ℕ := (s.val[2]'(by omega)).val
           (a = b ∧ b = c → r.val = 3) ∧
           (a ≠ b ∧ a ≠ c ∧ b ≠ c → r.val = 6) ∧
           (¬(a = b ∧ b = c) ∧ ¬(a ≠ b ∧ a ≠ c ∧ b ≠ c) → r.val = 4))) := by
    sorry

  end AegisSpec.EqualDigitFrequency
