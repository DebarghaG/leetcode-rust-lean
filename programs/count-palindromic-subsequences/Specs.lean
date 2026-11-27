import Aegis.CountPalindromes.Code.Funs

/-!
# Specifications of `Aegis.CountPalindromes.count_palindromes`

LeetCode problem `count-palindromic-subsequences`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountPalindromes

  namespace AegisSpec.CountPalindromes

  def MOD : ℤ := 1000000007

  def IsPalTuple (l : List Std.U8) (i : Fin 5 → Fin l.length) : Prop :=
    i 0 < i 1 ∧ i 1 < i 2 ∧ i 2 < i 3 ∧ i 3 < i 4 ∧
      (l.get (i 0)).val = (l.get (i 4)).val ∧ (l.get (i 1)).val = (l.get (i 3)).val

  instance instDecidableIsPalTuple (l : List Std.U8) (i : Fin 5 → Fin l.length) :
      Decidable (IsPalTuple l i) := by
    unfold IsPalTuple
    infer_instance

  def palCount (l : List Std.U8) : ℕ :=
    ((Finset.univ : Finset (Fin 5 → Fin l.length)).filter (fun i => IsPalTuple l i)).card

  def byteValAt (s : Slice Std.U8) (i : ℕ) : Option ℕ := (s.val[i]?).map (fun b => b.val)

  /-- The function returns a result r and r = P(s) mod 1000000007, where P(s) is the number of index tuples (i0,i1,i2,i3,i4) such that 0 <= i0 < i1 < i2 < i3 < i4 < len(s), s[i0] = s[i4], and s[i1] = s[i3]. Different index tuples are counted separately even when they produce the same digit string, and 'mod 1000000007' denotes the unique integer in [0, 1000000007) congruent to P(s).
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧
        r.val = (palCount s.val : ℤ) % MOD := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧
          r.val = (palCount s.val : ℤ) % MOD) := by
    sorry

  /-- The function returns a result r and 0 <= r < 1000000007.
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧ 0 ≤ r.val ∧ r.val < MOD := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧ 0 ≤ r.val ∧ r.val < MOD) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r; in particular it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r) := by
    sorry

  /-- The function returns a result r and r = 0.
    Preconditions: 1 <= len(s) <= 4, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 4)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 4)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r, and r = 1 if s[0] = s[4] and s[1] = s[3], while r = 0 otherwise.
    Preconditions: len(s) = 5, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : s.val.length = 5)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧
        r.val = (if byteValAt s 0 = byteValAt s 4 ∧ byteValAt s 1 = byteValAt s 3
                 then 1 else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : s.val.length = 5)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧
          r.val = (if byteValAt s 0 = byteValAt s 4 ∧ byteValAt s 1 = byteValAt s 3
                   then 1 else 0)) := by
    sorry

  /-- The function returns a result r and r = C(n,5) mod 1000000007, where C(n,5) is the binomial coefficient and C(n,5) = 0 when n < 5.
    Preconditions: Let n = len(s). We have 1 <= n <= 10000, and there is a decimal-digit byte c such that s[i] = c for every i with 0 <= i < n. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hconst : ∃ c : Std.U8, 48 ≤ c.val ∧ c.val ≤ 57 ∧ ∀ b ∈ s.val, b = c) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧
        r.val = (Nat.choose s.val.length 5 : ℤ) % MOD := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hconst : ∃ c : Std.U8, 48 ≤ c.val ∧ c.val ≤ 57 ∧ ∀ b ∈ s.val, b = c), ∃ r : Std.I64, count_palindromes s = ok r ∧
          r.val = (Nat.choose s.val.length 5 : ℤ) % MOD) := by
    sorry

  /-- Let n = len(s) and let rev(s) be the byte sequence of length n defined by rev(s)[i] = s[n-1-i] for 0 <= i < n. The function returns a result r on input s and a result r_rev on input rev(s), and r = r_rev.
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_7 (s srev : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hrev : srev.val = s.val.reverse) :
      ∃ r rrev : Std.I64, count_palindromes s = ok r ∧ count_palindromes srev = ok rrev ∧
        r.val = rrev.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s srev : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hrev : srev.val = s.val.reverse), ∃ r rrev : Std.I64, count_palindromes s = ok r ∧ count_palindromes srev = ok rrev ∧
          r.val = rrev.val) := by
    sorry

  /-- The function returns a result r on input s and a result r' on input s', and r = r'.
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). Let D be the set of bytes occurring in s. Let f be a function from D to the set of decimal-digit bytes {48,...,57} such that f is injective on D. Define s' by s'[i] = f(s[i]) for 0 <= i < len(s). -/
  theorem spec_8 (s sp : Slice Std.U8) (g : Std.U8 → Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
      (hg_digit : ∀ b ∈ s.val, 48 ≤ (g b).val ∧ (g b).val ≤ 57)
      (hg_inj : ∀ b₁ ∈ s.val, ∀ b₂ ∈ s.val, g b₁ = g b₂ → b₁ = b₂)
      (hsp : sp.val = s.val.map g) :
      ∃ r r' : Std.I64, count_palindromes s = ok r ∧ count_palindromes sp = ok r' ∧
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s sp : Slice Std.U8) (g : Std.U8 → Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57)
        (hg_digit : ∀ b ∈ s.val, 48 ≤ (g b).val ∧ (g b).val ≤ 57)
        (hg_inj : ∀ b₁ ∈ s.val, ∀ b₂ ∈ s.val, g b₁ = g b₂ → b₁ = b₂)
        (hsp : sp.val = s.val.map g), ∃ r r' : Std.I64, count_palindromes s = ok r ∧ count_palindromes sp = ok r' ∧
          r.val = r'.val) := by
    sorry

  /-- The function returns a result r and 0 <= r <= C(n,5), where n = len(s), C(n,5) is the binomial coefficient, and C(n,5) = 0 when n < 5.
    Preconditions: len(s) is between 1 and 100 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_9 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧ 0 ≤ r.val ∧
        r.val ≤ (Nat.choose s.val.length 5 : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧ 0 ≤ r.val ∧
          r.val ≤ (Nat.choose s.val.length 5 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i0,i1,i2,i3,i4 such that 0 <= i0 < i1 < i2 < i3 < i4 < len(s), s[i0] = s[i4], and s[i1] = s[i3].
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_10 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∀ r : Std.I64, count_palindromes s = ok r → 0 < r.val →
        ∃ i : Fin 5 → Fin s.val.length, IsPalTuple s.val i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∀ r : Std.I64, count_palindromes s = ok r → 0 < r.val →
          ∃ i : Fin 5 → Fin s.val.length, IsPalTuple s.val i) := by
    sorry

  /-- Let n = len(s) and let P(s) be the count defined in spec_1. The function returns a result r, and P(s) <= C(n,5) (where C(n,5) is the binomial coefficient, with C(n,5)=0 for n<5). Consequently P(s) <= C(10000,5) < 2^63 and r <= C(n,5).
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_11 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧
        palCount s.val ≤ Nat.choose s.val.length 5 ∧
        palCount s.val ≤ Nat.choose 10000 5 ∧
        (palCount s.val : ℤ) < 2 ^ 63 ∧
        r.val ≤ (Nat.choose s.val.length 5 : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧
          palCount s.val ≤ Nat.choose s.val.length 5 ∧
          palCount s.val ≤ Nat.choose 10000 5 ∧
          (palCount s.val : ℤ) < 2 ^ 63 ∧
          r.val ≤ (Nat.choose s.val.length 5 : ℤ)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if P(s) is divisible by 1000000007, where P(s) is the count defined in spec_1.
    Preconditions: len(s) is between 1 and 10000 inclusive, and for every i with 0 <= i < len(s), s[i] is the ASCII code of a decimal digit (48 <= s[i] <= 57). -/
  theorem spec_12 (s : Slice Std.U8)
      (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
      (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57) :
      ∃ r : Std.I64, count_palindromes s = ok r ∧
        (r.val = 0 ↔ MOD ∣ (palCount s.val : ℤ)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 10000)
        (hdigits : ∀ b ∈ s.val, 48 ≤ b.val ∧ b.val ≤ 57), ∃ r : Std.I64, count_palindromes s = ok r ∧
          (r.val = 0 ↔ MOD ∣ (palCount s.val : ℤ))) := by
    sorry

  end AegisSpec.CountPalindromes
