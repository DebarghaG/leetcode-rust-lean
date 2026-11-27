import Aegis.HasSameDigits.Code.Funs

/-!
# Specifications of `Aegis.HasSameDigits.has_same_digits`

LeetCode problem `check-if-digits-are-equal-in-string-after-operations-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.HasSameDigits

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun u => u.val)

  def byteAt (s : Slice Std.U8) (i : ℕ) : ℕ := (bytes s).getD i 0

  def digits (s : Slice Std.U8) : List ℤ := (bytes s).map (fun b => (b : ℤ) - 48)

  def digitAt (s : Slice Std.U8) (i : ℕ) : ℤ := (digits s).getD i 0

  def AllDigits (s : Slice Std.U8) : Prop := ∀ u ∈ s.val, 48 ≤ u.val ∧ u.val ≤ 57

  def step (p : List ℤ) : List ℤ :=
    (List.range (p.length - 1)).map (fun i => (p.getD i 0 + p.getD (i + 1) 0) % 10)

  def P (d : List ℤ) : ℕ → List ℤ
    | 0 => d
    | t + 1 => step (P d t)

  def binomSum (d : List ℤ) (k : ℕ) : ℤ :=
    ((List.range (k + 1)).map
      (fun j => (Nat.choose k j : ℤ) * (d.getD j 0 - d.getD (j + 1) 0))).sum

  def binomRow (d : List ℤ) (t i : ℕ) : ℤ :=
    ((List.range (t + 1)).map (fun k => (Nat.choose t k : ℤ) * d.getD (i + k) 0)).sum % 10

  /-- Define P_0,...,P_{n-2} by: P_0 has length n and P_0[i] = d_i; for each t with 0 <= t <= n-3, P_{t+1} has length n-t-1 and P_{t+1}[i] = (P_t[i] + P_t[i+1]) mod 10 for every 0 <= i < n-t-1, where mod 10 gives the least nonnegative residue in {0,...,9}. Whenever has_same_digits(s) returns a result r, we have r = true if and only if P_{n-2}[0] = P_{n-2}[1]; equivalently r = false if and only if P_{n-2}[0] != P_{n-2}[1].
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. Write d_i = s[i] - 48 for 0 <= i < n. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s)
      (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r) :
      (r = true ↔
        (P (digits s) (s.val.length - 2)).getD 0 0 =
          (P (digits s) (s.val.length - 2)).getD 1 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s)
        (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r), (r = true ↔
          (P (digits s) (s.val.length - 2)).getD 0 0 =
            (P (digits s) (s.val.length - 2)).getD 1 0)) := by
    sorry

  /-- For every s satisfying the preconditions, evaluating has_same_digits(s) returns a result r (an Ok result containing a Bool); it does not fail, panic, access s out of bounds, or overflow a 64-bit integer while carrying out the computation.
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s) :
      ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s), ∃ r : Bool, Aegis.HasSameDigits.has_same_digits s = ok r) := by
    sorry

  /-- Whenever has_same_digits(s) returns a result r, we have r = true.
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. Write d_i = s[i] - 48 for 0 <= i < n. Assume there is a digit c with 0 <= c <= 9 such that d_i = c for every i with 0 <= i < n. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s)
      (hconst : ∃ c : ℤ, 0 ≤ c ∧ c ≤ 9 ∧ ∀ i, i < s.val.length → digitAt s i = c)
      (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r) :
      r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s)
        (hconst : ∃ c : ℤ, 0 ≤ c ∧ c ≤ 9 ∧ ∀ i, i < s.val.length → digitAt s i = c)
        (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r), r = true) := by
    sorry

  /-- If has_same_digits(s) returns a result r and has_same_digits(s') returns a result r', then r = r'.
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. Write d_i = s[i] - 48 for 0 <= i < n. Let c be an integer, and let s' be the byte slice of length n with s'[i] = 48 + ((d_i + c) mod 10) for every 0 <= i < n. -/
  theorem spec_4 (s s' : Slice Std.U8) (c : ℤ)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s)
      (hlen' : s'.val.length = s.val.length)
      (hshift : ∀ i, i < s.val.length →
        (byteAt s' i : ℤ) = 48 + ((digitAt s i + c) % 10))
      (r r' : Bool)
      (h : Aegis.HasSameDigits.has_same_digits s = ok r)
      (h' : Aegis.HasSameDigits.has_same_digits s' = ok r') :
      r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s s' : Slice Std.U8) (c : ℤ)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s)
        (hlen' : s'.val.length = s.val.length)
        (hshift : ∀ i, i < s.val.length →
          (byteAt s' i : ℤ) = 48 + ((digitAt s i + c) % 10))
        (r r' : Bool)
        (h : Aegis.HasSameDigits.has_same_digits s = ok r)
        (h' : Aegis.HasSameDigits.has_same_digits s' = ok r'), r = r') := by
    sorry

  /-- If has_same_digits(s) returns a result r and has_same_digits(s_rev) returns a result r_rev, then r = r_rev.
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. Let s_rev be the byte slice of length n with s_rev[i] = s[n-1-i] for every 0 <= i < n. -/
  theorem spec_5 (s srev : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s)
      (hlenrev : srev.val.length = s.val.length)
      (hrev : ∀ i, i < s.val.length → byteAt srev i = byteAt s (s.val.length - 1 - i))
      (r rrev : Bool)
      (h : Aegis.HasSameDigits.has_same_digits s = ok r)
      (h' : Aegis.HasSameDigits.has_same_digits srev = ok rrev) :
      r = rrev := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s srev : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s)
        (hlenrev : srev.val.length = s.val.length)
        (hrev : ∀ i, i < s.val.length → byteAt srev i = byteAt s (s.val.length - 1 - i))
        (r rrev : Bool)
        (h : Aegis.HasSameDigits.has_same_digits s = ok r)
        (h' : Aegis.HasSameDigits.has_same_digits srev = ok rrev), r = rrev) := by
    sorry

  /-- Whenever has_same_digits(s) returns a result r, we have r = true if and only if the integer sum from j=0 to n-2 of C(n-2,j) * (d_j - d_{j+1}) is divisible by 10, where C(a,b) is the usual binomial coefficient. Equivalently, r = false if and only if that sum is not divisible by 10.
    Preconditions: Let n = len(s). Assume 3 <= n <= 100000 and for every i with 0 <= i < n, 48 <= s[i] <= 57. Write d_i = s[i] - 48 for 0 <= i < n. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
      (hdigits : AllDigits s)
      (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r) :
      (r = true ↔ (10 : ℤ) ∣ binomSum (digits s) (s.val.length - 2)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen_lo : 3 ≤ s.val.length) (hlen_hi : s.val.length ≤ 100000)
        (hdigits : AllDigits s)
        (r : Bool) (h : Aegis.HasSameDigits.has_same_digits s = ok r), (r = true ↔ (10 : ℤ) ∣ binomSum (digits s) (s.val.length - 2))) := by
    sorry

  end AegisSpec.HasSameDigits
