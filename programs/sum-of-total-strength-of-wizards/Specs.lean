import Aegis.TotalStrength.Code.Funs

/-!
# Specifications of `Aegis.TotalStrength.total_strength`

LeetCode problem `sum-of-total-strength-of-wizards`. Each `spec_<n>` theorem states one property of the function.
-/

namespace AegisSpec.TotalStrength

def M : ℤ := 1000000007

def vals (s : Aeneas.Std.Slice Aeneas.Std.I64) : List ℤ := s.val.map fun x => x.val

def windowMin (l : List ℤ) (lo hi : ℕ) : ℤ :=
  ((l.drop lo).take (hi + 1 - lo)).foldr min (l.getD lo 0)

def windowSum (l : List ℤ) (lo hi : ℕ) : ℤ :=
  ((l.drop lo).take (hi + 1 - lo)).sum

def totalStrength (l : List ℤ) : ℤ :=
  (Finset.range l.length).sum fun lo =>
    (Finset.range l.length).sum fun hi =>
      if lo ≤ hi then windowMin l lo hi * windowSum l lo hi else 0

/-- Let M = 1000000007 and n = len(strength). Define T(strength) = sum over all pairs (l,r) with 0 <= l <= r < n of (min_{l <= k <= r} strength[k]) * (sum_{k=l}^{r} strength[k]). The function returns a result r (it does not fail) such that 0 <= r < M and r ≡ T(strength) (mod M); equivalently, r is the least nonnegative remainder of T(strength) modulo M.
  Preconditions: strength is a slice of 64-bit integers with 1 <= len(strength) <= 100000, and for every i with 0 <= i < len(strength), 1 <= strength[i] <= 1000000000. -/
theorem spec_1 (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = totalStrength (vals strength) % M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = totalStrength (vals strength) % M) := by
  sorry

/-- Let M = 1000000007 and a = strength[0]. The function returns a result r and r = (a * a) mod M, where mod M denotes the least nonnegative remainder.
  Preconditions: strength is a slice of 64-bit integers with len(strength) = 1 and 1 <= strength[0] <= 1000000000. -/
theorem spec_2 (strength : Aeneas.Std.Slice Aeneas.Std.I64) (a : ℤ)
    (hlen : strength.val.length = 1) (hval : vals strength = [a])
    (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (a * a) % M := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64) (a : ℤ)
    (hlen : strength.val.length = 1) (hval : vals strength = [a])
    (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (a * a) % M) := by
  sorry

/-- Let M = 1000000007, a = strength[0], and b = strength[1]. The function returns a result r and r = (a*a + b*b + min(a,b)*(a+b)) mod M, where mod M denotes the least nonnegative remainder.
  Preconditions: strength is a slice of 64-bit integers with len(strength) = 2, 1 <= strength[0] <= 1000000000, and 1 <= strength[1] <= 1000000000. -/
theorem spec_3 (strength : Aeneas.Std.Slice Aeneas.Std.I64) (a b : ℤ)
    (hlen : strength.val.length = 2) (hval : vals strength = [a, b])
    (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (a * a + b * b + min a b * (a + b)) % M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64) (a b : ℤ)
    (hlen : strength.val.length = 2) (hval : vals strength = [a, b])
    (ha1 : 1 ≤ a) (ha2 : a ≤ 1000000000)
    (hb1 : 1 ≤ b) (hb2 : b ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (a * a + b * b + min a b * (a + b)) % M) := by
  sorry

/-- Let M = 1000000007. The function returns a result r and r = (x*x * (n*(n+1)*(n+2)/6)) mod M, where the division by 6 is exact integer division; equivalently, r = (x^2 * C(n+2,3)) mod M.
  Preconditions: strength is a slice of 64-bit integers with n = len(strength), 1 <= n <= 100000, and there is an integer x with 1 <= x <= 1000000000 such that strength[i] = x for every i with 0 <= i < n. -/
theorem spec_4 (strength : Aeneas.Std.Slice Aeneas.Std.I64) (x : ℤ)
    (hn1 : 1 ≤ strength.val.length) (hn2 : strength.val.length ≤ 100000)
    (hconst : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val = x)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 1000000000) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (x * x *
          ((strength.val.length : ℤ) * ((strength.val.length : ℤ) + 1) *
            ((strength.val.length : ℤ) + 2) / 6)) % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64) (x : ℤ)
    (hn1 : 1 ≤ strength.val.length) (hn2 : strength.val.length ≤ 100000)
    (hconst : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val = x)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 1000000000), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        r.val = (x * x *
          ((strength.val.length : ℤ) * ((strength.val.length : ℤ) + 1) *
            ((strength.val.length : ℤ) + 2) / 6)) % M) := by
  sorry

/-- Let n = len(strength) and define rev by rev[i] = strength[n-1-i] for 0 <= i < n. Let r be the result returned by the function on strength and r_rev the result returned on rev. The function returns both results, and r = r_rev.
  Preconditions: strength is a slice of 64-bit integers with 1 <= len(strength) <= 100000 and, for every i with 0 <= i < len(strength), 1 <= strength[i] <= 1000000000. -/
theorem spec_5 (strength rev : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000)
    (hrev : vals rev = (vals strength).reverse) :
    ∃ r r_rev : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        Aegis.TotalStrength.total_strength rev = Aeneas.Std.Result.ok r_rev ∧
          r.val = r_rev.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strength rev : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000)
    (hrev : vals rev = (vals strength).reverse), ∃ r r_rev : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        Aegis.TotalStrength.total_strength rev = Aeneas.Std.Result.ok r_rev ∧
          r.val = r_rev.val) := by
  sorry

/-- Let M = 1000000007 and define scaled[i] = c * strength[i]. Let r be the result returned by the function on strength and r_c the result returned on scaled. The function returns both results, and r_c ≡ c^2 * r (mod M); equivalently, r_c = (c^2 * r) mod M using the least nonnegative remainder.
  Preconditions: strength is a slice of 64-bit integers with 1 <= len(strength) <= 100000 and, for every i with 0 <= i < len(strength), 1 <= strength[i] <= 1000000000. Also c is an integer with c >= 1 and c*strength[i] <= 1000000000 for every i with 0 <= i < len(strength). -/
theorem spec_6 (strength scaled : Aeneas.Std.Slice Aeneas.Std.I64) (c : ℤ)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000)
    (hc : 1 ≤ c)
    (hbound : ∀ i (h : i < strength.val.length), c * (strength.val[i]'h).val ≤ 1000000000)
    (hscaled : vals scaled = (vals strength).map fun x => c * x) :
    ∃ r r_c : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        Aegis.TotalStrength.total_strength scaled = Aeneas.Std.Result.ok r_c ∧
          r_c.val = (c * c * r.val) % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (strength scaled : Aeneas.Std.Slice Aeneas.Std.I64) (c : ℤ)
    (hlen1 : 1 ≤ strength.val.length) (hlen2 : strength.val.length ≤ 100000)
    (hpos : ∀ i (h : i < strength.val.length), 1 ≤ (strength.val[i]'h).val)
    (hle : ∀ i (h : i < strength.val.length), (strength.val[i]'h).val ≤ 1000000000)
    (hc : 1 ≤ c)
    (hbound : ∀ i (h : i < strength.val.length), c * (strength.val[i]'h).val ≤ 1000000000)
    (hscaled : vals scaled = (vals strength).map fun x => c * x), ∃ r r_c : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧
        Aegis.TotalStrength.total_strength scaled = Aeneas.Std.Result.ok r_c ∧
          r_c.val = (c * c * r.val) % M) := by
  sorry

/-- The function returns a result r and r = 44.
  Preconditions: len(strength) = 4, strength[0] = 1, strength[1] = 3, strength[2] = 1, strength[3] = 2. -/
theorem spec_7 (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 4) (hval : vals strength = [1, 3, 1, 2]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 44 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 4) (hval : vals strength = [1, 3, 1, 2]), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 44) := by
  sorry

/-- The function returns a result r and r = 213.
  Preconditions: len(strength) = 3, strength[0] = 5, strength[1] = 4, strength[2] = 6. -/
theorem spec_8 (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 3) (hval : vals strength = [5, 4, 6]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 213 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 3) (hval : vals strength = [5, 4, 6]), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 213) := by
  sorry

/-- The function returns a result r and r = 196.
  Preconditions: len(strength) = 2, strength[0] = 1000000000, strength[1] = 1000000000. -/
theorem spec_9 (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 2)
    (hval : vals strength = [1000000000, 1000000000]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 196 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 2)
    (hval : vals strength = [1000000000, 1000000000]), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 196) := by
  sorry

/-- The function returns a result r and r = 490.
  Preconditions: len(strength) = 3 and strength[0] = strength[1] = strength[2] = 1000000000. -/
theorem spec_10 (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 3)
    (hval : vals strength = [1000000000, 1000000000, 1000000000]) :
    ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 490 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strength : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen : strength.val.length = 3)
    (hval : vals strength = [1000000000, 1000000000, 1000000000]), ∃ r : Aeneas.Std.I64,
      Aegis.TotalStrength.total_strength strength = Aeneas.Std.Result.ok r ∧ r.val = 490) := by
  sorry

end AegisSpec.TotalStrength
