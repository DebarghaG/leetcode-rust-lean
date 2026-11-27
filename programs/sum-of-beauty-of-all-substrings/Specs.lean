import Aegis.BeautySum.Code.Funs

/-!
# Specifications of `Aegis.BeautySum.beauty_sum`

LeetCode problem `sum-of-beauty-of-all-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BeautySum

  open Aegis.BeautySum

  def byteList (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def byteLen (s : Slice Std.U8) : ℕ := s.val.length

  def IsLower (c : ℕ) : Prop := 97 ≤ c ∧ c ≤ 122

  def IsLowerSlice (s : Slice Std.U8) : Prop := ∀ b ∈ s.val, IsLower b.val

  def AllBytesEqual (s : Slice Std.U8) : Prop :=
    ∀ (i j : ℕ) (hi : i < s.val.length) (hj : j < s.val.length),
      (s.val[i]).val = (s.val[j]).val

  def frag (l : List ℕ) (i j : ℕ) : List ℕ := (l.drop i).take (j + 1 - i)

  def occIn (l : List ℕ) (i j c : ℕ) : ℕ := (frag l i j).countP (fun x => decide (x = c))

  def OccursIn (l : List ℕ) (i j c : ℕ) : Prop :=
    ∃ (k : ℕ) (hk : k < (frag l i j).length), (frag l i j)[k] = c

  def freqs (l : List ℕ) (i j : ℕ) : List ℕ := (frag l i j).dedup.map (fun c => occIn l i j c)

  def listMax : List ℕ → ℕ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => max a b) x

  def listMin : List ℕ → ℕ
    | [] => 0
    | x :: xs => xs.foldl (fun a b => min a b) x

  def beauty (l : List ℕ) (i j : ℕ) : ℤ :=
    (listMax (freqs l i j) : ℤ) - (listMin (freqs l i j) : ℤ)

  def beautyTotal (l : List ℕ) : ℤ :=
    Finset.sum (Finset.range l.length) (fun i =>
      Finset.sum (Finset.range l.length) (fun j => if i ≤ j then beauty l i j else 0))

  def beautyWindowSum (l : List ℕ) (L : ℕ) : ℤ :=
    Finset.sum (Finset.range (l.length - L + 1)) (fun i => beauty l i (i + L - 1))

  def IsLowerPerm (σ : ℕ → ℕ) : Prop :=
    (∀ c, IsLower c → IsLower (σ c)) ∧
      (∀ d, IsLower d → ∃ c, IsLower c ∧ σ c = d) ∧
        (∀ c d, IsLower c → IsLower d → σ c = σ d → c = d)

  /-- Let n = len(s). For 0 <= i <= j < n and a lowercase letter c, let F(i,j,c) be the number of indices k with i <= k <= j and s[k] = c. Let P(i,j) be the set of lowercase letters c with F(i,j,c) > 0. Define the beauty of the contiguous nonempty substring s[i..j] as B(i,j) = max_{c in P(i,j)} F(i,j,c) - min_{c in P(i,j)} F(i,j,c). Then beauty_sum(s) returns a result r : I64 whose mathematical integer value is sum_{0 <= i <= j < n} B(i,j).
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), s[i] is an ASCII lowercase letter, i.e. 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = beautyTotal (byteList s) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s), ∃ r : I64, beauty_sum s = ok r ∧ r.val = beautyTotal (byteList s)) := by
    sorry

  /-- For every s satisfying the preconditions, beauty_sum(s) returns a result r : I64; it does not panic, return an error, access out of bounds, or overflow.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) :
      ∃ r : I64, beauty_sum s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s), ∃ r : I64, beauty_sum s = ok r) := by
    sorry

  /-- For every s satisfying the preconditions, if beauty_sum(s) returns r, then the mathematical integer value of r satisfies r >= 0.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r), 0 ≤ r.val) := by
    sorry

  /-- Let n = len(s). For every s satisfying the preconditions, if beauty_sum(s) returns r, then the mathematical integer value of r satisfies r <= (n * (n - 1) * (n + 1)) / 6, where the division is ordinary integer division and the numerator is divisible by 6.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r) :
      r.val ≤ (((byteLen s * (byteLen s - 1) * (byteLen s + 1)) / 6 : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r), r.val ≤ (((byteLen s * (byteLen s - 1) * (byteLen s + 1)) / 6 : ℕ) : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, beauty_sum(s) returns r with mathematical integer value 0.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, every byte of s is an ASCII lowercase letter, and all bytes of s are equal: s[i] = s[0] for every i with 0 <= i < len(s). -/
  theorem spec_5 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (heq : AllBytesEqual s) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (heq : AllBytesEqual s), ∃ r : I64, beauty_sum s = ok r ∧ r.val = 0) := by
    sorry

  /-- Let n = len(s). For 0 <= i <= j < n, let P(i,j) be the set of lowercase letters occurring in s[i..j], and let F(i,j,c) be the number of occurrences of c in s[i..j]. If beauty_sum(s) returns r, then r = 0 if and only if for every 0 <= i <= j < n and every c,d in P(i,j), F(i,j,c) = F(i,j,d).
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r) :
      (r.val = 0 ↔
        ∀ i j, i ≤ j → j < byteLen s →
          ∀ c d, OccursIn (byteList s) i j c → OccursIn (byteList s) i j d →
            occIn (byteList s) i j c = occIn (byteList s) i j d) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r), (r.val = 0 ↔
          ∀ i j, i ≤ j → j < byteLen s →
            ∀ c d, OccursIn (byteList s) i j c → OccursIn (byteList s) i j d →
              occIn (byteList s) i j c = occIn (byteList s) i j d)) := by
    sorry

  /-- Let n = len(s), and for 0 <= i <= j < n let B(i,j) be the beauty of s[i..j], namely the largest positive character frequency in that substring minus the smallest positive character frequency. If beauty_sum(s) returns r, then for every L with 1 <= L <= n, r >= sum_{i=0}^{n-L} B(i,i+L-1).
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r) :
      ∀ L, 1 ≤ L → L ≤ byteLen s → r.val ≥ beautyWindowSum (byteList s) L := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (r : I64) (hr : beauty_sum s = ok r), ∀ L, 1 ≤ L → L ≤ byteLen s → r.val ≥ beautyWindowSum (byteList s) L) := by
    sorry

  /-- For every such s and c, beauty_sum(s) returns r, beauty_sum(s') returns r', and the mathematical integer values satisfy r' >= r.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 499, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Also c is an ASCII lowercase letter, and s' is the byte slice obtained by appending c to s. -/
  theorem spec_8 (s s' : Slice Std.U8) (c : ℕ)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 499)
      (hlower : IsLowerSlice s) (hc : IsLower c)
      (hs' : byteList s' = byteList s ++ [c])
      (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r') :
      r' ≥ r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s s' : Slice Std.U8) (c : ℕ)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 499)
        (hlower : IsLowerSlice s) (hc : IsLower c)
        (hs' : byteList s' = byteList s ++ [c])
        (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r'), r' ≥ r) := by
    sorry

  /-- For every s satisfying the preconditions, beauty_sum(s) returns r, beauty_sum(rev(s)) returns r', and the mathematical integer values satisfy r = r'.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let n = len(s), and let rev(s) be the byte slice of length n with rev(s)[i] = s[n - 1 - i] for 0 <= i < n. -/
  theorem spec_9 (s s' : Slice Std.U8)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s)
      (hrev : byteList s' = (byteList s).reverse)
      (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s s' : Slice Std.U8)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s)
        (hrev : byteList s' = (byteList s).reverse)
        (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r'), r.val = r'.val) := by
    sorry

  /-- For every s and every such permutation pi, beauty_sum(s) returns r, beauty_sum(pi(s)) returns r_pi, and the mathematical integer values satisfy r = r_pi.
    Preconditions: len(s) is an integer with 1 <= len(s) <= 500, and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. Let pi be any bijection of the set of ASCII lowercase letters to itself, and let pi(s) be the byte slice of length len(s) with pi(s)[i] = pi(s[i]). -/
  theorem spec_10 (s s' : Slice Std.U8) (σ : ℕ → ℕ)
      (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
      (hlower : IsLowerSlice s) (hσ : IsLowerPerm σ)
      (hmap : byteList s' = (byteList s).map σ)
      (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s s' : Slice Std.U8) (σ : ℕ → ℕ)
        (hlen : 1 ≤ byteLen s) (hlen' : byteLen s ≤ 500)
        (hlower : IsLowerSlice s) (hσ : IsLowerPerm σ)
        (hmap : byteList s' = (byteList s).map σ)
        (r r' : I64) (hr : beauty_sum s = ok r) (hr' : beauty_sum s' = ok r'), r.val = r'.val) := by
    sorry

  /-- For this s, beauty_sum(s) returns r with mathematical integer value 5.
    Preconditions: s is the byte slice with values [97,97,98,99,98], the ASCII codes of the string 'aabcb'. -/
  theorem spec_11 (s : Slice Std.U8)
      (hbytes : byteList s = [97, 97, 98, 99, 98]) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = 5 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hbytes : byteList s = [97, 97, 98, 99, 98]), ∃ r : I64, beauty_sum s = ok r ∧ r.val = 5) := by
    sorry

  /-- For this s, beauty_sum(s) returns r with mathematical integer value 87.
    Preconditions: s is the byte slice with values [120,121,122,122,120,121,122,122,120,121,122,122], the ASCII codes of the string 'xyzzxyzzxyzz'. -/
  theorem spec_12 (s : Slice Std.U8)
      (hbytes : byteList s = [120, 121, 122, 122, 120, 121, 122, 122, 120, 121, 122, 122]) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = 87 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hbytes : byteList s = [120, 121, 122, 122, 120, 121, 122, 122, 120, 121, 122, 122]), ∃ r : I64, beauty_sum s = ok r ∧ r.val = 87) := by
    sorry

  /-- For this s, beauty_sum(s) returns r with mathematical integer value 29.
    Preconditions: s is the byte slice with values [97,97,97,98,98,98,99,99,99], the ASCII codes of the string 'aaabbbccc'. -/
  theorem spec_13 (s : Slice Std.U8)
      (hbytes : byteList s = [97, 97, 97, 98, 98, 98, 99, 99, 99]) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = 29 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hbytes : byteList s = [97, 97, 97, 98, 98, 98, 99, 99, 99]), ∃ r : I64, beauty_sum s = ok r ∧ r.val = 29) := by
    sorry

  /-- For this s, beauty_sum(s) returns r with mathematical integer value 16.
    Preconditions: s is the byte slice with values [97,98,99,100,101,100,99,98,97], the ASCII codes of the string 'abcdedcba'. -/
  theorem spec_14 (s : Slice Std.U8)
      (hbytes : byteList s = [97, 98, 99, 100, 101, 100, 99, 98, 97]) :
      ∃ r : I64, beauty_sum s = ok r ∧ r.val = 16 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hbytes : byteList s = [97, 98, 99, 100, 101, 100, 99, 98, 97]), ∃ r : I64, beauty_sum s = ok r ∧ r.val = 16) := by
    sorry

  /-- For every such s and t, beauty_sum(s++t) returns r, beauty_sum(s) returns r_s, beauty_sum(t) returns r_t, and the mathematical integer values satisfy r >= r_s + r_t.
    Preconditions: len(s) and len(t) are integers with 1 <= len(s), 1 <= len(t), len(s)+len(t) <= 500, and every byte of s and t is an ASCII lowercase letter, i.e. 97 <= byte <= 122. Let s++t be the concatenated byte slice. -/
  theorem spec_15 (s t st : Slice Std.U8)
      (hlens : 1 ≤ byteLen s) (hlent : 1 ≤ byteLen t)
      (hlen : byteLen s + byteLen t ≤ 500)
      (hlowers : IsLowerSlice s) (hlowert : IsLowerSlice t)
      (hcat : byteList st = byteList s ++ byteList t)
      (r rs rt : I64)
      (hr : beauty_sum st = ok r) (hrs : beauty_sum s = ok rs) (hrt : beauty_sum t = ok rt) :
      r.val ≥ rs.val + rt.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s t st : Slice Std.U8)
        (hlens : 1 ≤ byteLen s) (hlent : 1 ≤ byteLen t)
        (hlen : byteLen s + byteLen t ≤ 500)
        (hlowers : IsLowerSlice s) (hlowert : IsLowerSlice t)
        (hcat : byteList st = byteList s ++ byteList t)
        (r rs rt : I64)
        (hr : beauty_sum st = ok r) (hrs : beauty_sum s = ok rs) (hrt : beauty_sum t = ok rt), r.val ≥ rs.val + rt.val) := by
    sorry

  end AegisSpec.BeautySum
