import Aegis.CountKReducibleNumbers.Code.Funs

/-!
# Specifications of `Aegis.CountKReducibleNumbers.count_k_reducible_numbers`

LeetCode problem `count-k-reducible-numbers-less-than-n`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountKReducibleNumbers

  open Aegis.CountKReducibleNumbers

  def MOD : ℕ := 1000000007

  def popcount : ℕ → ℕ
    | 0 => 0
    | n + 1 => popcount ((n + 1) / 2) + (n + 1) % 2
  termination_by x => x
  decreasing_by omega

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def N (s : Slice Std.U8) : ℕ := (bytes s).foldl (fun acc d => acc * 2 + (d - 48)) 0

  def reachesOneWithin (k x : ℕ) : Prop := ∃ t, t ≤ k ∧ (popcount^[t]) x = 1

  noncomputable def A (s : Slice Std.U8) (k : ℕ) : ℕ := by
    classical
    exact ((Finset.range (N s)).filter (fun x => 1 ≤ x ∧ reachesOneWithin k x)).card

  def P (s : Slice Std.U8) : ℕ :=
    ((Finset.range (s.val.length + 1)).filter (fun j => 2 ^ j < N s)).card

  def IsBinaryString (s : Slice Std.U8) : Prop := ∀ b, b ∈ s.val → b.val = 48 ∨ b.val = 49

  def HasAsciiPrefix (s : Slice Std.U8) (codes : List ℕ) : Prop :=
    (bytes s).take codes.length = codes

  /-- Let L = len(s), let N = sum_{i=0}^{L-1} (s[i] - 48) * 2^(L-1-i) be the integer whose binary representation is s, and let M = 1000000007. For a positive integer x let f(x) be the number of 1 bits in the binary representation of x, with f^0(x)=x and f^(t+1)(x)=f(f^t(x)). Let A(s,k) be the number of integers x such that 1 <= x < N and there exists t with 0 <= t <= k and f^t(x) = 1. The function returns a result r and r = A(s,k) mod M.
    Preconditions: len(s) >= 1 and len(s) <= 800; for every i with 0 <= i < len(s), s[i] is the ASCII code 48 ('0') or 49 ('1'); s[0] = 49 (no leading zero); 1 <= k <= 5. -/
  theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5) :
      ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧
        r.val = ((A s k.val.toNat % MOD : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5), ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧
          r.val = ((A s k.val.toNat % MOD : ℕ) : ℤ)) := by
    sorry

  /-- For every s and k satisfying the preconditions, the function returns a result r (an Ok value); it does not fail, panic, overflow, or access out of bounds.
    Preconditions: len(s) >= 1 and len(s) <= 800; for every i with 0 <= i < len(s), s[i] is the ASCII code 48 ('0') or 49 ('1'); s[0] = 49 (no leading zero); 1 <= k <= 5. -/
  theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5) :
      ∃ r : Std.I64, count_k_reducible_numbers s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5), ∃ r : Std.I64, count_k_reducible_numbers s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer r satisfies 0 <= r < 1000000007.
    Preconditions: len(s) >= 1 and len(s) <= 800; for every i with 0 <= i < len(s), s[i] is the ASCII code 48 ('0') or 49 ('1'); s[0] = 49 (no leading zero); 1 <= k <= 5. -/
  theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5) :
      ∀ r : Std.I64, count_k_reducible_numbers s k = ok r → 0 ≤ r.val ∧ r.val < (MOD : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5), ∀ r : Std.I64, count_k_reducible_numbers s k = ok r → 0 ≤ r.val ∧ r.val < (MOD : ℤ)) := by
    sorry

  /-- For every k with 1 <= k <= 5, the function returns a result r and r = 0.
    Preconditions: The general constraints hold and len(s) = 1. Since s[0] = 49, s is the ASCII text '1'. -/
  theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (h_len : s.val.length = 1) :
      ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (h_len : s.val.length = 1), ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧ r.val = 0) := by
    sorry

  /-- For every k with 1 <= k <= 5, the function returns a result r and r = 1.
    Preconditions: The general constraints hold, len(s) = 2, s[0] = 49, and s[1] = 48 (so s is the ASCII text '10'). -/
  theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (h_len : s.val.length = 2) (h_bytes : HasAsciiPrefix s [49, 48]) :
      ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (h_len : s.val.length = 2) (h_bytes : HasAsciiPrefix s [49, 48]), ∃ r : Std.I64, count_k_reducible_numbers s k = ok r ∧ r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = P mod 1000000007, where P = #{ j in Z : j >= 0 and 2^j < N } and N is the integer represented by s. Since P <= len(s) <= 800, equivalently r = P.
    Preconditions: The general constraints hold and k = 1. -/
  theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (h_k : k.val = 1) :
      ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
        r.val = ((P s % MOD : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (h_k : k.val = 1), ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
          r.val = ((P s % MOD : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = (N - 1) mod 1000000007, where N is the integer represented by s.
    Preconditions: The general constraints hold and k = 5. -/
  theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (h_k : k.val = 5) :
      ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
        r.val = (((N s - 1) % MOD : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (h_k : k.val = 5), ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
          r.val = (((N s - 1) % MOD : ℕ) : ℤ)) := by
    sorry

  /-- Let N be the integer represented by s, and let A(s,k) be the number of integers x with 1 <= x < N for which some t with 0 <= t <= k has f^t(x)=1, where f is the popcount function. Whenever the function returns a result r, r = A(s,k).
    Preconditions: The general constraints hold and len(s) <= 29. -/
  theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (h_len_29 : s.val.length ≤ 29) :
      ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
        r.val = ((A s k.val.toNat : ℕ) : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (h_len_29 : s.val.length ≤ 29), ∀ r : Std.I64, count_k_reducible_numbers s k = ok r →
          r.val = ((A s k.val.toNat : ℕ) : ℤ)) := by
    sorry

  /-- If the function returns r_s on input (s,k) and returns r_t on input (t,k), then r_s <= r_t.
    Preconditions: Both (s,k) and (t,k) satisfy the general constraints with the same k; len(s) <= 29 and len(t) <= 29; let N_s and N_t be the integers represented by s and t respectively, and assume N_s <= N_t. -/
  theorem spec_9 (s t : Slice Std.U8) (k : Std.I64)
      (hs_len_ge : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 800)
      (hs_bin : IsBinaryString s) (hs_head : HasAsciiPrefix s [49])
      (ht_len_ge : 1 ≤ t.val.length) (ht_len_le : t.val.length ≤ 800)
      (ht_bin : IsBinaryString t) (ht_head : HasAsciiPrefix t [49])
      (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
      (hs_len_29 : s.val.length ≤ 29) (ht_len_29 : t.val.length ≤ 29)
      (hN : N s ≤ N t) :
      ∀ r_s r_t : Std.I64, count_k_reducible_numbers s k = ok r_s →
        count_k_reducible_numbers t k = ok r_t → r_s.val ≤ r_t.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hs_len_ge : 1 ≤ s.val.length) (hs_len_le : s.val.length ≤ 800)
        (hs_bin : IsBinaryString s) (hs_head : HasAsciiPrefix s [49])
        (ht_len_ge : 1 ≤ t.val.length) (ht_len_le : t.val.length ≤ 800)
        (ht_bin : IsBinaryString t) (ht_head : HasAsciiPrefix t [49])
        (h_k_ge : 1 ≤ k.val) (h_k_le : k.val ≤ 5)
        (hs_len_29 : s.val.length ≤ 29) (ht_len_29 : t.val.length ≤ 29)
        (hN : N s ≤ N t), ∀ r_s r_t : Std.I64, count_k_reducible_numbers s k = ok r_s →
          count_k_reducible_numbers t k = ok r_t → r_s.val ≤ r_t.val) := by
    sorry

  /-- If the function returns r1 on input (s,k1) and returns r2 on input (s,k2), then r1 <= r2.
    Preconditions: s satisfies the general constraints and len(s) <= 29; 1 <= k1 <= k2 <= 5. -/
  theorem spec_10 (s : Slice Std.U8) (k1 k2 : Std.I64)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_len_29 : s.val.length ≤ 29)
      (h_k1_ge : 1 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 5) :
      ∀ r1 r2 : Std.I64, count_k_reducible_numbers s k1 = ok r1 →
        count_k_reducible_numbers s k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_len_29 : s.val.length ≤ 29)
        (h_k1_ge : 1 ≤ k1.val) (h_k12 : k1.val ≤ k2.val) (h_k2_le : k2.val ≤ 5), ∀ r1 r2 : Std.I64, count_k_reducible_numbers s k1 = ok r1 →
          count_k_reducible_numbers s k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  /-- Let r4 be the result returned by the function on input (s,4) and r5 the result returned on input (s,5). Whenever both results are returned, r4 = r5.
    Preconditions: s satisfies the general constraints and len(s) <= 63. -/
  theorem spec_11 (s : Slice Std.U8)
      (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
      (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
      (h_len_63 : s.val.length ≤ 63) :
      ∀ r4 r5 : Std.I64, count_k_reducible_numbers s 4#i64 = ok r4 →
        count_k_reducible_numbers s 5#i64 = ok r5 → r4.val = r5.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (h_len_ge : 1 ≤ s.val.length) (h_len_le : s.val.length ≤ 800)
        (h_bin : IsBinaryString s) (h_head : HasAsciiPrefix s [49])
        (h_len_63 : s.val.length ≤ 63), ∀ r4 r5 : Std.I64, count_k_reducible_numbers s 4#i64 = ok r4 →
          count_k_reducible_numbers s 5#i64 = ok r5 → r4.val = r5.val) := by
    sorry

  end AegisSpec.CountKReducibleNumbers
