import Aegis.LastRemaining.Code.Funs

/-!
# Specifications of `Aegis.LastRemaining.last_remaining`

LeetCode problem `elimination-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LastRemaining

  def passLTR : List Nat → List Nat
    | [] => []
    | [_] => []
    | _ :: x :: rest => x :: passLTR rest

  def passRTL (L : List Nat) : List Nat := (passLTR L.reverse).reverse

  def round (k : Nat) (L : List Nat) : List Nat :=
    if k % 2 = 0 then passLTR L else passRTL L

  theorem passLTR_length : ∀ L : List Nat, (passLTR L).length = L.length / 2
    | [] => rfl
    | [_] => by simp [passLTR]
    | _ :: x :: rest => by
      have h := passLTR_length rest
      simp only [passLTR, List.length_cons]
      omega

  def eliminate (k : Nat) (L : List Nat) : Nat :=
    if h : 1 < L.length then
      eliminate (k + 1) (round k L)
    else L.headD 0
  termination_by L.length
  decreasing_by
    simp only [round]
    split
    · simp only [passLTR_length]
      omega
    · simp only [passRTL, passLTR_length, List.length_reverse]
      omega

  def S (n : Nat) : Nat := eliminate 0 (List.range' 1 n)

  def floorLog2 (n : Nat) : Nat := Nat.log2 n

  def ceilHalf (p : Nat) : Nat := (p + 1) / 2

  /-- Let L_0 = [1, 2, ..., n]. For k >= 0, while len(L_k) > 1, define L_{k+1} to be the sublist of L_k obtained as follows: if k is even (0-based, so the first pass is left-to-right), keep exactly the elements of L_k in 1-based even positions 2, 4, 6, ...; if k is odd, keep exactly the elements of L_k in 1-based positions i such that len(L_k) - i is odd (this removes the last element and then every second element moving left). Let S(n) be the single element of the final list. The function returns a result r and r = S(n).
    Preconditions: n is an integer with 1 <= n <= 10^9. -/
  theorem spec_1 (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∃ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r ∧ r.val = (S n.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r ∧ r.val = (S n.val.toNat : ℤ)) := by
    sorry

  /-- The function returns a result r for every such n; it does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: n is an integer with 1 <= n <= 10^9. -/
  theorem spec_2 (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∃ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n.
    Preconditions: n is an integer with 1 <= n <= 10^9. -/
  theorem spec_3 (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → 1 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → 1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: n = 1. -/
  theorem spec_4 (n : Std.I64) (h_n : n.val = 1) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (h_n : n.val = 1), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 2.
    Preconditions: n = 2. -/
  theorem spec_5 (n : Std.I64) (h_n : n.val = 2) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (h_n : n.val = 2), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 2) := by
    sorry

  /-- Whenever the function returns a result r, r is even; that is, there exists an integer k such that r = 2*k.
    Preconditions: n is an integer with 2 <= n <= 10^9. -/
  theorem spec_6 (n : Std.I64) (h_pos : 2 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → ∃ k : ℤ, r.val = 2 * k := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 2 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → ∃ k : ℤ, r.val = 2 * k) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2^(floor(log_2 n)).
    Preconditions: n is an integer with 1 <= n <= 10^9. Here floor(log_2 n) denotes the unique integer p with 2^p <= n < 2^(p+1). -/
  theorem spec_7 (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
        r.val ≤ (2 : ℤ) ^ floorLog2 n.val.toNat := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 1 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
          r.val ≤ (2 : ℤ) ^ floorLog2 n.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r < n.
    Preconditions: n is an integer with 3 <= n <= 10^9. -/
  theorem spec_8 (n : Std.I64) (h_pos : 3 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val < n.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 3 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val < n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = S(n-1).
    Preconditions: n is an odd integer with 3 <= n <= 10^9. Let S(m) denote the last remaining number obtained by applying the alternating elimination process (first pass left-to-right) to [1, 2, ..., m]. -/
  theorem spec_9 (n : Std.I64) (h_odd : ∃ k : ℤ, n.val = 2 * k + 1)
      (h_pos : 3 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
        r.val = (S (n.val.toNat - 1) : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (h_odd : ∃ k : ℤ, n.val = 2 * k + 1)
        (h_pos : 3 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
          r.val = (S (n.val.toNat - 1) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if n mod 4 is 0 or 1 then r = 4*S(q) - 2, and if n mod 4 is 2 or 3 then r = 4*S(q).
    Preconditions: n is an integer with 4 <= n <= 10^9. Let S(m) denote the last remaining number for input m under the same elimination process, and let q = floor(n/4). -/
  theorem spec_10 (n : Std.I64) (h_pos : 4 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
        ((n.val.toNat % 4 = 0 ∨ n.val.toNat % 4 = 1) →
            r.val = 4 * (S (n.val.toNat / 4) : ℤ) - 2) ∧
          ((n.val.toNat % 4 = 2 ∨ n.val.toNat % 4 = 3) →
            r.val = 4 * (S (n.val.toNat / 4) : ℤ)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (h_pos : 4 ≤ n.val) (h_bound : n.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
          ((n.val.toNat % 4 = 0 ∨ n.val.toNat % 4 = 1) →
              r.val = 4 * (S (n.val.toNat / 4) : ℤ) - 2) ∧
            ((n.val.toNat % 4 = 2 ∨ n.val.toNat % 4 = 3) →
              r.val = 4 * (S (n.val.toNat / 4) : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = (4^(ceil(p/2)) + 2) / 3, where the division is exact integer division.
    Preconditions: n = 2^p for an integer p with 0 <= p <= 29. Here ceil denotes the ceiling function. -/
  theorem spec_11 (n : Std.I64) (p : Nat) (h_p : p ≤ 29) (h_n : n.val = 2 ^ p) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
        r.val = ((4 : ℤ) ^ ceilHalf p + 2) / 3 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (p : Nat) (h_p : p ≤ 29) (h_n : n.val = 2 ^ p), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r →
          r.val = ((4 : ℤ) ^ ceilHalf p + 2) / 3) := by
    sorry

  /-- Whenever the function returns a result r, r = 2^(p-1).
    Preconditions: n = 2^p - 1 for an integer p with 1 <= p <= 29. -/
  theorem spec_12 (n : Std.I64) (p : Nat) (h_p1 : 1 ≤ p) (h_p2 : p ≤ 29)
      (h_n : n.val = 2 ^ p - 1) :
      ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 2 ^ (p - 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (p : Nat) (h_p1 : 1 ≤ p) (h_p2 : p ≤ 29)
        (h_n : n.val = 2 ^ p - 1), ∀ r : Std.I64, Aegis.LastRemaining.last_remaining n = ok r → r.val = 2 ^ (p - 1)) := by
    sorry

  end AegisSpec.LastRemaining
