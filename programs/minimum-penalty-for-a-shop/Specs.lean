import Aegis.BestClosingTime.Code.Funs

/-!
# Specifications of `Aegis.BestClosingTime.best_closing_time`

LeetCode problem `minimum-penalty-for-a-shop`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BestClosingTime

  def byteY : Std.U8 := 89#u8

  def byteN : Std.U8 := 78#u8

  def atY (l : List Std.U8) (i : ℕ) : Prop := l[i]? = some byteY

  def atN (l : List Std.U8) (i : ℕ) : Prop := l[i]? = some byteN

  def isYByte (c : Std.U8) : Bool := c.val == 89

  def isNByte (c : Std.U8) : Bool := c.val == 78

  def isYAt (l : List Std.U8) (i : ℕ) : Bool := ((l[i]?).map isYByte).getD false

  def totalY (l : List Std.U8) : ℕ := l.countP isYByte

  def totalN (l : List Std.U8) : ℕ := l.countP isNByte

  def penalty (l : List Std.U8) (j : ℕ) : ℕ :=
    (l.take j).countP isNByte + (l.drop j).countP isYByte

  def leadingY (l : List Std.U8) : ℕ := (l.takeWhile isYByte).length

  def maxYSucc (l : List Std.U8) : ℕ :=
    (List.range l.length).foldr (fun i acc => if isYAt l i then max (i + 1) acc else acc) 0

  /-- The function returns a result r (i.e., it does not fail) such that 0 <= r <= n, where n = len(customers). Define penalty(j) for integer j with 0 <= j <= n as the number of indices i with 0 <= i < j and customers[i] = 'N' plus the number of indices i with j <= i < n and customers[i] = 'Y'. Then: (1) for every j with 0 <= j <= n, penalty(r) <= penalty(j); and (2) for every j with 0 <= j < r, penalty(j) > penalty(r). In other words, r is the smallest integer in [0, n] that minimizes penalty.
    Preconditions: len(customers) >= 1, len(customers) <= 100000, and for every i with 0 <= i < len(customers), customers[i] is the ASCII byte for 'Y' (89) or 'N' (78). -/
  theorem spec_1 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ (customers.val.length : ℤ) ∧
        (∀ j : ℕ, j ≤ customers.val.length →
          penalty customers.val r.val.toNat ≤ penalty customers.val j) ∧
        (∀ j : ℕ, j < r.val.toNat →
          penalty customers.val r.val.toNat < penalty customers.val j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          0 ≤ r.val ∧
          r.val ≤ (customers.val.length : ℤ) ∧
          (∀ j : ℕ, j ≤ customers.val.length →
            penalty customers.val r.val.toNat ≤ penalty customers.val j) ∧
          (∀ j : ℕ, j < r.val.toNat →
            penalty customers.val r.val.toNat < penalty customers.val j)) := by
    sorry

  /-- The function returns a result r, and r = 0.
    Preconditions: len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < len(customers), customers[i] is the ASCII byte for 'Y' (89) or 'N' (78), and for every i with 0 <= i < len(customers), customers[i] = 'N'. -/
  theorem spec_2 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i)
      (h_all_N : ∀ i, i < customers.val.length → atN customers.val i) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        r.val = 0 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i)
        (h_all_N : ∀ i, i < customers.val.length → atN customers.val i), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          r.val = 0) := by
    sorry

  /-- The function returns a result r, and r = n.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78), and for every i with 0 <= i < n, customers[i] = 'Y'. -/
  theorem spec_3 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i)
      (h_all_Y : ∀ i, i < customers.val.length → atY customers.val i) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        r.val = (customers.val.length : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i)
        (h_all_Y : ∀ i, i < customers.val.length → atY customers.val i), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          r.val = (customers.val.length : ℤ)) := by
    sorry

  /-- The function returns a result r, and r = 1.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78), and there is exactly one index k with 0 <= k < n such that customers[k] = 'Y', and that index k is 0. -/
  theorem spec_4 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i)
      (h_single_Y : ∃ k, k < customers.val.length ∧ atY customers.val k ∧ k = 0 ∧
        ∀ k', k' < customers.val.length → atY customers.val k' → k' = k) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i)
        (h_single_Y : ∃ k, k < customers.val.length ∧ atY customers.val k ∧ k = 0 ∧
          ∀ k', k' < customers.val.length → atY customers.val k' → k' = k), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, r >= L.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78). Let L be the number of leading 'Y's: L = 0 if customers[0] = 'N', otherwise L is the largest integer with 0 <= L <= n such that for all i with 0 <= i < L, customers[i] = 'Y', and either L = n or customers[L] = 'N'. -/
  theorem spec_5 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i) :
      ∀ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r →
        (leadingY customers.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i), ∀ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r →
          (leadingY customers.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= M.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78). Let M = max({i+1 : 0 <= i < n and customers[i] = 'Y'} ∪ {0}). Equivalently, M = n - T, where T is the number of trailing 'N's (the largest T with 0 <= T <= n such that for all i with n-T <= i < n, customers[i] = 'N', and either T = n or customers[n-T-1] = 'Y'). -/
  theorem spec_6 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i) :
      ∀ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r →
        r.val ≤ (maxYSucc customers.val : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i), ∀ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r →
          r.val ≤ (maxYSucc customers.val : ℤ)) := by
    sorry

  /-- The function returns a result r, and r > 0.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78). Let totalY be the number of indices i with 0 <= i < n and customers[i] = 'Y', and totalN be the number of indices i with 0 <= i < n and customers[i] = 'N'. Assume totalY > totalN. -/
  theorem spec_7 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i)
      (h_more_Y : totalN customers.val < totalY customers.val) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        0 < r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i)
        (h_more_Y : totalN customers.val < totalY customers.val), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          0 < r.val) := by
    sorry

  /-- The function returns a result r, and r < n.
    Preconditions: Let n = len(customers). len(customers) >= 1, len(customers) <= 100000, for every i with 0 <= i < n, customers[i] is the ASCII byte for 'Y' (89) or 'N' (78). Let totalY be the number of indices i with 0 <= i < n and customers[i] = 'Y', and totalN be the number of indices i with 0 <= i < n and customers[i] = 'N'. Assume totalY < totalN. -/
  theorem spec_8 (customers : Slice Std.U8)
      (h_len_ge : 1 ≤ customers.val.length)
      (h_len_le : customers.val.length ≤ 100000)
      (h_bytes : ∀ i, i < customers.val.length →
        atY customers.val i ∨ atN customers.val i)
      (h_more_N : totalY customers.val < totalN customers.val) :
      ∃ r : Std.I64,
        Aegis.BestClosingTime.best_closing_time customers = ok r ∧
        r.val < (customers.val.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (customers : Slice Std.U8)
        (h_len_ge : 1 ≤ customers.val.length)
        (h_len_le : customers.val.length ≤ 100000)
        (h_bytes : ∀ i, i < customers.val.length →
          atY customers.val i ∨ atN customers.val i)
        (h_more_N : totalY customers.val < totalN customers.val), ∃ r : Std.I64,
          Aegis.BestClosingTime.best_closing_time customers = ok r ∧
          r.val < (customers.val.length : ℤ)) := by
    sorry

  end AegisSpec.BestClosingTime
