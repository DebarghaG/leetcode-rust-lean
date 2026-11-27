import Aegis.BalancedStringSplit.Code.Funs

/-!
# Specifications of `Aegis.BalancedStringSplit.balanced_string_split`

LeetCode problem `split-a-string-in-balanced-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.BalancedStringSplit

  namespace AegisSpec.BalancedStringSplit

  def byteL : Nat := 76

  def byteR : Nat := 82

  def numL (l : List Std.U8) : Nat := l.countP (fun b => decide (b.val = 76))

  def numR (l : List Std.U8) : Nat := l.countP (fun b => decide (b.val = 82))

  def IsBalanced (l : List Std.U8) : Prop := numL l = numR l

  def substr (l : List Std.U8) (a b : Nat) : List Std.U8 := (l.drop a).take (b - a)

  def bal (l : List Std.U8) (i : Nat) : Int := (numR (l.take i) : Int) - (numL (l.take i) : Int)

  def numZeroBal (l : List Std.U8) : Nat :=
    (List.range (l.length + 1)).countP (fun i => decide (1 ≤ i ∧ bal l i = 0))

  def AllAdjacentPairsMixed (l : List Std.U8) : Prop :=
    ∀ j : Nat, j < l.length / 2 →
      numL (substr l (2 * j) (2 * j + 2)) = 1 ∧ numR (substr l (2 * j) (2 * j + 2)) = 1

  def IsBalancedCutSeq (l : List Std.U8) (k : Nat) (p : Nat → Nat) : Prop :=
    p 0 = 0 ∧ p k = l.length ∧
      (∀ t : Nat, t < k → p t < p (t + 1)) ∧
      (∀ t : Nat, t < k → 0 < p (t + 1) - p t) ∧
      (∀ t : Nat, t < k → IsBalanced (substr l (p t) (p (t + 1))))

  def swapLR (b : Std.U8) : Std.U8 := if b.val = 76 then 82#u8 else 76#u8

  def flipLR (l : List Std.U8) : List Std.U8 := l.map swapLR

  /-- Define, for 0 <= i <= n, bal(i) to be the number of bytes 82 ('R') in s[0:i] minus the number of bytes 76 ('L') in s[0:i]. Whenever balanced_string_split(s) returns a result r, we have r = #{ i | 1 <= i <= n and bal(i) = 0 }.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_1 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r → r.val = (numZeroBal s.val : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r → r.val = (numZeroBal s.val : Int)) := by
    sorry

  /-- The call balanced_string_split(s) returns a result r (an I64 value); it does not fail, panic, overflow, or access outside the slice.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_2 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∃ r : Std.I64, balanced_string_split s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∃ r : Std.I64, balanced_string_split s = ok r) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, we have r <= n / 2, where division is integer division by 2.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_3 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r → r.val ≤ ((s.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r → r.val ≤ ((s.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, we have 1 <= r.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_4 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r → (1 : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r → (1 : Int) ≤ r.val) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, we have r = n / 2 if and only if for every j with 0 <= j < n / 2, the two-byte substring s[2*j : 2*j+2] contains exactly one 'L' and one 'R'.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_5 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r →
        (r.val = ((s.val.length / 2 : Nat) : Int) ↔ AllAdjacentPairsMixed s.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r →
          (r.val = ((s.val.length / 2 : Nat) : Int) ↔ AllAdjacentPairsMixed s.val)) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, we have r = 1 if and only if for every i with 0 < i < n, the prefix s[0:i] does not contain equal numbers of 'L' and 'R'.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_6 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r →
        (r.val = 1 ↔
          ∀ i : Nat, 0 < i → i < s.val.length → numL (s.val.take i) ≠ numR (s.val.take i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r →
          (r.val = 1 ↔
            ∀ i : Nat, 0 < i → i < s.val.length → numL (s.val.take i) ≠ numR (s.val.take i))) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, there exist integers p_0, p_1, ..., p_r such that 0 = p_0 < p_1 < ... < p_r = n and, for every t with 1 <= t <= r, the substring s[p_{t-1}:p_t] is non-empty and contains equal numbers of 'L' and 'R'.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_7 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r →
        ∃ p : Nat → Nat, IsBalancedCutSeq s.val r.val.toNat p := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r →
          ∃ p : Nat → Nat, IsBalancedCutSeq s.val r.val.toNat p) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, for every integer k >= 1 and every sequence 0 = q_0 < q_1 < ... < q_k = n such that each substring s[q_{t-1}:q_t] for 1 <= t <= k contains equal numbers of 'L' and 'R', we have k <= r.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_8 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r →
        ∀ (k : Nat) (q : Nat → Nat), 1 ≤ k → IsBalancedCutSeq s.val k q → (k : Int) ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r →
          ∀ (k : Nat) (q : Nat → Nat), 1 ≤ k → IsBalancedCutSeq s.val k q → (k : Int) ≤ r.val) := by
    sorry

  /-- Whenever balanced_string_split(s) returns a result r, for every sequence 0 = p_0 < p_1 < ... < p_r = n such that each substring s[p_{t-1}:p_t] for 1 <= t <= r is balanced, the set of internal cut positions { p_1, ..., p_{r-1} } equals { i | 0 < i < n and the prefix s[0:i] contains equal numbers of 'L' and 'R' }.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_9 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ r : Std.I64, balanced_string_split s = ok r →
        ∀ p : Nat → Nat, IsBalancedCutSeq s.val r.val.toNat p →
          ∀ i : Nat,
            (∃ t : Nat, 1 ≤ t ∧ t < r.val.toNat ∧ p t = i) ↔
              (0 < i ∧ i < s.val.length ∧ numL (s.val.take i) = numR (s.val.take i)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ r : Std.I64, balanced_string_split s = ok r →
          ∀ p : Nat → Nat, IsBalancedCutSeq s.val r.val.toNat p →
            ∀ i : Nat,
              (∃ t : Nat, 1 ≤ t ∧ t < r.val.toNat ∧ p t = i) ↔
                (0 < i ∧ i < s.val.length ∧ numL (s.val.take i) = numR (s.val.take i))) := by
    sorry

  /-- Let t be the byte slice of length n defined by t[i] = 82 ('R') if s[i] = 76 ('L'), and t[i] = 76 ('L') if s[i] = 82 ('R'). Whenever the calls balanced_string_split(s) and balanced_string_split(t) return r_s and r_t, we have r_s = r_t.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_10 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ t : Slice Std.U8, t.val = flipLR s.val →
        ∀ r_s r_t : Std.I64,
          balanced_string_split s = ok r_s → balanced_string_split t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ t : Slice Std.U8, t.val = flipLR s.val →
          ∀ r_s r_t : Std.I64,
            balanced_string_split s = ok r_s → balanced_string_split t = ok r_t → r_s = r_t) := by
    sorry

  /-- Let t be the byte slice of length n defined by t[i] = s[n-1-i] for 0 <= i < n. Whenever the calls balanced_string_split(s) and balanced_string_split(t) return r_s and r_t, we have r_s = r_t.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. -/
  theorem spec_11 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ t : Slice Std.U8, t.val = s.val.reverse →
        ∀ r_s r_t : Std.I64,
          balanced_string_split s = ok r_s → balanced_string_split t = ok r_t → r_s = r_t := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ t : Slice Std.U8, t.val = s.val.reverse →
          ∀ r_s r_t : Std.I64,
            balanced_string_split s = ok r_s → balanced_string_split t = ok r_t → r_s = r_t) := by
    sorry

  /-- Let a = s[0:m] and b = s[m:n]. Whenever the calls balanced_string_split(s), balanced_string_split(a), and balanced_string_split(b) return r, r_a, and r_b, we have r = r_a + r_b.
    Preconditions: Let n = len(s). Assume 2 <= n <= 1000, each byte s[i] for 0 <= i < n is either 76 ('L') or 82 ('R'), and the number of 'L' bytes in s equals the number of 'R' bytes in s. Let m be an integer with 0 < m < n such that both slices s[0:m] and s[m:n] contain equal numbers of 'L' and 'R'. -/
  theorem spec_12 (s : Slice Std.U8)
      (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
      (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
      (hbal : numL s.val = numR s.val) :
      ∀ m : Nat, 0 < m → m < s.val.length →
        IsBalanced (s.val.take m) → IsBalanced (s.val.drop m) →
          ∀ a b : Slice Std.U8, a.val = s.val.take m → b.val = s.val.drop m →
            ∀ r r_a r_b : Std.I64,
              balanced_string_split s = ok r →
              balanced_string_split a = ok r_a →
              balanced_string_split b = ok r_b →
              r.val = r_a.val + r_b.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn2 : 2 ≤ s.val.length) (hn1 : s.val.length ≤ 1000)
        (hbytes : ∀ b ∈ s.val, b.val = byteL ∨ b.val = byteR)
        (hbal : numL s.val = numR s.val), ∀ m : Nat, 0 < m → m < s.val.length →
          IsBalanced (s.val.take m) → IsBalanced (s.val.drop m) →
            ∀ a b : Slice Std.U8, a.val = s.val.take m → b.val = s.val.drop m →
              ∀ r r_a r_b : Std.I64,
                balanced_string_split s = ok r →
                balanced_string_split a = ok r_a →
                balanced_string_split b = ok r_b →
                r.val = r_a.val + r_b.val) := by
    sorry

  end AegisSpec.BalancedStringSplit
