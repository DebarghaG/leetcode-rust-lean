import Aegis.CanConstruct.Code.Funs

/-!
# Specifications of `Aegis.CanConstruct.can_construct`

LeetCode problem `construct-k-palindrome-strings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanConstruct

  def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

  def freq (s : Slice Std.U8) (c : Nat) : Nat :=
    (bytes s).countP (fun x => decide (x = c))

  def oddFreq (s : Slice Std.U8) : Nat :=
    ((List.range 256).filter (fun c => freq s c % 2 == 1)).length

  def allLower (s : Slice Std.U8) : Prop :=
    ∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122

  def PalDecomp (s : Slice Std.U8) (P : List (List Std.U8)) : Prop :=
    (∀ p ∈ P, p ≠ [] ∧ p.reverse = p) ∧
      ∀ c : Nat, (P.flatten.map (fun b => b.val)).countP (fun x => decide (x = c)) = freq s c

  /-- Let n = len(s). Let odd(s) be the number of byte values c for which the number of indices i with 0 <= i < n and s[i] = c is odd. Whenever the function returns a result r, r = true if and only if k <= n, odd(s) <= k, and (k > 0 or n = 0).
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
        (r = true ↔
          k.val ≤ (s.val.length : Int) ∧ (oddFreq s : Int) ≤ k.val ∧
            (k.val > 0 ∨ s.val.length = 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
          (r = true ↔
            k.val ≤ (s.val.length : Int) ∧ (oddFreq s : Int) ≤ k.val ∧
              (k.val > 0 ∨ s.val.length = 0))) := by
    sorry

  /-- Whenever 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∃ r, Aegis.CanConstruct.can_construct s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∃ r, Aegis.CanConstruct.can_construct s k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then k <= len(s).
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true →
        k.val ≤ (s.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true →
          k.val ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then odd(s) <= k, where odd(s) is the number of byte values c whose frequency in s is odd.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true → (oddFreq s : Int) ≤ k.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true → (oddFreq s : Int) ≤ k.val) := by
    sorry

  /-- If len(s) = 0, then whenever the function returns a result r, r = true if and only if k = 0.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s)
      (hempty : s.val.length = 0) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ k.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s)
        (hempty : s.val.length = 0), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ k.val = 0)) := by
    sorry

  /-- If k = 0, then whenever the function returns a result r, r = true if and only if len(s) = 0.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s)
      (hk : k.val = 0) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ s.val.length = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s)
        (hk : k.val = 0), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ s.val.length = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if odd(s) <= 1, where odd(s) is the number of byte values c whose frequency in s is odd.
    Preconditions: k = 1, len(s) >= 1, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
      (hk : k.val = 1) (hlen_pos : 1 ≤ s.val.length)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ (oddFreq s : Int) ≤ 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk : k.val = 1) (hlen_pos : 1 ≤ s.val.length)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → (r = true ↔ (oddFreq s : Int) ≤ 1)) := by
    sorry

  /-- Whenever the function returns a result r, r = true.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, every byte of s is a lowercase English letter ('a'..'z'), and k = len(s). -/
  theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s)
      (hk : k.val = (s.val.length : Int)) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s)
        (hk : k.val = (s.val.length : Int)), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true) := by
    sorry

  /-- If odd(s) <= 1, where odd(s) is the number of byte values c whose frequency in s is odd, then whenever the function returns a result r, r = true if and only if k <= len(s).
    Preconditions: 0 <= k <= 100000, k >= 1, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_9 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_pos : 1 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s)
      (hodd : (oddFreq s : Int) ≤ 1) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
        (r = true ↔ k.val ≤ (s.val.length : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_pos : 1 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s)
        (hodd : (oddFreq s : Int) ≤ 1), ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
          (r = true ↔ k.val ≤ (s.val.length : Int))) := by
    sorry

  /-- Whenever the function returns a result r, r = true if and only if len(s) >= 2 and odd(s) <= 2, where odd(s) is the number of byte values c whose frequency in s is odd.
    Preconditions: k = 2, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_10 (s : Slice Std.U8) (k : Std.I64)
      (hk : k.val = 2)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
        (r = true ↔ 2 ≤ s.val.length ∧ (oddFreq s : Int) ≤ 2) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk : k.val = 2)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r →
          (r = true ↔ 2 ≤ s.val.length ∧ (oddFreq s : Int) ≤ 2)) := by
    sorry

  /-- Whenever the function returns a result r, r = false.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, every byte of s is a lowercase English letter ('a'..'z'), and k > len(s). -/
  theorem spec_11 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s)
      (hk : (s.val.length : Int) < k.val) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = false := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s)
        (hk : (s.val.length : Int) < k.val), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = false) := by
    sorry

  /-- Whenever the function returns a result r on input (s, k) with r = true, the function returns a result r' on input (s, k') with r' = true.
    Preconditions: 0 <= k <= k' <= len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_12 (s : Slice Std.U8) (k k' : Std.I64)
      (hk_lower : 0 ≤ k.val) (hkk' : k.val ≤ k'.val)
      (hk'_len : k'.val ≤ (s.val.length : Int))
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      Aegis.CanConstruct.can_construct s k = ok true →
        ∃ r', Aegis.CanConstruct.can_construct s k' = ok r' ∧ r' = true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (k k' : Std.I64)
        (hk_lower : 0 ≤ k.val) (hkk' : k.val ≤ k'.val)
        (hk'_len : k'.val ≤ (s.val.length : Int))
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), Aegis.CanConstruct.can_construct s k = ok true →
          ∃ r', Aegis.CanConstruct.can_construct s k' = ok r' ∧ r' = true) := by
    sorry

  /-- Whenever the function returns a result r_s on input (s, k) and a result r_t on input (t, k), we have r_s = r_t.
    Preconditions: len(s) = len(t) <= 100000, every byte of s and of t is a lowercase English letter ('a'..'z'), for every byte value c the number of indices i with 0 <= i < len(s) and s[i] = c equals the number of indices j with 0 <= j < len(t) and t[j] = c, and 0 <= k <= 100000. -/
  theorem spec_13 (s t : Slice Std.U8) (k : Std.I64)
      (hlen : s.val.length = t.val.length) (hlen_upper : s.val.length ≤ 100000)
      (hlow_s : allLower s) (hlow_t : allLower t)
      (hfreq : ∀ c : Nat, freq s c = freq t c)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000) :
      ∀ r_s r_t, Aegis.CanConstruct.can_construct s k = ok r_s →
        Aegis.CanConstruct.can_construct t k = ok r_t → r_s = r_t := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
        (hlen : s.val.length = t.val.length) (hlen_upper : s.val.length ≤ 100000)
        (hlow_s : allLower s) (hlow_t : allLower t)
        (hfreq : ∀ c : Nat, freq s c = freq t c)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000), ∀ r_s r_t, Aegis.CanConstruct.can_construct s k = ok r_s →
          Aegis.CanConstruct.can_construct t k = ok r_t → r_s = r_t) := by
    sorry

  /-- Whenever the function returns a result r with r = true, there exists a finite sequence P of length k such that every element of P is a non-empty byte list, every element of P equals its reverse (is a palindrome), and the concatenation of the elements of P has the same multiset of byte values as s.
    Preconditions: 0 <= k <= 100000, len(s) <= 100000, and every byte of s is a lowercase English letter ('a'..'z'). -/
  theorem spec_14 (s : Slice Std.U8) (k : Std.I64)
      (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
      (hlen : s.val.length ≤ 100000) (hlow : allLower s) :
      ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true →
        ∃ P : List (List Std.U8), ((P.length : Int) = k.val) ∧ PalDecomp s P := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
        (hk_lower : 0 ≤ k.val) (hk_upper : k.val ≤ 100000)
        (hlen : s.val.length ≤ 100000) (hlow : allLower s), ∀ r, Aegis.CanConstruct.can_construct s k = ok r → r = true →
          ∃ P : List (List Std.U8), ((P.length : Int) = k.val) ∧ PalDecomp s P) := by
    sorry

  end AegisSpec.CanConstruct
