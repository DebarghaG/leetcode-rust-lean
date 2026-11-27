import Aegis.CanTransform.Code.Funs

/-!
# Specifications of `Aegis.CanTransform.can_transform`

LeetCode problem `swap-adjacent-in-lr-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CanTransform

def IsLRX (l : List Std.U8) : Prop :=
  ∀ b ∈ l, b.val = 76 ∨ b.val = 82 ∨ b.val = 88

def nonX (l : List Std.U8) : List Std.U8 :=
  l.filter (fun b => b.val != 88)

def positionsWhere (p : Std.U8 → Bool) : Nat → List Std.U8 → List Nat
  | _, [] => []
  | i, b :: bs =>
    if p b then i :: positionsWhere p (i + 1) bs else positionsWhere p (i + 1) bs

def positions (p : Std.U8 → Bool) (l : List Std.U8) : List Nat :=
  positionsWhere p 0 l

def nonXPositions (l : List Std.U8) : List Nat :=
  positions (fun b => b.val != 88) l

def pos (s : List Std.U8) (j : Nat) : Nat :=
  (nonXPositions s).getD j 0

def nonXget (s : List Std.U8) (j : Nat) : Std.U8 :=
  (nonX s).getD j 0#u8

def LPositions (l : List Std.U8) : List Nat :=
  positions (fun b => b.val == 76) l

def RPositions (l : List Std.U8) : List Nat :=
  positions (fun b => b.val == 82) l

def posL (s : List Std.U8) (j : Nat) : Nat :=
  (LPositions s).getD j 0

def posR (s : List Std.U8) (j : Nat) : Nat :=
  (RPositions s).getD j 0

def countL (l : List Std.U8) : Nat :=
  (l.filter (fun b => b.val == 76)).length

def countR (l : List Std.U8) : Nat :=
  (l.filter (fun b => b.val == 82)).length

def Step (s t : List Std.U8) : Prop :=
  (∃ p q : List Std.U8, s = p ++ [88#u8, 76#u8] ++ q ∧ t = p ++ [76#u8, 88#u8] ++ q) ∨
    ∃ p q : List Std.U8, s = p ++ [82#u8, 88#u8] ++ q ∧ t = p ++ [88#u8, 82#u8] ++ q

/-- Let nonX(s) be the byte sequence obtained from s by deleting every occurrence of 'X'. For a byte sequence s and an index j with 0 <= j < len(nonX(s)), let pos(s,j) be the index in s of the j-th byte of nonX(s), counted from 0. The function returns a result r and r = true if and only if: (1) nonX(start) = nonX(result), and (2) for every j with 0 <= j < len(nonX(start)), if nonX(start)[j] = 'L' then pos(start,j) >= pos(result,j), and if nonX(start)[j] = 'R' then pos(start,j) <= pos(result,j).
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_1 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∃ (r : Bool), Aegis.CanTransform.can_transform start result = ok r ∧
      (r = true ↔
        (nonX start.val = nonX result.val ∧
          ∀ j, j < (nonX start.val).length →
            ((nonXget start.val j).val = 76 → pos result.val j ≤ pos start.val j) ∧
            ((nonXget start.val j).val = 82 → pos start.val j ≤ pos result.val j))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∃ (r : Bool), Aegis.CanTransform.can_transform start result = ok r ∧
      (r = true ↔
        (nonX start.val = nonX result.val ∧
          ∀ j, j < (nonX start.val).length →
            ((nonXget start.val j).val = 76 → pos result.val j ≤ pos start.val j) ∧
            ((nonXget start.val j).val = 82 → pos start.val j ≤ pos result.val j)))) := by
  sorry

/-- The function returns a result r and does not fail: there is no panic, out-of-bounds access, arithmetic overflow, or other runtime failure.
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_2 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∃ (r : Bool), Aegis.CanTransform.can_transform start result = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∃ (r : Bool), Aegis.CanTransform.can_transform start result = ok r) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the sequence of non-'X' bytes of start equals the sequence of non-'X' bytes of result.
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_3 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      nonX start.val = nonX result.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      nonX start.val = nonX result.val) := by
  sorry

/-- Whenever the function returns r = true, for every j with 0 <= j < number of 'L' bytes in start, the index in start of the j-th 'L' byte is greater than or equal to the index in result of the j-th 'L' byte. Here the j-th 'L' is counted from 0 among the 'L' bytes only, and the j-th 'L' of result is defined because r = true implies equal numbers of 'L' bytes.
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_4 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ j, j < countL start.val → posL result.val j ≤ posL start.val j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ j, j < countL start.val → posL result.val j ≤ posL start.val j) := by
  sorry

/-- Whenever the function returns r = true, for every j with 0 <= j < number of 'R' bytes in start, the index in start of the j-th 'R' byte is less than or equal to the index in result of the j-th 'R' byte. Here the j-th 'R' is counted from 0 among the 'R' bytes only, and the j-th 'R' of result is defined because r = true implies equal numbers of 'R' bytes.
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_5 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ j, j < countR start.val → posR start.val j ≤ posR result.val j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ j, j < countR start.val → posR start.val j ≤ posR result.val j) := by
  sorry

/-- Whenever the function returns r = true, for every prefix length k with 0 <= k <= len(start), the number of 'L' bytes in start[0..k) is less than or equal to the number of 'L' bytes in result[0..k).
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_6 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ k, k ≤ start.val.length → countL (start.val.take k) ≤ countL (result.val.take k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ k, k ≤ start.val.length → countL (start.val.take k) ≤ countL (result.val.take k)) := by
  sorry

/-- Whenever the function returns r = true, for every prefix length k with 0 <= k <= len(start), the number of 'R' bytes in start[0..k) is greater than or equal to the number of 'R' bytes in result[0..k).
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_7 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ k, k ≤ start.val.length → countR (result.val.take k) ≤ countR (start.val.take k) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∀ k, k ≤ start.val.length → countR (result.val.take k) ≤ countR (start.val.take k)) := by
  sorry

/-- If the function returns true on (start,result) and also returns true on the swapped arguments (result,start), then start[i] = result[i] for every i with 0 <= i < len(start).
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_8 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    Aegis.CanTransform.can_transform start result = ok true →
      Aegis.CanTransform.can_transform result start = ok true → start.val = result.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), Aegis.CanTransform.can_transform start result = ok true →
      Aegis.CanTransform.can_transform result start = ok true → start.val = result.val) := by
  sorry

/-- Whenever the function returns r = true, there exists a finite sequence of byte arrays s_0, ..., s_m with m >= 0 such that s_0 = start, s_m = result, each s_t has length len(start) and consists only of bytes 'L', 'R', 'X', and for every t with 0 <= t < m, s_{t+1} is obtained from s_t by replacing one occurrence of 'XL' with 'LX' or one occurrence of 'RX' with 'XR'.
  Preconditions: len(start) = len(result); 1 <= len(start) <= 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_9 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val) :
    ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∃ (m : Nat) (s : Fin (m + 1) → List Std.U8),
        s 0 = start.val ∧
          s ⟨m, Nat.lt_succ_self m⟩ = result.val ∧
          (∀ t : Fin (m + 1), (s t).length = start.val.length) ∧
          (∀ t : Fin (m + 1), IsLRX (s t)) ∧
          (∀ t : Fin m, Step (s t.castSucc) (s t.succ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length ≤ 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val), ∀ (r : Bool), Aegis.CanTransform.can_transform start result = ok r → r = true →
      ∃ (m : Nat) (s : Fin (m + 1) → List Std.U8),
        s 0 = start.val ∧
          s ⟨m, Nat.lt_succ_self m⟩ = result.val ∧
          (∀ t : Fin (m + 1), (s t).length = start.val.length) ∧
          (∀ t : Fin (m + 1), IsLRX (s t)) ∧
          (∀ t : Fin m, Step (s t.castSucc) (s t.succ))) := by
  sorry

/-- Let start' be the byte array of length len(start)+1 with start'[0] = 'X' and start'[i+1] = start[i] for every 0 <= i < len(start), and define result' analogously from result. Then the Boolean returned by the function on (start',result') equals the Boolean returned on (start,result).
  Preconditions: len(start) = len(result); 1 <= len(start) < 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_10 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length < 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val)
    (start' result' : Slice Std.U8)
    (hstart' : start'.val = 88#u8 :: start.val)
    (hresult' : result'.val = 88#u8 :: result.val) :
    ∃ (r : Bool), Aegis.CanTransform.can_transform start' result' = ok r ∧
      Aegis.CanTransform.can_transform start result = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length < 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val)
    (start' result' : Slice Std.U8)
    (hstart' : start'.val = 88#u8 :: start.val)
    (hresult' : result'.val = 88#u8 :: result.val), ∃ (r : Bool), Aegis.CanTransform.can_transform start' result' = ok r ∧
      Aegis.CanTransform.can_transform start result = ok r) := by
  sorry

/-- Let start' be start followed by one byte 'X', and let result' be result followed by one byte 'X'. Then the Boolean returned by the function on (start',result') equals the Boolean returned on (start,result).
  Preconditions: len(start) = len(result); 1 <= len(start) < 10000; for every i with 0 <= i < len(start), start[i] and result[i] are one of the bytes 'L', 'R', 'X' (ASCII 76, 82, 88). -/
theorem spec_11 (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length < 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val)
    (start' result' : Slice Std.U8)
    (hstart' : start'.val = start.val ++ [88#u8])
    (hresult' : result'.val = result.val ++ [88#u8]) :
    ∃ (r : Bool), Aegis.CanTransform.can_transform start' result' = ok r ∧
      Aegis.CanTransform.can_transform start result = ok r := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (start result : Slice Std.U8)
    (hlen : start.val.length = result.val.length)
    (hsize : 1 ≤ start.val.length ∧ start.val.length < 10000)
    (hstart : IsLRX start.val) (hresult : IsLRX result.val)
    (start' result' : Slice Std.U8)
    (hstart' : start'.val = start.val ++ [88#u8])
    (hresult' : result'.val = result.val ++ [88#u8]), ∃ (r : Bool), Aegis.CanTransform.can_transform start' result' = ok r ∧
      Aegis.CanTransform.can_transform start result = ok r) := by
  sorry

end AegisSpec.CanTransform
