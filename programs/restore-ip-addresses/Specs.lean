import Aegis.RestoreIpAddresses.Code.Funs

/-!
# Specifications of `Aegis.RestoreIpAddresses.restore_ip_addresses`

LeetCode problem `restore-ip-addresses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RestoreIpAddresses

  set_option autoImplicit false

  def IsAsciiDigit (b : Std.U8) : Prop := 48 ≤ b.val ∧ b.val ≤ 57

  def Pre (s : Slice Std.U8) : Prop :=
    1 ≤ s.val.length ∧ s.val.length ≤ 20 ∧
      ∀ i : Fin s.val.length, IsAsciiDigit (s.val.get i)

  def part (s : Slice Std.U8) (lo hi : ℕ) : List Std.U8 := (s.val.drop lo).take (hi - lo)

  def firstByte : List Std.U8 → ℕ
    | [] => 0
    | b :: _ => b.val

  def decimalValue (l : List Std.U8) : ℕ := l.foldl (fun acc b => acc * 10 + (b.val - 48)) 0

  def dot : Std.U8 := 46#u8

  def HasNoDot (l : List Std.U8) : Prop := ∀ b ∈ l, b.val ≠ 46

  def splitDots : List Std.U8 → List (List Std.U8)
    | [] => []
    | b :: bs =>
      if b.val = 46 then [] :: splitDots bs
      else
        match splitDots bs with
        | [] => [[b]]
        | p :: ps => (b :: p) :: ps

  def removeDots (l : List Std.U8) : List Std.U8 := l.filter (fun b => b.val ≠ 46)

  def countDots (l : List Std.U8) : ℕ := (l.filter (fun b => b.val = 46)).length

  def CutsOk (s : Slice Std.U8) (p0 p1 p2 p3 p4 : ℕ) : Prop :=
    p0 = 0 ∧ p4 = s.val.length ∧
    p0 < p1 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧
    (1 ≤ p1 - p0 ∧ p1 - p0 ≤ 3) ∧
    (1 ≤ p2 - p1 ∧ p2 - p1 ≤ 3) ∧
    (1 ≤ p3 - p2 ∧ p3 - p2 ≤ 3) ∧
    (1 ≤ p4 - p3 ∧ p4 - p3 ≤ 3) ∧
    (1 < p1 - p0 → firstByte (part s p0 p1) ≠ 48) ∧
    (1 < p2 - p1 → firstByte (part s p1 p2) ≠ 48) ∧
    (1 < p3 - p2 → firstByte (part s p2 p3) ≠ 48) ∧
    (1 < p4 - p3 → firstByte (part s p3 p4) ≠ 48) ∧
    decimalValue (part s p0 p1) ≤ 255 ∧
    decimalValue (part s p1 p2) ≤ 255 ∧
    decimalValue (part s p2 p3) ≤ 255 ∧
    decimalValue (part s p3 p4) ≤ 255

  def dotted (s : Slice Std.U8) (p0 p1 p2 p3 p4 : ℕ) : List Std.U8 :=
    part s p0 p1 ++ [dot] ++ part s p1 p2 ++ [dot] ++
      part s p2 p3 ++ [dot] ++ part s p3 p4

  def IsDottedFrom (s : Slice Std.U8) (v : List Std.U8) : Prop :=
    ∃ p0 p1 p2 p3 p4 : ℕ, CutsOk s p0 p1 p2 p3 p4 ∧ dotted s p0 p1 p2 p3 p4 = v

  def elems (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
    r.val.map (fun v => v.val)

  def countOcc (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) (v : List Std.U8) : ℕ :=
    (elems r).countP (fun w => decide (w = v))

  /-- The function returns a result r such that, for every byte vector v, v occurs as an element of r exactly once if and only if there exist cut positions 0 = p0 < p1 < p2 < p3 < p4 = len(s) satisfying: (1) for each k = 0,1,2,3, 1 <= p_{k+1} - p_k <= 3; (2) for each k = 0,1,2,3, if p_{k+1} - p_k > 1 then s[p_k] != 48 (the first digit of a multi-digit part is not '0'); (3) for each k = 0,1,2,3, the decimal value of s[p_k],...,s[p_{k+1}-1] is at most 255; and (4) v is the concatenation of s[p0..p1], byte 46 ('.'), s[p1..p2], byte 46, s[p2..p3], byte 46, and s[p3..p4], in that order. No order of the elements of r is required.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57 (s consists of ASCII decimal digits). -/
  theorem spec_1 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v : List Std.U8, countOcc r v = 1 ↔ IsDottedFrom s v := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v : List Std.U8, countOcc r v = 1 ↔ IsDottedFrom s v) := by
    sorry

  /-- For every s satisfying Pre(s), restore_ip_addresses(s) returns a result r (it does not fail by overflow, out-of-bounds access, or panic); thus every returned-value claim below refers to this r.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_2 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r) := by
    sorry

  /-- The function returns a result r and, for every element v of r, 7 <= len(v) <= 15.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_3 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, 7 ≤ v.val.length ∧ v.val.length ≤ 15 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, 7 ≤ v.val.length ∧ v.val.length ≤ 15) := by
    sorry

  /-- The function returns a result r and every element v of r satisfies: v contains exactly three occurrences of byte 46 ('.'), and every byte of v is either 46 or an ASCII decimal digit with 48 <= byte <= 57.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_4 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, countDots v.val = 3 ∧ ∀ b ∈ v.val, b.val = 46 ∨ IsAsciiDigit b := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, countDots v.val = 3 ∧ ∀ b ∈ v.val, b.val = 46 ∨ IsAsciiDigit b) := by
    sorry

  /-- The function returns a result r and every element v of r satisfies: when v is split at its three '.' bytes, exactly four nonempty byte sequences are obtained; equivalently, v[0] != 46, v[len(v)-1] != 46, and no two consecutive bytes of v are both 46.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_5 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, (splitDots v.val).length = 4 ∧ ∀ p ∈ splitDots v.val, p ≠ [] := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, (splitDots v.val).length = 4 ∧ ∀ p ∈ splitDots v.val, p ≠ []) := by
    sorry

  /-- The function returns a result r and, for every element v of r, deleting all bytes equal to 46 ('.') from v yields exactly the byte sequence s (same length and same bytes in the same order).
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_6 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, removeDots v.val = s.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, removeDots v.val = s.val) := by
    sorry

  /-- The function returns a result r and, for every element v of r, if v is written as p0 '.' p1 '.' p2 '.' p3 with each pi a byte sequence not containing 46, then 1 <= len(pi) <= 3 for i = 0,1,2,3.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_7 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, ∀ p0 p1 p2 p3 : List Std.U8,
            HasNoDot p0 → HasNoDot p1 → HasNoDot p2 → HasNoDot p3 →
              v.val = p0 ++ [dot] ++ p1 ++ [dot] ++ p2 ++ [dot] ++ p3 →
                1 ≤ p0.length ∧ p0.length ≤ 3 ∧
                1 ≤ p1.length ∧ p1.length ≤ 3 ∧
                1 ≤ p2.length ∧ p2.length ≤ 3 ∧
                1 ≤ p3.length ∧ p3.length ≤ 3 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, ∀ p0 p1 p2 p3 : List Std.U8,
              HasNoDot p0 → HasNoDot p1 → HasNoDot p2 → HasNoDot p3 →
                v.val = p0 ++ [dot] ++ p1 ++ [dot] ++ p2 ++ [dot] ++ p3 →
                  1 ≤ p0.length ∧ p0.length ≤ 3 ∧
                  1 ≤ p1.length ∧ p1.length ≤ 3 ∧
                  1 ≤ p2.length ∧ p2.length ≤ 3 ∧
                  1 ≤ p3.length ∧ p3.length ≤ 3) := by
    sorry

  /-- The function returns a result r and, for every element v of r, for every dot-separated part p of v, if len(p) > 1 then p[0] != 48 (the ASCII code of '0').
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_8 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, ∀ p ∈ splitDots v.val, 1 < p.length → firstByte p ≠ 48 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, ∀ p ∈ splitDots v.val, 1 < p.length → firstByte p ≠ 48) := by
    sorry

  /-- The function returns a result r and, for every element v of r, for every nonempty dot-separated part p of v, the decimal number represented by p, namely the sum over j with 0 <= j < len(p) of (p[j] - 48) * 10^(len(p)-1-j), is between 0 and 255 inclusive.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_9 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, ∀ p ∈ splitDots v.val,
            p ≠ [] → 0 ≤ decimalValue p ∧ decimalValue p ≤ 255 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, ∀ p ∈ splitDots v.val,
              p ≠ [] → 0 ≤ decimalValue p ∧ decimalValue p ≤ 255) := by
    sorry

  /-- The function returns a result r and every element v of r is obtainable from s by inserting exactly three dots: there exist cut positions 0 = p0 < p1 < p2 < p3 < p4 = len(s) such that 1 <= p_{k+1} - p_k <= 3 for k = 0,1,2,3, no multi-digit part begins with byte 48, each part has decimal value at most 255, and v is the dotted concatenation s[p0..p1] '.' s[p1..p2] '.' s[p2..p3] '.' s[p3..p4].
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_10 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ v ∈ r.val, IsDottedFrom s v.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ v ∈ r.val, IsDottedFrom s v.val) := by
    sorry

  /-- The function returns a result r and, for every choice of cut positions 0 = p0 < p1 < p2 < p3 < p4 = len(s) satisfying (1) 1 <= p_{k+1} - p_k <= 3 for k = 0,1,2,3, (2) no part of length greater than 1 starts with byte 48, and (3) each part's decimal value is at most 255, the byte vector formed by the dotted concatenation s[p0..p1] '.' s[p1..p2] '.' s[p2..p3] '.' s[p3..p4] occurs as an element of r.
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_11 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ p0 p1 p2 p3 p4 : ℕ, CutsOk s p0 p1 p2 p3 p4 →
            ∃ v ∈ r.val, v.val = dotted s p0 p1 p2 p3 p4 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ p0 p1 p2 p3 p4 : ℕ, CutsOk s p0 p1 p2 p3 p4 →
              ∃ v ∈ r.val, v.val = dotted s p0 p1 p2 p3 p4) := by
    sorry

  /-- The function returns a result r and, for every i,j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: Pre(s): s is a byte slice with 1 <= len(s) <= 20 and, for every i with 0 <= i < len(s), 48 <= s[i] <= 57. -/
  theorem spec_12 (s : Slice Std.U8) (h : Pre s) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
        Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
          ∀ i j : Fin r.val.length, i < j → r.val.get i ≠ r.val.get j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8) (h : Pre s), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
          Aegis.RestoreIpAddresses.restore_ip_addresses s = ok r ∧
            ∀ i j : Fin r.val.length, i < j → r.val.get i ≠ r.val.get j) := by
    sorry

  end AegisSpec.RestoreIpAddresses
