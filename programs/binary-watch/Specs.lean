import Aegis.ReadBinaryWatch.Code.Funs

/-!
# Specifications of `Aegis.ReadBinaryWatch.read_binary_watch`

LeetCode problem `binary-watch`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ReadBinaryWatch (read_binary_watch)

namespace AegisSpec.ReadBinaryWatch

def timeBytes (r : alloc.vec.Vec (alloc.vec.Vec Std.U8)) : List (List Std.U8) :=
  r.val.map (fun v => v.val)

def byteOf (n : Nat) : Std.U8 :=
  Std.U8.ofNatCore (n % 256) (by
    have h : Aeneas.Std.UScalarTy.U8.numBits = 8 := rfl
    rw [h]
    norm_num
    exact Nat.mod_lt _ (by norm_num))

def colonByte : Std.U8 := byteOf 58

def digitByte (d : Nat) : Std.U8 := byteOf (48 + d % 10)

def hourFieldOf (h : Nat) : List Std.U8 :=
  if h < 10 then [digitByte h] else [byteOf 49, digitByte (h - 10)]

def minuteFieldOf (m : Nat) : List Std.U8 :=
  [digitByte (m / 10), digitByte (m % 10)]

def fmtBytes (h m : Nat) : List Std.U8 :=
  hourFieldOf h ++ colonByte :: minuteFieldOf m

def fmt (h m : Int) : List Std.U8 := fmtBytes h.toNat m.toNat

def popcount (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 2 + popcount (n / 2)
termination_by n
decreasing_by omega

def pc4 (h : Int) : Int := (popcount (h.toNat % 16) : Int)

def pc6 (m : Int) : Int := (popcount (m.toNat % 64) : Int)

def allDigits (l : List Std.U8) : Prop := ∀ b ∈ l, 48 ≤ b.val ∧ b.val ≤ 57

def colonFormatted (v : List Std.U8) : Prop :=
  ∃ pre post : List Std.U8,
    v = pre ++ colonByte :: post ∧ (pre.length = 1 ∨ pre.length = 2) ∧ post.length = 2 ∧
      allDigits pre ∧ allDigits post ∧ (v.filter (fun b => b = colonByte)).length = 1

def digitsToNat (l : List Std.U8) : Nat :=
  l.foldl (fun acc b => acc * 10 + (b.val - 48)) 0

def hourField (v : List Std.U8) : List Std.U8 := v.takeWhile (fun b => b ≠ colonByte)

def minuteField (v : List Std.U8) : List Std.U8 :=
  (v.dropWhile (fun b => b ≠ colonByte)).drop 1

def parseHour (v : List Std.U8) : Int := (digitsToNat (hourField v) : Int)

def parseMinute (v : List Std.U8) : Int := (digitsToNat (minuteField v) : Int)

def countTimes (t : Int) : Nat :=
  (((List.range 12).product (List.range 60)).filter
      (fun p : Nat × Nat => pc4 (p.1 : Int) + pc6 (p.2 : Int) = t)).length

/-- Let pc4(h) be the number of set bits in the 4-bit binary representation of h, let pc6(m) be the number of set bits in the 6-bit binary representation of m, and let fmt(h,m) be the ASCII byte vector for hour h and minute m: the decimal representation of h with no leading zeros, then the byte ':' (ASCII 58), then the two decimal digits of m, using a leading zero when m < 10. Whenever the function returns a result r, r is a duplicate-free list whose elements, in some order, are exactly the byte vectors fmt(h,m) for all pairs (h,m) with 0 <= h < 12, 0 <= m < 60, and pc4(h)+pc6(m)=turnedOn. Equivalently, for every byte vector s, s occurs in r if and only if there exist such h,m with s=fmt(h,m), and no byte vector occurs twice in r.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_1 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    (timeBytes r).Nodup ∧
      ∀ s : List Std.U8,
        s ∈ timeBytes r ↔
          ∃ h m : Int,
            0 ≤ h ∧ h < 12 ∧ 0 ≤ m ∧ m < 60 ∧ pc4 h + pc6 m = turnedOn.val ∧ s = fmt h m := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), (timeBytes r).Nodup ∧
      ∀ s : List Std.U8,
        s ∈ timeBytes r ↔
          ∃ h m : Int,
            0 ≤ h ∧ h < 12 ∧ 0 ≤ m ∧ m < 60 ∧ pc4 h + pc6 m = turnedOn.val ∧ s = fmt h m) := by
  sorry

/-- For every turnedOn satisfying the precondition, the function returns a result r; it does not fail, overflow, or panic.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_2 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), read_binary_watch turnedOn = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8), read_binary_watch turnedOn = ok r) := by
  sorry

/-- For every index i with 0 <= i < len(r), the byte vector r[i] has length 4 or 5, contains exactly one colon byte (ASCII 58) at index len(r[i])-3, and every other byte is an ASCII decimal digit (byte value 48 through 57). Thus the two bytes after the colon are the minute field and the one or two bytes before it are the hour field.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_3 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    ∀ (i : Nat) (hi : i < (timeBytes r).length), colonFormatted ((timeBytes r)[i]'hi) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), ∀ (i : Nat) (hi : i < (timeBytes r).length), colonFormatted ((timeBytes r)[i]'hi)) := by
  sorry

/-- For every index i with 0 <= i < len(r), if r[i] is in the required colon format, let h be the nonnegative integer represented by the bytes of r[i] before the colon. Then 0 <= h <= 11, and the hour field is the usual decimal representation of h with no leading zero: h=0 is the single byte '0', for 1 <= h <= 9 the hour field is one digit, and for h=10 or h=11 it is the two bytes '10' or '11'.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_4 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        (let v := (timeBytes r)[i]'hi
         let h := parseHour v
         0 ≤ h ∧ h ≤ 11 ∧ hourField v = hourFieldOf h.toNat) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        (let v := (timeBytes r)[i]'hi
         let h := parseHour v
         0 ≤ h ∧ h ≤ 11 ∧ hourField v = hourFieldOf h.toNat)) := by
  sorry

/-- For every index i with 0 <= i < len(r), if r[i] is in the required colon format, let m be the nonnegative integer represented by the two bytes after the colon. Then 0 <= m <= 59, the minute field always consists of exactly two decimal digits, and when m < 10 its first digit is '0' (so minute 2 is written as '02', not '2').
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_5 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        (let v := (timeBytes r)[i]'hi
         let m := parseMinute v
         0 ≤ m ∧ m ≤ 59 ∧ minuteField v = minuteFieldOf m.toNat ∧ (minuteField v).length = 2) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        (let v := (timeBytes r)[i]'hi
         let m := parseMinute v
         0 ≤ m ∧ m ≤ 59 ∧ minuteField v = minuteFieldOf m.toNat ∧ (minuteField v).length = 2)) := by
  sorry

/-- For every index i with 0 <= i < len(r), if h and m are the hour and minute parsed from r[i] as above, then pc4(h)+pc6(m)=turnedOn, where pc4(h) is the number of set bits in the 4-bit representation of h and pc6(m) is the number of set bits in the 6-bit representation of m. Thus every returned time has exactly turnedOn LEDs on.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_6 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        pc4 (parseHour ((timeBytes r)[i]'hi)) + pc6 (parseMinute ((timeBytes r)[i]'hi)) =
          turnedOn.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), ∀ (i : Nat) (hi : i < (timeBytes r).length),
      colonFormatted ((timeBytes r)[i]'hi) →
        pc4 (parseHour ((timeBytes r)[i]'hi)) + pc6 (parseMinute ((timeBytes r)[i]'hi)) =
          turnedOn.val) := by
  sorry

/-- For every pair of integers h,m with 0 <= h < 12, 0 <= m < 60, and pc4(h)+pc6(m)=turnedOn, there exists an index i with 0 <= i < len(r) such that r[i] is exactly the ASCII byte vector fmt(h,m), where fmt(h,m) is the hour written without leading zero, then ':', then the two-digit minute with a leading zero when m < 10. Thus every possible time with exactly turnedOn LEDs on is present in the result.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_7 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    ∀ h m : Int,
      0 ≤ h →
        h < 12 →
          0 ≤ m →
            m < 60 →
              pc4 h + pc6 m = turnedOn.val →
                ∃ (i : Nat) (hi : i < (timeBytes r).length), (timeBytes r)[i]'hi = fmt h m := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), ∀ h m : Int,
      0 ≤ h →
        h < 12 →
          0 ≤ m →
            m < 60 →
              pc4 h + pc6 m = turnedOn.val →
                ∃ (i : Nat) (hi : i < (timeBytes r).length), (timeBytes r)[i]'hi = fmt h m) := by
  sorry

/-- Whenever the function returns a result r under this precondition, r has length 1, and r[0] is the four-byte ASCII vector for '0:00' (bytes '0', ':', '0', '0').
  Preconditions: 0 <= turnedOn <= 10 and turnedOn = 0. -/
theorem spec_8 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h0 : turnedOn.val = 0)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    (timeBytes r).length = 1 ∧ timeBytes r = [fmt 0 0] ∧
      fmt 0 0 = [byteOf 48, colonByte, byteOf 48, byteOf 48] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h0 : turnedOn.val = 0)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), (timeBytes r).length = 1 ∧ timeBytes r = [fmt 0 0] ∧
      fmt 0 0 = [byteOf 48, colonByte, byteOf 48, byteOf 48]) := by
  sorry

/-- Whenever the function returns a result r under this precondition, r is empty: len(r)=0.
  Preconditions: 0 <= turnedOn <= 10 and (turnedOn = 9 or turnedOn = 10). -/
theorem spec_9 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h9 : turnedOn.val = 9 ∨ turnedOn.val = 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    (timeBytes r).length = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h9 : turnedOn.val = 9 ∨ turnedOn.val = 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), (timeBytes r).length = 0) := by
  sorry

/-- Whenever the function returns a result r under this precondition, r has length 8, and its elements are exactly the eight ASCII byte vectors for the times 7:31, 7:47, 7:55, 7:59, 11:31, 11:47, 11:55, and 11:59, in any order.
  Preconditions: 0 <= turnedOn <= 10 and turnedOn = 8. -/
theorem spec_10 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h8 : turnedOn.val = 8)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    (timeBytes r).length = 8 ∧
      (timeBytes r).Perm
        [fmt 7 31, fmt 7 47, fmt 7 55, fmt 7 59, fmt 11 31, fmt 11 47, fmt 11 55, fmt 11 59] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (h8 : turnedOn.val = 8)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), (timeBytes r).length = 8 ∧
      (timeBytes r).Perm
        [fmt 7 31, fmt 7 47, fmt 7 55, fmt 7 59, fmt 11 31, fmt 11 47, fmt 11 55, fmt 11 59]) := by
  sorry

/-- Let r_t be any result returned by the function for input turnedOn=t, and let r_u be any result returned by the function for input turnedOn=u. Then no byte vector occurs in both r_t and r_u; equivalently, the sets of formatted times for two different LED counts are disjoint.
  Preconditions: 0 <= t <= 10, 0 <= u <= 10, and t != u. -/
theorem spec_11 (t u : Std.I64) (ht : 0 ≤ t.val ∧ t.val ≤ 10) (hu : 0 ≤ u.val ∧ u.val ≤ 10)
    (hne : t.val ≠ u.val)
    (rt ru : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hrt : read_binary_watch t = ok rt) (hru : read_binary_watch u = ok ru) :
    ∀ s : List Std.U8, s ∈ timeBytes rt → s ∉ timeBytes ru := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (t u : Std.I64) (ht : 0 ≤ t.val ∧ t.val ≤ 10) (hu : 0 ≤ u.val ∧ u.val ≤ 10)
    (hne : t.val ≠ u.val)
    (rt ru : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hrt : read_binary_watch t = ok rt) (hru : read_binary_watch u = ok ru), ∀ s : List Std.U8, s ∈ timeBytes rt → s ∉ timeBytes ru) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of pairs (h,m) with 0 <= h < 12, 0 <= m < 60, and pc4(h)+pc6(m)=turnedOn, where pc4(h) is the number of set bits in the 4-bit representation of h and pc6(m) is the number of set bits in the 6-bit representation of m.
  Preconditions: 0 <= turnedOn <= 10. -/
theorem spec_12 (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r) :
    (timeBytes r).length = countTimes turnedOn.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (turnedOn : Std.I64) (ht : 0 ≤ turnedOn.val ∧ turnedOn.val ≤ 10)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.U8))
    (hr : read_binary_watch turnedOn = ok r), (timeBytes r).length = countTimes turnedOn.val) := by
  sorry

/-- The function returns a result r and r is empty: len(r)=0.
  Preconditions: turnedOn = 11 (provided example test; outside the stated LeetCode constraint 0 <= turnedOn <= 10). -/
theorem spec_13 (turnedOn : Std.I64) (h11 : turnedOn.val = 11) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      read_binary_watch turnedOn = ok r ∧ (timeBytes r).length = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (turnedOn : Std.I64) (h11 : turnedOn.val = 11), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.U8),
      read_binary_watch turnedOn = ok r ∧ (timeBytes r).length = 0) := by
  sorry

end AegisSpec.ReadBinaryWatch
