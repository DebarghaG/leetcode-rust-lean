import Aegis.NumberOfRounds.Code.Funs

/-!
# Specifications of `Aegis.NumberOfRounds.number_of_rounds`

LeetCode problem `the-number-of-full-rounds-you-have-played`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.NumberOfRounds

  namespace AegisSpec.NumberOfRounds

  def byteAt (s : Slice Std.U8) (i : Nat) : Option Nat := (s.val[i]?).map UScalar.val

  def IsDigitByte (n : Nat) : Prop := 48 ≤ n ∧ n ≤ 57

  def digitAt (s : Slice Std.U8) (i : Nat) : Nat := (byteAt s i).getD 0 - 48

  def hh (s : Slice Std.U8) : Nat := 10 * digitAt s 0 + digitAt s 1

  def mm (s : Slice Std.U8) : Nat := 10 * digitAt s 3 + digitAt s 4

  def t (s : Slice Std.U8) : Nat := 60 * hh s + mm s

  def IsTime (s : Slice Std.U8) : Prop :=
    s.length = 5 ∧
    byteAt s 2 = some 58 ∧
    (∀ i, i < 5 → i ≠ 2 → ∃ d, byteAt s i = some d ∧ IsDigitByte d) ∧
    hh s ≤ 23 ∧ mm s ≤ 59

  def floor15 (x : Nat) : Nat := x / 15

  def ceil15 (x : Nat) : Nat := (x + 14) / 15

  def gap (tL tO : Nat) : Nat := if tL < tO then tO - tL else 1440 + tO - tL

  def IsRoundStart (tL tO : Nat) (k : Int) : Prop :=
    (tL < tO → (tL : Int) ≤ 15 * k ∧ 15 * k + 15 ≤ (tO : Int)) ∧
    (tO < tL → (tL : Int) ≤ 15 * k ∧ 15 * k + 15 ≤ 1440 + (tO : Int))

  noncomputable def roundCount (tL tO : Nat) : Nat :=
    ({k : Int | IsRoundStart tL tO k} : Set Int).ncard

  /-- The function returns a result r and r equals the number of integers k such that: if tL < tO, then tL <= 15*k and 15*k + 15 <= tO; if tL > tO, then tL <= 15*k and 15*k + 15 <= 1440 + tO. Equivalently, r is exactly the number of full 15-minute chess rounds completely contained in the played interval from loginTime forward to logoutTime, wrapping past midnight exactly when tL > tO.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_1 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
        r.val = (roundCount (t loginTime) (t logoutTime) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
          r.val = (roundCount (t loginTime) (t logoutTime) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_2 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∀ r, number_of_rounds loginTime logoutTime = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∀ r, number_of_rounds loginTime logoutTime = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 95.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_3 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∀ r, number_of_rounds loginTime logoutTime = ok r → r.val ≤ 95 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∀ r, number_of_rounds loginTime logoutTime = ok r → r.val ≤ 95) := by
    sorry

  /-- Let D = tO - tL when tL < tO, and D = 1440 + tO - tL when tL > tO. Whenever the function returns a result r, 15*r <= D, equivalently r <= floor15(D).
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_4 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∀ r, number_of_rounds loginTime logoutTime = ok r →
        15 * r.val ≤ ((gap (t loginTime) (t logoutTime) : Nat) : Int) ∧
        r.val ≤ ((floor15 (gap (t loginTime) (t logoutTime)) : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∀ r, number_of_rounds loginTime logoutTime = ok r →
          15 * r.val ≤ ((gap (t loginTime) (t logoutTime) : Nat) : Int) ∧
          r.val ≤ ((floor15 (gap (t loginTime) (t logoutTime)) : Nat) : Int)) := by
    sorry

  /-- The function returns a result r (evaluation is Ok r) and does not fail: there is no overflow, no out-of-bounds access, and no panic for any input satisfying the preconditions.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_5 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∃ r, number_of_rounds loginTime logoutTime = ok r) := by
    sorry

  /-- Let D = tO - tL when tL < tO, and D = 1440 + tO - tL when tL > tO. If D < 15, then the function returns a result r with r = 0.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_6 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hD : gap (t loginTime) (t logoutTime) < 15) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hD : gap (t loginTime) (t logoutTime) < 15), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧ r.val = 0) := by
    sorry

  /-- If tL < tO and both tL and tO are divisible by 15, then the function returns r = (tO - tL) / 15.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_7 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hlt : t loginTime < t logoutTime)
      (hdivO : 15 ∣ t logoutTime) (hdivL : 15 ∣ t loginTime) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
        r.val = (((t logoutTime - t loginTime) / 15 : Nat) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hlt : t loginTime < t logoutTime)
        (hdivO : 15 ∣ t logoutTime) (hdivL : 15 ∣ t loginTime), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
          r.val = (((t logoutTime - t loginTime) / 15 : Nat) : Int)) := by
    sorry

  /-- Let r1 be the result of number_of_rounds(L, O1) and r2 be the result of number_of_rounds(L, O2). Whenever both calls return results, r1 <= r2.
    Preconditions: L, O1, O2 are byte slices of length 5; for each such slice s, s[2] is byte 58, s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57, hh(s) = 10*(s[0]-48)+(s[1]-48) <= 23, mm(s) = 10*(s[3]-48)+(s[4]-48) <= 59, and t(s)=60*hh(s)+mm(s). Let tL=t(L), tO1=t(O1), tO2=t(O2). Require tL < tO1 <= tO2. -/
  theorem spec_8 (L O1 O2 : Slice Std.U8)
      (hL : IsTime L) (h1 : IsTime O1) (h2 : IsTime O2)
      (hlt : t L < t O1) (hle : t O1 ≤ t O2) :
      ∀ r1 r2, number_of_rounds L O1 = ok r1 → number_of_rounds L O2 = ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (L O1 O2 : Slice Std.U8)
        (hL : IsTime L) (h1 : IsTime O1) (h2 : IsTime O2)
        (hlt : t L < t O1) (hle : t O1 ≤ t O2), ∀ r1 r2, number_of_rounds L O1 = ok r1 → number_of_rounds L O2 = ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- For every integer c, let Lc and Oc be the unique byte strings in hh:mm format with t(Lc) = (tL + 15*c) mod 1440 and t(Oc) = (tO + 15*c) mod 1440. Then number_of_rounds(Lc, Oc) returns the same result as number_of_rounds(loginTime, logoutTime).
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_9 (loginTime logoutTime L O : Slice Std.U8) (c : Int)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hL' : IsTime L) (hO' : IsTime O)
      (hLt : (t L : Int) = ((t loginTime : Int) + 15 * c) % 1440)
      (hOt : (t O : Int) = ((t logoutTime : Int) + 15 * c) % 1440) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧ number_of_rounds L O = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (loginTime logoutTime L O : Slice Std.U8) (c : Int)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hL' : IsTime L) (hO' : IsTime O)
        (hLt : (t L : Int) = ((t loginTime : Int) + 15 * c) % 1440)
        (hOt : (t O : Int) = ((t logoutTime : Int) + 15 * c) % 1440), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧ number_of_rounds L O = ok r) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists an integer k such that: either tL < tO and tL <= 15*k and 15*k + 15 <= tO, or tL > tO and tL <= 15*k and 15*k + 15 <= 1440 + tO.
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_10 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime) :
      ∀ r, number_of_rounds loginTime logoutTime = ok r → 0 < r.val →
        ∃ k : Int,
          (t loginTime < t logoutTime ∧ (t loginTime : Int) ≤ 15 * k ∧
            15 * k + 15 ≤ (t logoutTime : Int)) ∨
          (t logoutTime < t loginTime ∧ (t loginTime : Int) ≤ 15 * k ∧
            15 * k + 15 ≤ 1440 + (t logoutTime : Int)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime), ∀ r, number_of_rounds loginTime logoutTime = ok r → 0 < r.val →
          ∃ k : Int,
            (t loginTime < t logoutTime ∧ (t loginTime : Int) ≤ 15 * k ∧
              15 * k + 15 ≤ (t logoutTime : Int)) ∨
            (t logoutTime < t loginTime ∧ (t loginTime : Int) ≤ 15 * k ∧
              15 * k + 15 ≤ 1440 + (t logoutTime : Int))) := by
    sorry

  /-- If tL > tO, then the function returns r = (96 - ceil15(tL)) + floor15(tO).
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_11 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hgt : t loginTime > t logoutTime) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
        r.val = (((96 - ceil15 (t loginTime)) + floor15 (t logoutTime) : Nat) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hgt : t loginTime > t logoutTime), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
          r.val = (((96 - ceil15 (t loginTime)) + floor15 (t logoutTime) : Nat) : Int)) := by
    sorry

  /-- If tL = 0, then the function returns r = floor15(tO).
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_12 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hzero : t loginTime = 0) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
        r.val = ((floor15 (t logoutTime) : Nat) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hzero : t loginTime = 0), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
          r.val = ((floor15 (t logoutTime) : Nat) : Int)) := by
    sorry

  /-- If tL < tO, then the function returns r = max(0, floor15(tO) - ceil15(tL)).
    Preconditions: loginTime and logoutTime are byte slices of length 5. In each slice s, s[2] is the colon byte 58, and s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57. Let hh(s) = 10*(s[0]-48) + (s[1]-48) and mm(s) = 10*(s[3]-48) + (s[4]-48). Require hh(s) <= 23 and mm(s) <= 59. Let t(s) = 60*hh(s)+mm(s), the minute after midnight. Let tL = t(loginTime) and tO = t(logoutTime), and require tL != tO. Write floor15(x) for the greatest integer q with 15*q <= x, and ceil15(x) for the least integer q with 15*q >= x. -/
  theorem spec_13 (loginTime logoutTime : Slice Std.U8)
      (hL : IsTime loginTime) (hO : IsTime logoutTime)
      (hne : t loginTime ≠ t logoutTime)
      (hlt : t loginTime < t logoutTime) :
      ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
        r.val = ((max 0 (floor15 (t logoutTime) - ceil15 (t loginTime)) : Nat) : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (loginTime logoutTime : Slice Std.U8)
        (hL : IsTime loginTime) (hO : IsTime logoutTime)
        (hne : t loginTime ≠ t logoutTime)
        (hlt : t loginTime < t logoutTime), ∃ r, number_of_rounds loginTime logoutTime = ok r ∧
          r.val = ((max 0 (floor15 (t logoutTime) - ceil15 (t loginTime)) : Nat) : Int)) := by
    sorry

  /-- Let r1 be the result of number_of_rounds(L1, O) and r2 be the result of number_of_rounds(L2, O). Whenever both calls return results, r2 <= r1.
    Preconditions: L1, L2, O are byte slices of length 5; for each such slice s, s[2] is byte 58, s[0], s[1], s[3], s[4] are ASCII digit bytes in 48..57, hh(s) = 10*(s[0]-48)+(s[1]-48) <= 23, mm(s) = 10*(s[3]-48)+(s[4]-48) <= 59, and t(s)=60*hh(s)+mm(s). Let tL1=t(L1), tL2=t(L2), tO=t(O). Require tL1 <= tL2 < tO. -/
  theorem spec_14 (L1 L2 O : Slice Std.U8)
      (h1 : IsTime L1) (h2 : IsTime L2) (hO : IsTime O)
      (hle : t L1 ≤ t L2) (hlt : t L2 < t O) :
      ∀ r1 r2, number_of_rounds L1 O = ok r1 → number_of_rounds L2 O = ok r2 →
        r2.val ≤ r1.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (L1 L2 O : Slice Std.U8)
        (h1 : IsTime L1) (h2 : IsTime L2) (hO : IsTime O)
        (hle : t L1 ≤ t L2) (hlt : t L2 < t O), ∀ r1 r2, number_of_rounds L1 O = ok r1 → number_of_rounds L2 O = ok r2 →
          r2.val ≤ r1.val) := by
    sorry

  end AegisSpec.NumberOfRounds
