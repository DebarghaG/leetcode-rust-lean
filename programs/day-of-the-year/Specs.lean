import Aegis.DayOfYear.Code.Funs

/-!
# Specifications of `Aegis.DayOfYear.day_of_year`

LeetCode problem `day-of-the-year`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.DayOfYear

  namespace AegisSpec.DayOfYear

  def byteAt (date : Slice U8) (i : ℕ) : ℕ := (date.val.getD i 0#u8).val

  def Y (date : Slice U8) : ℤ :=
    1000 * ((byteAt date 0 : ℤ) - 48) + 100 * ((byteAt date 1 : ℤ) - 48)
      + 10 * ((byteAt date 2 : ℤ) - 48) + ((byteAt date 3 : ℤ) - 48)

  def M (date : Slice U8) : ℤ := 10 * ((byteAt date 5 : ℤ) - 48) + ((byteAt date 6 : ℤ) - 48)

  def D (date : Slice U8) : ℤ := 10 * ((byteAt date 8 : ℤ) - 48) + ((byteAt date 9 : ℤ) - 48)

  def Leap (y : ℤ) : Bool := y % 4 = 0 && (y % 100 ≠ 0 || y % 400 = 0)

  def Dim (y k : ℤ) : ℤ :=
    if k = 1 ∨ k = 3 ∨ k = 5 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ k = 12 then 31
    else if k = 4 ∨ k = 6 ∨ k = 9 ∨ k = 11 then 30
    else if k = 2 then (if Leap y then 29 else 28)
    else 0

  def DaysThrough (y : ℤ) (n : ℕ) : ℤ :=
    Finset.sum (Finset.range n) fun k => Dim y ((k : ℤ) + 1)

  def Valid (date : Slice U8) : Prop :=
    date.val.length = 10 ∧
      byteAt date 4 = 45 ∧ byteAt date 7 = 45 ∧
      (∀ i, i < 10 → i ≠ 4 → i ≠ 7 → 48 ≤ byteAt date i ∧ byteAt date i ≤ 57) ∧
      1900 ≤ Y date ∧ Y date ≤ 2019 ∧
      1 ≤ M date ∧ M date ≤ 12 ∧
      1 ≤ D date ∧ D date ≤ Dim (Y date) (M date)

  /-- The function returns a result r and r = D + sum_{k=1}^{M-1} Dim(Y,k).
    Preconditions: `date` has len(date)=10; date[4]=45 and date[7]=45 (ASCII '-'); for every i with 0<=i<10 and i not in {4,7}, 48<=date[i]<=57 (ASCII digits). Define Y=1000*(date[0]-48)+100*(date[1]-48)+10*(date[2]-48)+(date[3]-48), M=10*(date[5]-48)+(date[6]-48), D=10*(date[8]-48)+(date[9]-48). Assume 1900<=Y<=2019, 1<=M<=12, and 1<=D<=Dim(Y,M), where Leap(y) iff y mod 4 = 0 and (y mod 100 != 0 or y mod 400 = 0), and Dim(y,k)=31 for k in {1,3,5,7,8,10,12}, 30 for k in {4,6,9,11}, and 28+(if Leap(y) then 1 else 0) for k=2. -/
  theorem spec_1 (date : Slice U8) (h : Valid date) :
      ∃ r, day_of_year date = ok r ∧ r.val = D date + DaysThrough (Y date) (M date - 1).toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date), ∃ r, day_of_year date = ok r ∧ r.val = D date + DaysThrough (Y date) (M date - 1).toNat) := by
    sorry

  /-- For every such input, the function returns a result r; it does not fail, panic, access out of bounds, or overflow.
    Preconditions: `date` satisfies the S1 input shape and calendar validity: len(date)=10; date[4]=date[7]=45; all other bytes are in 48..57; with Y,M,D and Leap,Dim as defined in spec_1, 1900<=Y<=2019, 1<=M<=12, and 1<=D<=Dim(Y,M). -/
  theorem spec_2 (date : Slice U8) (h : Valid date) : ∃ r, day_of_year date = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date), ∃ r, day_of_year date = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 366.
    Preconditions: `date` satisfies the S1 input shape and calendar validity: len(date)=10; date[4]=date[7]=45; all other bytes are in 48..57; with Y,M,D and Leap,Dim as defined in spec_1, 1900<=Y<=2019, 1<=M<=12, and 1<=D<=Dim(Y,M). -/
  theorem spec_3 (date : Slice U8) (h : Valid date) (r : I64) (hr : day_of_year date = ok r) :
      1 ≤ r.val ∧ r.val ≤ 366 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date) (r : I64) (hr : day_of_year date = ok r), 1 ≤ r.val ∧ r.val ≤ 366) := by
    sorry

  /-- The function returns a result r and r=1.
    Preconditions: `date` satisfies the S1 input shape and calendar validity, and its decoded M,D satisfy M=1 and D=1. -/
  theorem spec_4 (date : Slice U8) (h : Valid date) (hm : M date = 1) (hd : D date = 1) :
      ∃ r, day_of_year date = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date) (hm : M date = 1) (hd : D date = 1), ∃ r, day_of_year date = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r, where r = (if Leap(Y) then 366 else 365).
    Preconditions: `date` satisfies the S1 input shape and calendar validity, and its decoded M,D satisfy M=12 and D=31. -/
  theorem spec_5 (date : Slice U8) (h : Valid date) (hm : M date = 12) (hd : D date = 31) :
      ∃ r, day_of_year date = ok r ∧ r.val = (if Leap (Y date) then (366 : ℤ) else 365) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date) (hm : M date = 12) (hd : D date = 31), ∃ r, day_of_year date = ok r ∧ r.val = (if Leap (Y date) then (366 : ℤ) else 365)) := by
    sorry

  /-- The function returns a result r, where r = (if Leap(Y) then 61 else 60).
    Preconditions: `date` satisfies the S1 input shape and calendar validity, and its decoded M,D satisfy M=3 and D=1. -/
  theorem spec_6 (date : Slice U8) (h : Valid date) (hm : M date = 3) (hd : D date = 1) :
      ∃ r, day_of_year date = ok r ∧ r.val = (if Leap (Y date) then (61 : ℤ) else 60) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date) (hm : M date = 3) (hd : D date = 1), ∃ r, day_of_year date = ok r ∧ r.val = (if Leap (Y date) then (61 : ℤ) else 60)) := by
    sorry

  /-- The function returns a result r and r=59.
    Preconditions: `date` satisfies the S1 input shape and calendar validity, and its decoded Y,M,D satisfy Y=1900, M=2, D=28. -/
  theorem spec_7 (date : Slice U8) (h : Valid date)
      (hy : Y date = 1900) (hm : M date = 2) (hd : D date = 28) :
      ∃ r, day_of_year date = ok r ∧ r.val = 59 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date)
        (hy : Y date = 1900) (hm : M date = 2) (hd : D date = 28), ∃ r, day_of_year date = ok r ∧ r.val = 59) := by
    sorry

  /-- The function returns a result r and r=61.
    Preconditions: `date` satisfies the S1 input shape and calendar validity, and its decoded Y,M,D satisfy Y=2000, M=3, D=1. -/
  theorem spec_8 (date : Slice U8) (h : Valid date)
      (hy : Y date = 2000) (hm : M date = 3) (hd : D date = 1) :
      ∃ r, day_of_year date = ok r ∧ r.val = 61 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (date : Slice U8) (h : Valid date)
        (hy : Y date = 2000) (hm : M date = 3) (hd : D date = 1), ∃ r, day_of_year date = ok r ∧ r.val = 61) := by
    sorry

  /-- When the function returns r_a on date_a and r_b on date_b, r_b - r_a = (if Leap(Y(date_b)) then 1 else 0) - (if Leap(Y(date_a)) then 1 else 0).
    Preconditions: `date_a` and `date_b` each satisfy the S1 input shape and calendar validity; M(date_a)=M(date_b), D(date_a)=D(date_b), and M(date_a)>=3, using the Y,M,D,Leap,Dim definitions from spec_1. -/
  theorem spec_9 (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
      (hm : M date_a = M date_b) (hd : D date_a = D date_b) (hm3 : 3 ≤ M date_a)
      (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b) :
      r_b.val - r_a.val
        = (if Leap (Y date_b) then (1 : ℤ) else 0) - (if Leap (Y date_a) then (1 : ℤ) else 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
        (hm : M date_a = M date_b) (hd : D date_a = D date_b) (hm3 : 3 ≤ M date_a)
        (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b), r_b.val - r_a.val
          = (if Leap (Y date_b) then (1 : ℤ) else 0) - (if Leap (Y date_a) then (1 : ℤ) else 0)) := by
    sorry

  /-- When the function returns r_a on date_a and r_b on date_b, r_a = r_b.
    Preconditions: `date_a` and `date_b` each satisfy the S1 input shape and calendar validity; M(date_a)=M(date_b), D(date_a)=D(date_b), and M(date_a)<=2, using the Y,M,D,Leap,Dim definitions from spec_1. -/
  theorem spec_10 (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
      (hm : M date_a = M date_b) (hd : D date_a = D date_b) (hm2 : M date_a ≤ 2)
      (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b) :
      r_a = r_b := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
        (hm : M date_a = M date_b) (hd : D date_a = D date_b) (hm2 : M date_a ≤ 2)
        (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b), r_a = r_b) := by
    sorry

  /-- When the function returns r_a on date_a and r_b on date_b, r_b = r_a + 1.
    Preconditions: `date_a` and `date_b` each satisfy the S1 input shape and calendar validity; Y(date_a)=Y(date_b), M(date_a)=M(date_b), D(date_a)<Dim(Y(date_a),M(date_a)), and D(date_b)=D(date_a)+1. -/
  theorem spec_11 (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
      (hy : Y date_a = Y date_b) (hm : M date_a = M date_b)
      (hdim : D date_a < Dim (Y date_a) (M date_a)) (hd : D date_b = D date_a + 1)
      (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b) :
      r_b.val = r_a.val + 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
        (hy : Y date_a = Y date_b) (hm : M date_a = M date_b)
        (hdim : D date_a < Dim (Y date_a) (M date_a)) (hd : D date_b = D date_a + 1)
        (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b), r_b.val = r_a.val + 1) := by
    sorry

  /-- When the function returns r_a on date_a and r_b on date_b, r_b = 1 and r_a = (if Leap(Y(date_a)) then 366 else 365).
    Preconditions: `date_a` and `date_b` each satisfy the S1 input shape and calendar validity; Y(date_b)=Y(date_a)+1, M(date_a)=12, D(date_a)=31, M(date_b)=1, and D(date_b)=1. -/
  theorem spec_12 (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
      (hy : Y date_b = Y date_a + 1) (hma : M date_a = 12) (hda : D date_a = 31)
      (hmb : M date_b = 1) (hdb : D date_b = 1)
      (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b) :
      r_b.val = 1 ∧ r_a.val = (if Leap (Y date_a) then (366 : ℤ) else 365) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
        (hy : Y date_b = Y date_a + 1) (hma : M date_a = 12) (hda : D date_a = 31)
        (hmb : M date_b = 1) (hdb : D date_b = 1)
        (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b), r_b.val = 1 ∧ r_a.val = (if Leap (Y date_a) then (366 : ℤ) else 365)) := by
    sorry

  /-- When the function returns r_a on date_a and r_b on date_b, r_b - r_a = Dim(Y(date_a),2).
    Preconditions: `date_a` and `date_b` each satisfy the S1 input shape and calendar validity; Y(date_a)=Y(date_b), M(date_a)=2, D(date_a)=1, M(date_b)=3, and D(date_b)=1. -/
  theorem spec_13 (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
      (hy : Y date_a = Y date_b) (hma : M date_a = 2) (hda : D date_a = 1)
      (hmb : M date_b = 3) (hdb : D date_b = 1)
      (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b) :
      r_b.val - r_a.val = Dim (Y date_a) 2 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (date_a date_b : Slice U8) (ha : Valid date_a) (hb : Valid date_b)
        (hy : Y date_a = Y date_b) (hma : M date_a = 2) (hda : D date_a = 1)
        (hmb : M date_b = 3) (hdb : D date_b = 1)
        (r_a r_b : I64) (hra : day_of_year date_a = ok r_a) (hrb : day_of_year date_b = ok r_b), r_b.val - r_a.val = Dim (Y date_a) 2) := by
    sorry

  /-- The function returns a result r and r=9.
    Preconditions: `date` is exactly the byte array [50,48,49,57,45,48,49,45,48,57], the ASCII text '2019-01-09'. -/
  theorem spec_14 (date : Slice U8)
      (hdate : date.val = [50#u8, 48#u8, 49#u8, 57#u8, 45#u8, 48#u8, 49#u8, 45#u8, 48#u8, 57#u8]) :
      ∃ r, day_of_year date = ok r ∧ r.val = 9 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (date : Slice U8)
        (hdate : date.val = [50#u8, 48#u8, 49#u8, 57#u8, 45#u8, 48#u8, 49#u8, 45#u8, 48#u8, 57#u8]), ∃ r, day_of_year date = ok r ∧ r.val = 9) := by
    sorry

  /-- The function returns a result r and r=232.
    Preconditions: `date` is exactly the byte array [50,48,49,56,45,48,56,45,50,48], the ASCII text '2018-08-20'. -/
  theorem spec_15 (date : Slice U8)
      (hdate : date.val = [50#u8, 48#u8, 49#u8, 56#u8, 45#u8, 48#u8, 56#u8, 45#u8, 50#u8, 48#u8]) :
      ∃ r, day_of_year date = ok r ∧ r.val = 232 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (date : Slice U8)
        (hdate : date.val = [50#u8, 48#u8, 49#u8, 56#u8, 45#u8, 48#u8, 56#u8, 45#u8, 50#u8, 48#u8]), ∃ r, day_of_year date = ok r ∧ r.val = 232) := by
    sorry

  end AegisSpec.DayOfYear
