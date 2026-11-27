import Aegis.LemonadeChange.Code.Funs

/-!
# Specifications of `Aegis.LemonadeChange.lemonade_change`

LeetCode problem `lemonade-change`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LemonadeChange

def vals (bills : Slice Std.I64) : List ℤ := bills.val.map fun b => b.val

def IsBill (v : ℤ) : Prop := v = 5 ∨ v = 10 ∨ v = 20

def AllBills (bills : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i < bills.val.length), IsBill ((bills.val[i]'hi).val)

def countOf (v : ℤ) (bills : Slice Std.I64) (k : ℕ) : ℕ :=
  ((bills.val.take k).filter fun b => b.val = v).length

def count5 (bills : Slice Std.I64) (k : ℕ) : ℕ := countOf 5 bills k

def count10 (bills : Slice Std.I64) (k : ℕ) : ℕ := countOf 10 bills k

def count20 (bills : Slice Std.I64) (k : ℕ) : ℕ := countOf 20 bills k

def StepOk (b : ℤ) (f5 f10 : ℕ → ℕ) (k : ℕ) : Prop :=
  (b = 5 → f5 (k + 1) = f5 k + 1 ∧ f10 (k + 1) = f10 k) ∧
  (b = 10 → 1 ≤ f5 k ∧ f5 (k + 1) = f5 k - 1 ∧ f10 (k + 1) = f10 k + 1) ∧
  (b = 20 →
    (1 ≤ f5 k ∧ 1 ≤ f10 k ∧ f5 (k + 1) = f5 k - 1 ∧ f10 (k + 1) = f10 k - 1) ∨
    (3 ≤ f5 k ∧ f5 (k + 1) = f5 k - 3 ∧ f10 (k + 1) = f10 k))

def ValidStrategy (l : List ℤ) (f5 f10 : ℕ → ℕ) : Prop :=
  f5 0 = 0 ∧ f10 0 = 0 ∧
    ∀ (k : ℕ), k < l.length → ∀ b : ℤ, l[k]? = some b → StepOk b f5 f10 k

def countC1 (l : List ℤ) (f5 f10 : ℕ → ℕ) : ℕ :=
  ((List.range l.length).filter (fun k =>
    l[k]? = some (20 : ℤ) ∧ 1 ≤ f5 k ∧ 1 ≤ f10 k ∧
      f5 (k + 1) = f5 k - 1 ∧ f10 (k + 1) = f10 k - 1)).length

theorem listN_toList_length {α : Type} {n : ℕ} (l : Aeneas.Data.ListN.ListN α n) :
    l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [Aeneas.Data.ListN.ListN.toList, ih]

theorem listN_cast_toList {α : Type} {n m : ℕ} (h : n = m)
    (l : Aeneas.Data.ListN.ListN α n) : (h ▸ l).toList = l.toList := by
  cases h
  rfl

def prefixSlice (bills : Slice Std.I64) (k : ℕ) (hk : k ≤ bills.val.length) : Slice Std.I64 :=
  { leng := k
    list := (show (bills.val.take k).length = k from by
              rw [List.length_take]; exact Nat.min_eq_left hk) ▸
            Aeneas.Data.ListN.ListN.fromList (bills.val.take k)
    bound := by
      have h1 : bills.val.length = bills.leng := listN_toList_length bills.list
      have h2 : bills.leng ≤ Std.Usize.max := bills.bound
      omega }

theorem prefixSlice_val (bills : Slice Std.I64) (k : ℕ) (hk : k ≤ bills.val.length) :
    (prefixSlice bills k hk).val = bills.val.take k :=
  (listN_cast_toList _ _).trans Aeneas.Data.ListN.ListN.from_to_inverse

theorem prefixSlice_length (bills : Slice Std.I64) (k : ℕ) (hk : k ≤ bills.val.length) :
    (prefixSlice bills k hk).val.length = k := by
  rw [prefixSlice_val, List.length_take]
  exact Nat.min_eq_left hk

theorem vals_prefixSlice (bills : Slice Std.I64) (k : ℕ) (hk : k ≤ bills.val.length) :
    vals (prefixSlice bills k hk) = (vals bills).take k := by
  simp [vals, prefixSlice_val, List.map_take]

/-- Let n = len(bills). Call a sequence (f5(k), f10(k)) of pairs of nonnegative integers for k = 0,...,n a valid change strategy if f5(0)=f10(0)=0 and for every k with 0 <= k < n: (a) if bills[k]=5, then f5(k+1)=f5(k)+1 and f10(k+1)=f10(k); (b) if bills[k]=10, then f5(k)>=1, f5(k+1)=f5(k)-1, and f10(k+1)=f10(k)+1; (c) if bills[k]=20, then either (c1) f5(k)>=1 and f10(k)>=1 and f5(k+1)=f5(k)-1 and f10(k+1)=f10(k)-1, or (c2) f5(k)>=3 and f5(k+1)=f5(k)-3 and f10(k+1)=f10(k). The function returns a result r (it does not fail) and r=true if and only if such a valid change strategy for bills exists; otherwise r=false.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_1 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∃ f5 f10 : ℕ → ℕ, ValidStrategy (vals bills) f5 f10) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∃ f5 f10 : ℕ → ℕ, ValidStrategy (vals bills) f5 f10)) := by
  sorry

/-- For every input satisfying the preconditions, lemonade_change returns a result r (either true or false) and does not fail: no arithmetic overflow, no out-of-bounds access, and no panic occurs.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_2 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r) := by
  sorry

/-- Whenever the function returns a result r and r=true, then for every k with 0 <= k <= len(bills), writing a = count5(bills,k), b = count10(bills,k), c = count20(bills,k), where count5(bills,k) is the number of indices i with 0 <= i < k and bills[i]=5 and similarly for 10 and 20, we have a >= b + 3*c - 2*min(b,c).
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_3 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = true →
      ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥
          count10 bills k + 3 * count20 bills k -
            2 * Nat.min (count10 bills k) (count20 bills k) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = true →
      ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥
          count10 bills k + 3 * count20 bills k -
            2 * Nat.min (count10 bills k) (count20 bills k)) := by
  sorry

/-- If for every k with 0 <= k <= len(bills), writing a = count5(bills,k), b = count10(bills,k), c = count20(bills,k), we have a >= b + 3*c, then the function returns true.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_4 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (h : ∀ k : ℕ, k ≤ bills.val.length →
      count5 bills k ≥ count10 bills k + 3 * count20 bills k) :
    Aegis.LemonadeChange.lemonade_change bills = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (h : ∀ k : ℕ, k ≤ bills.val.length →
      count5 bills k ≥ count10 bills k + 3 * count20 bills k), Aegis.LemonadeChange.lemonade_change bills = ok true) := by
  sorry

/-- If bills[i] != 20 for every i with 0 <= i < len(bills), then the function returns a result r and r=true if and only if for every k with 0 <= k <= len(bills), count5(bills,k) >= count10(bills,k).
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_5 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hno20 : ∀ (i : ℕ) (hi : i < bills.val.length), (bills.val[i]'hi).val ≠ 20) :
    ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥ count10 bills k) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hno20 : ∀ (i : ℕ) (hi : i < bills.val.length), (bills.val[i]'hi).val ≠ 20), ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥ count10 bills k)) := by
  sorry

/-- If bills[i] != 10 for every i with 0 <= i < len(bills), then the function returns a result r and r=true if and only if for every k with 0 <= k <= len(bills), count5(bills,k) >= 3*count20(bills,k).
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_6 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hno10 : ∀ (i : ℕ) (hi : i < bills.val.length), (bills.val[i]'hi).val ≠ 10) :
    ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥ 3 * count20 bills k) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hno10 : ∀ (i : ℕ) (hi : i < bills.val.length), (bills.val[i]'hi).val ≠ 10), ∃ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r ∧
      (r = true ↔ ∀ k : ℕ, k ≤ bills.val.length →
        count5 bills k ≥ 3 * count20 bills k)) := by
  sorry

/-- If bills' is obtained from bills by appending one additional bill equal to 5 (so len(bills') = len(bills)+1, bills'[i]=bills[i] for 0 <= i < len(bills), and bills'[len(bills)]=5), then lemonade_change returns the same Boolean value on bills and on bills'.
  Preconditions: bills and bills' are Slice Std.I64 values, each satisfying 1 <= len <= 100000 and all entries in {5,10,20}. -/
theorem spec_7 (bills bills' : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hpos' : 1 ≤ bills'.val.length) (hlen' : bills'.val.length ≤ 100000)
    (hbills' : AllBills bills') (happend : bills'.val = bills.val ++ [5#i64]) :
    ∃ r : Bool,
      Aegis.LemonadeChange.lemonade_change bills = ok r ∧
        Aegis.LemonadeChange.lemonade_change bills' = ok r := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bills bills' : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hpos' : 1 ≤ bills'.val.length) (hlen' : bills'.val.length ≤ 100000)
    (hbills' : AllBills bills') (happend : bills'.val = bills.val ++ [5#i64]), ∃ r : Bool,
      Aegis.LemonadeChange.lemonade_change bills = ok r ∧
        Aegis.LemonadeChange.lemonade_change bills' = ok r) := by
  sorry

/-- If bills' extends bills (len(bills') >= len(bills) and bills'[i]=bills[i] for every i with 0 <= i < len(bills)) and lemonade_change(bills) returns false, then lemonade_change(bills') returns false.
  Preconditions: bills and bills' are Slice Std.I64 values satisfying 1 <= len <= 100000 and all entries in {5,10,20}. -/
theorem spec_8 (bills bills' : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hpos' : 1 ≤ bills'.val.length) (hlen' : bills'.val.length ≤ 100000)
    (hbills' : AllBills bills')
    (hext : ∃ tl : List Std.I64, bills'.val = bills.val ++ tl) :
    Aegis.LemonadeChange.lemonade_change bills = ok false →
      Aegis.LemonadeChange.lemonade_change bills' = ok false := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bills bills' : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills)
    (hpos' : 1 ≤ bills'.val.length) (hlen' : bills'.val.length ≤ 100000)
    (hbills' : AllBills bills')
    (hext : ∃ tl : List Std.I64, bills'.val = bills.val ++ tl), Aegis.LemonadeChange.lemonade_change bills = ok false →
      Aegis.LemonadeChange.lemonade_change bills' = ok false) := by
  sorry

/-- If lemonade_change(bills) returns true, then for every k with 1 <= k <= len(bills), lemonade_change applied to the prefix slice bills[0..k) (the slice of length k containing bills[0],...,bills[k-1]) returns true.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_9 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    Aegis.LemonadeChange.lemonade_change bills = ok true →
      ∀ (k : ℕ) (hk : k ≤ bills.val.length), 1 ≤ k →
        Aegis.LemonadeChange.lemonade_change (prefixSlice bills k hk) = ok true := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), Aegis.LemonadeChange.lemonade_change bills = ok true →
      ∀ (k : ℕ) (hk : k ≤ bills.val.length), 1 ≤ k →
        Aegis.LemonadeChange.lemonade_change (prefixSlice bills k hk) = ok true) := by
  sorry

/-- Whenever lemonade_change(bills) returns true, there exists a valid change strategy for bills (as defined in spec_1). For any such strategy, let f5 and f10 be the nonnegative numbers of $5 and $10 bills held after all customers are served, and let t be the number of customers who pay with a $20 bill and receive one $10 bill plus one $5 bill as change. Then t is an integer with 0 <= t <= min(count10(bills,n), count20(bills,n)), f10 = count10(bills,n) - t, and f5 = count5(bills,n) - count10(bills,n) - 3*count20(bills,n) + 2*t, where n=len(bills) and count5, count10, count20 denote total counts in bills.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_10 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = true →
      (∃ f5 f10 : ℕ → ℕ, ValidStrategy (vals bills) f5 f10) ∧
        (∀ (f5 f10 : ℕ → ℕ), ValidStrategy (vals bills) f5 f10 →
          countC1 (vals bills) f5 f10 ≤
              Nat.min (count10 bills bills.val.length) (count20 bills bills.val.length) ∧
            (f10 bills.val.length : ℤ) =
              (count10 bills bills.val.length : ℤ) - (countC1 (vals bills) f5 f10 : ℤ) ∧
            (f5 bills.val.length : ℤ) =
              (count5 bills bills.val.length : ℤ) -
                  (count10 bills bills.val.length : ℤ) -
                  3 * (count20 bills bills.val.length : ℤ) +
                2 * (countC1 (vals bills) f5 f10 : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = true →
      (∃ f5 f10 : ℕ → ℕ, ValidStrategy (vals bills) f5 f10) ∧
        (∀ (f5 f10 : ℕ → ℕ), ValidStrategy (vals bills) f5 f10 →
          countC1 (vals bills) f5 f10 ≤
              Nat.min (count10 bills bills.val.length) (count20 bills bills.val.length) ∧
            (f10 bills.val.length : ℤ) =
              (count10 bills bills.val.length : ℤ) - (countC1 (vals bills) f5 f10 : ℤ) ∧
            (f5 bills.val.length : ℤ) =
              (count5 bills bills.val.length : ℤ) -
                  (count10 bills bills.val.length : ℤ) -
                  3 * (count20 bills bills.val.length : ℤ) +
                2 * (countC1 (vals bills) f5 f10 : ℤ))) := by
  sorry

/-- Whenever lemonade_change(bills) returns false, there exists an integer k with 1 <= k <= len(bills) such that the prefix bills[0..k) is not servable (there is no valid change strategy for that prefix, in the sense of spec_1), while every prefix bills[0..j) with 1 <= j < k is servable.
  Preconditions: bills is a Slice Std.I64 with 1 <= len(bills) <= 100000, and for every i with 0 <= i < len(bills), bills[i] is either 5, 10, or 20. -/
theorem spec_11 (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills) :
    ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = false →
      ∃ (k : ℕ) (hk : k ≤ bills.val.length),
        1 ≤ k ∧
          (¬ ∃ f5 f10 : ℕ → ℕ, ValidStrategy ((vals bills).take k) f5 f10) ∧
          (∀ (j : ℕ), 1 ≤ j → j < k →
            ∃ f5 f10 : ℕ → ℕ, ValidStrategy ((vals bills).take j) f5 f10) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (bills : Slice Std.I64) (hpos : 1 ≤ bills.val.length)
    (hlen : bills.val.length ≤ 100000) (hbills : AllBills bills), ∀ r : Bool, Aegis.LemonadeChange.lemonade_change bills = ok r → r = false →
      ∃ (k : ℕ) (hk : k ≤ bills.val.length),
        1 ≤ k ∧
          (¬ ∃ f5 f10 : ℕ → ℕ, ValidStrategy ((vals bills).take k) f5 f10) ∧
          (∀ (j : ℕ), 1 ≤ j → j < k →
            ∃ f5 f10 : ℕ → ℕ, ValidStrategy ((vals bills).take j) f5 f10)) := by
  sorry

end AegisSpec.LemonadeChange
