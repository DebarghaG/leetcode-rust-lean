import Aegis.MinEnd.Code.Funs

/-!
# Specifications of `Aegis.MinEnd.min_end`

LeetCode problem `minimum-array-end`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinEnd

open Aegis.MinEnd

def bAnd (a b : ℤ) : ℤ := (Nat.land a.toNat b.toNat : ℤ)

def inS (x z : ℤ) : Prop := 0 < z ∧ bAnd z x = x

instance instDecidableInS (x : ℤ) : DecidablePred (inS x) := fun z => by
  unfold inS bAnd
  infer_instance

def SBelow (x : ℤ) (b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (fun z => inS x (z : ℤ))

def countBelow (x : ℤ) (b : ℕ) : ℕ := (SBelow x b).card

def countUpto (x : ℤ) (b : ℕ) : ℕ := (SBelow x (b + 1)).card

def listAnd : List ℤ → ℤ
  | [] => 0
  | z :: zs => zs.foldl bAnd z

def bitAt (z : ℤ) (i : ℕ) : Bool := z.toNat.testBit i

def zeroBitsBelow (x : ℤ) (i : ℕ) : ℕ :=
  ((Finset.range i).filter (fun k => bitAt x k = false)).card

/-- The function returns a result r. Let S be the set of positive integers z such that (z & x) == x, where & denotes bitwise AND on 64-bit integers. Then r is the n-th smallest element of S. Equivalently, (r & x) == x and the number of positive integers z with z < r and (z & x) == x is exactly n - 1.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_1 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∃ r : Std.I64,
      min_end n x = ok r ∧ inS x.val r.val ∧ countBelow x.val r.val.toNat = n.val.toNat - 1 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∃ r : Std.I64,
      min_end n x = ok r ∧ inS x.val r.val ∧ countBelow x.val r.val.toNat = n.val.toNat - 1) := by
  sorry

/-- When the function returns r, there exists an array a of length n of positive integers such that a is strictly increasing, the bitwise AND of all a[i] for 0 <= i < n equals x, and a[n-1] = r.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_2 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ z ∈ a, 0 < z) ∧
              a.Pairwise (· < ·) ∧ listAnd a = x.val ∧ a.getLast? = some r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ z ∈ a, 0 < z) ∧
              a.Pairwise (· < ·) ∧ listAnd a = x.val ∧ a.getLast? = some r.val) := by
  sorry

/-- When the function returns r, for every array a of length n of positive integers that is strictly increasing and whose bitwise AND equals x, we have a[n-1] >= r.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_3 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ a : List ℤ,
          a.length = n.val.toNat →
            (∀ z ∈ a, 0 < z) →
              a.Pairwise (· < ·) →
                listAnd a = x.val → ∀ last : ℤ, a.getLast? = some last → r.val ≤ last := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ a : List ℤ,
          a.length = n.val.toNat →
            (∀ z ∈ a, 0 < z) →
              a.Pairwise (· < ·) →
                listAnd a = x.val → ∀ last : ℤ, a.getLast? = some last → r.val ≤ last) := by
  sorry

/-- When the function returns r, we have r >= x.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_4 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64, min_end n x = ok r → x.val ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64, min_end n x = ok r → x.val ≤ r.val) := by
  sorry

/-- When the function returns r and n > 1, we have r > x.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8, 1 <= x <= 10^8, and n > 1. -/
theorem spec_5 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) (hn : 1 < n.val) :
    ∀ r : Std.I64, min_end n x = ok r → x.val < r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) (hn : 1 < n.val), ∀ r : Std.I64, min_end n x = ok r → x.val < r.val) := by
  sorry

/-- When the function returns r, (r & x) == x.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_6 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64, min_end n x = ok r → bAnd r.val x.val = x.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64, min_end n x = ok r → bAnd r.val x.val = x.val) := by
  sorry

/-- When the function returns r, the number of positive integers z with z <= r and (z & x) == x is exactly n.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_7 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64, min_end n x = ok r → countUpto x.val r.val.toNat = n.val.toNat := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64, min_end n x = ok r → countUpto x.val r.val.toNat = n.val.toNat) := by
  sorry

/-- When the function returns r, for any positive integer r', if (r' & x) == x and the number of positive integers z with z <= r' and (z & x) == x is exactly n, then r' = r.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_8 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ r' : ℕ,
          0 < r' →
            bAnd (r' : ℤ) x.val = x.val → countUpto x.val r' = n.val.toNat → (r' : ℤ) = r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ r' : ℕ,
          0 < r' →
            bAnd (r' : ℤ) x.val = x.val → countUpto x.val r' = n.val.toNat → (r' : ℤ) = r.val) := by
  sorry

/-- Let r1 be the result of min_end(n1, x) and r2 be the result of min_end(n2, x). Then r1 < r2.
  Preconditions: x is a 64-bit integer with 1 <= x <= 10^8, and n1, n2 are 64-bit integers with 1 <= n1 < n2 <= 10^8. -/
theorem spec_9 (n1 n2 x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val < n2.val) (hn2 : n2.val ≤ 10 ^ 8) :
    ∀ r1 r2 : Std.I64,
      min_end n1 x = ok r1 → min_end n2 x = ok r2 → r1.val < r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n1 n2 x : Std.I64) (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val < n2.val) (hn2 : n2.val ≤ 10 ^ 8), ∀ r1 r2 : Std.I64,
      min_end n1 x = ok r1 → min_end n2 x = ok r2 → r1.val < r2.val) := by
  sorry

/-- When the function returns r, for every bit position i with 0 <= i < 64: if the i-th bit of x is 1 then the i-th bit of r is 1; if the i-th bit of x is 0 and j is the number of zero bits of x below i, then the i-th bit of r equals the j-th bit of (n - 1).
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_10 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ i : ℕ,
          i < 64 →
            (bitAt x.val i = true → bitAt r.val i = true) ∧
              (bitAt x.val i = false →
                bitAt r.val i = bitAt (n.val - 1) (zeroBitsBelow x.val i)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∀ i : ℕ,
          i < 64 →
            (bitAt x.val i = true → bitAt r.val i = true) ∧
              (bitAt x.val i = false →
                bitAt r.val i = bitAt (n.val - 1) (zeroBitsBelow x.val i))) := by
  sorry

/-- When the function returns r, there exists an array a of length n of positive integers such that a[0] = x, a is strictly increasing, the bitwise AND of all a[i] equals x, and a[n-1] = r.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_11 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ z ∈ a, 0 < z) ∧
              a.Pairwise (· < ·) ∧
                a.head? = some x.val ∧ listAnd a = x.val ∧ a.getLast? = some r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ z ∈ a, 0 < z) ∧
              a.Pairwise (· < ·) ∧
                a.head? = some x.val ∧ listAnd a = x.val ∧ a.getLast? = some r.val) := by
  sorry

/-- When the function returns r, there exists an array a of length n of positive integers such that for every i with 0 <= i < n, a[i] is the (i+1)-th smallest element of S = {z > 0 : (z & x) == x}, and a[n-1] = r.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_12 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ i : Fin a.length, inS x.val (a.get i) ∧ countBelow x.val (a.get i).toNat = i.val) ∧
              a.getLast? = some r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∀ r : Std.I64,
      min_end n x = ok r →
        ∃ a : List ℤ,
          a.length = n.val.toNat ∧
            (∀ i : Fin a.length, inS x.val (a.get i) ∧ countBelow x.val (a.get i).toNat = i.val) ∧
              a.getLast? = some r.val) := by
  sorry

/-- The function returns a result r for every n, x satisfying the preconditions.
  Preconditions: n and x are 64-bit integers with 1 <= n <= 10^8 and 1 <= x <= 10^8. -/
theorem spec_13 (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8) :
    ∃ r : Std.I64, min_end n x = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n x : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10 ^ 8)
    (hx1 : 1 ≤ x.val) (hx2 : x.val ≤ 10 ^ 8), ∃ r : Std.I64, min_end n x = ok r) := by
  sorry

end AegisSpec.MinEnd
