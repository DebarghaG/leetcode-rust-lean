import Aegis.CountOrders.Code.Funs

/-!
# Specifications of `Aegis.CountOrders.count_orders`

LeetCode problem `count-all-valid-pickup-and-delivery-options`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountOrders

  def modulus : Nat := 1000000007

  def modulusZ : Int := (modulus : Int)

  def modM (z : Int) : Int := z % modulusZ

  abbrev Symbol (n : Nat) : Type := Fin n × Bool

  abbrev symP {n : Nat} (i : Fin n) : Symbol n := (i, false)

  abbrev symD {n : Nat} (i : Fin n) : Symbol n := (i, true)

  abbrev Arrangement (n : Nat) : Type := Fin (2 * n) ≃ Symbol n

  noncomputable instance arrangementFintype (n : Nat) : Fintype (Arrangement n) :=
    Fintype.ofInjective (fun e : Arrangement n => (e : Fin (2 * n) → Symbol n))
      (fun _ _ h => Equiv.ext (fun x => congrFun h x))

  abbrev pBeforeD {n : Nat} (e : Arrangement n) (i : Fin n) : Prop :=
    e.symm (symP i) < e.symm (symD i)

  noncomputable def goodArrangements (n : Nat) : Finset (Arrangement n) :=
    Finset.univ.filter (fun e => ∀ i : Fin n, pBeforeD e i)

  noncomputable def countSequences (n : Nat) : Nat := (goodArrangements n).card

  def prodScales (n : Nat) : Nat := (Finset.Icc 1 n).prod (fun i => i * (2 * i - 1))

  def oddProd (n : Nat) : Nat := (Finset.Icc 1 n).prod (fun i => 2 * i - 1)

  def factDivPow (n : Nat) : Nat := Nat.factorial (2 * n) / 2 ^ n

  /-- Let M = 10^9 + 7. Let C(n) be the number of ordered sequences of length 2n containing each of the 2n distinct symbols P_1,...,P_n,D_1,...,D_n exactly once, such that for every i with 1 <= i <= n, P_i appears before D_i. The function returns a result r, and the integer value of r is C(n) mod M, the unique integer in [0, M-1] congruent to C(n) modulo M.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) :
      ∃ r : Std.I64,
        Aegis.CountOrders.count_orders n = ok r ∧
        r.val = modM (↑(countSequences n.val.toNat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500), ∃ r : Std.I64,
          Aegis.CountOrders.count_orders n = ok r ∧
          r.val = modM (↑(countSequences n.val.toNat) : Int)) := by
    sorry

  /-- For every n with 1 <= n <= 500, count_orders(n) returns a result r; in particular, it does not fail, panic, or overflow.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) :
      ∃ r : Std.I64, Aegis.CountOrders.count_orders n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500), ∃ r : Std.I64, Aegis.CountOrders.count_orders n = ok r) := by
    sorry

  /-- For every n with 1 <= n <= 500, if count_orders(n) returns r, then 0 <= r <= 10^9 + 6.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
      (hr : Aegis.CountOrders.count_orders n = ok r) :
      0 ≤ r.val ∧ r.val ≤ modulusZ - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
        (hr : Aegis.CountOrders.count_orders n = ok r), 0 ≤ r.val ∧ r.val ≤ modulusZ - 1) := by
    sorry

  /-- For every n with 1 <= n <= 500, if count_orders(n) returns r, then r = (product from i=1 to n of i*(2*i-1)) mod M, where M = 10^9 + 7, the product is taken in ordinary integers, and x mod M denotes the least nonnegative residue.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
      (hr : Aegis.CountOrders.count_orders n = ok r) :
      r.val = modM (↑(prodScales n.val.toNat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
        (hr : Aegis.CountOrders.count_orders n = ok r), r.val = modM (↑(prodScales n.val.toNat) : Int)) := by
    sorry

  /-- For every n with 1 <= n <= 500, if count_orders(n) returns r, then r = (((2*n)! / (2^n)) mod M), where M = 10^9 + 7, ! denotes integer factorial, and the division is exact in the integers.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
      (hr : Aegis.CountOrders.count_orders n = ok r) :
      r.val = modM (↑(factDivPow n.val.toNat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
        (hr : Aegis.CountOrders.count_orders n = ok r), r.val = modM (↑(factDivPow n.val.toNat) : Int)) := by
    sorry

  /-- For every n with 1 <= n <= 500, if count_orders(n) returns r, then r = (n! * (1*3*5*...*(2*n-1))) mod M, where M = 10^9 + 7 and the odd product has exactly n factors.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n <= 500. -/
  theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
      (hr : Aegis.CountOrders.count_orders n = ok r) :
      r.val = modM (↑(Nat.factorial n.val.toNat * oddProd n.val.toNat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 500) (r : Std.I64)
        (hr : Aegis.CountOrders.count_orders n = ok r), r.val = modM (↑(Nat.factorial n.val.toNat * oddProd n.val.toNat) : Int)) := by
    sorry

  /-- Let r_n be the integer result of count_orders(n) and r_{n+1} the integer result of count_orders(n+1), both of which are returned. Then r_{n+1} = (r_n * (n+1) * (2*n+1)) mod M, where M = 10^9 + 7.
    Preconditions: The I64 argument n, interpreted as an ordinary integer, satisfies 1 <= n < 500. -/
  theorem spec_7 (n m : Std.I64) (hn : 1 ≤ n.val ∧ n.val < 500) (hm : m.val = n.val + 1)
      (rn rm : Std.I64) (hrn : Aegis.CountOrders.count_orders n = ok rn)
      (hrm : Aegis.CountOrders.count_orders m = ok rm) :
      rm.val = modM (rn.val * (n.val + 1) * (2 * n.val + 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m : Std.I64) (hn : 1 ≤ n.val ∧ n.val < 500) (hm : m.val = n.val + 1)
        (rn rm : Std.I64) (hrn : Aegis.CountOrders.count_orders n = ok rn)
        (hrm : Aegis.CountOrders.count_orders m = ok rm), rm.val = modM (rn.val * (n.val + 1) * (2 * n.val + 1))) := by
    sorry

  end AegisSpec.CountOrders
