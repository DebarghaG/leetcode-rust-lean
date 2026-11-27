import Aegis.MaxTastiness.Code.Funs

/-!
# Specifications of `Aegis.MaxTastiness.max_tastiness`

LeetCode problem `maximize-total-tastiness-of-purchased-fruits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxTastiness

  def entry (s : Slice I64) (i : Nat) : Int := (s.val.getD i 0#i64).val

  def half (p : Int) : Int := p.fdiv 2

  def planCost (price : Slice I64) (n : Nat) (S C : Finset (Fin n)) : Int :=
    (∑ i ∈ S \ C, entry price i.val) + ∑ i ∈ C, half (entry price i.val)

  def planTastiness (tastiness : Slice I64) (n : Nat) (S : Finset (Fin n)) : Int :=
    ∑ i ∈ S, entry tastiness i.val

  def Feasible (price : Slice I64) (maxAmount maxCoupons : Int) (n : Nat)
      (S C : Finset (Fin n)) : Prop :=
    C ⊆ S ∧ (C.card : Int) ≤ maxCoupons ∧ planCost price n S C ≤ maxAmount

  def Achievable (price tastiness : Slice I64) (maxAmount maxCoupons : Int) (n : Nat) :
      Set Int :=
    {v | ∃ S C : Finset (Fin n), Feasible price maxAmount maxCoupons n S C ∧
      planTastiness tastiness n S = v}

  def subsetPrice (price : Slice I64) (n : Nat) (S : Finset (Fin n)) : Int :=
    ∑ i ∈ S, entry price i.val

  def subsetHalfPrice (price : Slice I64) (n : Nat) (S : Finset (Fin n)) : Int :=
    ∑ i ∈ S, half (entry price i.val)

  /-- The function returns a result r, and r is the maximum total tastiness over all purchase plans (S, C) such that S ⊆ {0,...,n-1}, C ⊆ S, |C| <= maxCoupons, and the total price sum_{i in S\C} price[i] + sum_{i in C} floor(price[i]/2) is at most maxAmount; the tastiness of such a plan is sum_{i in S} tastiness[i]. Equivalently, r = max { sum_{i in S} tastiness[i] | S ⊆ {0,...,n-1}, C ⊆ S, |C| <= maxCoupons, sum_{i in S\C} price[i] + sum_{i in C} floor(price[i]/2) <= maxAmount }. The empty plan (S = C = ∅) is allowed and gives tastiness 0.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. All values are 64-bit integers; price[i]/2 denotes integer division rounding down (floor). -/
  theorem spec_1 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5) :
      ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
        IsGreatest (Achievable price tastiness maxAmount.val maxCoupons.val n) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5), ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
          IsGreatest (Achievable price tastiness maxAmount.val maxCoupons.val n) r.val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail, panic, or overflow).
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_2 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5) :
      ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5), ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_3 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} tastiness[i].
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_4 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) :
      r.val ≤ ∑ i : Fin n, entry tastiness i.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r), r.val ≤ ∑ i : Fin n, entry tastiness i.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist sets S and C with C ⊆ S ⊆ {0,...,n-1} such that |C| <= maxCoupons, sum_{i in S\C} price[i] + sum_{i in C} floor(price[i]/2) <= maxAmount, and sum_{i in S} tastiness[i] = r.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_5 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) :
      ∃ S C : Finset (Fin n),
        Feasible price maxAmount.val maxCoupons.val n S C ∧ planTastiness tastiness n S = r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r), ∃ S C : Finset (Fin n),
          Feasible price maxAmount.val maxCoupons.val n S C ∧ planTastiness tastiness n S = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of sets S, C with C ⊆ S ⊆ {0,...,n-1}, |C| <= maxCoupons, and sum_{i in S\C} price[i] + sum_{i in C} floor(price[i]/2) <= maxAmount, we have sum_{i in S} tastiness[i] <= r.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_6 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) :
      ∀ S C : Finset (Fin n),
        Feasible price maxAmount.val maxCoupons.val n S C → planTastiness tastiness n S ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r), ∀ S C : Finset (Fin n),
          Feasible price maxAmount.val maxCoupons.val n S C → planTastiness tastiness n S ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S ⊆ {0,...,n-1} such that r = sum_{i in S} tastiness[i].
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_7 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r) :
      ∃ S : Finset (Fin n), r.val = planTastiness tastiness n S := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r : I64) (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r), ∃ S : Finset (Fin n), r.val = planTastiness tastiness n S) := by
    sorry

  /-- Whenever the function returns r on (price, tastiness, maxAmount, maxCoupons) and returns r' on (price', tastiness', maxAmount, maxCoupons), we have r = r'.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. Let π be any permutation of {0,...,n-1}, and define slices price' and tastiness' of length n by price'[i] = price[π(i)] and tastiness'[i] = tastiness[π(i)] for 0 <= i < n. -/
  theorem spec_8 (price tastiness price' tastiness' : Slice I64) (maxAmount maxCoupons : I64)
      (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (π : Equiv.Perm (Fin n))
      (hprice'_len : price'.val.length = n) (htast'_len : tastiness'.val.length = n)
      (hprice_perm : ∀ (i : Nat) (hi : i < n), entry price' i = entry price (π ⟨i, hi⟩).val)
      (htast_perm : ∀ (i : Nat) (hi : i < n), entry tastiness' i = entry tastiness (π ⟨i, hi⟩).val)
      (r r' : I64)
      (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r)
      (hr' : Aegis.MaxTastiness.max_tastiness price' tastiness' maxAmount maxCoupons = ok r') :
      r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (price tastiness price' tastiness' : Slice I64) (maxAmount maxCoupons : I64)
        (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (π : Equiv.Perm (Fin n))
        (hprice'_len : price'.val.length = n) (htast'_len : tastiness'.val.length = n)
        (hprice_perm : ∀ (i : Nat) (hi : i < n), entry price' i = entry price (π ⟨i, hi⟩).val)
        (htast_perm : ∀ (i : Nat) (hi : i < n), entry tastiness' i = entry tastiness (π ⟨i, hi⟩).val)
        (r r' : I64)
        (hr : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r)
        (hr' : Aegis.MaxTastiness.max_tastiness price' tastiness' maxAmount maxCoupons = ok r'), r = r') := by
    sorry

  /-- Whenever the function returns r1 on (price, tastiness, maxAmount1, maxCoupons) and returns r2 on (price, tastiness, maxAmount2, maxCoupons), we have r1 <= r2.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount1 <= maxAmount2 <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_9 (price tastiness : Slice I64) (maxAmount1 maxAmount2 maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount1.val ∧ maxAmount1.val ≤ maxAmount2.val ∧ maxAmount2.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r1 r2 : I64)
      (hr1 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount1 maxCoupons = ok r1)
      (hr2 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount2 maxCoupons = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount1 maxAmount2 maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount1.val ∧ maxAmount1.val ≤ maxAmount2.val ∧ maxAmount2.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r1 r2 : I64)
        (hr1 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount1 maxCoupons = ok r1)
        (hr2 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount2 maxCoupons = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r1 on (price, tastiness, maxAmount, maxCoupons1) and returns r2 on (price, tastiness, maxAmount, maxCoupons2), we have r1 <= r2.
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons1 <= maxCoupons2 <= 5. -/
  theorem spec_10 (price tastiness : Slice I64) (maxAmount maxCoupons1 maxCoupons2 : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons1.val ∧ maxCoupons1.val ≤ maxCoupons2.val ∧ maxCoupons2.val ≤ 5)
      (r1 r2 : I64)
      (hr1 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons1 = ok r1)
      (hr2 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons2 = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons1 maxCoupons2 : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons1.val ∧ maxCoupons1.val ≤ maxCoupons2.val ∧ maxCoupons2.val ≤ 5)
        (r1 r2 : I64)
        (hr1 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons1 = ok r1)
        (hr2 : Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons2 = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- Whenever the function returns r1 on (p1, tastiness, maxAmount, maxCoupons) and returns r2 on (p2, tastiness, maxAmount, maxCoupons), we have r1 >= r2.
    Preconditions: n = len(p1) = len(p2) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= p1[i] <= p2[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_11 (p1 p2 tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hp1_len : p1.val.length = n) (hp2_len : p2.val.length = n)
      (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hp1_bounds : ∀ i, i < n → 0 ≤ entry p1 i ∧ entry p1 i ≤ 1000)
      (hp2_bounds : ∀ i, i < n → 0 ≤ entry p2 i ∧ entry p2 i ≤ 1000)
      (hp_le : ∀ i, i < n → entry p1 i ≤ entry p2 i)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r1 r2 : I64)
      (hr1 : Aegis.MaxTastiness.max_tastiness p1 tastiness maxAmount maxCoupons = ok r1)
      (hr2 : Aegis.MaxTastiness.max_tastiness p2 tastiness maxAmount maxCoupons = ok r2) :
      r1.val ≥ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (p1 p2 tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hp1_len : p1.val.length = n) (hp2_len : p2.val.length = n)
        (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hp1_bounds : ∀ i, i < n → 0 ≤ entry p1 i ∧ entry p1 i ≤ 1000)
        (hp2_bounds : ∀ i, i < n → 0 ≤ entry p2 i ∧ entry p2 i ≤ 1000)
        (hp_le : ∀ i, i < n → entry p1 i ≤ entry p2 i)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r1 r2 : I64)
        (hr1 : Aegis.MaxTastiness.max_tastiness p1 tastiness maxAmount maxCoupons = ok r1)
        (hr2 : Aegis.MaxTastiness.max_tastiness p2 tastiness maxAmount maxCoupons = ok r2), r1.val ≥ r2.val) := by
    sorry

  /-- Whenever the function returns r1 on (price, t1, maxAmount, maxCoupons) and returns r2 on (price, t2, maxAmount, maxCoupons), we have r1 <= r2.
    Preconditions: n = len(price) = len(t1) = len(t2); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= t1[i] <= t2[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5. -/
  theorem spec_12 (price t1 t2 : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n)
      (ht1_len : t1.val.length = n) (ht2_len : t2.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (ht1_bounds : ∀ i, i < n → 0 ≤ entry t1 i ∧ entry t1 i ≤ 1000)
      (ht2_bounds : ∀ i, i < n → 0 ≤ entry t2 i ∧ entry t2 i ≤ 1000)
      (ht_le : ∀ i, i < n → entry t1 i ≤ entry t2 i)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (r1 r2 : I64)
      (hr1 : Aegis.MaxTastiness.max_tastiness price t1 maxAmount maxCoupons = ok r1)
      (hr2 : Aegis.MaxTastiness.max_tastiness price t2 maxAmount maxCoupons = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (price t1 t2 : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n)
        (ht1_len : t1.val.length = n) (ht2_len : t2.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (ht1_bounds : ∀ i, i < n → 0 ≤ entry t1 i ∧ entry t1 i ≤ 1000)
        (ht2_bounds : ∀ i, i < n → 0 ≤ entry t2 i ∧ entry t2 i ≤ 1000)
        (ht_le : ∀ i, i < n → entry t1 i ≤ entry t2 i)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (r1 r2 : I64)
        (hr1 : Aegis.MaxTastiness.max_tastiness price t1 maxAmount maxCoupons = ok r1)
        (hr2 : Aegis.MaxTastiness.max_tastiness price t2 maxAmount maxCoupons = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{n-1} tastiness[i].
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; 0 <= maxCoupons <= 5; and sum_{i=0}^{n-1} price[i] <= maxAmount. -/
  theorem spec_13 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
      (hprice_sum : subsetPrice price n Finset.univ ≤ maxAmount.val) :
      ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
        r.val = ∑ i : Fin n, entry tastiness i.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : 0 ≤ maxCoupons.val ∧ maxCoupons.val ≤ 5)
        (hprice_sum : subsetPrice price n Finset.univ ≤ maxAmount.val), ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
          r.val = ∑ i : Fin n, entry tastiness i.val) := by
    sorry

  /-- The function returns a result r, and r equals the maximum over all subsets S ⊆ {0,...,n-1} with sum_{i in S} price[i] <= maxAmount of sum_{i in S} tastiness[i].
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; maxCoupons = 0. -/
  theorem spec_14 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : maxCoupons.val = 0) :
      ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
        IsGreatest
          {v | ∃ S : Finset (Fin n),
            subsetPrice price n S ≤ maxAmount.val ∧ planTastiness tastiness n S = v} r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : maxCoupons.val = 0), ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
          IsGreatest
            {v | ∃ S : Finset (Fin n),
              subsetPrice price n S ≤ maxAmount.val ∧ planTastiness tastiness n S = v} r.val) := by
    sorry

  /-- The function returns a result r, and r equals the maximum over all subsets S ⊆ {0,...,n-1} with sum_{i in S} floor(price[i]/2) <= maxAmount of sum_{i in S} tastiness[i].
    Preconditions: n = len(price) = len(tastiness); 1 <= n <= 100; for every i with 0 <= i < n, 0 <= price[i] <= 1000 and 0 <= tastiness[i] <= 1000; 0 <= maxAmount <= 1000; maxCoupons >= n. -/
  theorem spec_15 (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
      (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
      (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
      (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
      (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
      (hcoupons : n ≤ maxCoupons.val) :
      ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
        IsGreatest
          {v | ∃ S : Finset (Fin n),
            subsetHalfPrice price n S ≤ maxAmount.val ∧ planTastiness tastiness n S = v} r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (price tastiness : Slice I64) (maxAmount maxCoupons : I64) (n : Nat)
        (hprice_len : price.val.length = n) (htast_len : tastiness.val.length = n)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 100)
        (hprice_bounds : ∀ i, i < n → 0 ≤ entry price i ∧ entry price i ≤ 1000)
        (htast_bounds : ∀ i, i < n → 0 ≤ entry tastiness i ∧ entry tastiness i ≤ 1000)
        (hamount : 0 ≤ maxAmount.val ∧ maxAmount.val ≤ 1000)
        (hcoupons : n ≤ maxCoupons.val), ∃ r : I64, Aegis.MaxTastiness.max_tastiness price tastiness maxAmount maxCoupons = ok r ∧
          IsGreatest
            {v | ∃ S : Finset (Fin n),
              subsetHalfPrice price n S ≤ maxAmount.val ∧ planTastiness tastiness n S = v} r.val) := by
    sorry

  end AegisSpec.MaxTastiness
