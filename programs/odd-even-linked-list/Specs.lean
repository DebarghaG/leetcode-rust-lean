import Aegis.OddEvenList.Code.Funs

/-!
# Specifications of `Aegis.OddEvenList.odd_even_list`

LeetCode problem `odd-even-linked-list`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.OddEvenList

  open Aegis.OddEvenList (odd_even_list)

  abbrev RList := Aegis.OddEvenList.List

  def contents : RList → List ℤ
    | .Nil => []
    | .Cons x xs => x.val :: contents xs

  def len (head : RList) : Nat := (contents head).length

  def nth (head : RList) (k : Nat) : ℤ := (contents head).getD k 0

  def IsBijectionOn (n : Nat) (f : Nat → Nat) : Prop :=
    (∀ i : Nat, i < n → f i < n) ∧
    (∀ i j : Nat, i < n → j < n → f i = f j → i = j) ∧
    (∀ j : Nat, j < n → ∃ i : Nat, i < n ∧ f i = j)

  /-- Let n = len(head) and p = (n + 1) / 2, using integer division. The function returns a result r such that len(r) = n, and for every integer k: (a) if 0 <= k < p then r[k] = head[2*k]; (b) if p <= k < n and j = k - p then r[k] = head[2*j + 1].
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_1 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ k : Nat, k < (len head + 1) / 2 → nth r k = nth head (2 * k)) ∧
        (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
          nth r k = nth head (2 * (k - (len head + 1) / 2) + 1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ k : Nat, k < (len head + 1) / 2 → nth r k = nth head (2 * k)) ∧
          (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
            nth r k = nth head (2 * (k - (len head + 1) / 2) + 1))) := by
    sorry

  /-- Let n = len(head). The function returns a result r and len(r) = n.
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_2 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList, odd_even_list head = ok r ∧ len r = len head := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList, odd_even_list head = ok r ∧ len r = len head) := by
    sorry

  /-- Let n = len(head) and p = (n + 1) / 2, using integer division. The function returns a result r such that len(r) = n and for every k with 0 <= k < p, r[k] = head[2*k].
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_3 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ k : Nat, k < (len head + 1) / 2 → nth r k = nth head (2 * k)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ k : Nat, k < (len head + 1) / 2 → nth r k = nth head (2 * k))) := by
    sorry

  /-- Let n = len(head) and p = (n + 1) / 2, using integer division. The function returns a result r such that len(r) = n and for every k with p <= k < n, with j = k - p, r[k] = head[2*j + 1].
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_4 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
          nth r k = nth head (2 * (k - (len head + 1) / 2) + 1)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
            nth r k = nth head (2 * (k - (len head + 1) / 2) + 1))) := by
    sorry

  /-- Let n = len(head). The function returns a result r such that len(r) = n and for every integer value v, the number of indices i with 0 <= i < n and r[i] = v equals the number of indices i with 0 <= i < n and head[i] = v.
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_5 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ v : ℤ, (contents r).count v = (contents head).count v) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ v : ℤ, (contents r).count v = (contents head).count v)) := by
    sorry

  /-- Let n = len(head) and p = (n + 1) / 2, using integer division. The function returns a result r such that len(r) = n, for every k with 0 <= k < p there exists an even i with 0 <= i < n such that r[k] = head[i], and for every k with p <= k < n there exists an odd j with 0 <= j < n such that r[k] = head[j].
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_6 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ k : Nat, k < (len head + 1) / 2 →
          ∃ i : Nat, i < len head ∧ Even i ∧ nth r k = nth head i) ∧
        (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
          ∃ j : Nat, j < len head ∧ Odd j ∧ nth r k = nth head j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ k : Nat, k < (len head + 1) / 2 →
            ∃ i : Nat, i < len head ∧ Even i ∧ nth r k = nth head i) ∧
          (∀ k : Nat, (len head + 1) / 2 ≤ k → k < len head →
            ∃ j : Nat, j < len head ∧ Odd j ∧ nth r k = nth head j)) := by
    sorry

  /-- Let n = len(head). The function returns a result r such that len(r) = n and for every k with 0 <= k < n, -1000000 <= r[k] <= 1000000.
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_7 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        (∀ k : Nat, k < len head → -1000000 ≤ nth r k ∧ nth r k ≤ 1000000) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          (∀ k : Nat, k < len head → -1000000 ≤ nth r k ∧ nth r k ≤ 1000000)) := by
    sorry

  /-- For every head satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_8 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList, odd_even_list head = ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList, odd_even_list head = ok r) := by
    sorry

  /-- Let n = len(head) and p = (n + 1) / 2, using integer division. The function returns a result r such that len(r) = n and there exists a bijection f from {i | 0 <= i < n} to {i | 0 <= i < n} such that: (a) for every i with 0 <= i < n, r[f(i)] = head[i]; (b) for every k with 0 <= k < p, f(2*k) = k; (c) for every k with 0 <= 2*k+1 < n, f(2*k+1) = p + k.
    Preconditions: len(head) <= 10000 and for every i with 0 <= i < len(head), -1000000 <= head[i] <= 1000000. -/
  theorem spec_9 (head : RList)
      (h_len : len head ≤ 10000)
      (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000) :
      ∃ r : RList,
        odd_even_list head = ok r ∧
        len r = len head ∧
        ∃ f : Nat → Nat,
          IsBijectionOn (len head) f ∧
          (∀ i : Nat, i < len head → nth r (f i) = nth head i) ∧
          (∀ k : Nat, k < (len head + 1) / 2 → f (2 * k) = k) ∧
          (∀ k : Nat, 2 * k + 1 < len head → f (2 * k + 1) = (len head + 1) / 2 + k) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (head : RList)
        (h_len : len head ≤ 10000)
        (h_bnd : ∀ i : Nat, i < len head → -1000000 ≤ nth head i ∧ nth head i ≤ 1000000), ∃ r : RList,
          odd_even_list head = ok r ∧
          len r = len head ∧
          ∃ f : Nat → Nat,
            IsBijectionOn (len head) f ∧
            (∀ i : Nat, i < len head → nth r (f i) = nth head i) ∧
            (∀ k : Nat, k < (len head + 1) / 2 → f (2 * k) = k) ∧
            (∀ k : Nat, 2 * k + 1 < len head → f (2 * k + 1) = (len head + 1) / 2 + k)) := by
    sorry

  end AegisSpec.OddEvenList
