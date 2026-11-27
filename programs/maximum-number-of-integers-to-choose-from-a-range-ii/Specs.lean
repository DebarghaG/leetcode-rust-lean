import Aegis.MaxCount.Code.Funs

/-!
# Specifications of `Aegis.MaxCount.max_count`

LeetCode problem `maximum-number-of-integers-to-choose-from-a-range-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxCount

def occursIn (l : List I64) (v : ℤ) : Prop := ∃ x ∈ l, x.val = v

def forbidden (banned : Slice I64) : Finset ℤ := (banned.val.map (fun x => x.val)).toFinset

def allowed (banned : Slice I64) (n : ℤ) : Finset ℤ :=
  (((List.range (n.toNat + 1)).map (fun k : ℕ => (k : ℤ))).toFinset).filter
    (fun x => 1 ≤ x ∧ x ∉ forbidden banned)

def totalAllowed (banned : Slice I64) (n : ℤ) : ℤ := (allowed banned n).sum (fun x => x)

noncomputable def increasingEnum (A : Finset ℤ) : List ℤ := A.toList.insertionSort (· ≤ ·)

def prefixSum (l : List ℤ) (k : ℕ) : ℤ := (l.take k).sum

noncomputable def S (A : Finset ℤ) (k : ℤ) : ℤ := prefixSum (increasingEnum A) k.toNat

/-- Let B = { banned[i] | 0 <= i < len(banned) } (a set, so duplicates are ignored). Let A = { x | 1 <= x <= n and x not in B }. Let m = |A| and let a_1 < a_2 < ... < a_m be the elements of A in increasing order. For k = 0, ..., m define S(k) = a_1 + ... + a_k, with S(0) = 0. Whenever the function returns a result r, r = max { k | 0 <= k <= m and S(k) <= maxSum }.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic; the size bounds keep all sums mentioned below within 64-bit range. r denotes the returned mathematical integer. -/
theorem spec_1 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    IsGreatest {k : ℤ | 0 ≤ k ∧ k ≤ ((allowed banned n.val).card : ℤ) ∧
      S (allowed banned n.val) k ≤ maxSum.val} r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), IsGreatest {k : ℤ | 0 ≤ k ∧ k ≤ ((allowed banned n.val).card : ℤ) ∧
      S (allowed banned n.val) k ≤ maxSum.val} r.val) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) } and let A = { x | 1 <= x <= n and x not in B }. Let m = |A|. Whenever the function returns a result r, 0 <= r <= m.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_2 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((allowed banned n.val).card : ℤ) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), 0 ≤ r.val ∧ r.val ≤ ((allowed banned n.val).card : ℤ)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not panic, go out of bounds, or overflow.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_3 (banned : Slice I64) (n maxSum : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val) :
    ∃ r : I64, Aegis.MaxCount.max_count banned n maxSum = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val), ∃ r : I64, Aegis.MaxCount.max_count banned n maxSum = ok r) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) }. Whenever the function returns a result r, there exist r distinct integers x_1, ..., x_r such that for every j with 1 <= j <= r, 1 <= x_j <= n and x_j not in B, and x_1 + ... + x_r <= maxSum. For r = 0 the empty selection is allowed and has sum 0.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_4 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    ∃ Y : Finset ℤ, Y ⊆ allowed banned n.val ∧ (Y.card : ℤ) = r.val ∧
      Y.sum (fun x => x) ≤ maxSum.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), ∃ Y : Finset ℤ, Y ⊆ allowed banned n.val ∧ (Y.card : ℤ) = r.val ∧
      Y.sum (fun x => x) ≤ maxSum.val) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) } and A = { x | 1 <= x <= n and x not in B }. Let m = |A|. Whenever the function returns a result r, for every integer k with r < k <= m and every choice of k distinct integers y_1, ..., y_k from A, we have y_1 + ... + y_k > maxSum. Equivalently, no selection of more than r allowed integers has sum at most maxSum.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_5 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    ∀ Y : Finset ℤ, Y ⊆ allowed banned n.val → r.val < (Y.card : ℤ) →
      maxSum.val < Y.sum (fun x => x) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), ∀ Y : Finset ℤ, Y ⊆ allowed banned n.val → r.val < (Y.card : ℤ) →
      maxSum.val < Y.sum (fun x => x)) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) }. Whenever the function returns a result r, r = 0 if and only if there is no integer x such that 1 <= x <= n, x not in B, and x <= maxSum. In other words, r = 0 exactly when every allowed integer in [1,n] is strictly greater than maxSum, including the case where there are no allowed integers.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_6 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    r.val = 0 ↔ ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ x ∉ forbidden banned ∧ x ≤ maxSum.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), r.val = 0 ↔ ¬ ∃ x : ℤ, 1 ≤ x ∧ x ≤ n.val ∧ x ∉ forbidden banned ∧ x ≤ maxSum.val) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) }, A = { x | 1 <= x <= n and x not in B }, m = |A|, and T = sum_{x in A} x, with T = 0 when A is empty. Whenever the function returns a result r, r = m if and only if T <= maxSum.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_7 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    r.val = ((allowed banned n.val).card : ℤ) ↔ totalAllowed banned n.val ≤ maxSum.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), r.val = ((allowed banned n.val).card : ℤ) ↔ totalAllowed banned n.val ≤ maxSum.val) := by
  sorry

/-- Assume len(banned) = 0. Whenever the function returns a result r, r is the unique integer such that 0 <= r <= n, r(r+1)/2 <= maxSum, and either r = n or (r+1)(r+2)/2 > maxSum.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; len(banned) = 0; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_8 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen_nil : banned.val.length = 0)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val ∧ r.val * (r.val + 1) / 2 ≤ maxSum.val ∧
      (r.val = n.val ∨ (r.val + 1) * (r.val + 2) / 2 > maxSum.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen_nil : banned.val.length = 0)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), 0 ≤ r.val ∧ r.val ≤ n.val ∧ r.val * (r.val + 1) / 2 ≤ maxSum.val ∧
      (r.val = n.val ∨ (r.val + 1) * (r.val + 2) / 2 > maxSum.val)) := by
  sorry

/-- Assume n = 1. Whenever the function returns a result r, r = 1 if there is no index i with 0 <= i < len(banned) and banned[i] = 1; otherwise r = 0.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; n = 1; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. -/
theorem spec_9 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn : n.val = 1)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    (r.val = 1 ↔ ¬ occursIn banned.val 1) ∧ (r.val = 0 ↔ occursIn banned.val 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn : n.val = 1)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), (r.val = 1 ↔ ¬ occursIn banned.val 1) ∧ (r.val = 0 ↔ occursIn banned.val 1)) := by
  sorry

/-- Whenever the function returns a result r, r(r+1)/2 <= maxSum.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_10 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    r.val * (r.val + 1) / 2 ≤ maxSum.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), r.val * (r.val + 1) / 2 ≤ maxSum.val) := by
  sorry

/-- Let B = { banned[i] | 0 <= i < len(banned) }. Whenever the function returns a result r, for every integer k with 0 <= k < r, there exist k distinct integers y_1, ..., y_k such that for every j with 1 <= j <= k, 1 <= y_j <= n and y_j not in B, and y_1 + ... + y_k <= maxSum. For k = 0 the empty selection is allowed and has sum 0.
  Preconditions: banned is a slice of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_11 (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r) :
    ∀ k : ℕ, (k : ℤ) < r.val →
      ∃ Y : Finset ℤ, Y ⊆ allowed banned n.val ∧ Y.card = k ∧
        Y.sum (fun x => x) ≤ maxSum.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64) (r : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r), ∀ k : ℕ, (k : ℤ) < r.val →
      ∃ Y : Finset ℤ, Y ⊆ allowed banned n.val ∧ Y.card = k ∧
        Y.sum (fun x => x) ≤ maxSum.val) := by
  sorry

/-- Whenever the call max_count(banned, n, maxSum) returns r and the call max_count(banned', n, maxSum) returns r', we have r' = r.
  Preconditions: banned and banned' are slices of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 0 <= len(banned') <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n; for every i with 0 <= i < len(banned'), 1 <= banned'[i] <= n; for every integer v, v occurs in banned' if and only if v occurs in banned. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_12 (banned banned' : Slice I64) (n maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen' : banned'.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hbanned' : ∀ x ∈ banned'.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hocc : ∀ v : ℤ, occursIn banned'.val v ↔ occursIn banned.val v)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned' n maxSum = ok r') :
    r' = r := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (banned banned' : Slice I64) (n maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen' : banned'.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hbanned' : ∀ x ∈ banned'.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hocc : ∀ v : ℤ, occursIn banned'.val v ↔ occursIn banned.val v)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned' n maxSum = ok r'), r' = r) := by
  sorry

/-- Whenever the call max_count(banned, n, maxSum) returns r and the call max_count(banned, n', maxSum) returns r', we have r' >= r.
  Preconditions: banned is a slice of 64-bit integers; n, n', and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= n' <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_13 (banned : Slice I64) (n n' maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_le : n.val ≤ n'.val) (hn_hi : n'.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned n' maxSum = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (banned : Slice I64) (n n' maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_le : n.val ≤ n'.val) (hn_hi : n'.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned n' maxSum = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the call max_count(banned, n, maxSum) returns r and the call max_count(banned, n, maxSum') returns r', we have r' >= r.
  Preconditions: banned is a slice of 64-bit integers; n, maxSum, and maxSum' are 64-bit integers; 0 <= len(banned) <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= maxSum' <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n. Duplicates in banned are allowed and treated as the same forbidden value. All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_14 (banned : Slice I64) (n maxSum maxSum' : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_le : maxSum.val ≤ maxSum'.val)
    (hm_hi : maxSum'.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned n maxSum' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum maxSum' : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_le : maxSum.val ≤ maxSum'.val)
    (hm_hi : maxSum'.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned n maxSum' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Whenever the call max_count(banned, n, maxSum) returns r and the call max_count(banned', n, maxSum) returns r', we have r' >= r.
  Preconditions: banned and banned' are slices of 64-bit integers; n and maxSum are 64-bit integers; 0 <= len(banned) <= 100000; 0 <= len(banned') <= 100000; 1 <= n <= 1000000000; 1 <= maxSum <= 1000000000000000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= n; for every i with 0 <= i < len(banned'), 1 <= banned'[i] <= n; for every integer v, if v occurs in banned' then v occurs in banned (the forbidden set of banned' is a subset of that of banned). All arithmetic in the statement is mathematical integer arithmetic. -/
theorem spec_15 (banned banned' : Slice I64) (n maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen' : banned'.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hbanned' : ∀ x ∈ banned'.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hsub : ∀ v : ℤ, occursIn banned'.val v → occursIn banned.val v)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned' n maxSum = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (banned banned' : Slice I64) (n maxSum : I64) (r r' : I64)
    (hlen : banned.val.length ≤ 100000)
    (hlen' : banned'.val.length ≤ 100000)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000000000)
    (hm_lo : 1 ≤ maxSum.val) (hm_hi : maxSum.val ≤ 1000000000000000)
    (hbanned : ∀ x ∈ banned.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hbanned' : ∀ x ∈ banned'.val, 1 ≤ x.val ∧ x.val ≤ n.val)
    (hsub : ∀ v : ℤ, occursIn banned'.val v → occursIn banned.val v)
    (hr : Aegis.MaxCount.max_count banned n maxSum = ok r)
    (hr' : Aegis.MaxCount.max_count banned' n maxSum = ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaxCount
