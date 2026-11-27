import Aegis.MaxIncreasingGroups.Code.Funs

/-!
# Specifications of `Aegis.MaxIncreasingGroups.max_increasing_groups`

LeetCode problem `maximum-number-of-groups-with-increasing-length`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxIncreasingGroups
open scoped BigOperators

namespace AegisSpec.MaxIncreasingGroups

def limits (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

def sz (s : Slice Std.I64) : Nat := (limits s).length

def usage (s : Slice Std.I64) (i : Nat) : Int := (limits s).getD i 0

def InRange (s : Slice Std.I64) : Prop :=
  ∀ i, i < sz s → 1 ≤ usage s i ∧ usage s i ≤ 1000000000

def ValidInput (s : Slice Std.I64) : Prop :=
  1 ≤ sz s ∧ sz s ≤ 100000 ∧ InRange s

def totalUsage (s : Slice Std.I64) : Int :=
  ∑ i ∈ Finset.range (sz s), usage s i

def cappedSum (s : Slice Std.I64) (t : Nat) : Int :=
  ∑ i ∈ Finset.range (sz s), min (usage s i) (t : Int)

def topSum (r t : Nat) : Int := (t : Int) * (2 * (r : Int) - (t : Int) + 1) / 2

def coverCount {n k : Nat} (G : Fin k → Finset (Fin n)) (i : Fin n) : Nat :=
  (Finset.univ.filter (fun t => i ∈ G t)).card

def HasGroups (s : Slice Std.I64) (k : Nat) : Prop :=
  ∃ G : Fin k → Finset (Fin (sz s)),
    (∀ t, (G t).Nonempty) ∧
    (∀ t t' : Fin k, t < t' → (G t).card < (G t').card) ∧
    (∀ i : Fin (sz s), (coverCount G i : Int) ≤ usage s i.val)

def HallConds (s : Slice Std.I64) (k : Nat) : Prop :=
  k ≤ sz s ∧ ∀ t, 1 ≤ t → t ≤ k → topSum k t ≤ cappedSum s t

/-- Let A(k) be the assertion that there exist subsets G_1, ..., G_k of {0, ..., n-1} such that: (1) every G_t is non-empty; (2) |G_1| < |G_2| < ... < |G_k|; and (3) for every i with 0 <= i < n, the number of t in {1, ..., k} with i in G_t is at most usageLimits[i]. The function returns a result r, and r is the largest integer k for which A(k) holds. Equivalently, A(r) holds and A(k) does not hold for any integer k > r.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_1 (s : Slice Std.I64) (h : ValidInput s) :
    ∃ r : Std.I64, max_increasing_groups s = ok r ∧
      HasGroups s r.val.toNat ∧
      ∀ k : Nat, r.val.toNat < k → ¬ HasGroups s k := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∃ r : Std.I64, max_increasing_groups s = ok r ∧
      HasGroups s r.val.toNat ∧
      ∀ k : Nat, r.val.toNat < k → ¬ HasGroups s k) := by
  sorry

/-- For every usageLimits satisfying the preconditions, max_increasing_groups(usageLimits) returns a result; it does not fail, panic, or overflow.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_2 (s : Slice Std.I64) (h : ValidInput s) :
    ∃ r : Std.I64, max_increasing_groups s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∃ r : Std.I64, max_increasing_groups s = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= n.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_3 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r → 1 ≤ r.val ∧ r.val ≤ (sz s : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r → 1 ≤ r.val ∧ r.val ≤ (sz s : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exist subsets G_1, ..., G_r of {0, ..., n-1} such that |G_t| = t for every t with 1 <= t <= r, and for every i with 0 <= i < n, the number of t in {1, ..., r} with i in G_t is at most usageLimits[i].
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_4 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∃ G : Fin r.val.toNat → Finset (Fin (sz s)),
        (∀ t : Fin r.val.toNat, (G t).card = t.val + 1) ∧
        (∀ i : Fin (sz s), (coverCount G i : Int) ≤ usage s i.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∃ G : Fin r.val.toNat → Finset (Fin (sz s)),
        (∀ t : Fin r.val.toNat, (G t).card = t.val + 1) ∧
        (∀ i : Fin (sz s), (coverCount G i : Int) ≤ usage s i.val)) := by
  sorry

/-- Whenever the function returns a result r, every sequence of subsets H_1, ..., H_k of {0, ..., n-1} satisfying (1) each H_t is non-empty, (2) |H_1| < |H_2| < ... < |H_k|, and (3) for every i with 0 <= i < n the number of t with i in H_t is at most usageLimits[i], must have k <= r.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_5 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ k : Nat, HasGroups s k → k ≤ r.val.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ k : Nat, HasGroups s k → k ≤ r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r, for every integer t with 1 <= t <= r, the sum over i from 0 to n-1 of min(usageLimits[i], t) is at least the sum of the t largest group sizes among 1, 2, ..., r, namely sum_{s=r-t+1}^{r} s = t*(2*r - t + 1)/2.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_6 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ t : Nat, 1 ≤ t → t ≤ r.val.toNat → topSum r.val.toNat t ≤ cappedSum s t := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ t : Nat, 1 ≤ t → t ≤ r.val.toNat → topSum r.val.toNat t ≤ cappedSum s t) := by
  sorry

/-- The result returned for a equals the result returned for b.
  Preconditions: Let a and b be two non-empty slices of i64 with the same length n = len(a) = len(b), satisfying 1 <= n <= 100000 and 1 <= a[i], b[i] <= 1000000000 for every i. The entries of a and b are the same multiset; explicitly, there exists a bijection p from {0, ..., n-1} to itself such that b[j] = a[p(j)] for every j with 0 <= j < n. -/
theorem spec_7 (a b : Slice Std.I64) (h : ValidInput a) (hlen : sz b = sz a)
    (hb : InRange b)
    (hperm : ∃ p : Fin (sz a) ≃ Fin (sz a),
      ∀ j : Fin (sz a), usage b j.val = usage a (p j).val) :
    max_increasing_groups a = max_increasing_groups b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice Std.I64) (h : ValidInput a) (hlen : sz b = sz a)
    (hb : InRange b)
    (hperm : ∃ p : Fin (sz a) ≃ Fin (sz a),
      ∀ j : Fin (sz a), usage b j.val = usage a (p j).val), max_increasing_groups a = max_increasing_groups b) := by
  sorry

/-- The result returned for a is at most the result returned for b.
  Preconditions: Let a and b be two slices of i64 with the same length n = len(a) = len(b), satisfying 1 <= n <= 100000 and 1 <= a[i], b[i] <= 1000000000 for every i with 0 <= i < n. Suppose a[i] <= b[i] for every i with 0 <= i < n. -/
theorem spec_8 (a b : Slice Std.I64) (h : ValidInput a) (hlen : sz b = sz a)
    (hb : InRange b) (hle : ∀ i, i < sz a → usage a i ≤ usage b i) :
    ∀ ra rb : Std.I64, max_increasing_groups a = ok ra → max_increasing_groups b = ok rb →
      ra.val ≤ rb.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (a b : Slice Std.I64) (h : ValidInput a) (hlen : sz b = sz a)
    (hb : InRange b) (hle : ∀ i, i < sz a → usage a i ≤ usage b i), ∀ ra rb : Std.I64, max_increasing_groups a = ok ra → max_increasing_groups b = ok rb →
      ra.val ≤ rb.val) := by
  sorry

/-- The function returns the same result r when called on capped.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000, and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. Let r be the result returned for usageLimits, and define capped[i] = min(usageLimits[i], r) for 0 <= i < n. -/
theorem spec_9 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ s' : Slice Std.I64, sz s' = sz s →
        (∀ i, i < sz s → usage s' i = min (usage s i) r.val) →
        max_increasing_groups s' = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      ∀ s' : Slice Std.I64, sz s' = sz s →
        (∀ i, i < sz s → usage s' i = min (usage s i) r.val) →
        max_increasing_groups s' = ok r) := by
  sorry

/-- The function returns n.
  Preconditions: usageLimits is a non-empty slice of i64 with n = len(usageLimits), satisfying 1 <= n <= 100000 and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. Suppose usageLimits[i] >= n for every i with 0 <= i < n. -/
theorem spec_10 (s : Slice Std.I64) (h : ValidInput s)
    (hbig : ∀ i, i < sz s → (sz s : Int) ≤ usage s i) :
    ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = (sz s : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s)
    (hbig : ∀ i, i < sz s → (sz s : Int) ≤ usage s i), ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = (sz s : Int)) := by
  sorry

/-- For every sequence of subsets G_1, ..., G_n of {0, ..., n-1} such that each G_t is non-empty, |G_1| < |G_2| < ... < |G_n|, and for every i with 0 <= i < n the number of t with i in G_t is at most usageLimits[i], it holds that |G_t| = t for every t with 1 <= t <= n; in particular |G_n| = n, so G_n = {0, ..., n-1}.
  Preconditions: usageLimits is a non-empty slice of i64 with n = len(usageLimits), satisfying 1 <= n <= 100000 and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. The function returns n. -/
theorem spec_11 (s : Slice Std.I64) (h : ValidInput s)
    (hret : ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = (sz s : Int)) :
    ∀ G : Fin (sz s) → Finset (Fin (sz s)),
      (∀ t, (G t).Nonempty) →
      (∀ t t' : Fin (sz s), t < t' → (G t).card < (G t').card) →
      (∀ i : Fin (sz s), (coverCount G i : Int) ≤ usage s i.val) →
      (∀ t : Fin (sz s), (G t).card = t.val + 1) ∧
        ∃ t : Fin (sz s), G t = Finset.univ := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s)
    (hret : ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = (sz s : Int)), ∀ G : Fin (sz s) → Finset (Fin (sz s)),
      (∀ t, (G t).Nonempty) →
      (∀ t t' : Fin (sz s), t < t' → (G t).card < (G t').card) →
      (∀ i : Fin (sz s), (coverCount G i : Int) ≤ usage s i.val) →
      (∀ t : Fin (sz s), (G t).card = t.val + 1) ∧
        ∃ t : Fin (sz s), G t = Finset.univ) := by
  sorry

/-- The function returns 2 if max(usageLimits[0], usageLimits[1]) >= 2, and returns 1 otherwise.
  Preconditions: usageLimits is a non-empty slice of i64 with n = len(usageLimits) = 2, satisfying 1 <= usageLimits[i] <= 1000000000 for i = 0 and i = 1. -/
theorem spec_12 (s : Slice Std.I64) (hlen : sz s = 2) (hb : InRange s) :
    (2 ≤ max (usage s 0) (usage s 1) →
        ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = 2) ∧
      (max (usage s 0) (usage s 1) < 2 →
        ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.I64) (hlen : sz s = 2) (hb : InRange s), (2 ≤ max (usage s 0) (usage s 1) →
        ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = 2) ∧
      (max (usage s 0) (usage s 1) < 2 →
        ∃ r : Std.I64, max_increasing_groups s = ok r ∧ r.val = 1)) := by
  sorry

/-- Let r be the returned value. Then r is the largest integer k with 0 <= k <= n such that for every integer t with 1 <= t <= k, sum_{i=0}^{n-1} min(usageLimits[i], t) >= t*(2*k - t + 1)/2 (the condition is vacuous for k = 0). In particular the Hall-type inequalities of spec_6 are not only necessary but sufficient, so this gives a computable, subset-free characterisation of the answer.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000 and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_13 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      HallConds s r.val.toNat ∧ ∀ k : Nat, r.val.toNat < k → ¬ HallConds s k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      HallConds s r.val.toNat ∧ ∀ k : Nat, r.val.toNat < k → ¬ HallConds s k) := by
  sorry

/-- The result returned for a is at most the result returned for b: appending a further number (with a positive usage limit) cannot decrease the maximum number of groups, since every grouping feasible for a uses only the numbers 0,...,len(a)-1 and is therefore feasible for b.
  Preconditions: Let a and b be slices of i64 with 1 <= len(a) <= 99999 and len(b) = len(a) + 1 <= 100000, satisfying b[i] = a[i] for every 0 <= i < len(a), with 1 <= a[i] <= 1000000000 and 1 <= b[len(a)] <= 1000000000. -/
theorem spec_14 (a b : Slice Std.I64) (ha : 1 ≤ sz a ∧ sz a ≤ 99999)
    (hb : sz b = sz a + 1) (ha_in : InRange a) (hb_in : InRange b)
    (hpref : ∀ i, i < sz a → usage b i = usage a i) :
    ∀ ra rb : Std.I64, max_increasing_groups a = ok ra → max_increasing_groups b = ok rb →
      ra.val ≤ rb.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (a b : Slice Std.I64) (ha : 1 ≤ sz a ∧ sz a ≤ 99999)
    (hb : sz b = sz a + 1) (ha_in : InRange a) (hb_in : InRange b)
    (hpref : ∀ i, i < sz a → usage b i = usage a i), ∀ ra rb : Std.I64, max_increasing_groups a = ok ra → max_increasing_groups b = ok rb →
      ra.val ≤ rb.val) := by
  sorry

/-- Whenever the function returns a result r, r*(r+1)/2 <= sum_{i=0}^{n-1} usageLimits[i]; that is, the total number of occurrences needed by groups of sizes 1, 2, ..., r does not exceed the total available usage budget.
  Preconditions: usageLimits is a non-empty slice of i64. Let n = len(usageLimits). The constraints hold: 1 <= n <= 100000 and 1 <= usageLimits[i] <= 1000000000 for every i with 0 <= i < n. -/
theorem spec_15 (s : Slice Std.I64) (h : ValidInput s) :
    ∀ r : Std.I64, max_increasing_groups s = ok r →
      r.val * (r.val + 1) / 2 ≤ totalUsage s := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (s : Slice Std.I64) (h : ValidInput s), ∀ r : Std.I64, max_increasing_groups s = ok r →
      r.val * (r.val + 1) / 2 ≤ totalUsage s) := by
  sorry

end AegisSpec.MaxIncreasingGroups
