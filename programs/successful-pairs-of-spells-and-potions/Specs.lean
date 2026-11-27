import Aegis.SuccessfulPairs.Code.Funs

/-!
# Specifications of `Aegis.SuccessfulPairs.successful_pairs`

LeetCode problem `successful-pairs-of-spells-and-potions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SuccessfulPairs

def sliceInts (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def vecInts (v : alloc.vec.Vec I64) : List ℤ := v.val.map (fun x => x.val)

def countReaching (s success : ℤ) (potions : List ℤ) : ℕ :=
  potions.countP (fun p => decide (success ≤ s * p))

def countPairs (spells potions : List ℤ) (success : ℤ) : ℕ :=
  (spells.map (fun s => countReaching s success potions)).sum

def countAtLeast (potions : List ℤ) (T : ℤ) : ℕ :=
  potions.countP (fun p => decide (T ≤ p))

/-- Whenever the function returns a result r, len(r) = n and for every i with 0 <= i < n, r[i] is the number of indices j with 0 <= j < m such that spells[i] * potions[j] >= success, where the product is taken over the integers (under the preconditions it fits in i64 and does not overflow).
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. -/
theorem spec_1
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r) :
    r.val.length = spells.val.length ∧
      ∃ (hlen : r.val.length = spells.val.length),
        ∀ (i : Fin spells.val.length),
          (r.val[i.cast hlen.symm]).val =
            ((countReaching (spells.val[i]).val success.val (sliceInts potions) : ℕ) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r), r.val.length = spells.val.length ∧
      ∃ (hlen : r.val.length = spells.val.length),
        ∀ (i : Fin spells.val.length),
          (r.val[i.cast hlen.symm]).val =
            ((countReaching (spells.val[i]).val success.val (sliceInts potions) : ℕ) : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, go out of bounds, or fail allocation.
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. -/
theorem spec_2
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000) :
    ∃ r : alloc.vec.Vec I64,
      Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000), ∃ r : alloc.vec.Vec I64,
      Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r) := by
  sorry

/-- Whenever the function returns a result r, for all i and k with 0 <= i < n and 0 <= k < n, if spells[i] <= spells[k] then r[i] <= r[k].
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. -/
theorem spec_3
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r) :
    ∃ (hlen : r.val.length = spells.val.length),
      ∀ (i k : Fin spells.val.length),
        (spells.val[i]).val ≤ (spells.val[k]).val →
          (r.val[i.cast hlen.symm]).val ≤ (r.val[k.cast hlen.symm]).val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r), ∃ (hlen : r.val.length = spells.val.length),
      ∀ (i k : Fin spells.val.length),
        (spells.val[i]).val ≤ (spells.val[k]).val →
          (r.val[i.cast hlen.symm]).val ≤ (r.val[k.cast hlen.symm]).val) := by
  sorry

/-- Whenever the function returns a result r, sum_{i=0}^{n-1} r[i] equals the number of ordered pairs (i,j) with 0 <= i < n, 0 <= j < m, and spells[i] * potions[j] >= success.
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. -/
theorem spec_4
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r) :
    (vecInts r).sum =
      ((countPairs (sliceInts spells) (sliceInts potions) success.val : ℕ) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r), (vecInts r).sum =
      ((countPairs (sliceInts spells) (sliceInts potions) success.val : ℕ) : ℤ)) := by
  sorry

/-- Whenever successful_pairs(spells, potions, success) returns a result r and successful_pairs(spells, potions', success) returns a result r', we have r = r', that is, for every i with 0 <= i < n, r[i] = r'[i].
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. Let potions' be any slice of i64 with len(potions') = m and 1 <= potions'[j] <= 100000 for every j with 0 <= j < m, such that potions' is a permutation of potions: there exists a bijection pi from {0,1,...,m-1} to itself with potions'[j] = potions[pi(j)] for every j with 0 <= j < m. -/
theorem spec_5
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (potions' : Slice I64)
    (hpotions'_len : potions'.val.length = potions.val.length)
    (hpotions'_lb : 1 ≤ potions'.val.length)
    (hpotions' : ∀ j : Fin potions'.val.length,
      1 ≤ (potions'.val[j]).val ∧ (potions'.val[j]).val ≤ 100000)
    (hperm : ∃ pi : Equiv.Perm (Fin potions.val.length),
      ∀ (j : Fin potions.val.length),
        (potions'.val[j.cast hpotions'_len.symm]).val = (potions.val[pi j]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions' success = ok r') :
    ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r.val[i.cast hlen.symm]).val = (r'.val[i.cast hlen'.symm]).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (potions' : Slice I64)
    (hpotions'_len : potions'.val.length = potions.val.length)
    (hpotions'_lb : 1 ≤ potions'.val.length)
    (hpotions' : ∀ j : Fin potions'.val.length,
      1 ≤ (potions'.val[j]).val ∧ (potions'.val[j]).val ≤ 100000)
    (hperm : ∃ pi : Equiv.Perm (Fin potions.val.length),
      ∀ (j : Fin potions.val.length),
        (potions'.val[j.cast hpotions'_len.symm]).val = (potions.val[pi j]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions' success = ok r'), ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r.val[i.cast hlen.symm]).val = (r'.val[i.cast hlen'.symm]).val) := by
  sorry

/-- Whenever successful_pairs(spells, potions, success) returns a result r and successful_pairs(spells, potions', success) returns a result r', then for every i with 0 <= i < n, r[i] <= r'[i].
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. Let potions' be any slice of i64 with len(potions') = m, 1 <= potions'[j] <= 100000 for every j with 0 <= j < m, and potions[j] <= potions'[j] for every j with 0 <= j < m. -/
theorem spec_6
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (potions' : Slice I64)
    (hpotions'_len : potions'.val.length = potions.val.length)
    (hpotions'_lb : 1 ≤ potions'.val.length)
    (hpotions' : ∀ j : Fin potions'.val.length,
      1 ≤ (potions'.val[j]).val ∧ (potions'.val[j]).val ≤ 100000)
    (hle : ∀ j : Fin potions.val.length,
      (potions.val[j]).val ≤ (potions'.val[j.cast hpotions'_len.symm]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions' success = ok r') :
    ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r.val[i.cast hlen.symm]).val ≤ (r'.val[i.cast hlen'.symm]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (potions' : Slice I64)
    (hpotions'_len : potions'.val.length = potions.val.length)
    (hpotions'_lb : 1 ≤ potions'.val.length)
    (hpotions' : ∀ j : Fin potions'.val.length,
      1 ≤ (potions'.val[j]).val ∧ (potions'.val[j]).val ≤ 100000)
    (hle : ∀ j : Fin potions.val.length,
      (potions.val[j]).val ≤ (potions'.val[j.cast hpotions'_len.symm]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions' success = ok r'), ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r.val[i.cast hlen.symm]).val ≤ (r'.val[i.cast hlen'.symm]).val) := by
  sorry

/-- Whenever successful_pairs(spells, potions, success) returns a result r and successful_pairs(spells, potions, success') returns a result r', then for every i with 0 <= i < n, r'[i] <= r[i].
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. Let success' be an i64 with success <= success' <= 10000000000. -/
theorem spec_7
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (success' : I64)
    (hsuccess'_lb : success.val ≤ success'.val)
    (hsuccess'_ub : success'.val ≤ 10000000000)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions success' = ok r') :
    ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r'.val[i.cast hlen'.symm]).val ≤ (r.val[i.cast hlen.symm]).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (success' : I64)
    (hsuccess'_lb : success.val ≤ success'.val)
    (hsuccess'_ub : success'.val ≤ 10000000000)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells potions success' = ok r'), ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length),
        (r'.val[i.cast hlen'.symm]).val ≤ (r.val[i.cast hlen.symm]).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n there exists an integer T_i such that 1 <= T_i <= success, spells[i] * (T_i - 1) < success <= spells[i] * T_i, and r[i] is the number of indices j with 0 <= j < m and potions[j] >= T_i.
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. -/
theorem spec_8
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r) :
    ∃ (hlen : r.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length), ∃ (T : ℤ),
        1 ≤ T ∧ T ≤ success.val ∧
          (spells.val[i]).val * (T - 1) < success.val ∧
          success.val ≤ (spells.val[i]).val * T ∧
          (r.val[i.cast hlen.symm]).val = ((countAtLeast (sliceInts potions) T : ℕ) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (r : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r), ∃ (hlen : r.val.length = spells.val.length),
      ∀ (i : Fin spells.val.length), ∃ (T : ℤ),
        1 ≤ T ∧ T ≤ success.val ∧
          (spells.val[i]).val * (T - 1) < success.val ∧
          success.val ≤ (spells.val[i]).val * T ∧
          (r.val[i.cast hlen.symm]).val = ((countAtLeast (sliceInts potions) T : ℕ) : ℤ)) := by
  sorry

/-- Whenever successful_pairs(spells, potions, success) returns a result r and successful_pairs(spells', potions, success) returns a result r', we have r[i0] = r'[i0].
  Preconditions: Let n = len(spells) and m = len(potions). Assume 1 <= n <= 100000, 1 <= m <= 100000, for every i with 0 <= i < n we have 1 <= spells[i] <= 100000, for every j with 0 <= j < m we have 1 <= potions[j] <= 100000, and 1 <= success <= 10000000000. Let i0 be any index with 0 <= i0 < n. Let spells' be any slice of i64 with len(spells') = n and 1 <= spells'[i] <= 100000 for every i with 0 <= i < n, such that spells'[i0] = spells[i0]. -/
theorem spec_9
    (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (i0 : Fin spells.val.length)
    (spells' : Slice I64)
    (hspells'_len : spells'.val.length = spells.val.length)
    (hspells'_lb : 1 ≤ spells'.val.length)
    (hspells' : ∀ i : Fin spells'.val.length,
      1 ≤ (spells'.val[i]).val ∧ (spells'.val[i]).val ≤ 100000)
    (hi0 : (spells'.val[i0.cast hspells'_len.symm]).val = (spells.val[i0]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells' potions success = ok r') :
    ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      (r.val[i0.cast hlen.symm]).val = (r'.val[i0.cast hlen'.symm]).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (spells potions : Slice I64) (success : I64)
    (hn_lb : 1 ≤ spells.val.length) (hn_ub : spells.val.length ≤ 100000)
    (hm_lb : 1 ≤ potions.val.length) (hm_ub : potions.val.length ≤ 100000)
    (hspells : ∀ i : Fin spells.val.length,
      1 ≤ (spells.val[i]).val ∧ (spells.val[i]).val ≤ 100000)
    (hpotions : ∀ j : Fin potions.val.length,
      1 ≤ (potions.val[j]).val ∧ (potions.val[j]).val ≤ 100000)
    (hsuccess : 1 ≤ success.val ∧ success.val ≤ 10000000000)
    (i0 : Fin spells.val.length)
    (spells' : Slice I64)
    (hspells'_len : spells'.val.length = spells.val.length)
    (hspells'_lb : 1 ≤ spells'.val.length)
    (hspells' : ∀ i : Fin spells'.val.length,
      1 ≤ (spells'.val[i]).val ∧ (spells'.val[i]).val ≤ 100000)
    (hi0 : (spells'.val[i0.cast hspells'_len.symm]).val = (spells.val[i0]).val)
    (r r' : alloc.vec.Vec I64)
    (hr : Aegis.SuccessfulPairs.successful_pairs spells potions success = ok r)
    (hr' : Aegis.SuccessfulPairs.successful_pairs spells' potions success = ok r'), ∃ (hlen : r.val.length = spells.val.length)
      (hlen' : r'.val.length = spells.val.length),
      (r.val[i0.cast hlen.symm]).val = (r'.val[i0.cast hlen'.symm]).val) := by
  sorry

end AegisSpec.SuccessfulPairs
