import Aegis.MinimumSteps.Code.Funs

/-!
# Specifications of `Aegis.MinimumSteps.minimum_steps`

LeetCode problem `separate-black-and-white-balls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.MinimumSteps

def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

def entry (l : List ℕ) (i : ℕ) : Option ℕ := l[i]?

def countOf (x : ℕ) (l : List ℕ) : ℕ := l.count x

def onesCount (l : List ℕ) : ℕ := countOf 49 l

def zerosCount (l : List ℕ) : ℕ := countOf 48 l

def zerosAfter (l : List ℕ) (n : ℕ) (i : ℕ) : ℕ :=
  ((Finset.range n).filter (fun j => i < j ∧ entry l j = some 48)).card

def onesBefore (l : List ℕ) (i : ℕ) : ℕ := (l.take i).count 49

def stepCount (l : List ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if entry l i = some 49 then zerosAfter l n i else 0

def stepCountPairs (l : List ℕ) (n : ℕ) : ℕ :=
  (((Finset.range n).product (Finset.range n)).filter
      (fun q => q.1 < q.2 ∧ entry l q.1 = some 49 ∧ entry l q.2 = some 48)).card

def maxStepCount (l : List ℕ) (n : ℕ) : ℕ := onesCount l * (n - onesCount l)

def oneIndices (l : List ℕ) : List ℕ :=
  (l.zipIdx.filter (fun q => q.1 == 49)).map (fun q => q.2)

def oneIndex (l : List ℕ) (j : ℕ) : ℕ := (oneIndices l).getD j 0

def stepCountByPositions (l : List ℕ) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (onesCount l), ((n - onesCount l + j) - oneIndex l j)

def swapAdj (l : List ℕ) (i : ℕ) : List ℕ :=
  match l[i + 1]?, l[i]? with
  | some b, some a => (l.set i b).set (i + 1) a
  | _, _ => l

def SwappableIn : ℕ → List ℕ → List ℕ → Prop
  | 0, u, v => u = v
  | m + 1, u, v => ∃ i, i + 1 < u.length ∧ SwappableIn m (swapAdj u i) v

/-- The function returns a result r, and r = sum over all i with 0 <= i < n and s[i] = 49 of (the number of j with i < j < n and s[j] = 48). Equivalently, r is the number of pairs (i,j) with 0 <= i < j < n, s[i] = 49, and s[j] = 48.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_1 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val = (stepCount (bytes s) n : ℤ) ∧
        r.val = (stepCountPairs (bytes s) n : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val = (stepCount (bytes s) n : ℤ) ∧
        r.val = (stepCountPairs (bytes s) n : ℤ)) := by
  sorry

/-- Let k be the number of i with 0 <= i < n and s[i] = 49. If r is the returned result, then there exists a sequence of exactly r adjacent swaps of entries of s that transforms s into a sequence t of length n with t[i] = 48 for 0 <= i < n-k and t[i] = 49 for n-k <= i < n.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_2 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ (r : Std.I64) (t : List ℕ) (m : ℕ),
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val = (m : ℤ) ∧
        t.length = n ∧
        SwappableIn m (bytes s) t ∧
        (∀ i, i < n - onesCount (bytes s) → entry t i = some 48) ∧
        (∀ i, n - onesCount (bytes s) ≤ i → i < n → entry t i = some 49) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ (r : Std.I64) (t : List ℕ) (m : ℕ),
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val = (m : ℤ) ∧
        t.length = n ∧
        SwappableIn m (bytes s) t ∧
        (∀ i, i < n - onesCount (bytes s) → entry t i = some 48) ∧
        (∀ i, n - onesCount (bytes s) ≤ i → i < n → entry t i = some 49)) := by
  sorry

/-- Let k be the number of i with 0 <= i < n and s[i] = 49. The function returns a result r, and r <= k * (n - k).
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_3 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val ≤ (maxStepCount (bytes s) n : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        r.val ≤ (maxStepCount (bytes s) n : ℤ)) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if there do not exist indices i,j with 0 <= i < j < n, s[i] = 49, and s[j] = 48. Equivalently, r = 0 exactly when every 48 in s occurs before every 49 in s.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_4 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (r.val = 0 ↔
          ¬ ∃ i j, i < j ∧ j < n ∧ entry (bytes s) i = some 49 ∧ entry (bytes s) j = some 48) ∧
        (r.val = 0 ↔
          ∀ i j, i < n → j < n → entry (bytes s) i = some 48 → entry (bytes s) j = some 49 →
            i < j) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (r.val = 0 ↔
          ¬ ∃ i j, i < j ∧ j < n ∧ entry (bytes s) i = some 49 ∧ entry (bytes s) j = some 48) ∧
        (r.val = 0 ↔
          ∀ i j, i < n → j < n → entry (bytes s) i = some 48 → entry (bytes s) j = some 49 →
            i < j)) := by
  sorry

/-- Let k be the number of i with 0 <= i < n and s[i] = 49. The function returns a result r, and r = k * (n - k) if and only if s[i] = 49 for every i with 0 <= i < k and s[i] = 48 for every i with k <= i < n.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_5 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (r.val = (maxStepCount (bytes s) n : ℤ) ↔
          (∀ i, i < onesCount (bytes s) → entry (bytes s) i = some 49) ∧
            (∀ i, onesCount (bytes s) ≤ i → i < n → entry (bytes s) i = some 48)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (r.val = (maxStepCount (bytes s) n : ℤ) ↔
          (∀ i, i < onesCount (bytes s) → entry (bytes s) i = some 49) ∧
            (∀ i, onesCount (bytes s) ≤ i → i < n → entry (bytes s) i = some 48))) := by
  sorry

/-- Let k be the number of i with 0 <= i < n and s[i] = 49. For each j with 0 <= j < k, let p_j be the unique index such that s[p_j] = 49 and exactly j indices i with 0 <= i < p_j satisfy s[i] = 49. The function returns a result r, and r = sum_{j=0}^{k-1} (n - k + j - p_j).
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_6 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (∀ j, j < onesCount (bytes s) →
          entry (bytes s) (oneIndex (bytes s) j) = some 49 ∧
            onesBefore (bytes s) (oneIndex (bytes s) j) = j) ∧
        (∀ j q, j < onesCount (bytes s) → entry (bytes s) q = some 49 →
          onesBefore (bytes s) q = j → q = oneIndex (bytes s) j) ∧
        r.val = (stepCountByPositions (bytes s) n : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        (∀ j, j < onesCount (bytes s) →
          entry (bytes s) (oneIndex (bytes s) j) = some 49 ∧
            onesBefore (bytes s) (oneIndex (bytes s) j) = j) ∧
        (∀ j q, j < onesCount (bytes s) → entry (bytes s) q = some 49 →
          onesBefore (bytes s) q = j → q = oneIndex (bytes s) j) ∧
        r.val = (stepCountByPositions (bytes s) n : ℤ)) := by
  sorry

/-- Let c be the sequence of length n with c[i] = 97 - s[i] for every i with 0 <= i < n, and let k be the number of i with s[i] = 49. The function returns results r for s and r_c for c, and r + r_c = k * (n - k).
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_7 (s : Slice Std.U8) (n : ℕ) (c : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hc_len : c.length = n)
    (hc : ∀ i x, i < n → entry (bytes s) i = some x → entry (bytes c) i = some (97 - x)) :
    ∃ r r_c : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps c = ok r_c ∧
        r.val + r_c.val = (maxStepCount (bytes s) n : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (c : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hc_len : c.length = n)
    (hc : ∀ i x, i < n → entry (bytes s) i = some x → entry (bytes c) i = some (97 - x)), ∃ r r_c : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps c = ok r_c ∧
        r.val + r_c.val = (maxStepCount (bytes s) n : ℤ)) := by
  sorry

/-- Let t be the sequence of length n with t[i] = 97 - s[n-1-i] for every i with 0 <= i < n. The function returns results r for s and r_t for t, and r = r_t.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_8 (s : Slice Std.U8) (n : ℕ) (t : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (ht_len : t.length = n)
    (ht : ∀ i x, i < n → entry (bytes s) (n - 1 - i) = some x → entry (bytes t) i = some (97 - x)) :
    ∃ r r_t : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps t = ok r_t ∧
        r.val = r_t.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (t : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (ht_len : t.length = n)
    (ht : ∀ i x, i < n → entry (bytes s) (n - 1 - i) = some x → entry (bytes t) i = some (97 - x)), ∃ r r_t : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps t = ok r_t ∧
        r.val = r_t.val) := by
  sorry

/-- Let s' be the sequence of length n+1 with s'[0] = 48 and s'[i+1] = s[i] for every i with 0 <= i < n. The function returns results r for s and r' for s', and r' = r.
  Preconditions: The slice s has length n = len(s) with 1 <= n < 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_9 (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs'0 : entry (bytes s') 0 = some 48)
    (hs'succ : ∀ i, i < n → entry (bytes s') (i + 1) = entry (bytes s) i) :
    ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs'0 : entry (bytes s') 0 = some 48)
    (hs'succ : ∀ i, i < n → entry (bytes s') (i + 1) = entry (bytes s) i), ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val) := by
  sorry

/-- Let s' be the sequence of length n+1 with s'[i] = s[i] for every i with 0 <= i < n and s'[n] = 49. The function returns results r for s and r' for s', and r' = r.
  Preconditions: The slice s has length n = len(s) with 1 <= n < 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_10 (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs' : ∀ i, i < n → entry (bytes s') i = entry (bytes s) i)
    (hs'n : entry (bytes s') n = some 49) :
    ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs' : ∀ i, i < n → entry (bytes s') i = entry (bytes s) i)
    (hs'n : entry (bytes s') n = some 49), ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val) := by
  sorry

/-- Let z be the number of i with 0 <= i < n and s[i] = 48. Let s' be the sequence of length n+1 with s'[0] = 49 and s'[i+1] = s[i] for every i with 0 <= i < n. The function returns results r for s and r' for s', and r' = r + z.
  Preconditions: The slice s has length n = len(s) with 1 <= n < 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_11 (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs'0 : entry (bytes s') 0 = some 49)
    (hs'succ : ∀ i, i < n → entry (bytes s') (i + 1) = entry (bytes s) i) :
    ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val + (zerosCount (bytes s) : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs'0 : entry (bytes s') 0 = some 49)
    (hs'succ : ∀ i, i < n → entry (bytes s') (i + 1) = entry (bytes s) i), ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val + (zerosCount (bytes s) : ℤ)) := by
  sorry

/-- Let k be the number of i with 0 <= i < n and s[i] = 49. Let s' be the sequence of length n+1 with s'[i] = s[i] for every i with 0 <= i < n and s'[n] = 48. The function returns results r for s and r' for s', and r' = r + k.
  Preconditions: The slice s has length n = len(s) with 1 <= n < 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_12 (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs' : ∀ i, i < n → entry (bytes s') i = entry (bytes s) i)
    (hs'n : entry (bytes s') n = some 48) :
    ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val + (onesCount (bytes s) : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (s' : Slice Std.U8) (hn : n = s.length)
    (hn1 : 1 ≤ n) (hn2 : n < 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49)
    (hs'len : s'.length = n + 1)
    (hs' : ∀ i, i < n → entry (bytes s') i = entry (bytes s) i)
    (hs'n : entry (bytes s') n = some 48), ∃ r r' : Std.I64,
      Aegis.MinimumSteps.minimum_steps s = ok r ∧
        Aegis.MinimumSteps.minimum_steps s' = ok r' ∧
        r'.val = r.val + (onesCount (bytes s) : ℤ)) := by
  sorry

/-- For every s satisfying the preconditions, the function returns a result r; it does not fail, overflow, or access an index out of bounds.
  Preconditions: The slice s has length n = len(s) with 1 <= n <= 100000. For every i with 0 <= i < n, s[i] is either 48 (the byte '0') or 49 (the byte '1'). -/
theorem spec_13 (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49) :
    ∃ r : Std.I64, Aegis.MinimumSteps.minimum_steps s = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (n : ℕ) (hn : n = s.length) (hn1 : 1 ≤ n) (hn2 : n ≤ 100000)
    (hbits : ∀ i, i < n → entry (bytes s) i = some 48 ∨ entry (bytes s) i = some 49), ∃ r : Std.I64, Aegis.MinimumSteps.minimum_steps s = ok r) := by
  sorry

end AegisSpec.MinimumSteps
