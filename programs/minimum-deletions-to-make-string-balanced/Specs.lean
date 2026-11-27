import Aegis.MinimumDeletions.Code.Funs

/-!
# Specifications of `Aegis.MinimumDeletions.minimum_deletions`

LeetCode problem `minimum-deletions-to-make-string-balanced`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumDeletions

  open Aegis.MinimumDeletions (minimum_deletions)

  def len (s : Slice Std.U8) : ℕ := (Slice.len s).val

  def bytes (s : Slice Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def byteAt (s : Slice Std.U8) (i : ℕ) : Option ℕ := (bytes s)[i]?

  def countB (t : List ℕ) (k : ℕ) : ℕ :=
    ((List.range k).filter (fun i => decide (t[i]? = some 98))).length

  def countA (t : List ℕ) (k : ℕ) : ℕ :=
    (((List.range t.length).drop k).filter (fun j => decide (t[j]? = some 97))).length

  def cost (t : List ℕ) (k : ℕ) : ℕ := countB t k + countA t k

  def minCost (t : List ℕ) (lo hi : ℕ) : ℕ :=
    ((List.range (hi + 1)).drop lo).foldr (fun k acc => min (cost t k) acc) (cost t lo)

  def B (s : Slice Std.U8) (k : ℕ) : ℕ := countB (bytes s) k

  def A (s : Slice Std.U8) (k : ℕ) : ℕ := countA (bytes s) k

  def swapReverse (s : Slice Std.U8) : List ℕ :=
    (bytes s).reverse.map (fun c => if c = 97 then 98 else if c = 98 then 97 else c)

  def deleteIdx (t : List ℕ) (D : Finset ℕ) : List ℕ :=
    (List.range t.length).filterMap (fun i => if i ∈ D then (none : Option ℕ) else t[i]?)

  def Balanced (t : List ℕ) : Prop :=
    ∀ i j : ℕ, i < j → t[i]? = some 98 → t[j]? = some 97 → False

  /-- The function returns a result r and r = min { B(k) + A(k) | 0 <= k <= n }, where B(k) = #{ i | 0 <= i < k and s[i] = 'b' } and A(k) = #{ j | k <= j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_1 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98) :
      ∃ r : Std.I64, minimum_deletions s = ok r ∧ r.val = (minCost (bytes s) 0 (len s) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98), ∃ r : Std.I64, minimum_deletions s = ok r ∧ r.val = (minCost (bytes s) 0 (len s) : ℤ)) := by
    sorry

  /-- For every s satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_2 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98) :
      ∃ r : Std.I64, minimum_deletions s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98), ∃ r : Std.I64, minimum_deletions s = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_3 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      0 ≤ r.val ∧ r.val ≤ (len s : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), 0 ≤ r.val ∧ r.val ≤ (len s : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there do not exist integers i and j with 0 <= i < j < n such that s[i] = 'b' and s[j] = 'a'.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_4 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < j ∧ j < len s ∧ byteAt s i = some 98 ∧
        byteAt s j = some 97) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), (r.val = 0 ↔ ¬ ∃ i j : ℕ, i < j ∧ j < len s ∧ byteAt s i = some 98 ∧
          byteAt s j = some 97)) := by
    sorry

  /-- Whenever the function returns a result r, r <= min(a_count, b_count), where a_count = #{ i | 0 <= i < n and s[i] = 'a' } and b_count = #{ i | 0 <= i < n and s[i] = 'b' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_5 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      r.val ≤ (min (A s 0) (B s (len s)) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), r.val ≤ (min (A s 0) (B s (len s)) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer k with 0 <= k <= n such that r = B(k) + A(k), where B(k) = #{ i | 0 <= i < k and s[i] = 'b' } and A(k) = #{ j | k <= j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_6 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      ∃ k : ℕ, k ≤ len s ∧ r.val = (B s k : ℤ) + (A s k : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), ∃ k : ℕ, k ≤ len s ∧ r.val = (B s k : ℤ) + (A s k : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 0 <= k <= n, r <= B(k) + A(k), where B(k) = #{ i | 0 <= i < k and s[i] = 'b' } and A(k) = #{ j | k <= j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_7 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      ∀ k : ℕ, k ≤ len s → r.val ≤ (B s k : ℤ) + (A s k : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), ∀ k : ℕ, k ≤ len s → r.val ≤ (B s k : ℤ) + (A s k : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a finite set D of indices with D subset of {0,1,...,n-1} and |D| = r such that deleting exactly the indices in D (keeping the remaining characters in their original order) leaves a string that is balanced, meaning it contains no 'b' occurring before an 'a'.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_8 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      ∃ D : Finset ℕ, D ⊆ Finset.range (len s) ∧ (D.card : ℤ) = r.val ∧
        Balanced (deleteIdx (bytes s) D) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), ∃ D : Finset ℕ, D ⊆ Finset.range (len s) ∧ (D.card : ℤ) = r.val ∧
          Balanced (deleteIdx (bytes s) D)) := by
    sorry

  /-- Whenever the function returns a result r, for every finite set D of indices with D subset of {0,1,...,n-1} and |D| < r, deleting exactly the indices in D (keeping the remaining characters in their original order) does not leave a balanced string, where balanced means no 'b' occurs before an 'a'.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_9 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      ∀ D : Finset ℕ, D ⊆ Finset.range (len s) → (D.card : ℤ) < r.val →
        ¬ Balanced (deleteIdx (bytes s) D) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), ∀ D : Finset ℕ, D ⊆ Finset.range (len s) → (D.card : ℤ) < r.val →
          ¬ Balanced (deleteIdx (bytes s) D)) := by
    sorry

  /-- Whenever the function returns a result r, let t be the length-n byte string defined for 0 <= i < n by: if s[n-1-i] = 'a' then t[i] = 'b', and if s[n-1-i] = 'b' then t[i] = 'a'. Then r = min { B_t(k) + A_t(k) | 0 <= k <= n }, where B_t(k) = #{ i | 0 <= i < k and t[i] = 'b' } and A_t(k) = #{ j | k <= j < n and t[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_10 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r) :
      r.val = (minCost (swapReverse s) 0 (len s) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r), r.val = (minCost (swapReverse s) 0 (len s) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if n >= 1 and s[0] = 'a', then r = min { B(k) + A(k) | 1 <= k <= n }, where B(k) = #{ i | 0 <= i < k and s[i] = 'b' } and A(k) = #{ j | k <= j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_11 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r)
      (h0 : byteAt s 0 = some 97) :
      r.val = (minCost (bytes s) 1 (len s) : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r)
        (h0 : byteAt s 0 = some 97), r.val = (minCost (bytes s) 1 (len s) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if n >= 1 and s[n-1] = 'b', then r = min { B(k) + A(k) | 0 <= k <= n-1 }, where B(k) = #{ i | 0 <= i < k and s[i] = 'b' } and A(k) = #{ j | k <= j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_12 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r)
      (hlast : byteAt s (len s - 1) = some 98) :
      r.val = (minCost (bytes s) 0 (len s - 1) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r)
        (hlast : byteAt s (len s - 1) = some 98), r.val = (minCost (bytes s) 0 (len s - 1) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if s has the form p copies of 'b' followed by q copies of 'a' (so p + q = n, p >= 0, q >= 0), then r = min(p, q).
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_13 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r)
      (p q : ℕ) (hform : bytes s = List.replicate p 98 ++ List.replicate q 97) :
      r.val = (min p q : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r)
        (p q : ℕ) (hform : bytes s = List.replicate p 98 ++ List.replicate q 97), r.val = (min p q : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if s contains at least one 'a', let p be the largest index with 0 <= p < n and s[p] = 'a'; then r <= #{ i | 0 <= i < p and s[i] = 'b' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_14 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r)
      (p : ℕ) (hp : p < len s) (hpa : byteAt s p = some 97)
      (hlast : ∀ j : ℕ, p < j → j < len s → byteAt s j ≠ some 97) :
      r.val ≤ (B s p : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r)
        (p : ℕ) (hp : p < len s) (hpa : byteAt s p = some 97)
        (hlast : ∀ j : ℕ, p < j → j < len s → byteAt s j ≠ some 97), r.val ≤ (B s p : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if s contains at least one 'b', let q be the smallest index with 0 <= q < n and s[q] = 'b'; then r <= #{ j | q < j < n and s[j] = 'a' }.
    Preconditions: Let n = len(s). The slice s satisfies 1 <= n <= 100000, and for every integer i with 0 <= i < n, s[i] is ASCII code 97 ('a') or ASCII code 98 ('b'). -/
  theorem spec_15 (s : Slice Std.U8)
      (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
      (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
      (r : Std.I64) (hr : minimum_deletions s = ok r)
      (q : ℕ) (hq : q < len s) (hqb : byteAt s q = some 98)
      (hfirst : ∀ j : ℕ, j < q → byteAt s j ≠ some 98) :
      r.val ≤ (A s (q + 1) : ℤ) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice Std.U8)
        (hn : 1 ≤ len s) (hnle : len s ≤ 100000)
        (hab : ∀ i, i < len s → byteAt s i = some 97 ∨ byteAt s i = some 98)
        (r : Std.I64) (hr : minimum_deletions s = ok r)
        (q : ℕ) (hq : q < len s) (hqb : byteAt s q = some 98)
        (hfirst : ∀ j : ℕ, j < q → byteAt s j ≠ some 98), r.val ≤ (A s (q + 1) : ℤ)) := by
    sorry

  end AegisSpec.MinimumDeletions
