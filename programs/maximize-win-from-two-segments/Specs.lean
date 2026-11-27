import Aegis.MaximizeWin.Code.Funs

/-!
# Specifications of `Aegis.MaximizeWin.maximize_win`

LeetCode problem `maximize-win-from-two-segments`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximizeWin

def vals (p : Slice Std.I64) : List ℤ := p.val.map (fun x => x.val)

def InRange (xs : List ℤ) : Prop := ∀ x ∈ xs, 1 ≤ x ∧ x ≤ 1000000000

def SortedNondec (xs : List ℤ) : Prop := xs.Pairwise (· ≤ ·)

def countSeg (xs : List ℤ) (k a : ℤ) : ℕ :=
  (xs.filter (fun x => decide (a ≤ x ∧ x ≤ a + k))).length

def countTwo (xs : List ℤ) (k a b : ℤ) : ℕ :=
  (xs.filter (fun x => decide (a ≤ x ∧ x ≤ a + k ∨ b ≤ x ∧ x ≤ b + k))).length

def countEq (xs : List ℤ) (a b : ℤ) : ℕ :=
  (xs.filter (fun x => decide (x = a ∨ x = b))).length

def IsMaxOverAll (f : ℤ → ℕ) (m : ℕ) : Prop := (∀ a : ℤ, f a ≤ m) ∧ ∃ a : ℤ, f a = m

def IsMaxSplit (xs : List ℤ) (k : ℤ) (m : ℕ) : Prop :=
  (∀ (t : ℕ) (a b : ℤ), t ≤ xs.length →
      countSeg (xs.take t) k a + countSeg (xs.drop t) k b ≤ m) ∧
    (∃ (t : ℕ) (a b : ℤ), t ≤ xs.length ∧
      countSeg (xs.take t) k a + countSeg (xs.drop t) k b = m)

def ValidInput (p : Slice Std.I64) (k : Std.I64) : Prop :=
  1 ≤ (vals p).length ∧ (vals p).length ≤ 100000 ∧ InRange (vals p) ∧
    SortedNondec (vals p) ∧ 0 ≤ k.val ∧ k.val ≤ 1000000000

@[simp] theorem vals_length (p : Slice Std.I64) : (vals p).length = p.val.length := by
  simp [vals]

theorem countSeg_le_length (xs : List ℤ) (k a : ℤ) : countSeg xs k a ≤ xs.length := by
  simpa [countSeg] using
    List.length_filter_le (fun x => decide (a ≤ x ∧ x ≤ a + k)) xs

theorem countTwo_le_length (xs : List ℤ) (k a b : ℤ) : countTwo xs k a b ≤ xs.length := by
  simpa [countTwo] using
    List.length_filter_le (fun x => decide (a ≤ x ∧ x ≤ a + k ∨ b ≤ x ∧ x ≤ b + k)) xs

theorem countEq_le_length (xs : List ℤ) (a b : ℤ) : countEq xs a b ≤ xs.length := by
  simpa [countEq] using List.length_filter_le (fun x => decide (x = a ∨ x = b)) xs

/-- For integers a and b, let C(a,b) be the number of indices i with 0 <= i < n such that either a <= prizePositions[i] <= a+k or b <= prizePositions[i] <= b+k. A segment of length k with integer left endpoint a is the set of integers x with a <= x <= a+k. The function returns a result r and r = max over all integers a,b of C(a,b).
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_1 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∃ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r ∧
        (∀ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) ≤ r.val) ∧
        (∃ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∃ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r ∧
        (∀ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) ≤ r.val) ∧
        (∃ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) = r.val)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (the Lean value is Result.ok r for some integer r); it does not fail, overflow, panic, or access out of bounds.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_2 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∃ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∃ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= n.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_3 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r → r.val ≤ ((vals p).length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r → r.val ≤ ((vals p).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_4 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r → 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = max over all integers a,b of the number of indices i with 0 <= i < n such that prizePositions[i] = a or prizePositions[i] = b.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and k = 0. -/
theorem spec_5 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hk : k.val = 0) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        (∀ a b : ℤ, (countEq (vals p) a b : ℤ) ≤ r.val) ∧
          (∃ a b : ℤ, (countEq (vals p) a b : ℤ) = r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hk : k.val = 0), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        (∀ a b : ℤ, (countEq (vals p) a b : ℤ) ≤ r.val) ∧
          (∃ a b : ℤ, (countEq (vals p) a b : ℤ) = r.val)) := by
  sorry

/-- Whenever the function returns a result r, r = n.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. Additionally assume k >= prizePositions[n-1] - prizePositions[0]. -/
theorem spec_6 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hk : (vals p).getLastD 0 - (vals p).headD 0 ≤ k.val) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r → r.val = ((vals p).length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hk : (vals p).getLastD 0 - (vals p).headD 0 ≤ k.val), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r → r.val = ((vals p).length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = 2.
  Preconditions: Let n = len(prizePositions). Assume n = 2; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_7 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hn : (vals p).length = 2) :
    ∀ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r → r.val = 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hn : (vals p).length = 2), ∀ r : Std.I64, Aegis.MaximizeWin.maximize_win p k = ok r → r.val = 2) := by
  sorry

/-- Whenever the function returns a result r, r >= M.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. Define M = max over integers a of the number of indices i with a <= prizePositions[i] <= a+k. -/
theorem spec_8 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ M : ℕ, IsMaxOverAll (fun a => countSeg (vals p) k.val a) M → (M : ℤ) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ M : ℕ, IsMaxOverAll (fun a => countSeg (vals p) k.val a) M → (M : ℤ) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 2*M.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. Define M = max over integers a of the number of indices i with a <= prizePositions[i] <= a+k. -/
theorem spec_9 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ M : ℕ,
          IsMaxOverAll (fun a => countSeg (vals p) k.val a) M → r.val ≤ 2 * (M : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ M : ℕ,
          IsMaxOverAll (fun a => countSeg (vals p) k.val a) M → r.val ≤ 2 * (M : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = max over 0 <= t <= n of (L(t) + R(t)).
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. For 0 <= t <= n, define L(t) = max over integers a of the number of i with 0 <= i < t and a <= prizePositions[i] <= a+k, and R(t) = max over integers a of the number of i with t <= i < n and a <= prizePositions[i] <= a+k; for t=0 or t=n the empty maximum is 0. -/
theorem spec_10 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ m : ℕ, IsMaxSplit (vals p) k.val m → r.val = (m : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ m : ℕ, IsMaxSplit (vals p) k.val m → r.val = (m : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, there exist indices u and v with 0 <= u < n and 0 <= v < n such that r equals the number of indices i with 0 <= i < n satisfying prizePositions[u] <= prizePositions[i] <= prizePositions[u]+k or prizePositions[v] <= prizePositions[i] <= prizePositions[v]+k.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_11 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∃ (u v : ℕ) (pu pv : ℤ),
          u < (vals p).length ∧ v < (vals p).length ∧
            (vals p)[u]? = some pu ∧ (vals p)[v]? = some pv ∧
              r.val = (countTwo (vals p) k.val pu pv : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∃ (u v : ℕ) (pu pv : ℤ),
          u < (vals p).length ∧ v < (vals p).length ∧
            (vals p)[u]? = some pu ∧ (vals p)[v]? = some pv ∧
              r.val = (countTwo (vals p) k.val pu pv : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers a,b, C(a,b) <= r.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. For integers a,b, let C(a,b) be the number of indices i with 0 <= i < n such that a <= prizePositions[i] <= a+k or b <= prizePositions[i] <= b+k. -/
theorem spec_12 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        ∀ a b : ℤ, (countTwo (vals p) k.val a b : ℤ) ≤ r.val) := by
  sorry

/-- Let p'_i = prizePositions[i] + c for 0 <= i < n. If maximize_win(prizePositions,k) returns r and maximize_win(p',k) returns r', then r = r'.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. Let c be an integer such that 1 <= prizePositions[i] + c <= 1000000000 for every i. -/
theorem spec_13 (p q : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) (c : ℤ)
    (hrange : ∀ x ∈ vals p, 1 ≤ x + c ∧ x + c ≤ 1000000000)
    (hq : vals q = (vals p).map (fun x => x + c)) :
    ∀ r r' : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        Aegis.MaximizeWin.maximize_win q k = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (p q : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) (c : ℤ)
    (hrange : ∀ x ∈ vals p, 1 ≤ x + c ∧ x + c ≤ 1000000000)
    (hq : vals q = (vals p).map (fun x => x + c)), ∀ r r' : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        Aegis.MaximizeWin.maximize_win q k = ok r' → r.val = r'.val) := by
  sorry

/-- If maximize_win(prizePositions,k1) returns r1 and maximize_win(prizePositions,k2) returns r2, then r1 <= r2.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k1 <= k2 <= 1000000000. -/
theorem spec_14 (p : Slice Std.I64) (k1 k2 : Std.I64) (h : ValidInput p k2)
    (hk1 : 0 ≤ k1.val) (hle : k1.val ≤ k2.val) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaximizeWin.maximize_win p k1 = ok r1 →
        Aegis.MaximizeWin.maximize_win p k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (p : Slice Std.I64) (k1 k2 : Std.I64) (h : ValidInput p k2)
    (hk1 : 0 ≤ k1.val) (hle : k1.val ≤ k2.val), ∀ r1 r2 : Std.I64,
      Aegis.MaximizeWin.maximize_win p k1 = ok r1 →
        Aegis.MaximizeWin.maximize_win p k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Let C = prizePositions[0] + prizePositions[n-1] and define q_i = C - prizePositions[n-1-i] for 0 <= i < n. If maximize_win(prizePositions,k) returns r and maximize_win(q,k) returns r', then r = r'.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_15 (p q : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hq : vals q =
      (vals p).reverse.map (fun x => ((vals p).headD 0 + (vals p).getLastD 0) - x)) :
    ∀ r r' : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        Aegis.MaximizeWin.maximize_win q k = ok r' → r.val = r'.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (p q : Slice Std.I64) (k : Std.I64) (h : ValidInput p k)
    (hq : vals q =
      (vals p).reverse.map (fun x => ((vals p).headD 0 + (vals p).getLastD 0) - x)), ∀ r r' : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        Aegis.MaximizeWin.maximize_win q k = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if there exist integers a and b such that for every i with 0 <= i < n, either a <= prizePositions[i] <= a+k or b <= prizePositions[i] <= b+k.
  Preconditions: Let n = len(prizePositions). Assume 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= prizePositions[i] <= 1000000000; prizePositions is sorted non-decreasing; and 0 <= k <= 1000000000. -/
theorem spec_16 (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k) :
    ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        (r.val = ((vals p).length : ℤ) ↔
          ∃ a b : ℤ,
            ∀ x ∈ vals p, (a ≤ x ∧ x ≤ a + k.val) ∨ (b ≤ x ∧ x ≤ b + k.val)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (p : Slice Std.I64) (k : Std.I64) (h : ValidInput p k), ∀ r : Std.I64,
      Aegis.MaximizeWin.maximize_win p k = ok r →
        (r.val = ((vals p).length : ℤ) ↔
          ∃ a b : ℤ,
            ∀ x ∈ vals p, (a ≤ x ∧ x ≤ a + k.val) ∨ (b ≤ x ∧ x ≤ b + k.val))) := by
  sorry

end AegisSpec.MaximizeWin
