import Aegis.MinSkips.Code.Funs

/-!
# Specifications of `Aegis.MinSkips.min_skips`

LeetCode problem `minimum-skips-to-arrive-at-meeting-on-time`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSkips

  set_option autoImplicit false

  noncomputable def arrivalAux (s : ℤ) (S : Finset ℕ) : ℕ → ℚ → List Std.I64 → ℚ
    | _, tau, [] => tau
    | _, tau, [d] => tau + (d.val : ℚ) / (s : ℚ)
    | i, tau, d :: d' :: rest =>
        let tau' : ℚ := tau + (d.val : ℚ) / (s : ℚ)
        let tau'' : ℚ := if i ∈ S then tau' else ((Rat.ceil tau' : ℤ) : ℚ)
        arrivalAux s S (i + 1) tau'' (d' :: rest)

  noncomputable def arrival (dist : Slice Std.I64) (s : ℤ) (S : Finset ℕ) : ℚ :=
    arrivalAux s S 0 0 dist.val

  def restSet (dist : Slice Std.I64) : Finset ℕ :=
    Finset.range (dist.val.length - 1)

  noncomputable def Feasible (dist : Slice Std.I64) (s H : ℤ) (S : Finset ℕ) : Prop :=
    S ⊆ restSet dist ∧ arrival dist s S ≤ (H : ℚ)

  def totalDist (dist : Slice Std.I64) : ℤ :=
    (dist.val.map (fun x => x.val)).sum

  /-- Let n = len(dist), s = speed, H = hoursBefore. For a subset S of {0,1,...,n-2}, let A(S) be the arrival time when exactly the rests indexed by S are skipped, defined as follows. Set tau = 0. For i = 0,1,...,n-1: set tau := tau + dist[i]/s, where division is exact real division; if i < n-1 and i is not in S, set tau := ceil(tau), where ceil(x) is the least integer >= x; if i < n-1 and i is in S, leave tau unchanged. After processing i = n-1, A(S) is the final value of tau. The function returns a result r, and: if there exists S subset of {0,1,...,n-2} with A(S) <= H, then r = min { |S| : S subset of {0,1,...,n-2} and A(S) <= H }; otherwise r = -1.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_1 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000) :
      ∃ r : Std.I64,
        Aegis.MinSkips.min_skips dist speed hoursBefore = ok r ∧
          ((∃ S : Finset ℕ, Feasible dist speed.val hoursBefore.val S ∧
              r.val = (S.card : ℤ) ∧
              ∀ S' : Finset ℕ, Feasible dist speed.val hoursBefore.val S' →
                S.card ≤ S'.card) ∨
            (r.val = -1 ∧ ∀ S : Finset ℕ, ¬ Feasible dist speed.val hoursBefore.val S)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000), ∃ r : Std.I64,
          Aegis.MinSkips.min_skips dist speed hoursBefore = ok r ∧
            ((∃ S : Finset ℕ, Feasible dist speed.val hoursBefore.val S ∧
                r.val = (S.card : ℤ) ∧
                ∀ S' : Finset ℕ, Feasible dist speed.val hoursBefore.val S' →
                  S.card ≤ S'.card) ∨
              (r.val = -1 ∧ ∀ S : Finset ℕ, ¬ Feasible dist speed.val hoursBefore.val S))) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_2 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000) :
      ∃ r : Std.I64, Aegis.MinSkips.min_skips dist speed hoursBefore = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000), ∃ r : Std.I64, Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) := by
    sorry

  /-- When the function returns a result r, either r = -1 or 0 <= r <= n-1, where n = len(dist).
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_3 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) :
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r), r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1)) := by
    sorry

  /-- When the function returns a result r, r = -1 if and only if sum_{i=0}^{n-1} dist[i] > hoursBefore * speed, where n = len(dist).
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_4 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) :
      (r.val = -1 ↔ totalDist dist > hoursBefore.val * speed.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r), (r.val = -1 ↔ totalDist dist > hoursBefore.val * speed.val)) := by
    sorry

  /-- Let n = len(dist), s = speed, H = hoursBefore, and let A(empty) be the arrival time when no rests are skipped, computed by the recurrence in the main specification with S = empty. When the function returns a result r, r = 0 if and only if A(empty) <= H.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_5 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) :
      (r.val = 0 ↔ arrival dist speed.val ∅ ≤ (hoursBefore.val : ℚ)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r), (r.val = 0 ↔ arrival dist speed.val ∅ ≤ (hoursBefore.val : ℚ))) := by
    sorry

  /-- Let n = len(dist), s = speed, H = hoursBefore, and define A(S) as in the main specification. When the function returns a result r and r >= 0, there exists a subset S of {0,1,...,n-2} such that |S| = r and A(S) <= H.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_6 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r)
      (hr_nonneg : 0 ≤ r.val) :
      ∃ S : Finset ℕ, Feasible dist speed.val hoursBefore.val S ∧ r.val = (S.card : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r)
        (hr_nonneg : 0 ≤ r.val), ∃ S : Finset ℕ, Feasible dist speed.val hoursBefore.val S ∧ r.val = (S.card : ℤ)) := by
    sorry

  /-- Let n = len(dist), s = speed, H = hoursBefore, and define A(S) as in the main specification. When the function returns a result r and r >= 0, for every subset S of {0,1,...,n-2} with |S| < r, we have A(S) > H.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_7 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r)
      (hr_nonneg : 0 ≤ r.val) :
      ∀ S : Finset ℕ, S ⊆ restSet dist → (S.card : ℤ) < r.val →
        (hoursBefore.val : ℚ) < arrival dist speed.val S := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r)
        (hr_nonneg : 0 ≤ r.val), ∀ S : Finset ℕ, S ⊆ restSet dist → (S.card : ℤ) < r.val →
          (hoursBefore.val : ℚ) < arrival dist speed.val S) := by
    sorry

  /-- If n = len(dist) = 1, then when the function returns a result r, r = 0 if dist[0] <= hoursBefore * speed, and r = -1 if dist[0] > hoursBefore * speed.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_8 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (hn_one : n = 1)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) :
      ((dist.val.get ⟨0, by omega⟩).val ≤ hoursBefore.val * speed.val → r.val = 0) ∧
        (hoursBefore.val * speed.val < (dist.val.get ⟨0, by omega⟩).val → r.val = -1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (hn_one : n = 1)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r), ((dist.val.get ⟨0, by omega⟩).val ≤ hoursBefore.val * speed.val → r.val = 0) ∧
          (hoursBefore.val * speed.val < (dist.val.get ⟨0, by omega⟩).val → r.val = -1)) := by
    sorry

  /-- Let n = len(dist), s = speed, H = hoursBefore, define A(S) as in the main specification, and let S_all = {0,1,...,n-2}. When the function returns a result r, r = n-1 if and only if A(S_all) <= H and for every subset S of {0,1,...,n-2} with |S| < n-1, A(S) > H.
    Preconditions: n = len(dist); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= dist[i] <= 100000; 1 <= speed <= 1000000; 1 <= hoursBefore <= 10000000. All integers are 64-bit signed integers within the stated ranges. -/
  theorem spec_9 (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
      (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r) :
      (r.val = (n : ℤ) - 1 ↔
        arrival dist speed.val (restSet dist) ≤ (hoursBefore.val : ℚ) ∧
          ∀ S : Finset ℕ, S ⊆ restSet dist → S.card < n - 1 →
            (hoursBefore.val : ℚ) < arrival dist speed.val S) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed hoursBefore : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (hhours_pos : 1 ≤ hoursBefore.val) (hhours_le : hoursBefore.val ≤ 10000000)
        (r : Std.I64) (hr : Aegis.MinSkips.min_skips dist speed hoursBefore = ok r), (r.val = (n : ℤ) - 1 ↔
          arrival dist speed.val (restSet dist) ≤ (hoursBefore.val : ℚ) ∧
            ∀ S : Finset ℕ, S ⊆ restSet dist → S.card < n - 1 →
              (hoursBefore.val : ℚ) < arrival dist speed.val S)) := by
    sorry

  /-- Let r(H) denote the result of min_skips(dist, speed, H) for H in [1, 10000000]. When both calls min_skips(dist, speed, H1) and min_skips(dist, speed, H2) return results r1 and r2, either r1 = -1, or (r2 != -1 and r2 <= r1).
    Preconditions: dist is a slice of n Int64 values with n = len(dist), 1 <= n <= 1000, and 1 <= dist[i] <= 100000 for every 0 <= i < n; speed is an integer with 1 <= speed <= 1000000; H1 and H2 are integers with 1 <= H1 <= H2 <= 10000000. -/
  theorem spec_10 (dist : Slice Std.I64) (speed H1 H2 : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hH1_pos : 1 ≤ H1.val) (hH12 : H1.val ≤ H2.val) (hH2_le : H2.val ≤ 10000000)
      (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
      (r1 r2 : Std.I64)
      (hr1 : Aegis.MinSkips.min_skips dist speed H1 = ok r1)
      (hr2 : Aegis.MinSkips.min_skips dist speed H2 = ok r2) :
      r1.val = -1 ∨ (r2.val ≠ -1 ∧ r2.val ≤ r1.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (dist : Slice Std.I64) (speed H1 H2 : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hH1_pos : 1 ≤ H1.val) (hH12 : H1.val ≤ H2.val) (hH2_le : H2.val ≤ 10000000)
        (hspeed_pos : 1 ≤ speed.val) (hspeed_le : speed.val ≤ 1000000)
        (r1 r2 : Std.I64)
        (hr1 : Aegis.MinSkips.min_skips dist speed H1 = ok r1)
        (hr2 : Aegis.MinSkips.min_skips dist speed H2 = ok r2), r1.val = -1 ∨ (r2.val ≠ -1 ∧ r2.val ≤ r1.val)) := by
    sorry

  /-- Let r(s) denote the result of min_skips(dist, s, H) for s in [1, 1000000]. When both calls min_skips(dist, s1, H) and min_skips(dist, s2, H) return results r1 and r2, either r1 = -1, or (r2 != -1 and r2 <= r1).
    Preconditions: dist is a slice of n Int64 values with n = len(dist), 1 <= n <= 1000, and 1 <= dist[i] <= 100000 for every 0 <= i < n; H is an integer with 1 <= H <= 10000000; s1 and s2 are integers with 1 <= s1 <= s2 <= 1000000. -/
  theorem spec_11 (dist : Slice Std.I64) (H s1 s2 : Std.I64) (n : ℕ)
      (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
      (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hH_pos : 1 ≤ H.val) (hH_le : H.val ≤ 10000000)
      (hs1_pos : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2_le : s2.val ≤ 1000000)
      (r1 r2 : Std.I64)
      (hr1 : Aegis.MinSkips.min_skips dist s1 H = ok r1)
      (hr2 : Aegis.MinSkips.min_skips dist s2 H = ok r2) :
      r1.val = -1 ∨ (r2.val ≠ -1 ∧ r2.val ≤ r1.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (dist : Slice Std.I64) (H s1 s2 : Std.I64) (n : ℕ)
        (hn_len : n = dist.val.length) (hn_pos : 1 ≤ n) (hn_le : n ≤ 1000)
        (hdist : ∀ x ∈ dist.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hH_pos : 1 ≤ H.val) (hH_le : H.val ≤ 10000000)
        (hs1_pos : 1 ≤ s1.val) (hs12 : s1.val ≤ s2.val) (hs2_le : s2.val ≤ 1000000)
        (r1 r2 : Std.I64)
        (hr1 : Aegis.MinSkips.min_skips dist s1 H = ok r1)
        (hr2 : Aegis.MinSkips.min_skips dist s2 H = ok r2), r1.val = -1 ∨ (r2.val ≠ -1 ∧ r2.val ≤ r1.val)) := by
    sorry

  end AegisSpec.MinSkips
