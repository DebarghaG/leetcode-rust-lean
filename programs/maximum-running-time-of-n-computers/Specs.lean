import Aegis.MaxRunTime.Code.Funs

/-!
# Specifications of `Aegis.MaxRunTime.max_run_time`

LeetCode problem `maximum-running-time-of-n-computers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxRunTime

  def sliceSum (batteries : Slice Std.I64) : ℤ :=
    (batteries.val.map (fun b => b.val)).sum

  def cappedSum (batteries : Slice Std.I64) (T : ℤ) : ℤ :=
    (batteries.val.map (fun b => min b.val T)).sum

  def sliceMin (batteries : Slice Std.I64) : ℤ :=
    match batteries.val with
    | [] => 0
    | b :: bs => bs.foldr (fun x acc => min x.val acc) b.val

  def sliceMax (batteries : Slice Std.I64) : ℤ :=
    match batteries.val with
    | [] => 0
    | b :: bs => bs.foldr (fun x acc => max x.val acc) b.val

  def usageCount (n T b : ℕ) (batt : ℕ → ℕ → ℕ) : ℕ :=
    (((Finset.range T).product (Finset.range n)).filter (fun p => batt p.1 p.2 = b)).card

  def IsSchedule (caps : List ℤ) (n T : ℕ) (batt : ℕ → ℕ → ℕ) : Prop :=
    (∀ (t c : ℕ), t < T → c < n → batt t c < caps.length) ∧
      (∀ (t c₁ c₂ : ℕ), t < T → c₁ < n → c₂ < n → batt t c₁ = batt t c₂ → c₁ = c₂) ∧
        (∀ (b : ℕ) (hb : b < caps.length),
          (usageCount n T b batt : ℤ) ≤ caps.get ⟨b, hb⟩)

  /-- The function returns a result r (it does not fail), and r is the greatest integer T such that T >= 0 and n*T <= sum_{i=0}^{len(batteries)-1} min(batteries[i], T).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_1 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r ∧
          0 ≤ r.val ∧ n.val * r.val ≤ cappedSum batteries r.val ∧
            ∀ T : ℤ, 0 ≤ T → n.val * T ≤ cappedSum batteries T → T ≤ r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r ∧
            0 ≤ r.val ∧ n.val * r.val ≤ cappedSum batteries r.val ∧
              ∀ T : ℤ, 0 ≤ T → n.val * T ≤ cappedSum batteries T → T ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r and n*r <= sum_{i=0}^{len(batteries)-1} batteries[i]; equivalently, r <= floor((sum_{i=0}^{len(batteries)-1} batteries[i]) / n).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_2 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          0 ≤ r.val ∧ n.val * r.val ≤ sliceSum batteries ∧
            r.val ≤ sliceSum batteries / n.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            0 ≤ r.val ∧ n.val * r.val ≤ sliceSum batteries ∧
              r.val ≤ sliceSum batteries / n.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_3 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64, Aegis.MaxRunTime.max_run_time n batteries = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64, Aegis.MaxRunTime.max_run_time n batteries = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a schedule that runs all n computers simultaneously for the full interval of r minutes starting at time 0; in that schedule every computer is powered at every moment, every computer uses at most one battery at any moment, every battery i is used for at most batteries[i] minutes in total, and no battery is used by two different computers at the same moment.
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_4 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          ∃ batt : ℕ → ℕ → ℕ,
            IsSchedule (batteries.val.map (fun b => b.val)) n.val.toNat r.val.toNat batt := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            ∃ batt : ℕ → ℕ → ℕ,
              IsSchedule (batteries.val.map (fun b => b.val)) n.val.toNat r.val.toNat batt) := by
    sorry

  /-- Whenever the function returns a result r, for every integer T with T > r, there is no schedule that runs all n computers simultaneously for T minutes under the rules that every computer uses at most one battery at any moment, every battery i is used for at most batteries[i] minutes in total, and no battery is used by two different computers at the same moment.
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_5 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          ∀ T : ℤ,
            r.val < T →
              ¬∃ batt : ℕ → ℕ → ℕ,
                IsSchedule (batteries.val.map (fun b => b.val)) n.val.toNat T.toNat batt := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            ∀ T : ℤ,
              r.val < T →
                ¬∃ batt : ℕ → ℕ → ℕ,
                  IsSchedule (batteries.val.map (fun b => b.val)) n.val.toNat T.toNat batt) := by
    sorry

  /-- Whenever the function returns a result r and n = 1, r = sum_{i=0}^{len(batteries)-1} batteries[i].
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_6 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          n.val = 1 → r.val = sliceSum batteries := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            n.val = 1 → r.val = sliceSum batteries) := by
    sorry

  /-- Whenever the function returns a result r and n = len(batteries), r = min_{0 <= i < len(batteries)} batteries[i].
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_7 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          n.val = (batteries.val.length : ℤ) → r.val = sliceMin batteries := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            n.val = (batteries.val.length : ℤ) → r.val = sliceMin batteries) := by
    sorry

  /-- Whenever the function returns a result r and there exists an integer c such that batteries[i] = c for every i with 0 <= i < len(batteries), we have r = floor((len(batteries) * c) / n).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_8 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ (r : Std.I64) (c : ℤ),
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          (∀ b ∈ batteries.val, b.val = c) →
            r.val = (batteries.val.length : ℤ) * c / n.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ (r : Std.I64) (c : ℤ),
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            (∀ b ∈ batteries.val, b.val = c) →
              r.val = (batteries.val.length : ℤ) * c / n.val) := by
    sorry

  /-- Whenever the function returns a result r and n = 2, r = min(floor((sum_{i=0}^{len(batteries)-1} batteries[i]) / 2), (sum_{i=0}^{len(batteries)-1} batteries[i]) - max_{0 <= i < len(batteries)} batteries[i]).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_9 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          n.val = 2 →
            r.val = min (sliceSum batteries / 2) (sliceSum batteries - sliceMax batteries) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            n.val = 2 →
              r.val = min (sliceSum batteries / 2) (sliceSum batteries - sliceMax batteries)) := by
    sorry

  /-- If the call max_run_time(n1, batteries) returns r1 and the call max_run_time(n2, batteries) returns r2, then r2 <= r1.
    Preconditions: batteries is a list with 1 <= len(batteries) <= 100000 and 1 <= batteries[i] <= 1000000000 for every 0 <= i < len(batteries); n1 and n2 are integers with 1 <= n1 <= n2 <= len(batteries). -/
  theorem spec_10 (n1 n2 : Std.I64) (batteries : Slice Std.I64)
      (hlen1 : 1 ≤ batteries.val.length) (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
      (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val)
      (hn2 : n2.val ≤ (batteries.val.length : ℤ)) :
      ∀ r1 r2 : Std.I64,
        Aegis.MaxRunTime.max_run_time n1 batteries = ok r1 →
          Aegis.MaxRunTime.max_run_time n2 batteries = ok r2 → r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n1 n2 : Std.I64) (batteries : Slice Std.I64)
        (hlen1 : 1 ≤ batteries.val.length) (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
        (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val)
        (hn2 : n2.val ≤ (batteries.val.length : ℤ)), ∀ r1 r2 : Std.I64,
          Aegis.MaxRunTime.max_run_time n1 batteries = ok r1 →
            Aegis.MaxRunTime.max_run_time n2 batteries = ok r2 → r2.val ≤ r1.val) := by
    sorry

  /-- If max_run_time(n, batteries) returns r and max_run_time(n, batteries2) returns r2, then r <= r2.
    Preconditions: batteries and batteries2 are lists of the same length m with 1 <= n <= m <= 100000, and for every i with 0 <= i < m, 1 <= batteries[i] <= batteries2[i] <= 1000000000. -/
  theorem spec_11 (n : Std.I64) (batteries batteries2 : Slice Std.I64) (m : ℕ)
      (hm1 : 1 ≤ m) (hmle : m ≤ 100000)
      (hlen1 : batteries.val.length = m) (hlen2 : batteries2.val.length = m)
      (hn1 : 1 ≤ n.val) (hnm : n.val ≤ (m : ℤ))
      (hbound : ∀ (i : ℕ), i < m → 1 ≤ (batteries.val[i]!).val ∧
        (batteries.val[i]!).val ≤ (batteries2.val[i]!).val ∧
          (batteries2.val[i]!).val ≤ 1000000000) :
      ∀ r r2 : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          Aegis.MaxRunTime.max_run_time n batteries2 = ok r2 → r.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (batteries batteries2 : Slice Std.I64) (m : ℕ)
        (hm1 : 1 ≤ m) (hmle : m ≤ 100000)
        (hlen1 : batteries.val.length = m) (hlen2 : batteries2.val.length = m)
        (hn1 : 1 ≤ n.val) (hnm : n.val ≤ (m : ℤ))
        (hbound : ∀ (i : ℕ), i < m → 1 ≤ (batteries.val[i]!).val ∧
          (batteries.val[i]!).val ≤ (batteries2.val[i]!).val ∧
            (batteries2.val[i]!).val ≤ 1000000000), ∀ r r2 : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            Aegis.MaxRunTime.max_run_time n batteries2 = ok r2 → r.val ≤ r2.val) := by
    sorry

  /-- If max_run_time(n, batteries) returns r and max_run_time(n, batteries2) returns r2, then r = r2.
    Preconditions: batteries and batteries2 are lists of the same length m with 1 <= n <= m <= 100000 and all entries in the range 1..1000000000; batteries2 is a permutation of batteries (the same multiset of values). -/
  theorem spec_12 (n : Std.I64) (batteries batteries2 : Slice Std.I64) (m : ℕ)
      (hm1 : 1 ≤ m) (hmle : m ≤ 100000)
      (hlen1 : batteries.val.length = m) (hlen2 : batteries2.val.length = m)
      (hn1 : 1 ≤ n.val) (hnm : n.val ≤ (m : ℤ))
      (hbound1 : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
      (hbound2 : ∀ b ∈ batteries2.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
        (hperm : List.Perm (batteries.val.map (fun b => b.val))
          (batteries2.val.map (fun b => b.val))) :
      ∀ r r2 : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          Aegis.MaxRunTime.max_run_time n batteries2 = ok r2 → r.val = r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (batteries batteries2 : Slice Std.I64) (m : ℕ)
        (hm1 : 1 ≤ m) (hmle : m ≤ 100000)
        (hlen1 : batteries.val.length = m) (hlen2 : batteries2.val.length = m)
        (hn1 : 1 ≤ n.val) (hnm : n.val ≤ (m : ℤ))
        (hbound1 : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
        (hbound2 : ∀ b ∈ batteries2.val, 1 ≤ b.val ∧ b.val ≤ 1000000000)
          (hperm : List.Perm (batteries.val.map (fun b => b.val))
            (batteries2.val.map (fun b => b.val))), ∀ r r2 : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            Aegis.MaxRunTime.max_run_time n batteries2 = ok r2 → r.val = r2.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer T with 0 <= T <= r, n*T <= sum_{i=0}^{len(batteries)-1} min(batteries[i], T).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_13 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          ∀ T : ℤ, 0 ≤ T → T ≤ r.val → n.val * T ≤ cappedSum batteries T := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            ∀ T : ℤ, 0 ≤ T → T ≤ r.val → n.val * T ≤ cappedSum batteries T) := by
    sorry

  /-- Whenever the function returns a result r, n*(r+1) > sum_{i=0}^{len(batteries)-1} min(batteries[i], r+1).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_14 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          n.val * (r.val + 1) > cappedSum batteries (r.val + 1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            n.val * (r.val + 1) > cappedSum batteries (r.val + 1)) := by
    sorry

  /-- Whenever the function returns a result r, r >= min_{0 <= i < len(batteries)} batteries[i].
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), batteries[i] is an integer with 1 <= batteries[i] <= 1000000000. -/
  theorem spec_15 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r → sliceMin batteries ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r → sliceMin batteries ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = floor(S/n).
    Preconditions: n is an integer with 1 <= n <= len(batteries) <= 100000, and for every i with 0 <= i < len(batteries), 1 <= batteries[i] <= 1000000000. Let S = sum_{i=0}^{len(batteries)-1} batteries[i] and M = max_{0 <= i < len(batteries)} batteries[i], and assume M <= floor(S/n). -/
  theorem spec_16 (n : Std.I64) (batteries : Slice Std.I64)
      (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
      (hlen : batteries.val.length ≤ 100000)
      (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.MaxRunTime.max_run_time n batteries = ok r →
          sliceMax batteries ≤ sliceSum batteries / n.val →
            r.val = sliceSum batteries / n.val := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : Std.I64) (batteries : Slice Std.I64)
        (hn1 : 1 ≤ n.val) (hnle : n.val ≤ (batteries.val.length : ℤ))
        (hlen : batteries.val.length ≤ 100000)
        (hbound : ∀ b ∈ batteries.val, 1 ≤ b.val ∧ b.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.MaxRunTime.max_run_time n batteries = ok r →
            sliceMax batteries ≤ sliceSum batteries / n.val →
              r.val = sliceSum batteries / n.val) := by
    sorry

  end AegisSpec.MaxRunTime
