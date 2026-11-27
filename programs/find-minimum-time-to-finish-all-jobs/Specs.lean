import Aegis.MinimumTimeRequired.Code.Funs

/-!
# Specifications of `Aegis.MinimumTimeRequired.minimum_time_required`

LeetCode problem `find-minimum-time-to-finish-all-jobs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumTimeRequired

  def jobTimes (jobs : Slice Std.I64) : List ℤ := jobs.val.map (fun x => x.val)

  def totalTime (js : List ℤ) : ℤ := js.sum

  def maxJob (js : List ℤ) : ℤ := (js.max?).getD 0

  def minJob (js : List ℤ) : ℤ := (js.min?).getD 0

  def ceilDiv (n k : ℕ) : ℕ := (n + k - 1) / k

  def IsAssignment (n k : ℕ) (A : ℕ → ℕ) : Prop := ∀ i, i < n → A i < k

  def load (js : List ℤ) (A : ℕ → ℕ) (w : ℕ) : ℤ :=
    ((List.finRange js.length).map (fun i => if A i.val = w then js.get i else 0)).sum

  def maxLoad (js : List ℤ) (k : ℕ) (A : ℕ → ℕ) : ℤ :=
    ((List.range k).map (fun w => load js A w)).max?.getD 0

  def allAssignments : ℕ → ℕ → List (ℕ → ℕ)
    | 0, _ => [fun _ => 0]
    | n + 1, k =>
      (List.range k).flatMap (fun w =>
        (allAssignments n k).map (fun A i => if i = n then w else A i))

  def minMaxLoad (js : List ℤ) (n k : ℕ) : ℤ :=
    ((allAssignments n k).map (fun A => maxLoad js k A)).min?.getD 0

  def IsIndexPermutation (n : ℕ) (pi : ℕ → ℕ) : Prop :=
    (∀ i, i < n → pi i < n) ∧ ((List.range n).map pi).Nodup

  def permuteJobs (js : List ℤ) (pi : ℕ → ℕ) : List ℤ :=
    (List.finRange js.length).map (fun i => js.getD (pi i.val) 0)

  /-- Let an assignment be any function A from {0,...,len(jobs)-1} to {0,...,k-1}. For a worker w with 0 <= w < k, define load(A,w) = sum of jobs[i] over all i with A(i)=w, using the empty sum 0 if no job is assigned to w, and define maxload(A) = max over 0 <= w < k of load(A,w). The function returns a result r and r = min over all assignments A of maxload(A).
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_1 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∃ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r ∧
        r.val = minMaxLoad (jobTimes jobs) jobs.val.length k.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∃ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r ∧
          r.val = minMaxLoad (jobTimes jobs) jobs.val.length k.val.toNat) := by
    sorry

  /-- The function returns a result r and does not fail, overflow, panic, access out of bounds, or otherwise produce an error.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_2 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∃ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∃ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(jobs), r >= jobs[i]. Equivalently, r is at least the largest job time.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_3 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        ∀ (i : ℕ) (hi : i < jobs.val.length),
          r.val ≥ (jobs.val.get ⟨i, hi⟩).val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          ∀ (i : ℕ) (hi : i < jobs.val.length),
            r.val ≥ (jobs.val.get ⟨i, hi⟩).val) := by
    sorry

  /-- Whenever the function returns a result r, k * r >= sum_{i=0}^{len(jobs)-1} jobs[i].
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_4 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        k.val * r.val ≥ totalTime (jobTimes jobs) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          k.val * r.val ≥ totalTime (jobTimes jobs)) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_{i=0}^{len(jobs)-1} jobs[i].
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_5 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        r.val ≤ totalTime (jobTimes jobs) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          r.val ≤ totalTime (jobTimes jobs)) := by
    sorry

  /-- Let M = max_{0 <= i < len(jobs)} jobs[i], and let m be the least integer such that m * k >= len(jobs). Whenever the function returns a result r, r <= m * M.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_6 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        r.val ≤ (ceilDiv jobs.val.length k.val.toNat : ℤ) * maxJob (jobTimes jobs) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          r.val ≤ (ceilDiv jobs.val.length k.val.toNat : ℤ) * maxJob (jobTimes jobs)) := by
    sorry

  /-- Whenever the function returns a result r, there exists an assignment A from {0,...,len(jobs)-1} to {0,...,k-1} such that, defining load(A,w) as the sum of jobs[i] over all i with A(i)=w (empty sum 0), max_{0 <= w < k} load(A,w) = r.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_7 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        ∃ A : ℕ → ℕ,
          IsAssignment jobs.val.length k.val.toNat A ∧
            maxLoad (jobTimes jobs) k.val.toNat A = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          ∃ A : ℕ → ℕ,
            IsAssignment jobs.val.length k.val.toNat A ∧
              maxLoad (jobTimes jobs) k.val.toNat A = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every assignment A from {0,...,len(jobs)-1} to {0,...,k-1}, if load(A,w) is the sum of jobs[i] over all i with A(i)=w (empty sum 0), then max_{0 <= w < k} load(A,w) >= r.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_8 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        ∀ A : ℕ → ℕ, IsAssignment jobs.val.length k.val.toNat A →
          maxLoad (jobTimes jobs) k.val.toNat A ≥ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          ∀ A : ℕ → ℕ, IsAssignment jobs.val.length k.val.toNat A →
            maxLoad (jobTimes jobs) k.val.toNat A ≥ r.val) := by
    sorry

  /-- Let s = sum_{i=0}^{len(jobs)-1} jobs[i] and let m = min_{0 <= i < len(jobs)} jobs[i]. Whenever the function returns a result r, r <= s - (k - 1) * m.
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_9 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        r.val ≤ totalTime (jobTimes jobs) - (k.val - 1) * minJob (jobTimes jobs) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          r.val ≤ totalTime (jobTimes jobs) - (k.val - 1) * minJob (jobTimes jobs)) := by
    sorry

  /-- Whenever the function returns a result r, for every permutation pi of the index set {0,...,len(jobs)-1}, r is equal to the minimum over all assignments A from {0,...,len(jobs)-1} to {0,...,k-1} of max_{0 <= w < k} (sum of jobs[pi(i)] over all i with A(i)=w).
    Preconditions: len(jobs) >= 1, 1 <= k <= len(jobs) <= 12, and for every i with 0 <= i < len(jobs), 1 <= jobs[i] <= 10^7. -/
  theorem spec_10 (jobs : Slice Std.I64) (k : Std.I64)
      (hlen : 1 ≤ jobs.val.length)
      (hk1 : 1 ≤ k.val)
      (hkle : k.val ≤ (jobs.val.length : ℤ))
      (hlen12 : jobs.val.length ≤ 12)
      (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
        1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000) :
      ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
        ∀ pi : ℕ → ℕ, IsIndexPermutation jobs.val.length pi →
          r.val = minMaxLoad (permuteJobs (jobTimes jobs) pi) jobs.val.length k.val.toNat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (jobs : Slice Std.I64) (k : Std.I64)
        (hlen : 1 ≤ jobs.val.length)
        (hk1 : 1 ≤ k.val)
        (hkle : k.val ≤ (jobs.val.length : ℤ))
        (hlen12 : jobs.val.length ≤ 12)
        (hjobs : ∀ (i : ℕ) (hi : i < jobs.val.length),
          1 ≤ (jobs.val.get ⟨i, hi⟩).val ∧ (jobs.val.get ⟨i, hi⟩).val ≤ 10000000), ∀ r, Aegis.MinimumTimeRequired.minimum_time_required jobs k = ok r →
          ∀ pi : ℕ → ℕ, IsIndexPermutation jobs.val.length pi →
            r.val = minMaxLoad (permuteJobs (jobTimes jobs) pi) jobs.val.length k.val.toNat) := by
    sorry

end AegisSpec.MinimumTimeRequired
