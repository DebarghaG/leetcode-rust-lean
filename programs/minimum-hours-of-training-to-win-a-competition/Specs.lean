import Aegis.MinNumberOfHours.Code.Funs

/-!
# Specifications of `Aegis.MinNumberOfHours.min_number_of_hours`

LeetCode problem `minimum-hours-of-training-to-win-a-competition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinNumberOfHours

  def ints (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def entry (s : Slice Std.I64) (i : ℕ) : ℤ :=
    match s.val[i]? with
    | none => 0
    | some x => x.val

  def prefixSum (s : Slice Std.I64) (i : ℕ) : ℤ := ((s.val.take i).map (fun x => x.val)).sum

  def totalSum (s : Slice Std.I64) : ℤ := (ints s).sum

  def rangeMax (n : ℕ) (f : ℕ → ℤ) : ℤ :=
    match (List.range n).map f with
    | [] => 0
    | a :: t => t.foldr max a

  def energyNeed (initialEnergy : ℤ) (energy : Slice Std.I64) : ℤ :=
    max 0 (totalSum energy + 1 - initialEnergy)

  def expNeed (initialExperience : ℤ) (experience : Slice Std.I64) (n : ℕ) : ℤ :=
    max 0 (rangeMax n
      (fun i => entry experience i + 1 - initialExperience - prefixSum experience i))

  theorem entry_eq (s : Slice Std.I64) (i : ℕ) (h : i < s.val.length) :
      entry s i = (s.val[i]'h).val := by
    unfold entry
    simp [h]

  theorem prefixSum_zero (s : Slice Std.I64) : prefixSum s 0 = 0 := by
    simp [prefixSum]

  theorem prefixSum_length (s : Slice Std.I64) : prefixSum s s.val.length = totalSum s := by
    simp [prefixSum, totalSum, ints]

  /-- Whenever the function returns a result r, r = HE + HX, where HE = max(0, (sum_{j=0}^{n-1} energy[j]) + 1 - initialEnergy) and HX = max(0, max_{0 <= i < n} (experience[i] + 1 - initialExperience - sum_{j=0}^{i-1} experience[j])). An empty sum (i = 0) is 0. All arithmetic and maxima/minima here are over mathematical integers, and r is the returned i64 interpreted as that integer.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_1
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        r.val = energyNeed initialEnergy.val energy + expNeed initialExperience.val experience n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          r.val = energyNeed initialEnergy.val energy + expNeed initialExperience.val experience n) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (there exists an i64 r such that the Lean result is ok r); it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_2
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      ∃ r : Std.I64,
        Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), ∃ r : Std.I64,
          Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_3
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        r.val ≥ 0 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          r.val ≥ 0) := by
    sorry

  /-- Whenever the function returns a result r, r <= (sum_{j=0}^{n-1} energy[j]) + max_{0 <= i < n} experience[i].
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_4
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        r.val ≤ totalSum energy + rangeMax n (entry experience) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          r.val ≤ totalSum energy + rangeMax n (entry experience)) := by
    sorry

  /-- Whenever the function returns a result r, r >= max(0, (sum_{j=0}^{n-1} energy[j]) + 1 - initialEnergy).
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_5
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        r.val ≥ energyNeed initialEnergy.val energy := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          r.val ≥ energyNeed initialEnergy.val energy) := by
    sorry

  /-- Whenever the function returns a result r, r >= max(0, max_{0 <= i < n} (experience[i] + 1 - initialExperience - sum_{j=0}^{i-1} experience[j])). An empty sum (i = 0) is 0.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_6
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        r.val ≥ expNeed initialExperience.val experience n := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          r.val ≥ expNeed initialExperience.val experience n) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers a and b with a + b = r such that, after training a hours on energy and b hours on experience, every opponent can be defeated in order: for every i with 0 <= i < n, initialEnergy + a - sum_{j=0}^{i-1} energy[j] > energy[i] and initialExperience + b + sum_{j=0}^{i-1} experience[j] > experience[i]. Empty sums are 0.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_7
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = r.val ∧
          ∀ i, i < n →
            initialEnergy.val + a - prefixSum energy i > entry energy i ∧
            initialExperience.val + b + prefixSum experience i > entry experience i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = r.val ∧
            ∀ i, i < n →
              initialEnergy.val + a - prefixSum energy i > entry energy i ∧
              initialExperience.val + b + prefixSum experience i > entry experience i) := by
    sorry

  /-- Whenever the function returns a result r, for every pair of nonnegative integers a and b such that initialEnergy + a - sum_{j=0}^{i-1} energy[j] > energy[i] and initialExperience + b + sum_{j=0}^{i-1} experience[j] > experience[i] for all i with 0 <= i < n, it holds that a + b >= r. Empty sums are 0.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_8
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
          (∀ i, i < n →
            initialEnergy.val + a - prefixSum energy i > entry energy i ∧
            initialExperience.val + b + prefixSum experience i > entry experience i) →
          a + b ≥ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          ∀ a b : ℤ, 0 ≤ a → 0 ≤ b →
            (∀ i, i < n →
              initialEnergy.val + a - prefixSum energy i > entry energy i ∧
              initialExperience.val + b + prefixSum experience i > entry experience i) →
            a + b ≥ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if both of the following hold: (1) initialEnergy > sum_{j=0}^{n-1} energy[j]; and (2) for every i with 0 <= i < n, initialExperience + sum_{j=0}^{i-1} experience[j] > experience[i]. Empty sums are 0.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. -/
  theorem spec_9
      (initialEnergy initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        (r.val = 0 ↔
          initialEnergy.val > totalSum energy ∧
            ∀ i, i < n → initialExperience.val + prefixSum experience i > entry experience i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          (r.val = 0 ↔
            initialEnergy.val > totalSum energy ∧
              ∀ i, i < n → initialExperience.val + prefixSum experience i > entry experience i)) := by
    sorry

  /-- Whenever the call with (initialEnergy, initialExperience, energy, experience) returns r and the call with (initialEnergy, initialExperience, energy2, experience) returns r2, we have r = r2.
    Preconditions: Let n = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= experience[i] <= 100. Let energy and energy2 be two slices of length n whose entries all lie between 1 and 100 and whose sums are equal. -/
  theorem spec_10
      (initialEnergy initialExperience : Std.I64)
      (energy energy2 experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
      (hnX : experience.val.length = n)
      (hnE : energy.val.length = n) (hnE2 : energy2.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hEnergy2 : ∀ i, i < n → 1 ≤ entry energy2 i ∧ entry energy2 i ≤ 100)
      (hsum : totalSum energy = totalSum energy2) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy2 experience
            = ok r2 →
          r.val = r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy energy2 experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
        (hnX : experience.val.length = n)
        (hnE : energy.val.length = n) (hnE2 : energy2.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hEnergy2 : ∀ i, i < n → 1 ≤ entry energy2 i ∧ entry energy2 i ≤ 100)
        (hsum : totalSum energy = totalSum energy2), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy2 experience
              = ok r2 →
            r.val = r2.val) := by
    sorry

  /-- Whenever the call with (initialEnergy, initialExperience, energy, experience) returns r and the call with (initialEnergy2, initialExperience, energy, experience) returns r2, we have r2 <= r.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. Let initialEnergy and initialEnergy2 be integers with 1 <= initialEnergy <= initialEnergy2 <= 100. -/
  theorem spec_11
      (initialEnergy initialEnergy2 initialExperience : Std.I64)
      (energy experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val)
      (hInitE2_lo : 1 ≤ initialEnergy2.val) (hInitE2_hi : initialEnergy2.val ≤ 100)
      (hInitE_le : initialEnergy.val ≤ initialEnergy2.val)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        Aegis.MinNumberOfHours.min_number_of_hours initialEnergy2 initialExperience energy experience
            = ok r2 →
          r2.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (initialEnergy initialEnergy2 initialExperience : Std.I64)
        (energy experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val)
        (hInitE2_lo : 1 ≤ initialEnergy2.val) (hInitE2_hi : initialEnergy2.val ≤ 100)
        (hInitE_le : initialEnergy.val ≤ initialEnergy2.val)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          Aegis.MinNumberOfHours.min_number_of_hours initialEnergy2 initialExperience energy experience
              = ok r2 →
            r2.val ≤ r.val) := by
    sorry

  /-- Whenever the call with (initialEnergy, initialExperience, energy, experience) returns r and the call with (initialEnergy, initialExperience2, energy, experience) returns r2, we have r2 <= r.
    Preconditions: Let n = len(energy) = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, and for every i with 0 <= i < n, 1 <= energy[i] <= 100 and 1 <= experience[i] <= 100. Let initialExperience and initialExperience2 be integers with 1 <= initialExperience <= initialExperience2 <= 100. -/
  theorem spec_12
      (initialEnergy initialExperience initialExperience2 : Std.I64)
      (energy experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
      (hnE : energy.val.length = n) (hnX : experience.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val)
      (hInitX2_lo : 1 ≤ initialExperience2.val) (hInitX2_hi : initialExperience2.val ≤ 100)
      (hInitX_le : initialExperience.val ≤ initialExperience2.val)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience2 energy experience
            = ok r2 →
          r2.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (initialEnergy initialExperience initialExperience2 : Std.I64)
        (energy experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
        (hnE : energy.val.length = n) (hnX : experience.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val)
        (hInitX2_lo : 1 ≤ initialExperience2.val) (hInitX2_hi : initialExperience2.val ≤ 100)
        (hInitX_le : initialExperience.val ≤ initialExperience2.val)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience2 energy experience
              = ok r2 →
            r2.val ≤ r.val) := by
    sorry

  /-- Whenever the call with (initialEnergy, initialExperience, energy, experience) returns r and the call with (initialEnergy, initialExperience, energy2, experience) returns r2, we have r2 >= r.
    Preconditions: Let n = len(experience). Assume 1 <= n <= 100, 1 <= initialEnergy <= 100, 1 <= initialExperience <= 100, and for every i with 0 <= i < n, 1 <= experience[i] <= 100. Let energy and energy2 be two slices of length n whose entries all lie between 1 and 100, and assume energy2[i] >= energy[i] for every i with 0 <= i < n. -/
  theorem spec_13
      (initialEnergy initialExperience : Std.I64)
      (energy energy2 experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
      (hnX : experience.val.length = n)
      (hnE : energy.val.length = n) (hnE2 : energy2.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
      (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
      (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100)
      (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
      (hEnergy2 : ∀ i, i < n → 1 ≤ entry energy2 i ∧ entry energy2 i ≤ 100)
      (hmono : ∀ i, i < n → entry energy2 i ≥ entry energy i) :
      Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
          = ok r →
        Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy2 experience
            = ok r2 →
          r2.val ≥ r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (initialEnergy initialExperience : Std.I64)
        (energy energy2 experience : Slice Std.I64) (r r2 : Std.I64) (n : ℕ)
        (hnX : experience.val.length = n)
        (hnE : energy.val.length = n) (hnE2 : energy2.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hInitE_lo : 1 ≤ initialEnergy.val) (hInitE_hi : initialEnergy.val ≤ 100)
        (hInitX_lo : 1 ≤ initialExperience.val) (hInitX_hi : initialExperience.val ≤ 100)
        (hExperience : ∀ i, i < n → 1 ≤ entry experience i ∧ entry experience i ≤ 100)
        (hEnergy : ∀ i, i < n → 1 ≤ entry energy i ∧ entry energy i ≤ 100)
        (hEnergy2 : ∀ i, i < n → 1 ≤ entry energy2 i ∧ entry energy2 i ≤ 100)
        (hmono : ∀ i, i < n → entry energy2 i ≥ entry energy i), Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy experience
            = ok r →
          Aegis.MinNumberOfHours.min_number_of_hours initialEnergy initialExperience energy2 experience
              = ok r2 →
            r2.val ≥ r.val) := by
    sorry

  end AegisSpec.MinNumberOfHours
