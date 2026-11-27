import Aegis.MaximumEnergy.Code.Funs

/-!
# Specifications of `Aegis.MaximumEnergy.maximum_energy`

LeetCode problem `taking-maximum-energy-from-the-mystic-dungeon`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumEnergy

  def energyVals (energy : Slice Std.I64) : List Int := energy.val.map (fun x => x.val)

  def engAt (energy : Slice Std.I64) (i : Nat) : Int := (energyVals energy).getD i 0

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def rangeSum (m : Nat) (f : Nat → Int) : Int := ((List.range m).map f).sum

  def rangeMax (m : Nat) (f : Nat → Int) : Int := listMax ((List.range m).map f)

  def rangeMaxFrom (lo hi : Nat) (f : Nat → Int) : Int := rangeMax (hi - lo) (fun t => f (lo + t))

  def step (k : Std.I64) : Nat := k.val.toNat

  def chainLen (n kk i : Nat) : Nat := if i < n then (n - 1 - i) / kk + 1 else 0

  def chain (energy : Slice Std.I64) (kk i : Nat) : List Int :=
    (List.range (chainLen energy.val.length kk i)).map (fun t => engAt energy (i + t * kk))

  def chainSum (energy : Slice Std.I64) (kk i : Nat) : Int := (chain energy kk i).sum

  def chainTailSum (energy : Slice Std.I64) (kk i t : Nat) : Int :=
    ((chain energy kk i).drop t).sum

  /-- The function returns a result r and r = max_{0 <= i < len(energy)} S(i), where for each i with 0 <= i < len(energy), S(i) = Σ_{t=0}^{⌊(len(energy)-1-i)/k⌋} energy[i + t*k].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_1 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∃ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r ∧
        r.val = rangeMax energy.val.length (fun i => chainSum energy (step k) i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∃ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r ∧
          r.val = rangeMax energy.val.length (fun i => chainSum energy (step k) i)) := by
    sorry

  /-- Whenever the function returns a result r, r <= Σ_{i=0}^{len(energy)-1} max(energy[i], 0).
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_2 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        r.val ≤ rangeSum energy.val.length (fun i => max (engAt energy i) 0) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          r.val ≤ rangeSum energy.val.length (fun i => max (engAt energy i) 0)) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions (it does not panic, overflow, or otherwise fail).
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_3 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∃ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∃ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index i with 0 <= i < len(energy) such that r = Σ_{t=0}^{⌊(len(energy)-1-i)/k⌋} energy[i + t*k].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_4 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        ∃ i : Nat, i < energy.val.length ∧ r.val = chainSum energy (step k) i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          ∃ i : Nat, i < energy.val.length ∧ r.val = chainSum energy (step k) i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(energy), r >= Σ_{t=0}^{⌊(len(energy)-1-i)/k⌋} energy[i + t*k].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_5 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        ∀ i : Nat, i < energy.val.length → chainSum energy (step k) i ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          ∀ i : Nat, i < energy.val.length → chainSum energy (step k) i ≤ r.val) := by
    sorry

  /-- Let n = len(energy). For each integer r0 with 0 <= r0 < k, let C_{r0} be the sequence [energy[r0], energy[r0 + k], energy[r0 + 2k], ...] restricted to indices < n, and let m(r0) be its length. Whenever the function returns a result r, r = max_{0 <= r0 < k} max_{0 <= t < m(r0)} (Σ_{s=t}^{m(r0)-1} C_{r0}[s]).
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_6 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        r.val = rangeMax (step k) (fun r0 =>
          rangeMax ((chain energy (step k) r0).length)
            (fun t => chainTailSum energy (step k) r0 t)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          r.val = rangeMax (step k) (fun r0 =>
            rangeMax ((chain energy (step k) r0).length)
              (fun t => chainTailSum energy (step k) r0 t))) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= i < k} Σ_{t=0}^{⌊(len(energy)-1-i)/k⌋} energy[i + t*k].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1; for every i with 0 <= i < len(energy), energy[i] >= 0. -/
  theorem spec_7 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1)
      (h_nonneg : ∀ i (h : i < energy.val.length), 0 ≤ (energy.val[i]).val) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        r.val = rangeMax (step k) (fun i => chainSum energy (step k) i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1)
        (h_nonneg : ∀ i (h : i < energy.val.length), 0 ≤ (energy.val[i]).val), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          r.val = rangeMax (step k) (fun i => chainSum energy (step k) i)) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{len(energy)-k <= i < len(energy)} energy[i].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1; for every i with 0 <= i < len(energy), energy[i] <= 0. -/
  theorem spec_8 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1)
      (h_nonpos : ∀ i (h : i < energy.val.length), (energy.val[i]).val ≤ 0) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        r.val = rangeMaxFrom (energy.val.length - step k) energy.val.length (engAt energy) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1)
        (h_nonpos : ∀ i (h : i < energy.val.length), (energy.val[i]).val ≤ 0), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          r.val = rangeMaxFrom (energy.val.length - step k) energy.val.length (engAt energy)) := by
    sorry

  /-- Let n = len(energy). Whenever the function returns a result r, r <= max_{0 <= i < k} Σ_{t=0}^{⌊(n-1-i)/k⌋} max(energy[i + t*k], 0).
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_9 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        r.val ≤ rangeMax (step k) (fun i =>
          rangeSum (chainLen energy.val.length (step k) i)
            (fun t => max (engAt energy (i + t * step k)) 0)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          r.val ≤ rangeMax (step k) (fun i =>
            rangeSum (chainLen energy.val.length (step k) i)
              (fun t => max (engAt energy (i + t * step k)) 0))) := by
    sorry

  /-- Whenever the function returns a result r, r >= max_{len(energy)-k <= i < len(energy)} energy[i].
    Preconditions: 1 <= len(energy) <= 100000; for every i with 0 <= i < len(energy), -1000 <= energy[i] <= 1000; 1 <= k <= len(energy) - 1. -/
  theorem spec_10 (energy : Slice Std.I64) (k : Std.I64)
      (h_len_ge : 1 ≤ energy.val.length)
      (h_len_le : energy.val.length ≤ 100000)
      (h_bounds : ∀ i (h : i < energy.val.length),
        -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
      (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1) :
      ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
        rangeMaxFrom (energy.val.length - step k) energy.val.length (engAt energy) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (energy : Slice Std.I64) (k : Std.I64)
        (h_len_ge : 1 ≤ energy.val.length)
        (h_len_le : energy.val.length ≤ 100000)
        (h_bounds : ∀ i (h : i < energy.val.length),
          -1000 ≤ (energy.val[i]).val ∧ (energy.val[i]).val ≤ 1000)
        (h_k : 1 ≤ k.val ∧ k.val ≤ (energy.val.length : Int) - 1), ∀ r : Std.I64, Aegis.MaximumEnergy.maximum_energy energy k = ok r →
          rangeMaxFrom (energy.val.length - step k) energy.val.length (engAt energy) ≤ r.val) := by
    sorry

  end AegisSpec.MaximumEnergy
