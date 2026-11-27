import Aegis.MaxPerformance.Code.Funs

/-!
# Specifications of `Aegis.MaxPerformance.max_performance`

LeetCode problem `maximum-performance-of-a-team`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxPerformance

def M : Int := 1000000007

def elem (s : Slice I64) (i : Nat) : Int := (s.val[i]!).val

def vals (s : Slice I64) : List Int := s.val.map (fun x => x.val)

def Feasible (n k : Nat) (S : Finset Nat) : Prop :=
  S.Nonempty ∧ S ⊆ Finset.range n ∧ S.card ≤ k

def perf (speed efficiency : Slice I64) (S : Finset Nat) (hS : S.Nonempty) : Int :=
  (S.sum (fun i => elem speed i)) * ((S.image (fun i => elem efficiency i)).min' (hS.image _))

def IsMaxPerf (n k : Nat) (speed efficiency : Slice I64) (P : Int) : Prop :=
  (∃ (S : Finset Nat) (hS : S.Nonempty), Feasible n k S ∧ P = perf speed efficiency S hS) ∧
  (∀ (S : Finset Nat) (hS : S.Nonempty), Feasible n k S → perf speed efficiency S hS ≤ P)

def IsSumOfKLargestIn (k : Nat) (A : Finset Nat) (f : Nat → Int) (T : Int) : Prop :=
  ∃ S : Finset Nat, S ⊆ A ∧ S.card = min k A.card ∧
    (∀ i ∈ S, ∀ j ∈ A, j ∉ S → f j ≤ f i) ∧ T = S.sum f

def IsMaxProd (n : Nat) (speed efficiency : Slice I64) (Q : Int) : Prop :=
  (∃ i : Nat, i < n ∧ Q = elem speed i * elem efficiency i) ∧
  (∀ i : Nat, i < n → elem speed i * elem efficiency i ≤ Q)

def IsDescSortedVals (efficiency : Slice I64) (l : List Int) : Prop :=
  l.Pairwise (fun a b => b ≤ a) ∧ l.Perm (vals efficiency)

def IsMaxOverM (s : Int) (d : List Int) (k : Nat) (P : Int) : Prop :=
  (∃ m : Nat, 1 ≤ m ∧ m ≤ k ∧ P = (m : Int) * s * d[m - 1]!) ∧
  (∀ m : Nat, 1 ≤ m → m ≤ k → (m : Int) * s * d[m - 1]! ≤ P)

def Aeff (n : Nat) (efficiency : Slice I64) (j : Nat) : Finset Nat :=
  (Finset.range n).filter (fun i => elem efficiency j ≤ elem efficiency i)

def IsMaxOverJ (n k : Nat) (speed efficiency : Slice I64) (P : Int) : Prop :=
  (∃ (j : Nat) (S : Int), j < n ∧
    IsSumOfKLargestIn k (Aeff n efficiency j) (fun i => elem speed i) S ∧
    P = elem efficiency j * S) ∧
  (∀ (j : Nat) (S : Int), j < n →
    IsSumOfKLargestIn k (Aeff n efficiency j) (fun i => elem speed i) S →
    elem efficiency j * S ≤ P)

/-- Let M = 1000000007. For a nonempty set S of indices from {0, ..., n-1}, define perf(S) = (sum_{i in S} speed[i]) * (min_{i in S} efficiency[i]). Let P* = max { perf(S) : S is nonempty and |S| <= k }. The function returns a result r, and r is the unique integer such that 0 <= r < M and r ≡ P* (mod M); equivalently, r = P* mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_1 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000) :
    ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r.val = P % M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000), ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r.val = P % M) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_2 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000) :
    ∃ r : I64, Aegis.MaxPerformance.max_performance n speed efficiency k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000), ∃ r : I64, Aegis.MaxPerformance.max_performance n speed efficiency k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r < M, where M = 1000000007.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_3 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000) :
    ∀ r : I64, Aegis.MaxPerformance.max_performance n speed efficiency k = ok r →
      0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000), ∀ r : I64, Aegis.MaxPerformance.max_performance n speed efficiency k = ok r →
      0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Let M = 1000000007 and let Q = max_{0 <= i < n} (speed[i] * efficiency[i]). The function returns a result r, and r = Q mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; k = 1; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_4 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val) (h_k_val : k.val = 1)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000) :
    ∃ (r : I64) (Q : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxProd n.val.toNat speed efficiency Q ∧ r.val = Q % M := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val) (h_k_val : k.val = 1)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000), ∃ (r : I64) (Q : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxProd n.val.toNat speed efficiency Q ∧ r.val = Q % M) := by
  sorry

/-- Let M = 1000000007. Let T be the sum of the k largest values among speed[0], ..., speed[n-1], counted with multiplicity (so if these speeds are sorted nonincreasingly as u_1 >= ... >= u_n, then T = u_1 + ... + u_k). The function returns a result r, and r = (e * T) mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000; there exists an integer e such that efficiency[i] = e for every i with 0 <= i < n. -/
theorem spec_5 (n k : I64) (speed efficiency : Slice I64) (e : Int)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_eff_const : ∀ i : Nat, i < n.val.toNat → elem efficiency i = e) :
    ∃ (r : I64) (T : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsSumOfKLargestIn k.val.toNat (Finset.range n.val.toNat) (fun i => elem speed i) T ∧
      r.val = (e * T) % M := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64) (e : Int)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_eff_const : ∀ i : Nat, i < n.val.toNat → elem efficiency i = e), ∃ (r : I64) (T : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsSumOfKLargestIn k.val.toNat (Finset.range n.val.toNat) (fun i => elem speed i) T ∧
      r.val = (e * T) % M) := by
  sorry

/-- Let M = 1000000007. Let d_1 >= d_2 >= ... >= d_n be the values efficiency[0], ..., efficiency[n-1] sorted in nonincreasing order. The function returns a result r, and r = ( max_{1 <= m <= k} (m * s * d_m) ) mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000; there exists an integer s such that speed[i] = s for every i with 0 <= i < n. -/
theorem spec_6 (n k : I64) (speed efficiency : Slice I64) (s : Int) (d : List Int)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_speed_const : ∀ i : Nat, i < n.val.toNat → elem speed i = s)
    (h_d_sorted : IsDescSortedVals efficiency d) :
    ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxOverM s d k.val.toNat P ∧ r.val = P % M := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64) (s : Int) (d : List Int)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_speed_const : ∀ i : Nat, i < n.val.toNat → elem speed i = s)
    (h_d_sorted : IsDescSortedVals efficiency d), ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxOverM s d k.val.toNat P ∧ r.val = P % M) := by
  sorry

/-- Whenever the function returns a result r, there exists a nonempty set S of indices with S subset of {0, ..., n-1} and |S| <= k such that r ≡ (sum_{i in S} speed[i]) * (min_{i in S} efficiency[i]) (mod 1000000007).
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_7 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (r : I64) (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r) :
    ∃ (S : Finset Nat) (hS : S.Nonempty),
      Feasible n.val.toNat k.val.toNat S ∧ Int.ModEq M r.val (perf speed efficiency S hS) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (r : I64) (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r), ∃ (S : Finset Nat) (hS : S.Nonempty),
      Feasible n.val.toNat k.val.toNat S ∧ Int.ModEq M r.val (perf speed efficiency S hS)) := by
  sorry

/-- Let M = 1000000007. For each index j with 0 <= j < n, let A_j = { i : 0 <= i < n and efficiency[i] >= efficiency[j] }, and let S_j be the sum of the min(k, |A_j|) largest values of speed[i] over i in A_j. Let P* = max_{0 <= j < n} (efficiency[j] * S_j). The function returns a result r, and r = P* mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_8 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000) :
    ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxOverJ n.val.toNat k.val.toNat speed efficiency P ∧ r.val = P % M := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000), ∃ (r : I64) (P : Int), Aegis.MaxPerformance.max_performance n speed efficiency k = ok r ∧
      IsMaxOverJ n.val.toNat k.val.toNat speed efficiency P ∧ r.val = P % M) := by
  sorry

/-- Let M = 1000000007. For a nonempty set S of indices from {0, ..., n-1}, define perf(S) = (sum_{i in S} speed[i]) * (min_{i in S} efficiency[i]), and let P* = max { perf(S) : S is nonempty and |S| <= k }. Whenever the function returns a result r, r = 0 if and only if M divides P*.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_9 (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (r : I64) (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r) :
    ∃ P : Int, IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ (r.val = 0 ↔ M ∣ P) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k : I64) (speed efficiency : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (r : I64) (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r), ∃ P : Int, IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ (r.val = 0 ↔ M ∣ P)) := by
  sorry

/-- Let pi be any permutation of {0, ..., n-1}. Define speed'[i] = speed[pi(i)] and efficiency'[i] = efficiency[pi(i)] for 0 <= i < n. If r is the result for (n, speed, efficiency, k) and r' is the result for (n, speed', efficiency', k), then r = r'.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000. -/
theorem spec_10 (n k : I64) (speed efficiency speed' efficiency' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_n_speed' : n.val = (speed'.val.length : Int))
    (h_n_eff' : n.val = (efficiency'.val.length : Int))
    (pi : Equiv.Perm (Fin n.val.toNat))
    (h_speed' : speed'.val = List.ofFn (fun i : Fin n.val.toNat => speed.val[(pi i).val]!))
    (h_eff' : efficiency'.val = List.ofFn (fun i : Fin n.val.toNat => efficiency.val[(pi i).val]!))
    (r r' : I64)
    (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r)
    (hr' : Aegis.MaxPerformance.max_performance n speed' efficiency' k = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n k : I64) (speed efficiency speed' efficiency' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_n_speed' : n.val = (speed'.val.length : Int))
    (h_n_eff' : n.val = (efficiency'.val.length : Int))
    (pi : Equiv.Perm (Fin n.val.toNat))
    (h_speed' : speed'.val = List.ofFn (fun i : Fin n.val.toNat => speed.val[(pi i).val]!))
    (h_eff' : efficiency'.val = List.ofFn (fun i : Fin n.val.toNat => efficiency.val[(pi i).val]!))
    (r r' : I64)
    (hr : Aegis.MaxPerformance.max_performance n speed efficiency k = ok r)
    (hr' : Aegis.MaxPerformance.max_performance n speed' efficiency' k = ok r'), r.val = r'.val) := by
  sorry

/-- Let M = 1000000007. Let P* be the maximum performance for (n, speed, efficiency, k) as defined in the main specification. The function returns a result r' for (n, speed', efficiency, k), and r' = (c * P*) mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000; c is a positive integer, and the array speed' defined by speed'[i] = c * speed[i] for 0 <= i < n also satisfies 1 <= speed'[i] <= 100000 for every i. -/
theorem spec_11 (n k : I64) (c : Int) (speed efficiency speed' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_c_pos : 0 < c)
    (h_n_speed' : n.val = (speed'.val.length : Int))
    (h_speed'_def : ∀ i : Nat, i < n.val.toNat → elem speed' i = c * elem speed i)
    (h_speed'_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem speed' i ∧ elem speed' i ≤ 100000) :
    ∃ (r' : I64) (P : Int),
      Aegis.MaxPerformance.max_performance n speed' efficiency k = ok r' ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r'.val = (c * P) % M := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n k : I64) (c : Int) (speed efficiency speed' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_c_pos : 0 < c)
    (h_n_speed' : n.val = (speed'.val.length : Int))
    (h_speed'_def : ∀ i : Nat, i < n.val.toNat → elem speed' i = c * elem speed i)
    (h_speed'_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem speed' i ∧ elem speed' i ≤ 100000), ∃ (r' : I64) (P : Int),
      Aegis.MaxPerformance.max_performance n speed' efficiency k = ok r' ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r'.val = (c * P) % M) := by
  sorry

/-- Let M = 1000000007. Let P* be the maximum performance for (n, speed, efficiency, k) as defined in the main specification. The function returns a result r' for (n, speed, efficiency', k), and r' = (c * P*) mod M.
  Preconditions: n = len(speed) = len(efficiency); 1 <= n <= 100000; 1 <= k <= n; for every i with 0 <= i < n, 1 <= speed[i] <= 100000 and 1 <= efficiency[i] <= 100000000; c is a positive integer, and the array efficiency' defined by efficiency'[i] = c * efficiency[i] for 0 <= i < n also satisfies 1 <= efficiency'[i] <= 100000000 for every i. -/
theorem spec_12 (n k : I64) (c : Int) (speed efficiency efficiency' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_c_pos : 0 < c)
    (h_n_eff' : n.val = (efficiency'.val.length : Int))
    (h_eff'_def : ∀ i : Nat, i < n.val.toNat → elem efficiency' i = c * elem efficiency i)
    (h_eff'_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency' i ∧ elem efficiency' i ≤ 100000000) :
    ∃ (r' : I64) (P : Int),
      Aegis.MaxPerformance.max_performance n speed efficiency' k = ok r' ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r'.val = (c * P) % M := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n k : I64) (c : Int) (speed efficiency efficiency' : Slice I64)
    (h_n_speed : n.val = (speed.val.length : Int))
    (h_n_eff : n.val = (efficiency.val.length : Int))
    (h_n_pos : 1 ≤ n.val) (h_n_max : n.val ≤ 100000)
    (h_k_pos : 1 ≤ k.val) (h_k_max : k.val ≤ n.val)
    (h_speed_range : ∀ i : Nat, i < n.val.toNat → 1 ≤ elem speed i ∧ elem speed i ≤ 100000)
    (h_eff_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency i ∧ elem efficiency i ≤ 100000000)
    (h_c_pos : 0 < c)
    (h_n_eff' : n.val = (efficiency'.val.length : Int))
    (h_eff'_def : ∀ i : Nat, i < n.val.toNat → elem efficiency' i = c * elem efficiency i)
    (h_eff'_range : ∀ i : Nat,
      i < n.val.toNat → 1 ≤ elem efficiency' i ∧ elem efficiency' i ≤ 100000000), ∃ (r' : I64) (P : Int),
      Aegis.MaxPerformance.max_performance n speed efficiency' k = ok r' ∧
      IsMaxPerf n.val.toNat k.val.toNat speed efficiency P ∧ r'.val = (c * P) % M) := by
  sorry

end AegisSpec.MaxPerformance
