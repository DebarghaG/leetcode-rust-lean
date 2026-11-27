import Aegis.MinNumberOfSemesters.Code.Funs

/-!
# Specifications of `Aegis.MinNumberOfSemesters.min_number_of_semesters`

LeetCode problem `parallel-courses-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinNumberOfSemesters

  def IsPair (v : alloc.vec.Vec I64) (x y : I64) : Prop := v.val = [x, y]

  def Edge (relations : Slice (alloc.vec.Vec I64)) (a b : ℤ) : Prop :=
    ∃ v ∈ relations.val, ∃ x y : I64, IsPair v x y ∧ x.val = a ∧ y.val = b

  inductive Reaches (relations : Slice (alloc.vec.Vec I64)) : ℤ → ℤ → Prop where

    | step {a b : ℤ} (h : Edge relations a b) : Reaches relations a b

    | trans {a b c : ℤ} (hab : Reaches relations a b) (hbc : Reaches relations b c) :
        Reaches relations a c

  structure WellFormed (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) : Prop where

    len_bound : relations.val.length ≤ n_val.toNat * (n_val.toNat - 1) / 2

    len_eq_two : ∀ v ∈ relations.val, v.val.length = 2

    mem_bounds : ∀ v ∈ relations.val, ∀ x y : I64, IsPair v x y →
      1 ≤ x.val ∧ x.val ≤ n_val ∧ 1 ≤ y.val ∧ y.val ≤ n_val

    no_self_loop : ∀ v ∈ relations.val, ∀ x y : I64, IsPair v x y → x.val ≠ y.val

    pairs_distinct : relations.val.Pairwise (fun v w => v.val ≠ w.val)

    acyclic : ∀ a : ℤ, ¬ Reaches relations a a

  def semesterSize (n_val : ℤ) (A : ℤ → ℤ) (s : ℤ) : ℕ :=
    (((List.range n_val.toNat).map (fun i => (i : ℤ) + 1)).filter (fun c => A c = s)).length

  def IsSchedule (n_val k_val m : ℤ) (relations : Slice (alloc.vec.Vec I64))
      (A : ℤ → ℤ) : Prop :=
    (∀ c : ℤ, 1 ≤ c → c ≤ n_val → 1 ≤ A c ∧ A c ≤ m) ∧
    (∀ a b : ℤ, Edge relations a b → A a < A b) ∧
    (∀ s : ℤ, 1 ≤ s → s ≤ m → (semesterSize n_val A s : ℤ) ≤ k_val)

  def HasSchedule (n_val k_val m : ℤ) (relations : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ A : ℤ → ℤ, IsSchedule n_val k_val m relations A

  def IsLeastSemesters (n_val k_val : ℤ) (relations : Slice (alloc.vec.Vec I64))
      (m : ℤ) : Prop :=
    1 ≤ m ∧ HasSchedule n_val k_val m relations ∧
      ∀ m' : ℤ, 1 ≤ m' → m' < m → ¬ HasSchedule n_val k_val m' relations

  def IsCeilDiv (n_val k_val q : ℤ) : Prop :=
    1 ≤ q ∧ n_val ≤ q * k_val ∧ ∀ q' : ℤ, 1 ≤ q' → q' < q → q' * k_val < n_val

  def IsChain (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) (vs : List ℤ) : Prop :=
    (∀ v ∈ vs, 1 ≤ v ∧ v ≤ n_val) ∧
    vs.Nodup ∧
    ∀ (i : ℕ) (a b : ℤ), vs[i]? = some a → vs[i + 1]? = some b → Edge relations a b

  def IsLongestChain (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) (L : ℤ) : Prop :=
    (∃ vs : List ℤ, IsChain n_val relations vs ∧ (vs.length : ℤ) = L) ∧
      ∀ vs : List ℤ, IsChain n_val relations vs → (vs.length : ℤ) ≤ L

  def IsAntichain (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) (cs : List ℤ) : Prop :=
    (∀ c ∈ cs, 1 ≤ c ∧ c ≤ n_val) ∧
    cs.Nodup ∧
    ∀ a ∈ cs, ∀ b ∈ cs, a ≠ b → ¬ Reaches relations a b ∧ ¬ Reaches relations b a

  def IsWidestAntichain (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) (W : ℤ) : Prop :=
    (∃ cs : List ℤ, IsAntichain n_val relations cs ∧ (cs.length : ℤ) = W) ∧
      ∀ cs : List ℤ, IsAntichain n_val relations cs → (cs.length : ℤ) ≤ W

  def SameReachability (n_val : ℤ) (relations relations' : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ a b : ℤ, 1 ≤ a → a ≤ n_val → 1 ≤ b → b ≤ n_val →
      (Reaches relations a b ↔ Reaches relations' a b)

  def IsTotalOrder (n_val : ℤ) (relations : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ a b : ℤ, 1 ≤ a → a ≤ n_val → 1 ≤ b → b ≤ n_val → a ≠ b →
      Reaches relations a b ∨ Reaches relations b a

  def IsCourseBijection (n_val : ℤ) (pi : ℤ → ℤ) : Prop :=
    (∀ a : ℤ, 1 ≤ a → a ≤ n_val → 1 ≤ pi a ∧ pi a ≤ n_val) ∧
      ∀ a b : ℤ, 1 ≤ a → a ≤ n_val → 1 ≤ b → b ≤ n_val → pi a = pi b → a = b

  def IsRelabeling (relations relations' : Slice (alloc.vec.Vec I64)) (pi : ℤ → ℤ) : Prop :=
    ∀ a b : ℤ,
      Edge relations' a b ↔ ∃ a' b' : ℤ, Edge relations a' b' ∧ pi a' = a ∧ pi b' = b

  /-- Let V = {1,2,...,n}. A valid schedule with m semesters is a function A: V -> {1,2,...,m} such that (i) for every i with 0 <= i < len(relations), A(relations[i][0]) < A(relations[i][1]), and (ii) for every s with 1 <= s <= m, the number of courses c in V with A(c) = s is at most k. The function returns a result r and r is the least integer m >= 1 for which a valid schedule with m semesters exists.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_1 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∃ r : I64,
        Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r ∧
          IsLeastSemesters n.val k.val relations r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∃ r : I64,
          Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r ∧
            IsLeastSemesters n.val k.val relations r.val) := by
    sorry

  /-- Let V = {1,2,...,n}. The function returns a result r and there exists a function A: V -> {1,2,...,r} such that (i) for every i with 0 <= i < len(relations), A(relations[i][0]) < A(relations[i][1]), and (ii) for every s with 1 <= s <= r, the number of courses c in V with A(c) = s is at most k. Thus r semesters are sufficient.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_2 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∃ r : I64,
        Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r ∧
          HasSchedule n.val k.val r.val relations := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∃ r : I64,
          Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r ∧
            HasSchedule n.val k.val r.val relations) := by
    sorry

  /-- Let V = {1,2,...,n}. Whenever the function returns a result r, for every integer m with 1 <= m < r, there is no function A: V -> {1,2,...,m} such that (i) for every i with 0 <= i < len(relations), A(relations[i][0]) < A(relations[i][1]), and (ii) for every s with 1 <= s <= m, the number of courses c in V with A(c) = s is at most k.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_3 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ m : ℤ, 1 ≤ m → m < r.val → ¬ HasSchedule n.val k.val m relations := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ m : ℤ, 1 ≤ m → m < r.val → ¬ HasSchedule n.val k.val m relations) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= n.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_4 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        1 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the smallest integer q such that q * k >= n. Equivalently, r >= ceil(n / k).
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_5 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ q : ℤ, IsCeilDiv n.val k.val q → q ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ q : ℤ, IsCeilDiv n.val k.val q → q ≤ r.val) := by
    sorry

  /-- Let L be the largest integer t such that there exist distinct courses v_1, ..., v_t in {1,...,n} with, for every j with 1 <= j < t, the pair (v_j, v_{j+1}) occurs in relations (i.e., there is an edge from v_j to v_{j+1}). Since n >= 1, L >= 1. Whenever the function returns a result r, r >= L.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_6 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ L : ℤ, IsLongestChain n.val relations L → L ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ L : ℤ, IsLongestChain n.val relations L → L ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r and len(relations) = 0, r is the smallest integer q such that q * k >= n. Equivalently, r = ceil(n / k).
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_7 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        relations.val.length = 0 → IsCeilDiv n.val k.val r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          relations.val.length = 0 → IsCeilDiv n.val k.val r.val) := by
    sorry

  /-- Let L be the largest integer t such that there exist distinct courses v_1, ..., v_t in {1,...,n} with, for every j with 1 <= j < t, the pair (v_j, v_{j+1}) occurs in relations. Whenever the function returns a result r and k >= n, r = L.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_8 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        n.val ≤ k.val → ∀ L : ℤ, IsLongestChain n.val relations L → r.val = L := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          n.val ≤ k.val → ∀ L : ℤ, IsLongestChain n.val relations L → r.val = L) := by
    sorry

  /-- Whenever the function returns a result r and k = 1, r = n.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_9 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        k.val = 1 → r.val = n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          k.val = 1 → r.val = n.val) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_10 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∃ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∃ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for any slice relations' of vectors of Int64 (with the same n and k) satisfying the same preconditions such that the transitive closure of the edge set of relations' on {1,...,n} equals the transitive closure of the edge set of relations, the function applied to (n, relations', k) also returns r. The transitive closure is the set of pairs (a,b) such that there is a directed path of length at least 1 from a to b.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_11 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
          SameReachability n.val relations relations' →
            ∀ r' : I64,
              Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                r'.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
            SameReachability n.val relations relations' →
              ∀ r' : I64,
                Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                  r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k' with k <= k' <= n, the function applied to (n, relations, k') returns a result r' with r' <= r.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_12 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ k' : I64, k.val ≤ k'.val → k'.val ≤ n.val →
          ∃ r' : I64,
            Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k' = ok r' ∧
              r'.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ k' : I64, k.val ≤ k'.val → k'.val ≤ n.val →
            ∃ r' : I64,
              Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k' = ok r' ∧
                r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r and the prerequisite relation is a total order on {1,...,n} (i.e., for every two distinct courses a, b in {1,...,n}, either (a,b) or (b,a) belongs to the transitive closure of the edge set of relations), then r = n.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_13 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        IsTotalOrder n.val relations → r.val = n.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          IsTotalOrder n.val relations → r.val = n.val) := by
    sorry

  /-- Whenever the function applied to (n, relations, k) returns r and the function applied to (n, relations', k) returns r', then r' >= r. Adding prerequisite edges cannot reduce the minimum number of semesters.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. Let relations' be another slice of vectors of Int64 satisfying the same structural preconditions, with the additional condition that every pair (relations[i][0], relations[i][1]) occurring in relations also occurs as some pair (relations'[j][0], relations'[j][1]) in relations'. -/
  theorem spec_14 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
          (∀ a b : ℤ, Edge relations a b → Edge relations' a b) →
            ∀ r' : I64,
              Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                r.val ≤ r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
            (∀ a b : ℤ, Edge relations a b → Edge relations' a b) →
              ∀ r' : I64,
                Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                  r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function applied to (n, relations, k) returns r and the function applied to (n, relations', k) returns r', then r' = r. The answer is invariant under relabeling courses.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. Let pi : {1,...,n_val} -> {1,...,n_val} be a bijection, and let relations' be any slice of vectors of Int64 satisfying the same structural preconditions obtained by replacing each occurrence of a pair [a,b] in relations with [pi(a),pi(b)] and listing the resulting pairs in any order. -/
  theorem spec_15 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ (pi : ℤ → ℤ), IsCourseBijection n.val pi →
          ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
            IsRelabeling relations relations' pi →
              ∀ r' : I64,
                Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                  r'.val = r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ (pi : ℤ → ℤ), IsCourseBijection n.val pi →
            ∀ relations' : Slice (alloc.vec.Vec I64), WellFormed n.val relations' →
              IsRelabeling relations relations' pi →
                ∀ r' : I64,
                  Aegis.MinNumberOfSemesters.min_number_of_semesters n relations' k = ok r' →
                    r'.val = r.val) := by
    sorry

  /-- Let L be the largest integer t such that there exist distinct courses v_1, ..., v_t in {1,...,n} with, for every j with 1 <= j < t, the pair (v_j, v_{j+1}) occurs in relations. Let W be the largest integer w such that there exist courses c_1, ..., c_w in {1,...,n} that are pairwise incomparable with respect to the transitive closure of the edge set of relations, i.e. for every distinct i, j neither (c_i,c_j) nor (c_j,c_i) belongs to the transitive closure. Whenever the function returns a result r and k >= W, then r = L.
    Preconditions: Let n_val and k_val be the integer values of the parameters n and k. Assume: 1 <= n_val <= 15; 1 <= k_val <= n_val; relations is a slice of vectors of Int64 with 0 <= len(relations) <= n_val*(n_val-1)/2; for every i with 0 <= i < len(relations), len(relations[i]) = 2, 1 <= relations[i][0] <= n_val, 1 <= relations[i][1] <= n_val, and relations[i][0] != relations[i][1]; for every i, j with 0 <= i < j < len(relations), (relations[i][0], relations[i][1]) != (relations[j][0], relations[j][1]); the directed graph on vertices {1,...,n_val} with an edge from relations[i][0] to relations[i][1] for each i is acyclic. -/
  theorem spec_16 (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
      (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
      (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
      (h_wf : WellFormed n.val relations) :
      ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
        ∀ L W : ℤ, IsLongestChain n.val relations L → IsWidestAntichain n.val relations W →
          W ≤ k.val → r.val = L := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (n : I64) (relations : Slice (alloc.vec.Vec I64)) (k : I64)
        (h_n_lo : 1 ≤ n.val) (h_n_hi : n.val ≤ 15)
        (h_k_lo : 1 ≤ k.val) (h_k_hi : k.val ≤ n.val)
        (h_wf : WellFormed n.val relations), ∀ r : I64, Aegis.MinNumberOfSemesters.min_number_of_semesters n relations k = ok r →
          ∀ L W : ℤ, IsLongestChain n.val relations L → IsWidestAntichain n.val relations W →
            W ≤ k.val → r.val = L) := by
    sorry

end AegisSpec.MinNumberOfSemesters
