import Aegis.MaximumValueSum.Code.Funs

/-!
# Specifications of `Aegis.MaximumValueSum.maximum_value_sum`

LeetCode problem `find-the-maximum-sum-of-node-values`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumValueSum

def xorInt (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

def absInt (x : Int) : Int := if x < 0 then -x else x

def gain (a k : Int) : Int := xorInt a k - a

def listMin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl max x

def numVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def edgeVals (edges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  edges.val.map (fun v => v.val.map (fun x => x.val))

def gainAt (xs : List Int) (k : Int) (i : Nat) : Int := gain (xs.getD i 0) k

def gains (xs : List Int) (k : Int) : List Int := xs.map (fun a => gain a k)

def posIdx (xs : List Int) (k : Int) : Finset Nat :=
  (Finset.range xs.length).filter (fun i => 0 < gainAt xs k i)

def negIdx (xs : List Int) (k : Int) : Finset Nat :=
  (Finset.range xs.length).filter (fun i => gainAt xs k i ≤ 0)

def sumNums (xs : List Int) : Int := xs.sum

def sumBest (xs : List Int) (k : Int) : Int := (xs.map (fun a => max a (xorInt a k))).sum

def sumFlip (xs : List Int) (k : Int) : Int := (xs.map (fun a => xorInt a k)).sum

def posGainSum (xs : List Int) (k : Int) : Int :=
  ((gains xs k).filter (fun g => 0 < g)).sum

def minPosGain (xs : List Int) (k : Int) : Int :=
  listMin ((gains xs k).filter (fun g => 0 < g))

def maxNegGain (xs : List Int) (k : Int) : Int :=
  listMax ((gains xs k).filter (fun g => g ≤ 0))

def minAbsGain (xs : List Int) (k : Int) : Int :=
  listMin ((gains xs k).map absInt)

def valOfSet (xs : List Int) (k : Int) (T : Finset Nat) : Int :=
  (Finset.range xs.length).sum
    (fun i => if i ∈ T then xorInt (xs.getD i 0) k else xs.getD i 0)

def evenSubset (xs : List Int) (T : Finset Nat) : Prop :=
  T ⊆ Finset.range xs.length ∧ Even T.card

def Adj (edges : List (List Int)) (u v : Nat) : Prop :=
  ∃ e ∈ edges, e = [(u : Int), (v : Int)] ∨ e = [(v : Int), (u : Int)]

def Reach (edges : List (List Int)) : Nat → Nat → Prop :=
  Relation.ReflTransGen (Adj edges)

def Connected (n : Nat) (edges : List (List Int)) : Prop :=
  ∀ u v : Nat, u < n → v < n → Reach edges u v

def Acyclic (n : Nat) (edges : List (List Int)) : Prop :=
  ∀ e ∈ edges, ¬ Connected n (edges.erase e)

def IsTree (n : Nat) (edges : List (List Int)) : Prop :=
  Connected n edges ∧ Acyclic n edges

/-- Let n = len(nums). For a subset T of {0,...,n-1}, let S(T) = Σ_{i=0}^{n-1} ((nums[i] XOR k) if i ∈ T else nums[i]). The function returns a result r such that r = max { S(T) : T ⊆ {0,...,n-1} and |T| is even }. The empty set T=∅ is allowed, so this is a nonempty finite maximum.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_1
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∃ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r ∧
      (∃ T : Finset Nat,
        evenSubset (numVals nums) T ∧
          valOfSet (numVals nums) k.val T = r.val) ∧
      (∀ T : Finset Nat,
        evenSubset (numVals nums) T →
          valOfSet (numVals nums) k.val T ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∃ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r ∧
      (∃ T : Finset Nat,
        evenSubset (numVals nums) T ∧
          valOfSet (numVals nums) k.val T = r.val) ∧
      (∀ T : Finset Nat,
        evenSubset (numVals nums) T →
          valOfSet (numVals nums) k.val T ≤ r.val)) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, go out of bounds, or panic).
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_2
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∃ r : Std.I64, Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∃ r : Std.I64, Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= Σ_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_3
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        sumNums (numVals nums) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        sumNums (numVals nums) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= Σ_{i=0}^{n-1} max(nums[i], nums[i] XOR k).
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_4
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        r.val ≤ sumBest (numVals nums) k.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        r.val ≤ sumBest (numVals nums) k.val) := by
  sorry

/-- Whenever the function returns a result r, r = Σ_{i=0}^{n-1} nums[i] + Σ_{i : g_i > 0} g_i.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. Also let g_i = (nums[i] XOR k) - nums[i] for 0 <= i < n; the number of indices i with g_i > 0 is even. -/
theorem spec_5
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_pos_even : Even (posIdx (numVals nums) k.val).card) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_pos_even : Even (posIdx (numVals nums) k.val).card), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val) := by
  sorry

/-- Whenever the function returns a result r, the following holds. Let P = { i : 0 <= i < n and g_i > 0 } and N = { i : 0 <= i < n and g_i <= 0 }. P is nonempty. Let m = min_{i∈P} g_i. If N is empty, then r = Σ_{i=0}^{n-1} nums[i] + Σ_{i∈P} g_i - m. If N is nonempty, let M = max_{i∈N} g_i; then r = Σ_{i=0}^{n-1} nums[i] + Σ_{i∈P} g_i + max(-m, M).
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. Also let g_i = (nums[i] XOR k) - nums[i] for 0 <= i < n; the number of indices i with g_i > 0 is odd. -/
theorem spec_6
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_pos_odd : (posIdx (numVals nums) k.val).card % 2 = 1) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (posIdx (numVals nums) k.val).Nonempty ∧
          ((negIdx (numVals nums) k.val).card = 0 →
            r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val -
              minPosGain (numVals nums) k.val) ∧
          (0 < (negIdx (numVals nums) k.val).card →
            r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val +
              max (-(minPosGain (numVals nums) k.val)) (maxNegGain (numVals nums) k.val)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_pos_odd : (posIdx (numVals nums) k.val).card % 2 = 1), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (posIdx (numVals nums) k.val).Nonempty ∧
          ((negIdx (numVals nums) k.val).card = 0 →
            r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val -
              minPosGain (numVals nums) k.val) ∧
          (0 < (negIdx (numVals nums) k.val).card →
            r.val = sumNums (numVals nums) + posGainSum (numVals nums) k.val +
              max (-(minPosGain (numVals nums) k.val)) (maxNegGain (numVals nums) k.val))) := by
  sorry

/-- Whenever maximum_value_sum nums k edges returns r and maximum_value_sum nums k e2 returns r2, we have r = r2.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. Let e2 be any list of n-1 pairs [a,b] with 0 <= a,b < n such that the graph on vertices 0,...,n-1 with edges e2 is also a tree. -/
theorem spec_7
    (nums : Slice Std.I64) (k : Std.I64) (edges e2 : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_e2_len : (edgeVals e2).length = (numVals nums).length - 1)
    (h_e2_wf : ∀ e ∈ edgeVals e2,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_e2_tree : IsTree (numVals nums).length (edgeVals e2)) :
    ∀ r r2 : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        Aegis.MaximumValueSum.maximum_value_sum nums k e2 = ok r2 → r = r2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges e2 : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_e2_len : (edgeVals e2).length = (numVals nums).length - 1)
    (h_e2_wf : ∀ e ∈ edgeVals e2,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_e2_tree : IsTree (numVals nums).length (edgeVals e2)), ∀ r r2 : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        Aegis.MaximumValueSum.maximum_value_sum nums k e2 = ok r2 → r = r2) := by
  sorry

/-- Whenever maximum_value_sum nums k edges returns r and maximum_value_sum nums2 k e2 returns r2, we have r = r2.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. Let nums2 be any array of length n whose entries are a permutation of the entries of nums, and let e2 be any list of n-1 pairs [a,b] with 0 <= a,b < n forming a tree on vertices 0,...,n-1. -/
theorem spec_8
    (nums nums2 : Slice Std.I64) (k : Std.I64)
    (edges e2 : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_nums2_len : (numVals nums2).length = (numVals nums).length)
    (h_nums2_perm : (numVals nums2).Perm (numVals nums))
    (h_e2_len : (edgeVals e2).length = (numVals nums).length - 1)
    (h_e2_wf : ∀ e ∈ edgeVals e2,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_e2_tree : IsTree (numVals nums).length (edgeVals e2)) :
    ∀ r r2 : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        Aegis.MaximumValueSum.maximum_value_sum nums2 k e2 = ok r2 → r = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums2 : Slice Std.I64) (k : Std.I64)
    (edges e2 : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_nums2_len : (numVals nums2).length = (numVals nums).length)
    (h_nums2_perm : (numVals nums2).Perm (numVals nums))
    (h_e2_len : (edgeVals e2).length = (numVals nums).length - 1)
    (h_e2_wf : ∀ e ∈ edgeVals e2,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_e2_tree : IsTree (numVals nums).length (edgeVals e2)), ∀ r r2 : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        Aegis.MaximumValueSum.maximum_value_sum nums2 k e2 = ok r2 → r = r2) := by
  sorry

/-- Whenever the function returns a result r, there exists a subset T of {0,...,n-1} with |T| even such that r = Σ_{i∈T}(nums[i] XOR k) + Σ_{i∉T} nums[i], T contains at most one index i with (nums[i] XOR k) < nums[i], and T omits at most one index i with (nums[i] XOR k) > nums[i].
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_9
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        ∃ T : Finset Nat,
          evenSubset (numVals nums) T ∧
            r.val = valOfSet (numVals nums) k.val T ∧
            (T.filter (fun i => gainAt (numVals nums) k.val i < 0)).card ≤ 1 ∧
            ((posIdx (numVals nums) k.val).filter (fun i => i ∉ T)).card ≤ 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        ∃ T : Finset Nat,
          evenSubset (numVals nums) T ∧
            r.val = valOfSet (numVals nums) k.val T ∧
            (T.filter (fun i => gainAt (numVals nums) k.val i < 0)).card ≤ 1 ∧
            ((posIdx (numVals nums) k.val).filter (fun i => i ∉ T)).card ≤ 1) := by
  sorry

/-- Whenever the function returns a result r, r = Σ_{i=0}^{n-1} nums[i] if and only if for every subset T of {0,...,n-1} with |T| even, Σ_{i∈T} ((nums[i] XOR k) - nums[i]) <= 0.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_10
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (r.val = sumNums (numVals nums) ↔
          ∀ T : Finset Nat,
            evenSubset (numVals nums) T →
              T.sum (fun i => gainAt (numVals nums) k.val i) ≤ 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (r.val = sumNums (numVals nums) ↔
          ∀ T : Finset Nat,
            evenSubset (numVals nums) T →
              T.sum (fun i => gainAt (numVals nums) k.val i) ≤ 0)) := by
  sorry

/-- Let g_i = (nums[i] XOR k) - nums[i] for 0 <= i < n, and let P = {i : 0 <= i < n and g_i > 0}. Whenever the function returns a result r, if |P| is even then r = Σ_{i=0}^{n-1} max(nums[i], nums[i] XOR k); if |P| is odd then r = Σ_{i=0}^{n-1} max(nums[i], nums[i] XOR k) - min_{0 <= i < n} |g_i|.
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. -/
theorem spec_11
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (Even (posIdx (numVals nums) k.val).card →
          r.val = sumBest (numVals nums) k.val) ∧
        ((posIdx (numVals nums) k.val).card % 2 = 1 →
          r.val = sumBest (numVals nums) k.val - minAbsGain (numVals nums) k.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges)), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        (Even (posIdx (numVals nums) k.val).card →
          r.val = sumBest (numVals nums) k.val) ∧
        ((posIdx (numVals nums) k.val).card % 2 = 1 →
          r.val = sumBest (numVals nums) k.val - minAbsGain (numVals nums) k.val)) := by
  sorry

/-- Whenever the function returns a result r, r >= Σ_{i=0}^{n-1} (nums[i] XOR k).
  Preconditions: Let n = len(nums). The inputs satisfy: 2 <= n <= 20000; 1 <= k <= 1000000000; for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000; len(edges) = n - 1; every entry of edges is a pair [a,b] with 0 <= a,b < n; and the undirected graph with vertices 0,...,n-1 and these edges is a tree. Also n is even. -/
theorem spec_12
    (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_n_even : Even (numVals nums).length) :
    ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        sumFlip (numVals nums) k.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (edges : Slice (alloc.vec.Vec Std.I64))
    (h_n_lower : 2 ≤ (numVals nums).length)
    (h_n_upper : (numVals nums).length ≤ 20000)
    (h_k_lower : 1 ≤ k.val)
    (h_k_upper : k.val ≤ 1000000000)
    (h_nums_lower : ∀ x ∈ numVals nums, 0 ≤ x)
    (h_nums_upper : ∀ x ∈ numVals nums, x ≤ 1000000000)
    (h_edges_len : (edgeVals edges).length = (numVals nums).length - 1)
    (h_edges_wf : ∀ e ∈ edgeVals edges,
      ∃ a b : Int, e = [a, b] ∧ 0 ≤ a ∧ a < ((numVals nums).length : Int) ∧
        0 ≤ b ∧ b < ((numVals nums).length : Int))
    (h_edges_tree : IsTree (numVals nums).length (edgeVals edges))
    (h_n_even : Even (numVals nums).length), ∀ r : Std.I64,
      Aegis.MaximumValueSum.maximum_value_sum nums k edges = ok r →
        sumFlip (numVals nums) k.val ≤ r.val) := by
  sorry

end AegisSpec.MaximumValueSum
