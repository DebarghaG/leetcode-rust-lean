import Aegis.RemainingMethods.Code.Funs

/-!
# Specifications of `Aegis.RemainingMethods.remaining_methods`

LeetCode problem `remove-methods-from-project`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RemainingMethods

  namespace AegisSpec.RemainingMethods

  def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun (x : Std.I64) => x.val)

  def outVals (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun (x : Std.I64) => x.val)

  def invocVals (invocations : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    invocations.val.map vecVals

  def HasEdge (invocations : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
    [a, b] ∈ invocVals invocations

  inductive Reach (invocations : Slice (alloc.vec.Vec Std.I64)) (k : ℤ) : ℤ → Prop where
    | refl : Reach invocations k k
    | step : {a b : ℤ} → Reach invocations k a → HasEdge invocations a b →
        Reach invocations k b

  def InS (n k : ℤ) (invocations : Slice (alloc.vec.Vec Std.I64)) (v : ℤ) : Prop :=
    0 ≤ v ∧ v < n ∧ Reach invocations k v

  def Blocked (n k : ℤ) (invocations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ a b : ℤ, HasEdge invocations a b ∧ InS n k invocations b ∧
      ¬ InS n k invocations a

  def occCount (v : ℤ) : List ℤ → ℕ
    | [] => 0
    | x :: xs => (if x = v then 1 else 0) + occCount v xs

  def Occurs (v : ℤ) (r : List ℤ) : Prop := v ∈ r

  def OccursOnce (v : ℤ) (r : List ℤ) : Prop := occCount v r = 1

  noncomputable def SCard (n k : ℤ) (invocations : Slice (alloc.vec.Vec Std.I64)) : ℕ := by
    classical
    exact ((List.range n.toNat).filter (fun i => Reach invocations k (i : ℤ))).length

  /-- Let S be the set of all v with 0 <= v < n such that v is reachable from k in the directed graph whose directed edges are the ordered pairs [a,b] occurring as invocations[i] for some i; reachability includes the zero-length path. Let blocked be true iff there exists i with 0 <= i < len(invocations), invocations[i] = [a,b], b in S, and a not in S. For every input satisfying the preconditions, the function returns a result r and: (1) if blocked is false, then for every v with 0 <= v < n, v occurs in r exactly once iff v is not in S, and v does not occur in r iff v is in S; (2) if blocked is true, then for every v with 0 <= v < n, v occurs in r exactly once. In both cases every element of r is one of the integers v with 0 <= v < n, and no integer occurs twice in r. Here v occurs in r exactly once means there is exactly one index i with 0 <= i < len(r) and r[i] = v.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_1 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∃ r : alloc.vec.Vec Std.I64,
        remaining_methods n k invocations = ok r ∧
        (Blocked n.val k.val invocations →
          ∀ v : ℤ, 0 ≤ v → v < n.val → OccursOnce v (outVals r)) ∧
        (¬ Blocked n.val k.val invocations →
          ∀ v : ℤ, 0 ≤ v → v < n.val →
            (OccursOnce v (outVals r) ↔ ¬ InS n.val k.val invocations v) ∧
            (¬ Occurs v (outVals r) ↔ InS n.val k.val invocations v)) ∧
        (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val) ∧
        (outVals r).Nodup := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∃ r : alloc.vec.Vec Std.I64,
          remaining_methods n k invocations = ok r ∧
          (Blocked n.val k.val invocations →
            ∀ v : ℤ, 0 ≤ v → v < n.val → OccursOnce v (outVals r)) ∧
          (¬ Blocked n.val k.val invocations →
            ∀ v : ℤ, 0 ≤ v → v < n.val →
              (OccursOnce v (outVals r) ↔ ¬ InS n.val k.val invocations v) ∧
              (¬ Occurs v (outVals r) ↔ InS n.val k.val invocations v)) ∧
          (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val) ∧
          (outVals r).Nodup) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_2 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∃ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∃ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r) := by
    sorry

  /-- Whenever the function returns a result r, every element r[i] with 0 <= i < len(r) satisfies 0 <= r[i] < n.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_3 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        ∀ (i : ℕ) (hi : i < (outVals r).length),
          0 ≤ (outVals r)[i] ∧ (outVals r)[i] < n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          ∀ (i : ℕ) (hi : i < (outVals r).length),
            0 ≤ (outVals r)[i] ∧ (outVals r)[i] < n.val) := by
    sorry

  /-- Let S be the set of all v with 0 <= v < n reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. Let blocked be true iff some edge [a,b] in invocations has b in S and a not in S. Let c be the number of v with 0 <= v < n and v in S. Whenever the function returns a result r, len(r) = n if blocked is true, and len(r) = n - c if blocked is false.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_4 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        (Blocked n.val k.val invocations → (outVals r).length = n.val.toNat) ∧
        (¬ Blocked n.val k.val invocations →
          (outVals r).length = n.val.toNat - SCard n.val k.val invocations) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          (Blocked n.val k.val invocations → (outVals r).length = n.val.toNat) ∧
          (¬ Blocked n.val k.val invocations →
            (outVals r).length = n.val.toNat - SCard n.val k.val invocations)) := by
    sorry

  /-- Whenever the function returns a result r, for every v with 0 <= v < n, v occurs in r exactly once iff v != k, and no other integer occurs in r.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; len(invocations) = 0; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_5 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (h_empty : invocations.val.length = 0)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        (∀ v : ℤ, 0 ≤ v → v < n.val → (OccursOnce v (outVals r) ↔ v ≠ k.val)) ∧
        (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (h_empty : invocations.val.length = 0)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          (∀ v : ℤ, 0 ≤ v → v < n.val → (OccursOnce v (outVals r) ↔ v ≠ k.val)) ∧
          (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 0.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs; every v with 0 <= v < n is reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. -/
  theorem spec_6 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup)
      (h_reach_all : ∀ v : ℤ, 0 ≤ v → v < n.val → Reach invocations k.val v) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        (outVals r).length = 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup)
        (h_reach_all : ∀ v : ℤ, 0 ≤ v → v < n.val → Reach invocations k.val v), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          (outVals r).length = 0) := by
    sorry

  /-- Let S be the set of all v with 0 <= v < n reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. Whenever the function returns a result r, for every v with 0 <= v < n, if v is not in S then v occurs in r at least once.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_7 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        ∀ v : ℤ, 0 ≤ v → v < n.val → ¬ InS n.val k.val invocations v →
          Occurs v (outVals r) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          ∀ v : ℤ, 0 ≤ v → v < n.val → ¬ InS n.val k.val invocations v →
            Occurs v (outVals r)) := by
    sorry

  /-- Let S be the set of all v with 0 <= v < n reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. Let blocked be true iff some edge [a,b] in invocations has b in S and a not in S. Whenever the function returns a result r, for every v with 0 <= v < n, if v is in S then v occurs in r at least once iff blocked is true.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_8 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        ∀ v : ℤ, 0 ≤ v → v < n.val → InS n.val k.val invocations v →
          (Occurs v (outVals r) ↔ Blocked n.val k.val invocations) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          ∀ v : ℤ, 0 ≤ v → v < n.val → InS n.val k.val invocations v →
            (Occurs v (outVals r) ↔ Blocked n.val k.val invocations)) := by
    sorry

  /-- Let S be the set of all v with 0 <= v < n reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. Let blocked be true iff some edge [a,b] in invocations has b in S and a not in S. Whenever the function returns a result r, the following are equivalent: (a) no v with 0 <= v < n and v in S occurs in r; (b) blocked is false.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_9 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        ((∀ v : ℤ, 0 ≤ v → v < n.val → InS n.val k.val invocations v →
            ¬ Occurs v (outVals r)) ↔ ¬ Blocked n.val k.val invocations) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          ((∀ v : ℤ, 0 ≤ v → v < n.val → InS n.val k.val invocations v →
              ¬ Occurs v (outVals r)) ↔ ¬ Blocked n.val k.val invocations)) := by
    sorry

  /-- Let S be the set of all v with 0 <= v < n reachable from k in the directed graph whose edges are the ordered pairs occurring in invocations, with reachability including the zero-length path. Let blocked be true iff some edge [a,b] in invocations has b in S and a not in S. Whenever the function returns a result r and blocked is true, r is a permutation of all method numbers 0 through n - 1; equivalently, len(r) = n, every element of r satisfies 0 <= r[i] < n, and for every v with 0 <= v < n, v occurs in r exactly once.
    Preconditions: 1 <= n <= 100000; 0 <= k <= n - 1; invocations is a slice of vectors with len(invocations) <= 200000; for every i with 0 <= i < len(invocations), len(invocations[i]) = 2, and if invocations[i] = [a_i, b_i] then 0 <= a_i < n, 0 <= b_i < n, and a_i != b_i; for every i and j with 0 <= i < j < len(invocations), invocations[i] != invocations[j] as ordered pairs. -/
  theorem spec_10 (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup) :
      ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
        Blocked n.val k.val invocations →
          (outVals r).length = n.val.toNat ∧
          (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val) ∧
          (∀ v : ℤ, 0 ≤ v → v < n.val → OccursOnce v (outVals r)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n k : Std.I64) (invocations : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup), ∀ r : alloc.vec.Vec Std.I64, remaining_methods n k invocations = ok r →
          Blocked n.val k.val invocations →
            (outVals r).length = n.val.toNat ∧
            (∀ x ∈ outVals r, 0 ≤ x ∧ x < n.val) ∧
            (∀ v : ℤ, 0 ≤ v → v < n.val → OccursOnce v (outVals r))) := by
    sorry

  /-- Let E(invocations) be the set of ordered pairs [a,b] that occur as invocations[i] for some i. For any two valid inputs (n,k,invocations) and (n,k,invocations'), if E(invocations) = E(invocations'), and the function returns r for the first input and r' for the second input, then for every v with 0 <= v < n, v occurs in r iff v occurs in r'.
    Preconditions: Both (n,k,invocations) and (n,k,invocations') are valid inputs: 1 <= n <= 100000; 0 <= k <= n - 1; each invocation list has length at most 200000; every inner vector has length 2 with entries [a,b] satisfying 0 <= a < n, 0 <= b < n, and a != b; and no ordered pair is repeated within either list. -/
  theorem spec_11 (n k : Std.I64)
      (invocations invocations' : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
      (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
      (h_len : invocations.val.length ≤ 200000)
      (h_pairs : ∀ p ∈ invocVals invocations,
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup : (invocVals invocations).Nodup)
      (h_len' : invocations'.val.length ≤ 200000)
      (h_pairs' : ∀ p ∈ invocVals invocations',
        ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
      (h_ndup' : (invocVals invocations').Nodup)
      (h_edges : ∀ a b : ℤ, HasEdge invocations a b ↔ HasEdge invocations' a b) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        remaining_methods n k invocations = ok r →
        remaining_methods n k invocations' = ok r' →
        ∀ v : ℤ, 0 ≤ v → v < n.val →
          (Occurs v (outVals r) ↔ Occurs v (outVals r')) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k : Std.I64)
        (invocations invocations' : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100000)
        (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1)
        (h_len : invocations.val.length ≤ 200000)
        (h_pairs : ∀ p ∈ invocVals invocations,
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup : (invocVals invocations).Nodup)
        (h_len' : invocations'.val.length ≤ 200000)
        (h_pairs' : ∀ p ∈ invocVals invocations',
          ∃ a b : ℤ, p = [a, b] ∧ 0 ≤ a ∧ a < n.val ∧ 0 ≤ b ∧ b < n.val ∧ a ≠ b)
        (h_ndup' : (invocVals invocations').Nodup)
        (h_edges : ∀ a b : ℤ, HasEdge invocations a b ↔ HasEdge invocations' a b), ∀ r r' : alloc.vec.Vec Std.I64,
          remaining_methods n k invocations = ok r →
          remaining_methods n k invocations' = ok r' →
          ∀ v : ℤ, 0 ≤ v → v < n.val →
            (Occurs v (outVals r) ↔ Occurs v (outVals r'))) := by
    sorry

  end AegisSpec.RemainingMethods
