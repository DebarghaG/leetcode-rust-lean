import Aegis.NumberOfPermutations.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPermutations.number_of_permutations`

LeetCode problem `count-the-number-of-inversions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfPermutations

  open Aeneas.Std

  def reqPair (requirements : Slice (alloc.vec.Vec I64)) (i : Nat) : Option (Int × Int) :=
    (requirements.val[i]?).bind (fun row =>
      (row.val[0]?).bind (fun e => (row.val[1]?).map (fun c => (e.val, c.val))))

  def numReqs (requirements : Slice (alloc.vec.Vec I64)) : Nat :=
    requirements.val.length

  def reqPairs (requirements : Slice (alloc.vec.Vec I64)) : List (Int × Int) :=
    (List.range (numReqs requirements)).filterMap (reqPair requirements)

  def invNat (perm : List Int) (e : Nat) : Nat :=
    ((List.range (e + 1)).flatMap (fun b => (List.range b).map (fun a => (a, b)))).countP
      (fun p =>
        match perm[p.1]?, perm[p.2]? with
        | some x, some y => decide (y < x)
        | _, _ => false)

  def inv (perm : List Int) (e : Int) : Int :=
    (invNat perm e.toNat : Int)

  def SatisfiesReqs (perm : List Int) (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ i : Nat, i < numReqs requirements →
      ∀ e c : Int, reqPair requirements i = some (e, c) → inv perm e = c

  def IsPermutation (n : Nat) (perm : List Int) : Prop :=
    perm.length = n ∧ (∀ x ∈ perm, 0 ≤ x ∧ x < (n : Int)) ∧ perm.Nodup

  def allSeqs (n : Nat) : Finset (List Int) :=
    (Finset.univ : Finset (Fin n → Fin n)).image
      (fun f => List.ofFn (fun i => ((f i).val : Int)))

  noncomputable def permCount (n : Nat) (requirements : Slice (alloc.vec.Vec I64)) : Nat := by
    classical
    exact ((allSeqs n).filter (fun perm => perm.Nodup ∧ SatisfiesReqs perm requirements)).card

  def WellFormed (n : I64) (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    2 ≤ n.val ∧ n.val ≤ 300 ∧
    1 ≤ numReqs requirements ∧ (numReqs requirements : Int) ≤ n.val ∧
    (∀ i : Nat, i < numReqs requirements →
      (requirements.val[i]?).map (fun row => row.val.length) = some 2 ∧
      ∃ e c : Int, reqPair requirements i = some (e, c) ∧
        0 ≤ e ∧ e ≤ n.val - 1 ∧ 0 ≤ c ∧ c ≤ 400) ∧
    (∀ i j : Nat, i < numReqs requirements → j < numReqs requirements → i ≠ j →
      ∀ e c e' c' : Int, reqPair requirements i = some (e, c) →
        reqPair requirements j = some (e', c') → e ≠ e') ∧
    (∃ i : Nat, i < numReqs requirements ∧
      ∀ e c : Int, reqPair requirements i = some (e, c) → e = n.val - 1)

  def HasExceedingReq (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ i : Nat, i < numReqs requirements ∧
      ∀ e c : Int, reqPair requirements i = some (e, c) → c > e * (e + 1) / 2

  def AllCountsZero (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ i : Nat, i < numReqs requirements →
      ∀ e c : Int, reqPair requirements i = some (e, c) → c = 0

  def AllCountsMax (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∀ i : Nat, i < numReqs requirements →
      ∀ e c : Int, reqPair requirements i = some (e, c) → c = e * (e + 1) / 2

  def SmallCaseCond (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    (∃ i : Nat, i < numReqs requirements ∧
      ∀ e c : Int, reqPair requirements i = some (e, c) → e = 1 ∧ (c = 0 ∨ c = 1)) ∧
    (∀ j : Nat, j < numReqs requirements →
      ∀ e c : Int, reqPair requirements j = some (e, c) → e = 0 → c = 0)

  def IsPermutationOf (requirements2 requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ σ : Nat → Nat,
      (∀ i : Nat, i < numReqs requirements → σ i < numReqs requirements2) ∧
      (∀ i j : Nat, i < numReqs requirements → j < numReqs requirements → σ i = σ j → i = j) ∧
      (∀ i : Nat, i < numReqs requirements → reqPair requirements2 (σ i) = reqPair requirements i)

  def HasTooLargeDrop (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    ∃ p q : Nat, p < numReqs requirements ∧ q < numReqs requirements ∧
      ∀ ep cp eq cq : Int, reqPair requirements p = some (ep, cp) →
        reqPair requirements q = some (eq, cq) →
        ep < eq ∧ cq - cp > (eq * (eq + 1) - ep * (ep + 1)) / 2

  def countFor (requirements : Slice (alloc.vec.Vec I64)) (e : Int) : Option Int :=
    (List.range (numReqs requirements)).findSome? (fun i =>
      match reqPair requirements i with
      | some (e', c) => if e' = e then some c else none
      | none => none)

  def StepCounts (n : I64) (requirements : Slice (alloc.vec.Vec I64)) : Prop :=
    (∀ c : Int, countFor requirements 0 = some c → c = 0) ∧
    (∀ e c0 c1 : Int, 1 ≤ e → e ≤ n.val - 1 →
      countFor requirements (e - 1) = some c0 → countFor requirements e = some c1 →
      0 ≤ c1 - c0 ∧ c1 - c0 ≤ e)

  /-- Whenever number_of_permutations n requirements returns a result r, r = (N mod 1000000007), where N is the number of sequences perm of length n such that: (1) perm is a permutation of {0,1,...,n-1}, i.e. every perm[k] is in 0..n-1 and all entries are distinct; and (2) for every i with 0 <= i < len(requirements), inv(perm, requirements[i][0]) = requirements[i][1]. Here, for a sequence perm and an integer e with 0 <= e < n, inv(perm,e) is the number of pairs (a,b) such that 0 <= a < b <= e and perm[a] > perm[b].
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. -/
  theorem spec_1 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        r.val = (permCount n.val.toNat requirements : Int) % 1000000007 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          r.val = (permCount n.val.toNat requirements : Int) % 1000000007) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail, overflow, read out of bounds, or panic.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. -/
  theorem spec_2 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) :
      ∃ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements), ∃ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. -/
  theorem spec_3 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. Additionally, there exists an index i with 0 <= i < len(requirements) such that requirements[i][1] > (requirements[i][0] * (requirements[i][0] + 1)) / 2. -/
  theorem spec_4 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hbig : HasExceedingReq requirements) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hbig : HasExceedingReq requirements), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if requirements[j][1] = 0 for every j with 0 <= j < len(requirements), and r = 0 otherwise.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. Additionally, there exists an index i with requirements[i][0] = n - 1 and requirements[i][1] = 0. -/
  theorem spec_5 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements)
      (hend : ∃ i : Nat, i < numReqs requirements ∧
        ∀ e c : Int, reqPair requirements i = some (e, c) → e = n.val - 1 ∧ c = 0) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        (AllCountsZero requirements → r.val = 1) ∧
        (¬ AllCountsZero requirements → r.val = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements)
        (hend : ∃ i : Nat, i < numReqs requirements ∧
          ∀ e c : Int, reqPair requirements i = some (e, c) → e = n.val - 1 ∧ c = 0), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          (AllCountsZero requirements → r.val = 1) ∧
          (¬ AllCountsZero requirements → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if for every j with 0 <= j < len(requirements), requirements[j][1] = (requirements[j][0] * (requirements[j][0] + 1)) / 2, and r = 0 otherwise.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. Additionally, there exists an index i with requirements[i][0] = n - 1 and requirements[i][1] = (n * (n - 1)) / 2. -/
  theorem spec_6 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements)
      (hend : ∃ i : Nat, i < numReqs requirements ∧
        ∀ e c : Int, reqPair requirements i = some (e, c) →
          e = n.val - 1 ∧ c = n.val * (n.val - 1) / 2) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        (AllCountsMax requirements → r.val = 1) ∧
        (¬ AllCountsMax requirements → r.val = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements)
        (hend : ∃ i : Nat, i < numReqs requirements ∧
          ∀ e c : Int, reqPair requirements i = some (e, c) →
            e = n.val - 1 ∧ c = n.val * (n.val - 1) / 2), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          (AllCountsMax requirements → r.val = 1) ∧
          (¬ AllCountsMax requirements → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if both (a) there is an index i with requirements[i][0] = 1 and (requirements[i][1] = 0 or requirements[i][1] = 1), and (b) requirements[j][1] = 0 for every j with requirements[j][0] = 0; otherwise r = 0.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. Additionally, n = 2. -/
  theorem spec_7 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hn : n.val = 2) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        (SmallCaseCond requirements → r.val = 1) ∧
        (¬ SmallCaseCond requirements → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hn : n.val = 2), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          (SmallCaseCond requirements → r.val = 1) ∧
          (¬ SmallCaseCond requirements → r.val = 0)) := by
    sorry

  /-- Whenever number_of_permutations n requirements returns r and number_of_permutations n requirements2 returns r2, we have r = r2.
    Preconditions: For a first input let requirements satisfy the base constraints: 2 <= n <= 300; 1 <= len(requirements) <= n; each entry has length 2; for every i, 0 <= requirements[i][0] <= n-1 and 0 <= requirements[i][1] <= 400; the end indices are pairwise distinct; and some end index is n-1. For a second input requirements2, assume requirements2 satisfies the same constraints and is a permutation of requirements: len(requirements2) = len(requirements) and there is a bijection between indices preserving the pair (requirements[i][0], requirements[i][1]). -/
  theorem spec_8 (n : I64) (requirements requirements2 : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hvalid2 : WellFormed n requirements2)
      (hlen : numReqs requirements2 = numReqs requirements)
      (hperm : IsPermutationOf requirements2 requirements) :
      ∀ r r2 : I64,
        Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        Aegis.NumberOfPermutations.number_of_permutations n requirements2 = ok r2 →
        r = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (requirements requirements2 : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hvalid2 : WellFormed n requirements2)
        (hlen : numReqs requirements2 = numReqs requirements)
        (hperm : IsPermutationOf requirements2 requirements), ∀ r r2 : I64,
          Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          Aegis.NumberOfPermutations.number_of_permutations n requirements2 = ok r2 →
          r = r2) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then there exists a sequence perm of length n that is a permutation of {0,1,...,n-1} and satisfies inv(perm, requirements[i][0]) = requirements[i][1] for every i with 0 <= i < len(requirements), where inv(perm,e) is the number of pairs (a,b) with 0 <= a < b <= e and perm[a] > perm[b].
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. -/
  theorem spec_9 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        0 < r.val →
        ∃ perm : List Int,
          IsPermutation n.val.toNat perm ∧ SatisfiesReqs perm requirements := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          0 < r.val →
          ∃ perm : List Int,
            IsPermutation n.val.toNat perm ∧ SatisfiesReqs perm requirements) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 or r = 1.
    Preconditions: Let m = len(requirements). The input satisfies all problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i with 0 <= i < m, writing e_i = requirements[i][0] and c_i = requirements[i][1], we have 0 <= e_i <= n - 1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and there is an index i with e_i = n - 1. Additionally, len(requirements) = n. -/
  theorem spec_10 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hlen : (numReqs requirements : Int) = n.val) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        r.val = 0 ∨ r.val = 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hlen : (numReqs requirements : Int) = n.val), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          r.val = 0 ∨ r.val = 1) := by
    sorry

  /-- Whenever number_of_permutations n requirements returns a result r, r = 0.
    Preconditions: Let m = len(requirements). The input satisfies the base problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i, with e_i = requirements[i][0] and c_i = requirements[i][1], 0 <= e_i <= n-1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and some e_i = n-1. Additionally, there exist indices p and q such that e_p < e_q and c_q - c_p > (e_q*(e_q+1) - e_p*(e_p+1))/2. -/
  theorem spec_11 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hdrop : HasTooLargeDrop requirements) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        r.val = 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hdrop : HasTooLargeDrop requirements), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          r.val = 0) := by
    sorry

  /-- Whenever number_of_permutations n requirements returns a result r, r = 1 if c_0 = 0 and for every e with 1 <= e <= n-1 we have 0 <= c_e - c_{e-1} <= e; otherwise r = 0.
    Preconditions: Let m = len(requirements). The input satisfies the base problem constraints: 2 <= n <= 300; 1 <= m <= n; each requirements[i] has length exactly 2; for every i, with e_i = requirements[i][0] and c_i = requirements[i][1], 0 <= e_i <= n-1 and 0 <= c_i <= 400; the e_i are pairwise distinct; and some e_i = n-1. Additionally, len(requirements) = n. Since the end indices are unique and lie in 0..n-1, for each e in 0..n-1 let c_e be the unique requirement count with end index e. -/
  theorem spec_12 (n : I64) (requirements : Slice (alloc.vec.Vec I64))
      (hvalid : WellFormed n requirements) (hlen : (numReqs requirements : Int) = n.val) :
      ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
        (StepCounts n requirements → r.val = 1) ∧
        (¬ StepCounts n requirements → r.val = 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : I64) (requirements : Slice (alloc.vec.Vec I64))
        (hvalid : WellFormed n requirements) (hlen : (numReqs requirements : Int) = n.val), ∀ r : I64, Aegis.NumberOfPermutations.number_of_permutations n requirements = ok r →
          (StepCounts n requirements → r.val = 1) ∧
          (¬ StepCounts n requirements → r.val = 0)) := by
    sorry

  end AegisSpec.NumberOfPermutations
