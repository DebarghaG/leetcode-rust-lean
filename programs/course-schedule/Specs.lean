import Aegis.CanFinish.Code.Funs

/-!
# Specifications of `Aegis.CanFinish.can_finish`

LeetCode problem `course-schedule`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CanFinish

  namespace AegisSpec.CanFinish

  def pairsOf (prerequisites : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    prerequisites.val.map (fun v => v.val.map (fun x => x.val))

  def ValidPrereqs (n : Int) (P : List (List Int)) : Prop :=
    P.length ≤ 5000 ∧
      (∀ v ∈ P, v.length = 2) ∧
        (∀ v ∈ P, ∀ x ∈ v, 0 ≤ x ∧ x < n) ∧
          P.Nodup

  def IsCoursePermutation (n : Int) (p : List Int) : Prop :=
    p.Nodup ∧ p.length = n.toNat ∧ ∀ x ∈ p, 0 ≤ x ∧ x < n

  def pairFst (P : List (List Int)) (i : Nat) : Int := (P[i]!).getD 0 0

  def pairSnd (P : List (List Int)) (i : Nat) : Int := (P[i]!).getD 1 0

  def PairOccurs (P : List (List Int)) (a b : Int) : Prop := [a, b] ∈ P

  /-- The function returns a result r, and r = true if and only if there exists a sequence p of length numCourses such that (1) p is a permutation of {0, 1, ..., numCourses-1}, meaning every course label in that range occurs exactly once in p, and (2) for every i with 0 <= i < len(prerequisites), letting a = prerequisites[i][0] and b = prerequisites[i][1], the unique index j_b with p[j_b] = b is strictly less than the unique index j_a with p[j_a] = a (so prerequisite b is taken before course a).
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct. -/
  theorem spec_1
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites)) :
      ∃ r : Bool,
        can_finish numCourses prerequisites = ok r ∧
          (r = true ↔
            ∃ p : List Int,
              IsCoursePermutation numCourses.val p ∧
                ∀ i : Nat, i < prerequisites.val.length →
                  p.idxOf (pairSnd (pairsOf prerequisites) i) <
                    p.idxOf (pairFst (pairsOf prerequisites) i)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites)), ∃ r : Bool,
          can_finish numCourses prerequisites = ok r ∧
            (r = true ↔
              ∃ p : List Int,
                IsCoursePermutation numCourses.val p ∧
                  ∀ i : Nat, i < prerequisites.val.length →
                    p.idxOf (pairSnd (pairsOf prerequisites) i) <
                      p.idxOf (pairFst (pairsOf prerequisites) i))) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct. -/
  theorem spec_2
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites)) :
      ∃ r : Bool, can_finish numCourses prerequisites = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites)), ∃ r : Bool, can_finish numCourses prerequisites = ok r) := by
    sorry

  /-- The function returns a result r and r = true.
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct; len(prerequisites) = 0. -/
  theorem spec_3
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
      (h_empty : prerequisites.val.length = 0) :
      ∃ r : Bool, can_finish numCourses prerequisites = ok r ∧ r = true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
        (h_empty : prerequisites.val.length = 0), ∃ r : Bool, can_finish numCourses prerequisites = ok r ∧ r = true) := by
    sorry

  /-- The function returns a result r and r = false.
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct; there exists i with 0 <= i < len(prerequisites) such that prerequisites[i][0] = prerequisites[i][1]. -/
  theorem spec_4
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
      (h_self : ∃ i : Nat, i < prerequisites.val.length ∧
        pairFst (pairsOf prerequisites) i = pairSnd (pairsOf prerequisites) i) :
      ∃ r : Bool, can_finish numCourses prerequisites = ok r ∧ r = false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
        (h_self : ∃ i : Nat, i < prerequisites.val.length ∧
          pairFst (pairsOf prerequisites) i = pairSnd (pairsOf prerequisites) i), ∃ r : Bool, can_finish numCourses prerequisites = ok r ∧ r = false) := by
    sorry

  /-- Let a = prerequisites[0][0] and b = prerequisites[0][1]. The function returns a result r and r = true if and only if a != b.
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct; len(prerequisites) = 1. -/
  theorem spec_5
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
      (h_len : prerequisites.val.length = 1) :
      ∃ r : Bool,
        can_finish numCourses prerequisites = ok r ∧
          (r = true ↔
            pairFst (pairsOf prerequisites) 0 ≠ pairSnd (pairsOf prerequisites) 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
        (h_len : prerequisites.val.length = 1), ∃ r : Bool,
          can_finish numCourses prerequisites = ok r ∧
            (r = true ↔
              pairFst (pairsOf prerequisites) 0 ≠ pairSnd (pairsOf prerequisites) 0)) := by
    sorry

  /-- Let r_P be the result of can_finish(numCourses, P) and r_Q the result of can_finish(numCourses, Q). Both calls return results, and r_P = r_Q.
    Preconditions: 1 <= numCourses <= 2000; P and Q are two lists of pairs such that each of P and Q satisfies: 0 <= len <= 5000, each element has length 2, all entries are in [0,numCourses), and all pairs are distinct; and Q is a reordering of P (Q is obtained by permuting the elements of P). -/
  theorem spec_6
      (numCourses : I64) (P Q : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (hP : ValidPrereqs numCourses.val (pairsOf P))
      (hQ : ValidPrereqs numCourses.val (pairsOf Q))
      (h_perm : (pairsOf Q).Perm (pairsOf P)) :
      ∃ rP rQ : Bool,
        can_finish numCourses P = ok rP ∧
          can_finish numCourses Q = ok rQ ∧ rP = rQ := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (numCourses : I64) (P Q : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (hP : ValidPrereqs numCourses.val (pairsOf P))
        (hQ : ValidPrereqs numCourses.val (pairsOf Q))
        (h_perm : (pairsOf Q).Perm (pairsOf P)), ∃ rP rQ : Bool,
          can_finish numCourses P = ok rP ∧
            can_finish numCourses Q = ok rQ ∧ rP = rQ) := by
    sorry

  /-- Define Pπ to be the list of the same length as P whose i-th element is [π(P[i][0]), π(P[i][1])]. Let r be the result of can_finish(numCourses, P) and r' the result of can_finish(numCourses, Pπ). Both calls return results, and r = r'.
    Preconditions: 1 <= numCourses <= 2000; P is a valid prerequisite list for numCourses: 0 <= len(P) <= 5000, each element has length 2, all entries are in [0,numCourses), and all pairs are distinct; π is a bijection from {0,...,numCourses-1} to itself. -/
  theorem spec_7
      (numCourses : I64) (P Pπ : Slice (alloc.vec.Vec I64)) (π : Int → Int)
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (hP : ValidPrereqs numCourses.val (pairsOf P))
      (hπ_range : ∀ x : Int, 0 ≤ x ∧ x < numCourses.val → 0 ≤ π x ∧ π x < numCourses.val)
      (hπ_inj : ∀ x y : Int, 0 ≤ x ∧ x < numCourses.val → 0 ≤ y ∧ y < numCourses.val →
        π x = π y → x = y)
      (hPπ : pairsOf Pπ = (pairsOf P).map (fun v => v.map π)) :
      ∃ r r' : Bool,
        can_finish numCourses P = ok r ∧
          can_finish numCourses Pπ = ok r' ∧ r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (numCourses : I64) (P Pπ : Slice (alloc.vec.Vec I64)) (π : Int → Int)
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (hP : ValidPrereqs numCourses.val (pairsOf P))
        (hπ_range : ∀ x : Int, 0 ≤ x ∧ x < numCourses.val → 0 ≤ π x ∧ π x < numCourses.val)
        (hπ_inj : ∀ x y : Int, 0 ≤ x ∧ x < numCourses.val → 0 ≤ y ∧ y < numCourses.val →
          π x = π y → x = y)
        (hPπ : pairsOf Pπ = (pairsOf P).map (fun v => v.map π)), ∃ r r' : Bool,
          can_finish numCourses P = ok r ∧
            can_finish numCourses Pπ = ok r' ∧ r = r') := by
    sorry

  /-- Let r be the result of can_finish(n, P) and r' the result of can_finish(n+1, P). Both calls return results, and r = r'.
    Preconditions: 1 <= n < 2000; P is a valid prerequisite list for n: 0 <= len(P) <= 5000, each element has length 2, all entries are in [0,n), and all pairs are distinct. -/
  theorem spec_8
      (n n' : I64) (P : Slice (alloc.vec.Vec I64))
      (h_n : 1 ≤ n.val ∧ n.val < 2000)
      (h_n' : n'.val = n.val + 1)
      (hP : ValidPrereqs n.val (pairsOf P)) :
      ∃ r r' : Bool,
        can_finish n P = ok r ∧
          can_finish n' P = ok r' ∧ r = r' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n n' : I64) (P : Slice (alloc.vec.Vec I64))
        (h_n : 1 ≤ n.val ∧ n.val < 2000)
        (h_n' : n'.val = n.val + 1)
        (hP : ValidPrereqs n.val (pairsOf P)), ∃ r r' : Bool,
          can_finish n P = ok r ∧
            can_finish n' P = ok r' ∧ r = r') := by
    sorry

  /-- Let r_P be the result of can_finish(numCourses, P) and r_Q the result of can_finish(numCourses, Q). Both calls return results, and if r_Q = true then r_P = true.
    Preconditions: 1 <= numCourses <= 2000; P and Q are valid prerequisite lists for numCourses (each has 0 <= len <= 5000, each element has length 2, all entries are in [0,numCourses), and all pairs are distinct); every pair that occurs in P also occurs in Q. -/
  theorem spec_9
      (numCourses : I64) (P Q : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (hP : ValidPrereqs numCourses.val (pairsOf P))
      (hQ : ValidPrereqs numCourses.val (pairsOf Q))
      (h_subset : ∀ v ∈ pairsOf P, v ∈ pairsOf Q) :
      ∃ rP rQ : Bool,
        can_finish numCourses P = ok rP ∧
          can_finish numCourses Q = ok rQ ∧ (rQ = true → rP = true) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (numCourses : I64) (P Q : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (hP : ValidPrereqs numCourses.val (pairsOf P))
        (hQ : ValidPrereqs numCourses.val (pairsOf Q))
        (h_subset : ∀ v ∈ pairsOf P, v ∈ pairsOf Q), ∃ rP rQ : Bool,
          can_finish numCourses P = ok rP ∧
            can_finish numCourses Q = ok rQ ∧ (rQ = true → rP = true)) := by
    sorry

  /-- The function returns a result r and r = true if and only if len(prerequisites) = 0.
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct; numCourses = 1. -/
  theorem spec_10
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
      (h_one : numCourses.val = 1) :
      ∃ r : Bool,
        can_finish numCourses prerequisites = ok r ∧
          (r = true ↔ prerequisites.val.length = 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
        (h_one : numCourses.val = 1), ∃ r : Bool,
          can_finish numCourses prerequisites = ok r ∧
            (r = true ↔ prerequisites.val.length = 0)) := by
    sorry

  /-- The function returns a result r, and r = true if and only if (a) no prerequisite pair is [0,0] or [1,1], and (b) it is not the case that both [0,1] and [1,0] occur in prerequisites.
    Preconditions: 1 <= numCourses <= 2000; 0 <= len(prerequisites) <= 5000; for every i with 0 <= i < len(prerequisites), len(prerequisites[i]) = 2; for every i with 0 <= i < len(prerequisites), 0 <= prerequisites[i][0] < numCourses and 0 <= prerequisites[i][1] < numCourses; all pairs prerequisites[i] are distinct; numCourses = 2. -/
  theorem spec_11
      (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
      (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
      (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
      (h_two : numCourses.val = 2) :
      ∃ r : Bool,
        can_finish numCourses prerequisites = ok r ∧
          (r = true ↔
            ¬ PairOccurs (pairsOf prerequisites) 0 0 ∧
              ¬ PairOccurs (pairsOf prerequisites) 1 1 ∧
                ¬ (PairOccurs (pairsOf prerequisites) 0 1 ∧
                  PairOccurs (pairsOf prerequisites) 1 0)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (numCourses : I64) (prerequisites : Slice (alloc.vec.Vec I64))
        (h_numCourses : 1 ≤ numCourses.val ∧ numCourses.val ≤ 2000)
        (h_valid : ValidPrereqs numCourses.val (pairsOf prerequisites))
        (h_two : numCourses.val = 2), ∃ r : Bool,
          can_finish numCourses prerequisites = ok r ∧
            (r = true ↔
              ¬ PairOccurs (pairsOf prerequisites) 0 0 ∧
                ¬ PairOccurs (pairsOf prerequisites) 1 1 ∧
                  ¬ (PairOccurs (pairsOf prerequisites) 0 1 ∧
                    PairOccurs (pairsOf prerequisites) 1 0))) := by
    sorry

  end AegisSpec.CanFinish
