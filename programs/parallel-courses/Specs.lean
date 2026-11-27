import Aegis.MinimumSemesters.Code.Funs

/-!
# Specifications of `Aegis.MinimumSemesters.minimum_semesters`

LeetCode problem `parallel-courses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumSemesters

def vecVals (v : alloc.vec.Vec Std.I64) : List ℤ :=
  v.val.map (fun x => x.val)

def IsPair (v : alloc.vec.Vec Std.I64) (a b : ℤ) : Prop :=
  vecVals v = [a, b]

def OccursIn (relations : Slice (alloc.vec.Vec Std.I64)) (a b : ℤ) : Prop :=
  ∃ v ∈ relations.val, IsPair v a b

def pairAt (relations : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : Option (List ℤ) :=
  (relations.val[i]?).map vecVals

def ValidN (n : ℤ) : Prop :=
  1 ≤ n ∧ n ≤ 5000

def ValidRelations (n : ℤ) (relations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  relations.val.length ≤ 5000 ∧
    (∀ v ∈ relations.val, ∃ a b : ℤ,
      IsPair v a b ∧ 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ a ≠ b) ∧
    (relations.val.map vecVals).Nodup

def BaseInput (n : ℤ) (relations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ValidN n ∧ ValidRelations n relations

def IsSchedule (n k : ℤ) (relations : Slice (alloc.vec.Vec Std.I64))
    (sem : ℤ → ℤ) : Prop :=
  (∀ c : ℤ, 1 ≤ c → c ≤ n → 1 ≤ sem c ∧ sem c ≤ k) ∧
    (∀ a b : ℤ, OccursIn relations a b → sem a < sem b)

def HasSchedule (n k : ℤ) (relations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ sem : ℤ → ℤ, IsSchedule n k relations sem

def IsWalkUpTo (relations : Slice (alloc.vec.Vec Std.I64)) (c : ℕ → ℤ) (L : ℤ) : Prop :=
  ∀ j : ℕ, (j : ℤ) < L → OccursIn relations (c j) (c (j + 1))

def HasDirectedCycle (n : ℤ) (relations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ (L : ℕ) (c : ℕ → ℤ),
    1 ≤ L ∧ c L = c 0 ∧
      (∀ i : ℕ, i ≤ L → 1 ≤ c i ∧ c i ≤ n) ∧
      IsWalkUpTo relations c (L : ℤ)

def IsPermutationOf (relations relations2 : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  relations2.val.length = relations.val.length ∧
    ∃ f : ℕ → ℕ,
      (∀ i : ℕ, i < relations.val.length → f i < relations2.val.length) ∧
        (∀ i : ℕ, i < relations.val.length → pairAt relations2 (f i) = pairAt relations i) ∧
        (∀ j : ℕ, j < relations2.val.length →
          ∃ i : ℕ, i < relations.val.length ∧ f i = j)

def ContainedIn (relations1 relations2 : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∀ i : ℕ, i < relations1.val.length →
    ∃ j : ℕ, j < relations2.val.length ∧ pairAt relations2 j = pairAt relations1 i

def IsCourseChain (n : ℤ) (relations : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  ∃ c : ℕ → ℤ,
    (∀ i : ℕ, 1 ≤ i → (i : ℤ) ≤ n → 1 ≤ c i ∧ c i ≤ n) ∧
      (∀ i j : ℕ,
        1 ≤ i → (i : ℤ) ≤ n → 1 ≤ j → (j : ℤ) ≤ n → c i = c j → i = j) ∧
      (∀ i : ℕ, 1 ≤ i → (i : ℤ) < n → OccursIn relations (c i) (c (i + 1))) ∧
      (∀ a b : ℤ, OccursIn relations a b →
        ∃ i : ℕ, 1 ≤ i ∧ (i : ℤ) < n ∧ c i = a ∧ c (i + 1) = b)

def IsLabelPermutation (n : ℤ) (pi : ℤ → ℤ) : Prop :=
  (∀ c : ℤ, 1 ≤ c → c ≤ n → 1 ≤ pi c ∧ pi c ≤ n) ∧
    (∀ c d : ℤ, 1 ≤ c → c ≤ n → 1 ≤ d → d ≤ n → pi c = pi d → c = d) ∧
    (∀ d : ℤ, 1 ≤ d → d ≤ n → ∃ c : ℤ, 1 ≤ c ∧ c ≤ n ∧ pi c = d)

def IsRenaming (n : ℤ) (pi : ℤ → ℤ) (relations relations2 : Slice (alloc.vec.Vec Std.I64)) :
    Prop :=
  IsLabelPermutation n pi ∧
    (∀ a b : ℤ, OccursIn relations a b → OccursIn relations2 (pi a) (pi b)) ∧
    (∀ a b : ℤ, OccursIn relations2 a b →
      ∃ a' b' : ℤ, OccursIn relations a' b' ∧ pi a' = a ∧ pi b' = b)

/-- For every input satisfying the preconditions, minimum_semesters(n, relations) returns a result r; it does not fail.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_1 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∃ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∃ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r, either r = -1 or 1 <= r <= n.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_2 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val)) := by
  sorry

/-- The function returns a result r, and r is characterized as follows. For an integer k >= 1, call a total function sem from {1,...,n} to {1,...,k} a k-semester schedule if for every relation [a,b] appearing in relations we have sem(a) < sem(b). If there exists a k-semester schedule for some k >= 1, then r is the least such k; otherwise r = -1.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_3 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∃ r : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r ∧
        ((∃ k : ℤ, 1 ≤ k ∧ HasSchedule n.val k relations) →
          (1 ≤ r.val ∧ HasSchedule n.val r.val relations ∧
            ∀ k : ℤ, 1 ≤ k → HasSchedule n.val k relations → r.val ≤ k)) ∧
        ((¬ ∃ k : ℤ, 1 ≤ k ∧ HasSchedule n.val k relations) → r.val = -1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∃ r : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r ∧
        ((∃ k : ℤ, 1 ≤ k ∧ HasSchedule n.val k relations) →
          (1 ≤ r.val ∧ HasSchedule n.val r.val relations ∧
            ∀ k : ℤ, 1 ≤ k → HasSchedule n.val k relations → r.val ≤ k)) ∧
        ((¬ ∃ k : ℤ, 1 ≤ k ∧ HasSchedule n.val k relations) → r.val = -1)) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r, r = 1 if and only if len(relations) = 0.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_4 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      (r.val = 1 ↔ relations.val.length = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      (r.val = 1 ↔ relations.val.length = 0)) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r, r = -1 if and only if the directed graph on vertices {1,...,n} with an edge a -> b for each relation [a,b] in relations contains a directed cycle, that is, there exist L >= 1 and courses c_0,...,c_L such that c_L = c_0, each c_i is in {1,...,n}, and for every j with 0 <= j < L the ordered pair [c_j,c_{j+1}] is in relations.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_5 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      (r.val = -1 ↔ HasDirectedCycle n.val relations) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      (r.val = -1 ↔ HasDirectedCycle n.val relations)) := by
  sorry

/-- Under these additional preconditions, minimum_semesters(n, relations) returns n.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. Additionally, there exists a sequence c_1,...,c_n of courses such that {c_1,...,c_n} = {1,...,n} and relations consists exactly of the n-1 ordered pairs [c_i,c_{i+1}] for 1 <= i < n. -/
theorem spec_6 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) (hchain : IsCourseChain n.val relations) :
    Aegis.MinimumSemesters.minimum_semesters n relations = ok n := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) (hchain : IsCourseChain n.val relations), Aegis.MinimumSemesters.minimum_semesters n relations = ok n) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r with r != -1, there exists a total function sem from {1,...,n} to {1,...,r} such that for every relation [a,b] in relations we have sem(a) < sem(b).
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_7 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 → ∃ sem : ℤ → ℤ, IsSchedule n.val r.val relations sem := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 → ∃ sem : ℤ → ℤ, IsSchedule n.val r.val relations sem) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r with r != -1, for every integer k with 1 <= k < r there does not exist a total function sem from {1,...,n} to {1,...,k} such that for every relation [a,b] in relations we have sem(a) < sem(b).
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_8 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 → ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ HasSchedule n.val k relations := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 → ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ HasSchedule n.val k relations) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r with r != -1, for every L >= 0 and every sequence of courses c_0,...,c_L such that for each j with 0 <= j < L the ordered pair [c_j,c_{j+1}] is in relations, we have r >= L+1.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_9 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∀ (L : ℕ) (c : ℕ → ℤ), IsWalkUpTo relations c (L : ℤ) → (L : ℤ) + 1 ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∀ (L : ℕ) (c : ℕ → ℤ), IsWalkUpTo relations c (L : ℤ) → (L : ℤ) + 1 ≤ r.val) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r with r != -1, there exists a sequence of courses c_0,...,c_{r-1} such that each c_i is in {1,...,n} and for every j with 0 <= j < r-1 the ordered pair [c_j,c_{j+1}] is in relations.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_10 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∃ c : ℕ → ℤ,
          (∀ i : ℕ, (i : ℤ) ≤ r.val - 1 → 1 ≤ c i ∧ c i ≤ n.val) ∧
            IsWalkUpTo relations c (r.val - 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∃ c : ℕ → ℤ,
          (∀ i : ℕ, (i : ℤ) ≤ r.val - 1 → 1 ≤ c i ∧ c i ≤ n.val) ∧
            IsWalkUpTo relations c (r.val - 1)) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r and minimum_semesters(n, relations2) returns a result r2, we have r = r2.
  Preconditions: 1 <= n <= 5000. relations and relations2 each satisfy: 0 <= len(relations) <= 5000 and 0 <= len(relations2) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], 1 <= a <= n, 1 <= b <= n, and a != b; all ordered pairs in relations are distinct; and the analogous conditions hold with relations2 in place of relations. Also relations2 is a permutation of relations: len(relations2) = len(relations) and there exists a bijection f from {0,...,len(relations)-1} to {0,...,len(relations2)-1} such that relations[i] = relations2[f(i)] for every i. -/
theorem spec_11 (n : Std.I64) (relations relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations)
    (h2 : ValidRelations n.val relations2) (hperm : IsPermutationOf relations relations2) :
    ∀ r r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 → r = r2 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (relations relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations)
    (h2 : ValidRelations n.val relations2) (hperm : IsPermutationOf relations relations2), ∀ r r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 → r = r2) := by
  sorry

/-- Let r1 be the result of minimum_semesters(n, relations1) and r2 be the result of minimum_semesters(n, relations2). Whenever both calls return results, if r2 != -1 then r1 != -1 and r1 <= r2.
  Preconditions: 1 <= n <= 5000. relations1 and relations2 each satisfy: 0 <= len(relations1) <= 5000 and 0 <= len(relations2) <= 5000; for every i with 0 <= i < len(relations1), len(relations1[i]) = 2; letting a = relations1[i][0] and b = relations1[i][1], 1 <= a <= n, 1 <= b <= n, and a != b; all ordered pairs in relations1 are distinct; and the analogous conditions hold for relations2. Also, for every i with 0 <= i < len(relations1), the ordered pair relations1[i] occurs in relations2, i.e. there exists j with 0 <= j < len(relations2) such that relations2[j] = relations1[i]. -/
theorem spec_12 (n : Std.I64) (relations1 relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations1)
    (h2 : ValidRelations n.val relations2) (hsub : ContainedIn relations1 relations2) :
    ∀ r1 r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations1 = ok r1 →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 →
          r2.val ≠ -1 → r1.val ≠ -1 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Std.I64) (relations1 relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations1)
    (h2 : ValidRelations n.val relations2) (hsub : ContainedIn relations1 relations2), ∀ r1 r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations1 = ok r1 →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 →
          r2.val ≠ -1 → r1.val ≠ -1 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns a result r with r != -1, there exists a total function sem from {1,...,n} to {1,...,r} such that for every relation [a,b] in relations we have sem(a) < sem(b), and for every s with 1 <= s <= r there exists a course c in {1,...,n} with sem(c) = s.
  Preconditions: 1 <= n <= 5000; 0 <= len(relations) <= 5000; for every i with 0 <= i < len(relations), len(relations[i]) = 2; letting a = relations[i][0] and b = relations[i][1], we have 1 <= a <= n, 1 <= b <= n, and a != b; and for every i,j with 0 <= i < len(relations), 0 <= j < len(relations), and i != j, relations[i] != relations[j]. -/
theorem spec_13 (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations) :
    ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∃ sem : ℤ → ℤ,
          IsSchedule n.val r.val relations sem ∧
            (∀ s : ℤ, 1 ≤ s → s ≤ r.val → ∃ c : ℤ, 1 ≤ c ∧ c ≤ n.val ∧ sem c = s) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (relations : Slice (alloc.vec.Vec Std.I64))
    (h : BaseInput n.val relations), ∀ r : Std.I64, Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
      r.val ≠ -1 →
        ∃ sem : ℤ → ℤ,
          IsSchedule n.val r.val relations sem ∧
            (∀ s : ℤ, 1 ≤ s → s ≤ r.val → ∃ c : ℤ, 1 ≤ c ∧ c ≤ n.val ∧ sem c = s)) := by
  sorry

/-- Whenever minimum_semesters(n, relations) returns r and minimum_semesters(n, relations2) returns r2, we have r = r2; that is, renaming the course labels does not change the minimum number of semesters, including the -1 case.
  Preconditions: 1 <= n <= 5000; relations and relations2 are arrays of ordered pairs of courses satisfying the base input conditions: 0 <= len <= 5000, every entry has length 2, both entries lie in {1,...,n}, no pair has equal endpoints, and within each array all ordered pairs are distinct. Additionally, there exists a permutation pi of {1,...,n} such that relations2 consists exactly of the ordered pairs [pi(a), pi(b)] for every [a,b] in relations. -/
theorem spec_14 (n : Std.I64) (relations relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations)
    (h2 : ValidRelations n.val relations2)
    (hrename : ∃ pi : ℤ → ℤ, IsRenaming n.val pi relations relations2) :
    ∀ r r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 → r = r2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (relations relations2 : Slice (alloc.vec.Vec Std.I64))
    (h : ValidN n.val) (h1 : ValidRelations n.val relations)
    (h2 : ValidRelations n.val relations2)
    (hrename : ∃ pi : ℤ → ℤ, IsRenaming n.val pi relations relations2), ∀ r r2 : Std.I64,
      Aegis.MinimumSemesters.minimum_semesters n relations = ok r →
        Aegis.MinimumSemesters.minimum_semesters n relations2 = ok r2 → r = r2) := by
  sorry

end AegisSpec.MinimumSemesters
