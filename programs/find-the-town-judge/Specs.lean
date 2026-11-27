import Aegis.FindJudge.Code.Funs

/-!
# Specifications of `Aegis.FindJudge.find_judge`

LeetCode problem `find-the-town-judge`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindJudge

  abbrev TrustVec := Slice (alloc.vec.Vec Std.I64)

  def trustLen (trust : TrustVec) : Nat := trust.val.length

  def lenAt (trust : TrustVec) (i : Nat) : Option Nat :=
    (trust.val[i]?).map (fun v => v.val.length)

  def pairAt (trust : TrustVec) (i : Nat) : Option (ℤ × ℤ) :=
    match trust.val[i]? with
    | some v =>
      match v.val with
      | a :: b :: [] => some (a.val, b.val)
      | _ => none
    | _ => none

  def fstAt (trust : TrustVec) (i : Nat) : Option ℤ := (pairAt trust i).map Prod.fst

  def sndAt (trust : TrustVec) (i : Nat) : Option ℤ := (pairAt trust i).map Prod.snd

  def pairList (trust : TrustVec) : List (ℤ × ℤ) :=
    (List.range (trustLen trust)).filterMap (pairAt trust)

  def indeg (trust : TrustVec) (v : ℤ) : Nat :=
    ((List.range (trustLen trust)).filter (fun i => decide (sndAt trust i = some v))).length

  def outdeg (trust : TrustVec) (v : ℤ) : Nat :=
    ((List.range (trustLen trust)).filter (fun i => decide (fstAt trust i = some v))).length

  def IsPair (n : ℤ) (p : ℤ × ℤ) : Prop :=
    1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ n ∧ p.1 ≠ p.2

  def Precond (n : Std.I64) (trust : TrustVec) : Prop :=
    1 ≤ n.val ∧ n.val ≤ 1000 ∧
    trustLen trust ≤ 10000 ∧
    (∀ i : Nat, i < trustLen trust → lenAt trust i = some 2) ∧
    (∀ i : Nat, i < trustLen trust →
      ∃ p : ℤ × ℤ, pairAt trust i = some p ∧ IsPair n.val p) ∧
    (∀ i j : Nat, i < trustLen trust → j < trustLen trust → i ≠ j →
      pairAt trust i ≠ pairAt trust j)

  def NoOut (trust : TrustVec) (v : ℤ) : Prop :=
    ∀ i : Nat, i < trustLen trust → fstAt trust i ≠ some v

  def AllIn (n : ℤ) (trust : TrustVec) (v : ℤ) : Prop :=
    ∀ u : ℤ, 1 ≤ u → u ≤ n → u ≠ v →
      ∃ i : Nat, i < trustLen trust ∧ fstAt trust i = some u ∧ sndAt trust i = some v

  def IsJudge (n : ℤ) (trust : TrustVec) (v : ℤ) : Prop :=
    1 ≤ v ∧ v ≤ n ∧ NoOut trust v ∧ AllIn n trust v

  /-- Define that a label v is a judge exactly when 1 <= v <= n, there is no index i with 0 <= i < len(trust) and trust[i][0] = v, and for every label u with 1 <= u <= n and u != v there exists an index i with 0 <= i < len(trust), trust[i][0] = u, and trust[i][1] = v. The function returns a result r and: if a judge exists, then r is its label (under the preconditions there is at most one such label); if no judge exists, then r = -1.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_1 (n : Std.I64) (trust : TrustVec) (h : Precond n trust) :
      ∃ r : Std.I64, Aegis.FindJudge.find_judge n trust = ok r ∧
        ((∃ v : ℤ, IsJudge n.val trust v ∧ r.val = v) ∨
         (r.val = -1 ∧ ¬ ∃ v : ℤ, IsJudge n.val trust v)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust), ∃ r : Std.I64, Aegis.FindJudge.find_judge n trust = ok r ∧
          ((∃ v : ℤ, IsJudge n.val trust v ∧ r.val = v) ∨
           (r.val = -1 ∧ ¬ ∃ v : ℤ, IsJudge n.val trust v))) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, panic, or out-of-bounds error) for any input satisfying the preconditions.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_2 (n : Std.I64) (trust : TrustVec) (h : Precond n trust) :
      ∃ r : Std.I64, Aegis.FindJudge.find_judge n trust = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust), ∃ r : Std.I64, Aegis.FindJudge.find_judge n trust = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= n.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_3 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) :
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r), r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ n.val)) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every label u with 1 <= u <= n there is no index i with 0 <= i < len(trust) such that trust[i][0] = r and trust[i][1] = u.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_4 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1) :
      ∀ u : ℤ, 1 ≤ u → u ≤ n.val →
        ¬ ∃ i : Nat, i < trustLen trust ∧ fstAt trust i = some r.val ∧
            sndAt trust i = some u := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1), ∀ u : ℤ, 1 ≤ u → u ≤ n.val →
          ¬ ∃ i : Nat, i < trustLen trust ∧ fstAt trust i = some r.val ∧
              sndAt trust i = some u) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every label u with 1 <= u <= n and u != r, there exists an index i with 0 <= i < len(trust) such that trust[i][0] = u and trust[i][1] = r.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_5 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1) :
      ∀ u : ℤ, 1 ≤ u → u ≤ n.val → u ≠ r.val →
        ∃ i : Nat, i < trustLen trust ∧ fstAt trust i = some u ∧ sndAt trust i = some r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1), ∀ u : ℤ, 1 ≤ u → u ≤ n.val → u ≠ r.val →
          ∃ i : Nat, i < trustLen trust ∧ fstAt trust i = some u ∧ sndAt trust i = some r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there is no label v with 1 <= v <= n such that (i) no index i with 0 <= i < len(trust) has trust[i][0] = v, and (ii) for every label u with 1 <= u <= n and u != v, there exists an index i with 0 <= i < len(trust), trust[i][0] = u, and trust[i][1] = v.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_6 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) :
      r.val = -1 ↔ ¬ ∃ v : ℤ, 1 ≤ v ∧ v ≤ n.val ∧ NoOut trust v ∧ AllIn n.val trust v := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r), r.val = -1 ↔ ¬ ∃ v : ℤ, 1 ≤ v ∧ v ≤ n.val ∧ NoOut trust v ∧ AllIn n.val trust v) := by
    sorry

  /-- Whenever the function returns a result r, if there exists a label v with 1 <= v <= n such that (i) no index i with 0 <= i < len(trust) has trust[i][0] = v, and (ii) for every label u with 1 <= u <= n and u != v, there exists an index i with 0 <= i < len(trust), trust[i][0] = u, and trust[i][1] = v, then r = v.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_7 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) :
      ∀ v : ℤ, 1 ≤ v → v ≤ n.val → NoOut trust v → AllIn n.val trust v → r.val = v := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r), ∀ v : ℤ, 1 ≤ v → v ≤ n.val → NoOut trust v → AllIn n.val trust v → r.val = v) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, the number of indices i with 0 <= i < len(trust) and trust[i][1] = r is exactly n - 1.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_8 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1) :
      (indeg trust r.val : ℤ) = n.val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1), (indeg trust r.val : ℤ) = n.val - 1) := by
    sorry

  /-- For any two lists trust and trust' of trust pairs satisfying the preconditions for the same n, if trust' is a permutation of trust (the multiset of ordered pairs in trust' equals that in trust), then the result returned for (n, trust) equals the result returned for (n, trust').
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_9 (n : Std.I64) (trust trust' : TrustVec)
      (h : Precond n trust) (h' : Precond n trust')
      (hperm : (pairList trust).Perm (pairList trust')) :
      Aegis.FindJudge.find_judge n trust = Aegis.FindJudge.find_judge n trust' := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (trust trust' : TrustVec)
        (h : Precond n trust) (h' : Precond n trust')
        (hperm : (pairList trust).Perm (pairList trust')), Aegis.FindJudge.find_judge n trust = Aegis.FindJudge.find_judge n trust') := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there is no label w with 1 <= w <= n and w != r such that (i) no index i with 0 <= i < len(trust) has trust[i][0] = w, and (ii) for every label u with 1 <= u <= n and u != w, there exists an index i with 0 <= i < len(trust), trust[i][0] = u, and trust[i][1] = w.
    Preconditions: n and every trust entry are i64 integers; 1 <= n <= 1000; 0 <= len(trust) <= 10^4; for every i with 0 <= i < len(trust), len(trust[i]) = 2, 1 <= trust[i][0] <= n, 1 <= trust[i][1] <= n, and trust[i][0] != trust[i][1]; all ordered pairs (trust[i][0], trust[i][1]) for 0 <= i < len(trust) are pairwise distinct. -/
  theorem spec_10 (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
      (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1) :
      ¬ ∃ w : ℤ, 1 ≤ w ∧ w ≤ n.val ∧ w ≠ r.val ∧ NoOut trust w ∧ AllIn n.val trust w := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (trust : TrustVec) (h : Precond n trust)
        (r : Std.I64) (hr : Aegis.FindJudge.find_judge n trust = ok r) (hrne : r.val ≠ -1), ¬ ∃ w : ℤ, 1 ≤ w ∧ w ≤ n.val ∧ w ≠ r.val ∧ NoOut trust w ∧ AllIn n.val trust w) := by
    sorry

  end AegisSpec.FindJudge
