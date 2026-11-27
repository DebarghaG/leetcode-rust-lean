import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-to-convert-string-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumCost

namespace AegisSpec.MinimumCost

def sBytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def vecBytes (v : alloc.vec.Vec Std.U8) : List Nat := v.val.map (fun b => b.val)

def vBytes (s : Slice (alloc.vec.Vec Std.U8)) : List (List Nat) := s.val.map vecBytes

def cVals (s : Slice Std.I64) : List Int := s.val.map (fun i => i.val)

def IsLowerBytes (l : List Nat) : Prop := ∀ b ∈ l, 97 ≤ b ∧ b ≤ 122

def listMax : List Int → Int
  | [] => 0
  | a :: t => t.foldl max a

def listMin : List Int → Int
  | [] => 0
  | a :: t => t.foldl min a

structure ValidInput (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64) : Prop where
  len_source_target : source.val.length = target.val.length
  n_pos : 1 ≤ source.val.length
  n_le : source.val.length ≤ 1000
  source_lower : IsLowerBytes (sBytes source)
  target_lower : IsLowerBytes (sBytes target)
  cost_len : cost.val.length = original.val.length
  changed_len : changed.val.length = original.val.length
  m_pos : 1 ≤ original.val.length
  m_le : original.val.length ≤ 100
  entry : ∀ (j : Nat) (o c : alloc.vec.Vec Std.U8) (cj : Std.I64),
    original.val[j]? = some o → changed.val[j]? = some c → cost.val[j]? = some cj →
      o.val.length = c.val.length ∧
      1 ≤ o.val.length ∧ o.val.length ≤ source.val.length ∧
      IsLowerBytes (vecBytes o) ∧ IsLowerBytes (vecBytes c) ∧
      vecBytes o ≠ vecBytes c ∧
      (1 : Int) ≤ cj.val ∧ cj.val ≤ 1000000

structure Step where
  op : Nat
  start : Nat
deriving DecidableEq, Repr

def stepOrig (orig : List (List Nat)) (st : Step) : List Nat := orig.getD st.op []

def stepLen (orig : List (List Nat)) (st : Step) : Nat := (orig.getD st.op []).length

def StepLegalB (orig : List (List Nat)) (s : List Nat) (st : Step) : Bool :=
  (st.op < orig.length) && (st.start + stepLen orig st ≤ s.length) &&
    ((s.drop st.start).take (stepLen orig st) == stepOrig orig st)

def StepLegal (orig : List (List Nat)) (s : List Nat) (st : Step) : Prop :=
  st.op < orig.length ∧ st.start + stepLen orig st ≤ s.length ∧
    (s.drop st.start).take (stepLen orig st) = stepOrig orig st

def ApplyStep (orig chg : List (List Nat)) (s : List Nat) (st : Step) : List Nat :=
  s.take st.start ++ chg.getD st.op [] ++ s.drop (st.start + stepLen orig st)

def RunSteps (orig chg : List (List Nat)) (costs : List Int) :
    List Nat → List Step → Option (List Nat × Int)
  | s, [] => some (s, 0)
  | s, st :: rest =>
      if StepLegalB orig s st then
        match RunSteps orig chg costs (ApplyStep orig chg s st) rest with
        | some (s', c) => some (s', c + costs.getD st.op 0)
        | none => none
      else none

def IntervalsOK (orig : List (List Nat)) (steps : List Step) : Prop :=
  ∀ st₁ ∈ steps, ∀ st₂ ∈ steps,
    (st₁.start + stepLen orig st₁ ≤ st₂.start ∨
        st₂.start + stepLen orig st₂ ≤ st₁.start) ∨
      (st₁.start = st₂.start ∧ stepLen orig st₁ = stepLen orig st₂)

def CostSet (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64) : Set Int :=
  { c | ∃ steps : List Step,
      IntervalsOK (vBytes original) steps ∧
        RunSteps (vBytes original) (vBytes changed) (cVals cost) (sBytes source) steps =
          some (sBytes target, c) }

def StepCount (orig : List (List Nat)) (steps : List Step) (a l : Nat) : Nat :=
  (steps.filter (fun st => (st.start == a) && (stepLen orig st == l))).length

def IntervalCovered (orig : List (List Nat)) (steps : List Step) (i : Nat) : Prop :=
  ∃ st ∈ steps, st.start ≤ i ∧ i < st.start + stepLen orig st

def IsPerm (m : Nat) (π : Nat → Nat) : Prop :=
  (∀ i, i < m → π i < m) ∧
    (∀ i, i < m → ∀ j, j < m → π i = π j → i = j) ∧
      (∀ j, j < m → ∃ i, i < m ∧ π i = j)

/-- Let C be the set of total costs of all finite sequences of operations that are admissible in the following sense: each step chooses an index j with 0<=j<m and a start a>=0, is legal only when the current block of length len(original[j]) starting at a equals original[j], replaces that block by changed[j], and costs cost[j]; for every two steps with starts a,a' and lengths l=len(original[j]), l'=len(original[j']), the intervals [a,a+l-1] and [a',a'+l'-1] are either disjoint (no common index) or (a,l)=(a',l'). The sequence converts source to target if applying it to source yields target. Then whenever the function returns a result r: if C is nonempty, r = min(C); if C is empty, r = -1.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_1 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) :
    ((CostSet source target original changed cost).Nonempty →
        (∀ c, c ∈ CostSet source target original changed cost → r.val ≤ c) ∧
          r.val ∈ CostSet source target original changed cost) ∧
      (CostSet source target original changed cost = ∅ → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r), ((CostSet source target original changed cost).Nonempty →
        (∀ c, c ∈ CostSet source target original changed cost → r.val ≤ c) ∧
          r.val ∈ CostSet source target original changed cost) ∧
      (CostSet source target original changed cost = ∅ → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_2 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) :
    ∃ r : Std.I64, minimum_cost source target original changed cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost), ∃ r : Std.I64, minimum_cost source target original changed cost = ok r) := by
  sorry

/-- Let C be the set of total costs of all admissible operation sequences (as defined in spec_1) that convert source to target. Whenever the function returns r and r>=0, every c in C satisfies c >= r.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_3 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val) :
    ∀ c, c ∈ CostSet source target original changed cost → r.val ≤ c := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val), ∀ c, c ∈ CostSet source target original changed cost → r.val ≤ c) := by
  sorry

/-- Let C be the set of total costs of all admissible operation sequences (as defined in spec_1) that convert source to target. Whenever the function returns r = -1, the set C is empty; that is, no admissible operation sequence converts source to target.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_4 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr1 : r.val = -1) :
    CostSet source target original changed cost = ∅ := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr1 : r.val = -1), CostSet source target original changed cost = ∅) := by
  sorry

/-- Let C be the set of total costs of all admissible operation sequences (as defined in spec_1) that convert source to target. If C is empty, then whenever the function returns a result r, r = -1.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_5 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (hC : CostSet source target original changed cost = ∅) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) :
    r.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (hC : CostSet source target original changed cost = ∅) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r), r.val = -1) := by
  sorry

/-- Whenever the function returns r and r != -1, r >= 0.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_6 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr1 : r.val ≠ -1) :
    0 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr1 : r.val ≠ -1), 0 ≤ r.val) := by
  sorry

/-- Let M = max(cost[j] for 0<=j<m). Whenever the function returns r with r >= 0, r <= n * m * M.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_7 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val) :
    r.val ≤ (source.val.length : Int) * (original.val.length : Int) * listMax (cVals cost) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val), r.val ≤ (source.val.length : Int) * (original.val.length : Int) * listMax (cVals cost)) := by
  sorry

/-- Let cmin = min(cost[j] for 0<=j<m). Whenever source != target and the function returns r with r >= 0, r >= cmin.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_8 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hne : sBytes source ≠ sBytes target) (hr0 : 0 ≤ r.val) :
    listMin (cVals cost) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hne : sBytes source ≠ sBytes target) (hr0 : 0 ≤ r.val), listMin (cVals cost) ≤ r.val) := by
  sorry

/-- Let C be the set of total costs of all admissible operation sequences (as defined in spec_1) that convert source to target. Whenever the function returns r with r >= 0, there exists an admissible sequence of total cost r converting source to target such that: (i) if two steps use different start-length intervals, those intervals are disjoint; (ii) for each fixed start-length interval, at most m steps use that interval; and (iii) every index i not covered by any step interval satisfies source[i] = target[i].
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_9 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val) :
    ∃ steps : List Step,
      IntervalsOK (vBytes original) steps ∧
        RunSteps (vBytes original) (vBytes changed) (cVals cost) (sBytes source) steps =
          some (sBytes target, r.val) ∧
        (∀ a l, StepCount (vBytes original) steps a l ≤ original.val.length) ∧
          (∀ i, i < source.val.length → ¬ IntervalCovered (vBytes original) steps i →
            (sBytes source).getD i 0 = (sBytes target).getD i 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (r : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r) (hr0 : 0 ≤ r.val), ∃ steps : List Step,
      IntervalsOK (vBytes original) steps ∧
        RunSteps (vBytes original) (vBytes changed) (cVals cost) (sBytes source) steps =
          some (sBytes target, r.val) ∧
        (∀ a l, StepCount (vBytes original) steps a l ≤ original.val.length) ∧
          (∀ i, i < source.val.length → ¬ IntervalCovered (vBytes original) steps i →
            (sBytes source).getD i 0 = (sBytes target).getD i 0)) := by
  sorry

/-- Let r be the result returned by the function on (source,target,original,changed,cost), and let r' be the result returned on (source,target,original,changed,cost'). Whenever both results are returned, if r = -1 then r' = -1; if r >= 0 then r' >= 0 and r' <= r.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. Additionally, cost' is an array of length m with 1 <= cost'[j] <= cost[j] <= 1000000 for every j with 0<=j<m. -/
theorem spec_10 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost cost' : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (hcost'_len : cost'.val.length = original.val.length)
    (hcost' : ∀ (j : Nat) (c c' : Std.I64), cost.val[j]? = some c → cost'.val[j]? = some c' →
      (1 : Int) ≤ c'.val ∧ c'.val ≤ c.val ∧ c.val ≤ 1000000)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original changed cost' = ok r') :
    (r.val = -1 → r'.val = -1) ∧ (0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost cost' : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (hcost'_len : cost'.val.length = original.val.length)
    (hcost' : ∀ (j : Nat) (c c' : Std.I64), cost.val[j]? = some c → cost'.val[j]? = some c' →
      (1 : Int) ≤ c'.val ∧ c'.val ≤ c.val ∧ c.val ≤ 1000000)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original changed cost' = ok r'), (r.val = -1 → r'.val = -1) ∧ (0 ≤ r.val → 0 ≤ r'.val ∧ r'.val ≤ r.val)) := by
  sorry

/-- Define original'[i] = original[π(i)], changed'[i] = changed[π(i)], and cost'[i] = cost[π(i)] for 0<=i<m. Whenever the function returns r on (source,target,original,changed,cost) and r' on (source,target,original',changed',cost'), we have r = r'.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. Additionally, π is a permutation of {0,...,m-1}. -/
theorem spec_11 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (π : Nat → Nat) (hπ : IsPerm original.val.length π)
    (original' changed' : Slice (alloc.vec.Vec Std.U8)) (cost' : Slice Std.I64)
    (h_orig' : ∀ i, i < original.val.length → original'.val[i]? = original.val[π i]?)
    (h_chg' : ∀ i, i < original.val.length → changed'.val[i]? = changed.val[π i]?)
    (h_cost' : ∀ i, i < original.val.length → cost'.val[i]? = cost.val[π i]?)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original' changed' cost' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (π : Nat → Nat) (hπ : IsPerm original.val.length π)
    (original' changed' : Slice (alloc.vec.Vec Std.U8)) (cost' : Slice Std.I64)
    (h_orig' : ∀ i, i < original.val.length → original'.val[i]? = original.val[π i]?)
    (h_chg' : ∀ i, i < original.val.length → changed'.val[i]? = changed.val[π i]?)
    (h_cost' : ∀ i, i < original.val.length → cost'.val[i]? = cost.val[π i]?)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original' changed' cost' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns r on (source,target,original,changed,cost) and r' on (source,target,original,changed,cost'), we have r = r'.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. Additionally, p and q are indices with 0<=p,q<m, p != q, original[p]=original[q], changed[p]=changed[q], and cost[q] <= cost[p]. The array cost' has length m, satisfies cost'[i]=cost[i] for i != p, 1 <= cost'[p] <= 1000000, and cost'[p] >= cost[q]. -/
theorem spec_12 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost cost' : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (p q : Nat) (hp : p < original.val.length) (hq : q < original.val.length) (hpq : p ≠ q)
    (h_orig : ∀ (op oq : alloc.vec.Vec Std.U8),
      original.val[p]? = some op → original.val[q]? = some oq → vecBytes op = vecBytes oq)
    (h_chg : ∀ (cp cq : alloc.vec.Vec Std.U8),
      changed.val[p]? = some cp → changed.val[q]? = some cq → vecBytes cp = vecBytes cq)
    (h_cost : ∀ (cp cq : Std.I64),
      cost.val[p]? = some cp → cost.val[q]? = some cq → cq.val ≤ cp.val)
    (hcost'_len : cost'.val.length = original.val.length)
    (hcost'_other : ∀ (i : Nat) (ci ci' : Std.I64), i < original.val.length → i ≠ p →
      cost.val[i]? = some ci → cost'.val[i]? = some ci' → ci'.val = ci.val)
    (hcost'_p : ∀ (cp' cq : Std.I64), cost'.val[p]? = some cp' → cost.val[q]? = some cq →
      (1 : Int) ≤ cp'.val ∧ cp'.val ≤ 1000000 ∧ cq.val ≤ cp'.val)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original changed cost' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost cost' : Slice Std.I64)
    (h : ValidInput source target original changed cost)
    (p q : Nat) (hp : p < original.val.length) (hq : q < original.val.length) (hpq : p ≠ q)
    (h_orig : ∀ (op oq : alloc.vec.Vec Std.U8),
      original.val[p]? = some op → original.val[q]? = some oq → vecBytes op = vecBytes oq)
    (h_chg : ∀ (cp cq : alloc.vec.Vec Std.U8),
      changed.val[p]? = some cp → changed.val[q]? = some cq → vecBytes cp = vecBytes cq)
    (h_cost : ∀ (cp cq : Std.I64),
      cost.val[p]? = some cp → cost.val[q]? = some cq → cq.val ≤ cp.val)
    (hcost'_len : cost'.val.length = original.val.length)
    (hcost'_other : ∀ (i : Nat) (ci ci' : Std.I64), i < original.val.length → i ≠ p →
      cost.val[i]? = some ci → cost'.val[i]? = some ci' → ci'.val = ci.val)
    (hcost'_p : ∀ (cp' cq : Std.I64), cost'.val[p]? = some cp' → cost.val[q]? = some cq →
      (1 : Int) ≤ cp'.val ∧ cp'.val ≤ 1000000 ∧ cq.val ≤ cp'.val)
    (r r' : Std.I64)
    (hr : minimum_cost source target original changed cost = ok r)
    (hr' : minimum_cost source target original changed cost' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever source = target (as byte arrays), the function returns 0; the empty operation sequence is admissible, costs 0, and all operation costs are positive, so the minimum is 0.
  Preconditions: len(source)=len(target)=n with 1<=n<=1000; every byte of source and target is a lowercase English ASCII code (97..122). Let m=len(cost)=len(original)=len(changed) with 1<=m<=100. For every j with 0<=j<m: len(original[j])=len(changed[j]), 1<=len(original[j])<=n, every byte of original[j] and changed[j] is a lowercase English ASCII code, original[j]!=changed[j], and 1<=cost[j]<=1000000. -/
theorem spec_13 (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (hst : sBytes source = sBytes target) :
    ∃ r : Std.I64, minimum_cost source target original changed cost = ok r ∧ r.val = 0 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (source target : Slice Std.U8)
    (original changed : Slice (alloc.vec.Vec Std.U8)) (cost : Slice Std.I64)
    (h : ValidInput source target original changed cost) (hst : sBytes source = sBytes target), ∃ r : Std.I64, minimum_cost source target original changed cost = ok r ∧ r.val = 0) := by
  sorry

end AegisSpec.MinimumCost
