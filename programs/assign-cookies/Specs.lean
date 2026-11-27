import Aegis.FindContentChildren.Code.Funs

/-!
# Specifications of `Aegis.FindContentChildren.find_content_children`

LeetCode problem `assign-cookies`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindContentChildren

open Aegis.FindContentChildren (find_content_children)

def EntriesInRange (l : List Std.I64) : Prop :=
  ∀ (i : Nat) (hi : i < l.length), 1 ≤ (l[i]).val ∧ (l[i]).val ≤ 2147483647

def Feasible (g s : Slice Std.I64) (C : Finset (Fin g.val.length)) : Prop :=
  ∃ f : {i : Fin g.val.length // i ∈ C} → Fin s.val.length,
    Function.Injective f ∧
      ∀ (i : {i : Fin g.val.length // i ∈ C}),
        (g.val[i.1.val]).val ≤ (s.val[(f i).val]).val

def IsMaxFeasibleCard (g s : Slice Std.I64) (r : Int) : Prop :=
  (∃ C : Finset (Fin g.val.length), Feasible g s C ∧ (C.card : Int) = r) ∧
    ∀ C : Finset (Fin g.val.length), Feasible g s C → (C.card : Int) ≤ r

/-- The function returns a result r, and r is the maximum cardinality of a set C subset of {0,...,len(g)-1} for which there exists an injective function f from C to {0,...,len(s)-1} satisfying s[f(i)] >= g[i] for every i in C. The set C may be empty; f assigns each chosen child a distinct cookie large enough for that child.
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_1 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r ∧ IsMaxFeasibleCard g s r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r ∧ IsMaxFeasibleCard g s r.val) := by
  sorry

/-- The function returns a result r and 0 <= r <= min(len(g), len(s)).
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_2 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((min g.val.length s.val.length : Nat) : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r ∧
      0 ≤ r.val ∧ r.val ≤ ((min g.val.length s.val.length : Nat) : Int)) := by
  sorry

/-- The function returns some result r; it does not fail for any g and s satisfying the preconditions.
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_3 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r) := by
  sorry

/-- If len(s) = 0, the function returns r = 0.
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_4 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hs_empty : s.val.length = 0) :
    ∃ r, find_content_children g s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hs_empty : s.val.length = 0), ∃ r, find_content_children g s = ok r ∧ r.val = 0) := by
  sorry

/-- If len(g) = 0, the function returns r = 0.
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_5 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hg_empty : g.val.length = 0) :
    ∃ r, find_content_children g s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hg_empty : g.val.length = 0), ∃ r, find_content_children g s = ok r ∧ r.val = 0) := by
  sorry

/-- If for every i with 0 <= i < len(g) and every j with 0 <= j < len(s), s[j] < g[i], then the function returns r = 0.
  Preconditions: len(g) <= 30000, len(s) <= 30000, len(g) > 0, len(s) > 0, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_6 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length) (hs_pos : 0 < s.val.length)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hsmall : ∀ (i : Nat) (hi : i < g.val.length) (j : Nat) (hj : j < s.val.length),
      (s.val[j]).val < (g.val[i]).val) :
    ∃ r, find_content_children g s = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length) (hs_pos : 0 < s.val.length)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hsmall : ∀ (i : Nat) (hi : i < g.val.length) (j : Nat) (hj : j < s.val.length),
      (s.val[j]).val < (g.val[i]).val), ∃ r, find_content_children g s = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns r = len(g).
  Preconditions: len(g) <= 30000, len(s) <= 30000, len(g) > 0, len(g) <= len(s), for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647 and g[i] <= s[i], and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_7 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length) (hlen : g.val.length ≤ s.val.length)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hfit : ∀ (i : Nat) (hi : i < g.val.length),
      (g.val[i]).val ≤ (s.val[i]'(by omega)).val) :
    ∃ r, find_content_children g s = ok r ∧ r.val = (g.val.length : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length) (hlen : g.val.length ≤ s.val.length)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val)
    (hfit : ∀ (i : Nat) (hi : i < g.val.length),
      (g.val[i]).val ≤ (s.val[i]'(by omega)).val), ∃ r, find_content_children g s = ok r ∧ r.val = (g.val.length : Int)) := by
  sorry

/-- If every child has greed factor 1, then the function returns r = min(len(g), len(s)).
  Preconditions: len(g) <= 30000, len(s) <= 30000, len(g) > 0, for every i with 0 <= i < len(g), g[i] = 1, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_8 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length)
    (hg_one : ∀ (i : Nat) (hi : i < g.val.length), (g.val[i]).val = 1)
    (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r ∧
      r.val = ((min g.val.length s.val.length : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg_pos : 0 < g.val.length)
    (hg_one : ∀ (i : Nat) (hi : i < g.val.length), (g.val[i]).val = 1)
    (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r ∧
      r.val = ((min g.val.length s.val.length : Nat) : Int)) := by
  sorry

/-- If the function returns r for (g,s) and r' for (g',s), then r = r'.
  Preconditions: Both (g,s) and (g',s) satisfy: len(g) <= 30000, len(s) <= 30000, len(g') <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every i with 0 <= i < len(g'), 1 <= g'[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. Also len(g') = len(g) and there is a bijection pi from {0,...,len(g)-1} onto itself such that g'[i] = g[pi(i)] for every i with 0 <= i < len(g). -/
theorem spec_9 (g g' s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len : g'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hlen : g'.val.length = g.val.length)
    (π : Equiv.Perm (Fin g.val.length))
    (hπ : ∀ (i : Fin g.val.length), g'.val[i.val]'(by omega) = g.val[(π i).val]) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (g g' s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len : g'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hlen : g'.val.length = g.val.length)
    (π : Equiv.Perm (Fin g.val.length))
    (hπ : ∀ (i : Fin g.val.length), g'.val[i.val]'(by omega) = g.val[(π i).val]), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r = r') := by
  sorry

/-- If the function returns r for (g,s) and r' for (g,s'), then r = r'.
  Preconditions: Both (g,s) and (g,s') satisfy: len(g) <= 30000, len(s) <= 30000, len(s') <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647, and for every j with 0 <= j < len(s'), 1 <= s'[j] <= 2147483647. Also len(s') = len(s) and there is a bijection pi from {0,...,len(s)-1} onto itself such that s'[j] = s[pi(j)] for every j with 0 <= j < len(s). -/
theorem spec_10 (g s s' : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_len : s'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hlen : s'.val.length = s.val.length)
    (σ : Equiv.Perm (Fin s.val.length))
    (hσ : ∀ (j : Fin s.val.length), s'.val[j.val]'(by omega) = s.val[(σ j).val]) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (g s s' : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_len : s'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hlen : s'.val.length = s.val.length)
    (σ : Equiv.Perm (Fin s.val.length))
    (hσ : ∀ (j : Fin s.val.length), s'.val[j.val]'(by omega) = s.val[(σ j).val]), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r = r') := by
  sorry

/-- If the function returns r for (g,s) and r' for (g,s'), then r <= r' <= r + 1.
  Preconditions: len(g) <= 30000, len(s) <= 30000, len(s') = len(s)+1 <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647, and for every j with 0 <= j < len(s'), 1 <= s'[j] <= 2147483647. Moreover, s' is obtained by appending one value v to s: for 0 <= i < len(s), s'[i] = s[i], and s'[len(s)] = v with 1 <= v <= 2147483647. -/
theorem spec_11 (g s s' : Slice Std.I64) (v : Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_max : s'.val.length ≤ 30000) (hs'_len : s'.val.length = s.val.length + 1)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hprefix : ∀ (i : Nat) (hi : i < s.val.length), s'.val[i]'(by omega) = s.val[i])
    (hlast : s'.val[s.val.length]'(by omega) = v)
    (hv : 1 ≤ v.val ∧ v.val ≤ 2147483647) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (g s s' : Slice Std.I64) (v : Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_max : s'.val.length ≤ 30000) (hs'_len : s'.val.length = s.val.length + 1)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hprefix : ∀ (i : Nat) (hi : i < s.val.length), s'.val[i]'(by omega) = s.val[i])
    (hlast : s'.val[s.val.length]'(by omega) = v)
    (hv : 1 ≤ v.val ∧ v.val ≤ 2147483647), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- If the function returns r for (g,s) and r' for (g,s'), then r <= r'.
  Preconditions: Both (g,s) and (g,s') satisfy len(g) <= 30000, len(s) <= 30000, len(s') <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647, and for every j with 0 <= j < len(s'), 1 <= s'[j] <= 2147483647. Also len(s') = len(s) and for every j with 0 <= j < len(s), s'[j] >= s[j]. -/
theorem spec_12 (g s s' : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_len_max : s'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hlen : s'.val.length = s.val.length)
    (hge : ∀ (j : Nat) (hj : j < s.val.length), (s'.val[j]'(by omega)).val ≥ (s.val[j]).val) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (g s s' : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hs'_len_max : s'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) (hs' : EntriesInRange s'.val)
    (hlen : s'.val.length = s.val.length)
    (hge : ∀ (j : Nat) (hj : j < s.val.length), (s'.val[j]'(by omega)).val ≥ (s.val[j]).val), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g s' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- If the function returns r for (g,s) and r' for (g',s), then r <= r' <= r + 1.
  Preconditions: Both (g,s) and (g',s) satisfy len(g) <= 30000, len(s) <= 30000, len(g') <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every i with 0 <= i < len(g'), 1 <= g'[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. Also len(g') = len(g)+1 and there is a value v with 1 <= v <= 2147483647 such that for 0 <= i < len(g), g'[i] = g[i], and g'[len(g)] = v. -/
theorem spec_13 (g g' s : Slice Std.I64) (v : Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len_max : g'.val.length ≤ 30000) (hg'_len : g'.val.length = g.val.length + 1)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hprefix : ∀ (i : Nat) (hi : i < g.val.length), g'.val[i]'(by omega) = g.val[i])
    (hlast : g'.val[g.val.length]'(by omega) = v)
    (hv : 1 ≤ v.val ∧ v.val ≤ 2147483647) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (g g' s : Slice Std.I64) (v : Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len_max : g'.val.length ≤ 30000) (hg'_len : g'.val.length = g.val.length + 1)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hprefix : ∀ (i : Nat) (hi : i < g.val.length), g'.val[i]'(by omega) = g.val[i])
    (hlast : g'.val[g.val.length]'(by omega) = v)
    (hv : 1 ≤ v.val ∧ v.val ≤ 2147483647), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r.val ≤ r'.val ∧ r'.val ≤ r.val + 1) := by
  sorry

/-- If the function returns r for (g,s) and r' for (g',s), then r' <= r.
  Preconditions: Both (g,s) and (g',s) satisfy: len(g) <= 30000, len(s) <= 30000, len(g') <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, for every i with 0 <= i < len(g'), 1 <= g'[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. Also len(g') = len(g) and for every i with 0 <= i < len(g), g'[i] >= g[i]. -/
theorem spec_14 (g g' s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len_max : g'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hlen : g'.val.length = g.val.length)
    (hge : ∀ (i : Nat) (hi : i < g.val.length), (g'.val[i]'(by omega)).val ≥ (g.val[i]).val) :
    ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (g g' s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg'_len_max : g'.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hg' : EntriesInRange g'.val) (hs : EntriesInRange s.val)
    (hlen : g'.val.length = g.val.length)
    (hge : ∀ (i : Nat) (hi : i < g.val.length), (g'.val[i]'(by omega)).val ≥ (g.val[i]).val), ∀ (r r' : Std.I64), find_content_children g s = ok r →
      find_content_children g' s = ok r' → r'.val ≤ r.val) := by
  sorry

/-- The function returns r = 1 if there exists j with 0 <= j < len(s) and s[j] >= g[0], and returns r = 0 otherwise.
  Preconditions: len(g) = 1, len(s) <= 30000, 1 <= g[0] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_15 (g s : Slice Std.I64)
    (hg_len : g.val.length = 1) (hs_len : s.val.length ≤ 30000)
    (hg0 : 1 ≤ (g.val[0]'(by omega)).val ∧ (g.val[0]'(by omega)).val ≤ 2147483647)
    (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r ∧
      r.val = (if (∃ (j : Nat) (hj : j < s.val.length),
          (g.val[0]'(by omega)).val ≤ (s.val[j]).val) then (1 : Int) else 0) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length = 1) (hs_len : s.val.length ≤ 30000)
    (hg0 : 1 ≤ (g.val[0]'(by omega)).val ∧ (g.val[0]'(by omega)).val ≤ 2147483647)
    (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r ∧
      r.val = (if (∃ (j : Nat) (hj : j < s.val.length),
          (g.val[0]'(by omega)).val ≤ (s.val[j]).val) then (1 : Int) else 0)) := by
  sorry

/-- The function returns r = 1 if there exists i with 0 <= i < len(g) and g[i] <= s[0], and returns r = 0 otherwise.
  Preconditions: len(s) = 1, len(g) <= 30000, 1 <= s[0] <= 2147483647, and for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647. -/
theorem spec_16 (g s : Slice Std.I64)
    (hs_len : s.val.length = 1) (hg_len : g.val.length ≤ 30000)
    (hs0 : 1 ≤ (s.val[0]'(by omega)).val ∧ (s.val[0]'(by omega)).val ≤ 2147483647)
    (hg : EntriesInRange g.val) :
    ∃ r, find_content_children g s = ok r ∧
      r.val = (if (∃ (i : Nat) (hi : i < g.val.length),
          (g.val[i]).val ≤ (s.val[0]'(by omega)).val) then (1 : Int) else 0) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hs_len : s.val.length = 1) (hg_len : g.val.length ≤ 30000)
    (hs0 : 1 ≤ (s.val[0]'(by omega)).val ∧ (s.val[0]'(by omega)).val ≤ 2147483647)
    (hg : EntriesInRange g.val), ∃ r, find_content_children g s = ok r ∧
      r.val = (if (∃ (i : Nat) (hi : i < g.val.length),
          (g.val[i]).val ≤ (s.val[0]'(by omega)).val) then (1 : Int) else 0)) := by
  sorry

/-- The function returns r = 0 if and only if there is no pair (i,j) with 0 <= i < len(g), 0 <= j < len(s), and s[j] >= g[i].
  Preconditions: len(g) <= 30000, len(s) <= 30000, for every i with 0 <= i < len(g), 1 <= g[i] <= 2147483647, and for every j with 0 <= j < len(s), 1 <= s[j] <= 2147483647. -/
theorem spec_17 (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val) :
    ∃ r, find_content_children g s = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i : Nat) (hi : i < g.val.length) (j : Nat) (hj : j < s.val.length),
        (g.val[i]).val ≤ (s.val[j]).val) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (g s : Slice Std.I64)
    (hg_len : g.val.length ≤ 30000) (hs_len : s.val.length ≤ 30000)
    (hg : EntriesInRange g.val) (hs : EntriesInRange s.val), ∃ r, find_content_children g s = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i : Nat) (hi : i < g.val.length) (j : Nat) (hj : j < s.val.length),
        (g.val[i]).val ≤ (s.val[j]).val)) := by
  sorry

end AegisSpec.FindContentChildren
