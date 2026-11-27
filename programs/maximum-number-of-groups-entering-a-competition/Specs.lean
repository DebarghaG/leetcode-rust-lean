import Aegis.MaximumGroups.Code.Funs

/-!
# Specifications of `Aegis.MaximumGroups.maximum_groups`

LeetCode problem `maximum-number-of-groups-entering-a-competition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumGroups

def gradeAt (grades : Slice Std.I64) (j : Nat) : Int :=
  (grades.val.map (fun x => x.val)).getD j 0

def groupSum (grades : Slice Std.I64) (g : List Nat) : Int :=
  (g.map (gradeAt grades)).sum

def IsIndexPartition (n : Nat) (gs : List (List Nat)) : Prop :=
  (∀ g ∈ gs, g ≠ []) ∧ gs.flatten.Nodup ∧ (∀ j : Nat, j ∈ gs.flatten ↔ j < n)

def IncreasingGroups (grades : Slice Std.I64) : List (List Nat) → Prop
  | [] => True
  | [_] => True
  | g₁ :: g₂ :: rest =>
      g₁.length < g₂.length ∧ groupSum grades g₁ < groupSum grades g₂ ∧
        IncreasingGroups grades (g₂ :: rest)

def AchievableGroupCount (grades : Slice Std.I64) (k : Nat) : Prop :=
  ∃ gs : List (List Nat),
    gs.length = k ∧ IsIndexPartition grades.val.length gs ∧ IncreasingGroups grades gs

def IsMaxGroupCount (grades : Slice Std.I64) (k : Nat) : Prop :=
  1 ≤ k ∧ AchievableGroupCount grades k ∧
    ∀ m : Nat, 1 ≤ m → AchievableGroupCount grades m → m ≤ k

/-- The function returns a result r and r is the maximum integer k >= 1 for which the indices {0, ..., len(grades)-1} can be partitioned into k pairwise disjoint non-empty ordered groups G_1, ..., G_k whose union is all indices, such that, writing c_i = the number of indices in G_i and s_i = the sum of grades[j] over all j in G_i, we have c_i < c_{i+1} and s_i < s_{i+1} for every i with 1 <= i < k.
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_1 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧ IsMaxGroupCount grades r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧ IsMaxGroupCount grades r.val.toNat) := by
  sorry

/-- For every input satisfying the preconditions, the function does not fail: it returns a successful result r (there is no overflow, out-of-bounds access, or panic).
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_2 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64, Aegis.MaximumGroups.maximum_groups grades = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64, Aegis.MaximumGroups.maximum_groups grades = ok r) := by
  sorry

/-- The function returns a result r and 1 <= r.
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_3 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64, Aegis.MaximumGroups.maximum_groups grades = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64, Aegis.MaximumGroups.maximum_groups grades = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r*(r+1)/2 <= len(grades).
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_4 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        r.val * (r.val + 1) / 2 ≤ (grades.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        r.val * (r.val + 1) / 2 ≤ (grades.val.length : Int)) := by
  sorry

/-- The function returns a result r and (r+1)*(r+2)/2 > len(grades).
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_5 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        (r.val + 1) * (r.val + 2) / 2 > (grades.val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        (r.val + 1) * (r.val + 2) / 2 > (grades.val.length : Int)) := by
  sorry

/-- The function returns a result r and r is achievable: there exist pairwise disjoint non-empty groups G_1, ..., G_r whose union is {0, ..., len(grades)-1} such that, with c_i and s_i as in spec_1, c_i < c_{i+1} and s_i < s_{i+1} for every i with 1 <= i < r.
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_6 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        AchievableGroupCount grades r.val.toNat := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        AchievableGroupCount grades r.val.toNat) := by
  sorry

/-- The function returns a result r and there is no ordered partition of {0, ..., len(grades)-1} into r+1 pairwise disjoint non-empty groups G_1, ..., G_{r+1} satisfying both strict inequalities c_i < c_{i+1} and s_i < s_{i+1} for every i with 1 <= i <= r, where c_i and s_i are the group size and grade sum.
  Preconditions: len(grades) >= 1, len(grades) <= 100000, and for every index i with 0 <= i < len(grades), 1 <= grades[i] <= 100000. -/
theorem spec_7 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        ¬ AchievableGroupCount grades (r.val.toNat + 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        ¬ AchievableGroupCount grades (r.val.toNat + 1)) := by
  sorry

/-- The calls maximum_groups(grades1) and maximum_groups(grades2) both return results r1 and r2, and r1 = r2.
  Preconditions: grades1 and grades2 are two slices satisfying len >= 1, len <= 100000, and all grades in [1,100000], with len(grades1) = len(grades2). -/
theorem spec_8 (grades1 grades2 : Slice Std.I64)
    (hlen_lower1 : 1 ≤ grades1.val.length) (hlen_upper1 : grades1.val.length ≤ 100000)
    (hgrades1 : ∀ (i : Nat) (hi : i < grades1.val.length),
      1 ≤ grades1.val[i].val ∧ grades1.val[i].val ≤ 100000)
    (hlen_lower2 : 1 ≤ grades2.val.length) (hlen_upper2 : grades2.val.length ≤ 100000)
    (hgrades2 : ∀ (i : Nat) (hi : i < grades2.val.length),
      1 ≤ grades2.val[i].val ∧ grades2.val[i].val ≤ 100000)
    (hlen : grades1.val.length = grades2.val.length) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades1 = ok r1 ∧
        Aegis.MaximumGroups.maximum_groups grades2 = ok r2 ∧ r1 = r2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grades1 grades2 : Slice Std.I64)
    (hlen_lower1 : 1 ≤ grades1.val.length) (hlen_upper1 : grades1.val.length ≤ 100000)
    (hgrades1 : ∀ (i : Nat) (hi : i < grades1.val.length),
      1 ≤ grades1.val[i].val ∧ grades1.val[i].val ≤ 100000)
    (hlen_lower2 : 1 ≤ grades2.val.length) (hlen_upper2 : grades2.val.length ≤ 100000)
    (hgrades2 : ∀ (i : Nat) (hi : i < grades2.val.length),
      1 ≤ grades2.val[i].val ∧ grades2.val[i].val ≤ 100000)
    (hlen : grades1.val.length = grades2.val.length), ∃ r1 r2 : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades1 = ok r1 ∧
        Aegis.MaximumGroups.maximum_groups grades2 = ok r2 ∧ r1 = r2) := by
  sorry

/-- The calls maximum_groups(grades1) and maximum_groups(grades2) both return results r1 and r2, and r1 <= r2.
  Preconditions: grades1 and grades2 are two slices satisfying the problem constraints, with len(grades1) <= len(grades2). -/
theorem spec_9 (grades1 grades2 : Slice Std.I64)
    (hlen_lower1 : 1 ≤ grades1.val.length) (hlen_upper1 : grades1.val.length ≤ 100000)
    (hgrades1 : ∀ (i : Nat) (hi : i < grades1.val.length),
      1 ≤ grades1.val[i].val ∧ grades1.val[i].val ≤ 100000)
    (hlen_lower2 : 1 ≤ grades2.val.length) (hlen_upper2 : grades2.val.length ≤ 100000)
    (hgrades2 : ∀ (i : Nat) (hi : i < grades2.val.length),
      1 ≤ grades2.val[i].val ∧ grades2.val[i].val ≤ 100000)
    (hlen : grades1.val.length ≤ grades2.val.length) :
    ∃ r1 r2 : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades1 = ok r1 ∧
        Aegis.MaximumGroups.maximum_groups grades2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grades1 grades2 : Slice Std.I64)
    (hlen_lower1 : 1 ≤ grades1.val.length) (hlen_upper1 : grades1.val.length ≤ 100000)
    (hgrades1 : ∀ (i : Nat) (hi : i < grades1.val.length),
      1 ≤ grades1.val[i].val ∧ grades1.val[i].val ≤ 100000)
    (hlen_lower2 : 1 ≤ grades2.val.length) (hlen_upper2 : grades2.val.length ≤ 100000)
    (hgrades2 : ∀ (i : Nat) (hi : i < grades2.val.length),
      1 ≤ grades2.val[i].val ∧ grades2.val[i].val ≤ 100000)
    (hlen : grades1.val.length ≤ grades2.val.length), ∃ r1 r2 : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades1 = ok r1 ∧
        Aegis.MaximumGroups.maximum_groups grades2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- For that unique k, the function returns a result r and r = k.
  Preconditions: len(grades) >= 1, len(grades) <= 100000, all grades in [1,100000], and there exists an integer k >= 1 such that len(grades) = k*(k+1)/2. -/
theorem spec_10 (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000)
    (htriangular : ∃ k : Nat, 1 ≤ k ∧ grades.val.length = k * (k + 1) / 2) :
    ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        ∃ k : Nat, 1 ≤ k ∧ grades.val.length = k * (k + 1) / 2 ∧ r.val = (k : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grades : Slice Std.I64)
    (hlen_lower : 1 ≤ grades.val.length) (hlen_upper : grades.val.length ≤ 100000)
    (hgrades : ∀ (i : Nat) (hi : i < grades.val.length),
      1 ≤ grades.val[i].val ∧ grades.val[i].val ≤ 100000)
    (htriangular : ∃ k : Nat, 1 ≤ k ∧ grades.val.length = k * (k + 1) / 2), ∃ r : Std.I64,
      Aegis.MaximumGroups.maximum_groups grades = ok r ∧
        ∃ k : Nat, 1 ≤ k ∧ grades.val.length = k * (k + 1) / 2 ∧ r.val = (k : Int)) := by
  sorry

  end AegisSpec.MaximumGroups
