import Aegis.KEmptySlots.Code.Funs

/-!
# Specifications of `Aegis.KEmptySlots.k_empty_slots`

LeetCode problem `k-empty-slots`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.KEmptySlots (k_empty_slots)

namespace AegisSpec.KEmptySlots

def nOf (bulbs : Slice Std.I64) : Int := (bulbs.val.length : Int)

def labels (bulbs : Slice Std.I64) : List Int := bulbs.val.map (fun b => b.val)

def IsPermOfRange (bulbs : Slice Std.I64) : Prop :=
  (labels bulbs).Nodup ∧ ∀ x : Int, 1 ≤ x → x ≤ nOf bulbs → x ∈ labels bulbs

def dayOf (bulbs : Slice Std.I64) (x : Int) : Int :=
  ((labels bulbs).idxOf x : Int) + 1

def GapEnds (bulbs : Slice Std.I64) (k p : Int) : Prop :=
  1 ≤ p ∧ p + k + 1 ≤ nOf bulbs ∧
    ∀ y : Int, p < y → y < p + k + 1 →
      max (dayOf bulbs p) (dayOf bulbs (p + k + 1)) < dayOf bulbs y

def IsGapDay (bulbs : Slice Std.I64) (k d : Int) : Prop :=
  ∃ p : Int, GapEnds bulbs k p ∧ d = max (dayOf bulbs p) (dayOf bulbs (p + k + 1))

/-- Define C = { c | there exists p with 1 <= p, p+k+1 <= n, c = max(day(p), day(p+k+1)), and for every y with p < y < p+k+1, day(y) > c }. The function returns a result r and satisfies: if C is empty then r = -1; if C is nonempty then r = min(C). Equivalently, r is the least day d in {1,...,n} such that there exists p with positions p and p+k+1 turned on after d days and every one of the k positions strictly between them turned off after d days; if no such d exists, r = -1.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_1 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∃ r, k_empty_slots bulbs k = ok r ∧
      ((∃ d, IsGapDay bulbs k.val d) →
        (IsGapDay bulbs k.val r.val ∧ ∀ d, IsGapDay bulbs k.val d → r.val ≤ d)) ∧
      ((∀ d, ¬ IsGapDay bulbs k.val d) → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∃ r, k_empty_slots bulbs k = ok r ∧
      ((∃ d, IsGapDay bulbs k.val d) →
        (IsGapDay bulbs k.val r.val ∧ ∀ d, IsGapDay bulbs k.val d → r.val ≤ d)) ∧
      ((∀ d, ¬ IsGapDay bulbs k.val d) → r.val = -1)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; in particular, it does not fail by panic, out-of-bounds access, or arithmetic overflow.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. -/
theorem spec_2 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∃ r, k_empty_slots bulbs k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∃ r, k_empty_slots bulbs k = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= n.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_3 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r → r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ nOf bulbs) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r → r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ nOf bulbs)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists p such that 1 <= p, p+k+1 <= n, max(day(p), day(p+k+1)) = r, and for every y with p < y < p+k+1, day(y) > r.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_4 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∃ p : Int, GapEnds bulbs k.val p ∧
        max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1)) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∃ p : Int, GapEnds bulbs k.val p ∧
        max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1)) = r.val) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every day d with 1 <= d < r and every p with 1 <= p and p+k+1 <= n, at least one of the following holds: day(p) > d, day(p+k+1) > d, or there exists y with p < y < p+k+1 and day(y) <= d.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_5 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∀ d : Int, 1 ≤ d → d < r.val →
        ∀ p : Int, 1 ≤ p → p + k.val + 1 ≤ nOf bulbs →
          dayOf bulbs p > d ∨ dayOf bulbs (p + k.val + 1) > d ∨
            ∃ y : Int, p < y ∧ y < p + k.val + 1 ∧ dayOf bulbs y ≤ d := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∀ d : Int, 1 ≤ d → d < r.val →
        ∀ p : Int, 1 ≤ p → p + k.val + 1 ≤ nOf bulbs →
          dayOf bulbs p > d ∨ dayOf bulbs (p + k.val + 1) > d ∨
            ∃ y : Int, p < y ∧ y < p + k.val + 1 ∧ dayOf bulbs y ≤ d) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every p with 1 <= p and p+k+1 <= n there exists y such that p < y < p+k+1 and day(y) <= max(day(p), day(p+k+1)).
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_6 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r →
      (r.val = -1 ↔
        ∀ p : Int, 1 ≤ p → p + k.val + 1 ≤ nOf bulbs →
          ∃ y : Int, p < y ∧ y < p + k.val + 1 ∧
            dayOf bulbs y ≤ max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1))) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r →
      (r.val = -1 ↔
        ∀ p : Int, 1 ≤ p → p + k.val + 1 ≤ nOf bulbs →
          ∃ y : Int, p < y ∧ y < p + k.val + 1 ∧
            dayOf bulbs y ≤ max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1)))) := by
  sorry

/-- If k >= n-1, then the function returns r = -1.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. -/
theorem spec_7 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs)
    (hk_ge : nOf bulbs - 1 ≤ k.val) :
    ∃ r, k_empty_slots bulbs k = ok r ∧ r.val = -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs)
    (hk_ge : nOf bulbs - 1 ≤ k.val), ∃ r, k_empty_slots bulbs k = ok r ∧ r.val = -1) := by
  sorry

/-- The function returns a result r, and if n = 1 then r = -1, while if n >= 2 then r = min{ max(day(p), day(p+1)) | 1 <= p < n }.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, bulbs is a permutation of {1,2,...,n}, and k = 0. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_8 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs)
    (hk_zero : k.val = 0) :
    ∃ r, k_empty_slots bulbs k = ok r ∧
      (nOf bulbs = 1 → r.val = -1) ∧
      (2 ≤ nOf bulbs →
        (∀ p : Int, 1 ≤ p → p + 1 ≤ nOf bulbs →
          r.val ≤ max (dayOf bulbs p) (dayOf bulbs (p + 1))) ∧
        (∃ p : Int, 1 ≤ p ∧ p + 1 ≤ nOf bulbs ∧
          r.val = max (dayOf bulbs p) (dayOf bulbs (p + 1)))) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs)
    (hk_zero : k.val = 0), ∃ r, k_empty_slots bulbs k = ok r ∧
      (nOf bulbs = 1 → r.val = -1) ∧
      (2 ≤ nOf bulbs →
        (∀ p : Int, 1 ≤ p → p + 1 ≤ nOf bulbs →
          r.val ≤ max (dayOf bulbs p) (dayOf bulbs (p + 1))) ∧
        (∃ p : Int, 1 ≤ p ∧ p + 1 ≤ nOf bulbs ∧
          r.val = max (dayOf bulbs p) (dayOf bulbs (p + 1))))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, we have r <= n-1.
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 < k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_9 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 < k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 → r.val ≤ nOf bulbs - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 < k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 → r.val ≤ nOf bulbs - 1) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every p with 1 <= p and p+k+1 <= n such that for every y with p < y < p+k+1 we have day(y) > max(day(p), day(p+k+1)), it holds that r <= max(day(p), day(p+k+1)).
  Preconditions: Let n = len(bulbs). Assume 1 <= n <= 20000, 0 <= k <= 20000, and bulbs is a permutation of {1,2,...,n}. For 1 <= x <= n, let day(x) be the unique d in {1,...,n} with bulbs[d-1] = x. -/
theorem spec_10 (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs) :
    ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∀ p : Int, GapEnds bulbs k.val p →
        r.val ≤ max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (bulbs : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ nOf bulbs) (hn_le : nOf bulbs ≤ 20000)
    (hk_pos : 0 ≤ k.val) (hk_le : k.val ≤ 20000)
    (hperm : IsPermOfRange bulbs), ∀ r, k_empty_slots bulbs k = ok r → r.val ≠ -1 →
      ∀ p : Int, GapEnds bulbs k.val p →
        r.val ≤ max (dayOf bulbs p) (dayOf bulbs (p + k.val + 1))) := by
  sorry

end AegisSpec.KEmptySlots
