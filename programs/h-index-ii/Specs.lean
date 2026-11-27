import Aegis.HIndex.Code.Funs

/-!
# Specifications of `Aegis.HIndex.h_index`

LeetCode problem `h-index-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HIndex

def C (citations : Slice Std.I64) (h : Int) : Nat :=
  (citations.val.filter (fun c => decide (h ≤ c.val))).length

/-- Whenever the function returns a result r, r is the largest integer h satisfying 0 <= h <= n and C(h) >= h, where n = len(citations) and C(h) is the number of indices i with 0 <= i < n and citations[i] >= h. (The set of such h is nonempty because h = 0 satisfies C(0) = n >= 0.)
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_1 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      0 ≤ r.val ∧ r.val ≤ (citations.val.length : Int) ∧
        r.val ≤ (C citations r.val : Int) ∧
        ∀ h : Int, 0 ≤ h → h ≤ (citations.val.length : Int) →
          h ≤ (C citations h : Int) → h ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      0 ≤ r.val ∧ r.val ≤ (citations.val.length : Int) ∧
        r.val ≤ (C citations r.val : Int) ∧
        ∀ h : Int, 0 ≤ h → h ≤ (citations.val.length : Int) →
          h ≤ (C citations h : Int) → h ≤ r.val) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_2 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∃ r, Aegis.HIndex.h_index citations = .ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∃ r, Aegis.HIndex.h_index citations = Result.ok r) := by
  sorry

/-- Whenever the function returns r, 0 <= r <= n, where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_3 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      0 ≤ r.val ∧ r.val ≤ (citations.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      0 ≤ r.val ∧ r.val ≤ (citations.val.length : Int)) := by
  sorry

/-- Whenever the function returns r, r <= citations[n-1], where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_4 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      r.val ≤ (citations.val[citations.val.length - 1]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      r.val ≤ (citations.val[citations.val.length - 1]!).val) := by
  sorry

/-- Whenever the function returns r, C(r) >= r, where n = len(citations) and C(h) is the number of indices i with 0 <= i < n and citations[i] >= h.
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_5 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      r.val ≤ (C citations r.val : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      r.val ≤ (C citations r.val : Int)) := by
  sorry

/-- Whenever the function returns r, for every integer h with r < h <= n, C(h) < h, where n = len(citations) and C(h) is the number of indices i with 0 <= i < n and citations[i] >= h.
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_6 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      ∀ h : Int, r.val < h → h ≤ (citations.val.length : Int) →
        (C citations h : Int) < h := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      ∀ h : Int, r.val < h → h ≤ (citations.val.length : Int) →
        (C citations h : Int) < h) := by
  sorry

/-- Whenever the function returns r, if r >= 1 then n - r is an index with 0 <= n - r < n and citations[n - r] >= r, where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_7 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      1 ≤ r.val →
        ∃ i : Nat, i < citations.val.length ∧
          (i : Int) = (citations.val.length : Int) - r.val ∧
          r.val ≤ (citations.val[i]!).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      1 ≤ r.val →
        ∃ i : Nat, i < citations.val.length ∧
          (i : Int) = (citations.val.length : Int) - r.val ∧
          r.val ≤ (citations.val[i]!).val) := by
  sorry

/-- Whenever the function returns r, for every index i with 0 <= i < n - r, citations[i] <= r, where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_8 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      ∀ i : Nat, (i : Int) < (citations.val.length : Int) - r.val →
        (citations.val[i]!).val ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      ∀ i : Nat, (i : Int) < (citations.val.length : Int) - r.val →
        (citations.val[i]!).val ≤ r.val) := by
  sorry

/-- Whenever the function returns r, r = 0 if and only if citations[n-1] = 0, where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_9 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      (r.val = 0 ↔ (citations.val[citations.val.length - 1]!).val = 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      (r.val = 0 ↔ (citations.val[citations.val.length - 1]!).val = 0)) := by
  sorry

/-- Whenever the function returns r, r = n if and only if citations[0] >= n, where n = len(citations).
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_10 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      (r.val = (citations.val.length : Int) ↔
        (citations.val[0]!).val ≥ (citations.val.length : Int)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      (r.val = (citations.val.length : Int) ↔
        (citations.val[0]!).val ≥ (citations.val.length : Int))) := by
  sorry

/-- Whenever the function returns r, for every integer h with 0 <= h <= r, C(h) >= h, where n = len(citations) and C(h) is the number of indices i with 0 <= i < n and citations[i] >= h.
  Preconditions: Let n = len(citations). The input satisfies: 1 <= n <= 100000; for every i with 0 <= i < n, 0 <= citations[i] <= 1000; and citations is sorted in nondecreasing order, i.e., for every i with 0 <= i < n-1, citations[i] <= citations[i+1]. -/
theorem spec_11 (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val) :
    ∀ r, Aegis.HIndex.h_index citations = .ok r →
      ∀ h : Int, 0 ≤ h → h ≤ r.val → h ≤ (C citations h : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (citations : Slice Std.I64)
    (hn_pos : 1 ≤ citations.val.length)
    (hn_le : citations.val.length ≤ 100000)
    (hval : ∀ i, i < citations.val.length → 0 ≤ (citations.val[i]!).val ∧ (citations.val[i]!).val ≤ 1000)
    (hsorted : ∀ i, i + 1 < citations.val.length → (citations.val[i]!).val ≤ (citations.val[i + 1]!).val), ∀ r, Aegis.HIndex.h_index citations = Result.ok r →
      ∀ h : Int, 0 ≤ h → h ≤ r.val → h ≤ (C citations h : Int)) := by
  sorry

end AegisSpec.HIndex
