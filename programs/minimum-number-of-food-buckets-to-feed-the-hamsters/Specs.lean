import Aegis.MinimumBuckets.Code.Funs

/-!
# Specifications of `Aegis.MinimumBuckets.minimum_buckets`

LeetCode problem `minimum-number-of-food-buckets-to-feed-the-hamsters`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumBuckets

def byteAt (s : List Std.U8) (i : Nat) : Nat := ((s[i]?).map (fun b => b.val)).getD 0

def IsHamster (s : List Std.U8) (i : Nat) : Prop := byteAt s i = 72

def IsEmpty (s : List Std.U8) (i : Nat) : Prop := byteAt s i = 46

def countEmpty (s : List Std.U8) : Nat := (List.range s.length).countP (fun i => byteAt s i == 46)

def countHamster (s : List Std.U8) : Nat := (List.range s.length).countP (fun i => byteAt s i == 72)

def IsBucketPlacement (s : List Std.U8) (S : Finset Nat) : Prop :=
  ∀ j ∈ S, j < s.length ∧ IsEmpty s j

def FeedsAll (s : List Std.U8) (S : Finset Nat) : Prop :=
  ∀ i, i < s.length → IsHamster s i → ((0 < i ∧ i - 1 ∈ S) ∨ (i + 1 < s.length ∧ i + 1 ∈ S))

def cardinalities (s : List Std.U8) : Set Nat :=
  Set.ofPred (fun k => ∃ S : Finset Nat, IsBucketPlacement s S ∧ FeedsAll s S ∧ S.card = k)

def IsMinCardinality (C : Set Nat) (m : Nat) : Prop := m ∈ C ∧ ∀ k ∈ C, m ≤ k

/-- Let n = len(hamsters). A bucket placement is a set S of indices such that 0 <= j < n and hamsters[j] = '.' for every j in S. Such a placement feeds all hamsters if for every i with 0 <= i < n and hamsters[i] = 'H', either (i > 0 and i-1 in S) or (i+1 < n and i+1 in S). Let C be the set of cardinalities |S| of all bucket placements that feed all hamsters. The function returns a result r and: if C is empty, then r = -1; otherwise r = min(C).
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_1 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∃ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r ∧
      ((cardinalities hamsters.val = (∅ : Set Nat) ∧ r.val = -1) ∨
        (∃ m : Nat, IsMinCardinality (cardinalities hamsters.val) m ∧ r.val = (m : Int))) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∃ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r ∧
      ((cardinalities hamsters.val = (∅ : Set Nat) ∧ r.val = -1) ∨
        (∃ m : Nat, IsMinCardinality (cardinalities hamsters.val) m ∧ r.val = (m : Int)))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_2 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∃ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∃ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r, we have r = -1 if and only if there exists an index i with 0 <= i < n and hamsters[i] = 'H' such that both possible neighbors are unusable empty indices: (i = 0 or hamsters[i-1] != '.') and (i+1 = n or hamsters[i+1] != '.'). Equivalently, r != -1 exactly when every index i with hamsters[i] = 'H' has at least one in-range neighbor whose byte is '.'.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_3 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = -1 ↔
        ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i ∧
          (i = 0 ∨ ¬ IsEmpty hamsters.val (i - 1)) ∧
          (i + 1 = hamsters.val.length ∨ ¬ IsEmpty hamsters.val (i + 1))) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = -1 ↔
        ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i ∧
          (i = 0 ∨ ¬ IsEmpty hamsters.val (i - 1)) ∧
          (i + 1 = hamsters.val.length ∨ ¬ IsEmpty hamsters.val (i + 1)))) := by
  sorry

/-- Whenever the function returns a result r, either r = -1, or 0 <= r <= E, where E is the number of indices i with 0 <= i < len(hamsters) and hamsters[i] = '.'.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_4 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (countEmpty hamsters.val : Int))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ (countEmpty hamsters.val : Int)))) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, let H be the number of indices i with hamsters[i] = 'H'. Then 2*r >= H, equivalently r >= ceil(H/2).
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_5 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      2 * r.val ≥ (countHamster hamsters.val : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      2 * r.val ≥ (countHamster hamsters.val : Int)) := by
  sorry

/-- Whenever the function returns a result r with r >= 0, r <= H, where H is the number of indices i with hamsters[i] = 'H'.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_6 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      r.val ≤ (countHamster hamsters.val : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      r.val ≤ (countHamster hamsters.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < len(hamsters) and hamsters[i] = 'H'.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_7 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = 0 ↔ ¬ ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r →
      (r.val = 0 ↔ ¬ ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i)) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r with r >= 0, there exists a set S of indices such that: (a) 0 <= j < n and hamsters[j] = '.' for every j in S; (b) |S| = r; and (c) for every i with hamsters[i] = 'H', either (i > 0 and i-1 in S) or (i+1 < n and i+1 in S).
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_8 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∃ S : Finset Nat,
        IsBucketPlacement hamsters.val S ∧ (S.card : Int) = r.val ∧ FeedsAll hamsters.val S := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∃ S : Finset Nat,
        IsBucketPlacement hamsters.val S ∧ (S.card : Int) = r.val ∧ FeedsAll hamsters.val S) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r with r >= 0, every set S of indices with 0 <= j < n and hamsters[j] = '.' for every j in S, and with the property that every i with hamsters[i] = 'H' has either (i > 0 and i-1 in S) or (i+1 < n and i+1 in S), satisfies |S| >= r.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_9 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S →
        r.val ≤ (S.card : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S →
        r.val ≤ (S.card : Int)) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r with r >= 0, let S be any set of empty indices that feeds all hamsters and has |S| = r: all j in S satisfy hamsters[j] = '.', and every i with hamsters[i] = 'H' has an adjacent index in S. Then for every j in S there exists an index i with hamsters[i] = 'H' such that (i = j-1 or i = j+1), and for every k in S with k != j, neither k = i-1 nor k = i+1.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_10 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S →
        (S.card : Int) = r.val →
        ∀ j ∈ S, ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i ∧
          ((1 ≤ j ∧ i = j - 1) ∨ i = j + 1) ∧
          (∀ k ∈ S, k ≠ j → k ≠ i - 1 ∧ k ≠ i + 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S →
        (S.card : Int) = r.val →
        ∀ j ∈ S, ∃ i, i < hamsters.val.length ∧ IsHamster hamsters.val i ∧
          ((1 ≤ j ∧ i = j - 1) ∨ i = j + 1) ∧
          (∀ k ∈ S, k ≠ j → k ≠ i - 1 ∧ k ≠ i + 1)) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r with r >= 0, consider any index i with hamsters[i] = 'H' for which exactly one index e in {i-1, i+1} lies in [0,n) and has hamsters[e] = '.'. Then every bucket placement S that feeds all hamsters contains e.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_11 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ i, i < hamsters.val.length → IsHamster hamsters.val i →
        ∀ e, (e + 1 = i ∨ e = i + 1) → IsEmpty hamsters.val e →
          (∀ e', (e' + 1 = i ∨ e' = i + 1) → IsEmpty hamsters.val e' → e' = e) →
          ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S → e ∈ S := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ i, i < hamsters.val.length → IsHamster hamsters.val i →
        ∀ e, (e + 1 = i ∨ e = i + 1) → IsEmpty hamsters.val e →
          (∀ e', (e' + 1 = i ∨ e' = i + 1) → IsEmpty hamsters.val e' → e' = e) →
          ∀ S : Finset Nat, IsBucketPlacement hamsters.val S → FeedsAll hamsters.val S → e ∈ S) := by
  sorry

/-- Let n = len(hamsters). Whenever the function returns a result r with r >= 0, every maximal contiguous block [a,b] of indices such that hamsters[t] = 'H' for all a <= t <= b (with a = 0 or hamsters[a-1] != 'H', and with b+1 = n or hamsters[b+1] != 'H') has length 1 or 2. If its length is 1, then at least one of the existing neighbors a-1 (when a > 0) or b+1 (when b+1 < n) is '.'. If its length is 2, then a > 0, b+1 < n, hamsters[a-1] = '.', and hamsters[b+1] = '.'.
  Preconditions: 1 <= len(hamsters) <= 100000, and for every i with 0 <= i < len(hamsters), hamsters[i] is the ASCII byte for 'H' (72) or for '.' (46). -/
theorem spec_12 (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i) :
    ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ a b : Nat, a ≤ b →
        (∀ t, a ≤ t → t ≤ b → IsHamster hamsters.val t) →
        (a = 0 ∨ ¬ IsHamster hamsters.val (a - 1)) →
        (b + 1 = hamsters.val.length ∨ ¬ IsHamster hamsters.val (b + 1)) →
        ((b + 1 - a = 1 ∨ b + 1 - a = 2) ∧
          (b + 1 - a = 1 →
            (0 < a ∧ IsEmpty hamsters.val (a - 1)) ∨
              (b + 1 < hamsters.val.length ∧ IsEmpty hamsters.val (b + 1))) ∧
          (b + 1 - a = 2 →
            0 < a ∧ b + 1 < hamsters.val.length ∧
              IsEmpty hamsters.val (a - 1) ∧ IsEmpty hamsters.val (b + 1))) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hamsters : Slice Std.U8)
    (h_len_lb : 1 ≤ hamsters.val.length) (h_len_ub : hamsters.val.length ≤ 100000)
    (h_bytes : ∀ i, i < hamsters.val.length →
      IsHamster hamsters.val i ∨ IsEmpty hamsters.val i), ∀ r : Std.I64, Aegis.MinimumBuckets.minimum_buckets hamsters = ok r → 0 ≤ r.val →
      ∀ a b : Nat, a ≤ b →
        (∀ t, a ≤ t → t ≤ b → IsHamster hamsters.val t) →
        (a = 0 ∨ ¬ IsHamster hamsters.val (a - 1)) →
        (b + 1 = hamsters.val.length ∨ ¬ IsHamster hamsters.val (b + 1)) →
        ((b + 1 - a = 1 ∨ b + 1 - a = 2) ∧
          (b + 1 - a = 1 →
            (0 < a ∧ IsEmpty hamsters.val (a - 1)) ∨
              (b + 1 < hamsters.val.length ∧ IsEmpty hamsters.val (b + 1))) ∧
          (b + 1 - a = 2 →
            0 < a ∧ b + 1 < hamsters.val.length ∧
              IsEmpty hamsters.val (a - 1) ∧ IsEmpty hamsters.val (b + 1)))) := by
  sorry

end AegisSpec.MinimumBuckets
