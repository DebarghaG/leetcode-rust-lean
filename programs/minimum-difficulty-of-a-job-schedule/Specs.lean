import Aegis.MinDifficulty.Code.Funs

/-!
# Specifications of `Aegis.MinDifficulty.min_difficulty`

LeetCode problem `minimum-difficulty-of-a-job-schedule`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinDifficulty

  namespace AegisSpec.MinDifficulty

  def vals (jobDifficulty : Slice Std.I64) : List ℤ :=
    jobDifficulty.val.map fun x => x.val

  def listMax (l : List ℤ) : ℤ :=
    l.foldr max 0

  def rangeMax (l : List ℤ) (lo hi : ℕ) : ℤ :=
    listMax ((l.drop lo).take (hi - lo))

  def IsDPartition (n d : ℕ) (c : ℕ → ℕ) : Prop :=
    c 0 = 0 ∧ c d = n ∧ ∀ k, k < d → c k < c (k + 1)

  def partitionCost (l : List ℤ) (d : ℕ) (c : ℕ → ℕ) : ℤ :=
    ((List.range d).map fun k => rangeMax l (c k) (c (k + 1))).sum

  def IsMinCost (l : List ℤ) (d : ℕ) (r : ℤ) : Prop :=
    (∃ c, IsDPartition l.length d c ∧ partitionCost l d c = r) ∧
      ∀ c, IsDPartition l.length d c → r ≤ partitionCost l d c

  def EntrywiseLe (a b : List ℤ) : Prop :=
    ∀ p ∈ a.zip b, 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1000

  def ValidInput (jobDifficulty : Slice Std.I64) (d : Std.I64) : Prop :=
    1 ≤ jobDifficulty.val.length ∧ jobDifficulty.val.length ≤ 300 ∧
      1 ≤ d.val ∧ d.val ≤ 10 ∧ ∀ x ∈ vals jobDifficulty, 0 ≤ x ∧ x ≤ 1000

  /-- The function returns a result r and does not fail. If d > n, then r = -1. If d <= n, then r = min { T(c) : c is a d-partition of jobDifficulty }, where a d-partition is a sequence of indices c_0, c_1, ..., c_d with 0 = c_0 < c_1 < ... < c_d = n, and for such a partition T(c) = sum_{k=0}^{d-1} max { jobDifficulty[i] | c_k <= i < c_{k+1} }.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_1 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (if (jobDifficulty.val.length : ℤ) < d.val then r.val = -1
         else IsMinCost (vals jobDifficulty) d.val.toNat r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (if (jobDifficulty.val.length : ℤ) < d.val then r.val = -1
           else IsMinCost (vals jobDifficulty) d.val.toNat r.val)) := by
    sorry

  /-- The function returns a result r (it does not panic, overflow, or access out-of-bounds).
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_2 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r) := by
    sorry

  /-- The function returns a result r, and r = -1 if and only if d > len(jobDifficulty).
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_3 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (r.val = -1 ↔ (jobDifficulty.val.length : ℤ) < d.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (r.val = -1 ↔ (jobDifficulty.val.length : ℤ) < d.val)) := by
    sorry

  /-- If d <= len(jobDifficulty), then the returned result r satisfies r >= max { jobDifficulty[i] | 0 <= i < len(jobDifficulty) }.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_4 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (d.val ≤ (jobDifficulty.val.length : ℤ) →
          listMax (vals jobDifficulty) ≤ r.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (d.val ≤ (jobDifficulty.val.length : ℤ) →
            listMax (vals jobDifficulty) ≤ r.val)) := by
    sorry

  /-- If d <= len(jobDifficulty), then the returned result r satisfies r <= d * max { jobDifficulty[i] | 0 <= i < len(jobDifficulty) }.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_5 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (d.val ≤ (jobDifficulty.val.length : ℤ) →
          r.val ≤ d.val * listMax (vals jobDifficulty)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (d.val ≤ (jobDifficulty.val.length : ℤ) →
            r.val ≤ d.val * listMax (vals jobDifficulty))) := by
    sorry

  /-- If d <= len(jobDifficulty), then the returned result r satisfies r <= sum_{i=0}^{n-1} jobDifficulty[i], where n = len(jobDifficulty).
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_6 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (d.val ≤ (jobDifficulty.val.length : ℤ) →
          r.val ≤ (vals jobDifficulty).sum) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (d.val ≤ (jobDifficulty.val.length : ℤ) →
            r.val ≤ (vals jobDifficulty).sum)) := by
    sorry

  /-- For every integer d with 1 <= d < len(jobDifficulty), if r_d is the result of min_difficulty(jobDifficulty, d) and r_{d+1} is the result of min_difficulty(jobDifficulty, d+1), then r_d <= r_{d+1}.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_7 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      d.val < (jobDifficulty.val.length : ℤ) →
        ∀ (dnext : Std.I64), dnext.val = d.val + 1 →
          ∀ (r_d r_dnext : Std.I64),
            min_difficulty jobDifficulty d = ok r_d →
            min_difficulty jobDifficulty dnext = ok r_dnext →
            r_d.val ≤ r_dnext.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), d.val < (jobDifficulty.val.length : ℤ) →
          ∀ (dnext : Std.I64), dnext.val = d.val + 1 →
            ∀ (r_d r_dnext : Std.I64),
              min_difficulty jobDifficulty d = ok r_d →
              min_difficulty jobDifficulty dnext = ok r_dnext →
              r_d.val ≤ r_dnext.val) := by
    sorry

  /-- If d <= len(jobDifficulty), then for every d-partition c of jobDifficulty (as defined in spec_1), the returned result r satisfies r <= T(c), where T(c) is the total difficulty of c.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_8 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (d.val ≤ (jobDifficulty.val.length : ℤ) →
          ∀ c, IsDPartition (vals jobDifficulty).length d.val.toNat c →
            r.val ≤ partitionCost (vals jobDifficulty) d.val.toNat c) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (d.val ≤ (jobDifficulty.val.length : ℤ) →
            ∀ c, IsDPartition (vals jobDifficulty).length d.val.toNat c →
              r.val ≤ partitionCost (vals jobDifficulty) d.val.toNat c)) := by
    sorry

  /-- If d <= len(jobDifficulty), then there exists a d-partition c of jobDifficulty (as defined in spec_1) such that the returned result r equals T(c), the total difficulty of c.
    Preconditions: Let n = len(jobDifficulty). The input satisfies 1 <= n <= 300, 1 <= d <= 10, and 0 <= jobDifficulty[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_9 (jobDifficulty : Slice Std.I64) (d : Std.I64)
      (h : ValidInput jobDifficulty d) :
      ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
        (d.val ≤ (jobDifficulty.val.length : ℤ) →
          ∃ c, IsDPartition (vals jobDifficulty).length d.val.toNat c ∧
            partitionCost (vals jobDifficulty) d.val.toNat c = r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (jobDifficulty : Slice Std.I64) (d : Std.I64)
        (h : ValidInput jobDifficulty d), ∃ r : Std.I64, min_difficulty jobDifficulty d = ok r ∧
          (d.val ≤ (jobDifficulty.val.length : ℤ) →
            ∃ c, IsDPartition (vals jobDifficulty).length d.val.toNat c ∧
              partitionCost (vals jobDifficulty) d.val.toNat c = r.val)) := by
    sorry

  /-- Let r_a be the result of min_difficulty(a, d) and r_b be the result of min_difficulty(b, d). Then r_a <= r_b.
    Preconditions: Let a and b be two slices of the same length n with 1 <= n <= 300, let 1 <= d <= 10, and assume 0 <= a[i] <= b[i] <= 1000 for every 0 <= i < n. -/
  theorem spec_10 (a b : Slice Std.I64) (d : Std.I64)
      (hlen : (vals a).length = (vals b).length)
      (hn : 1 ≤ (vals a).length ∧ (vals a).length ≤ 300)
      (hd : 1 ≤ d.val ∧ d.val ≤ 10)
      (hle : EntrywiseLe (vals a) (vals b)) :
      ∀ (r_a r_b : Std.I64),
        min_difficulty a d = ok r_a →
        min_difficulty b d = ok r_b →
        r_a.val ≤ r_b.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b : Slice Std.I64) (d : Std.I64)
        (hlen : (vals a).length = (vals b).length)
        (hn : 1 ≤ (vals a).length ∧ (vals a).length ≤ 300)
        (hd : 1 ≤ d.val ∧ d.val ≤ 10)
        (hle : EntrywiseLe (vals a) (vals b)), ∀ (r_a r_b : Std.I64),
          min_difficulty a d = ok r_a →
          min_difficulty b d = ok r_b →
          r_a.val ≤ r_b.val) := by
    sorry

  end AegisSpec.MinDifficulty
