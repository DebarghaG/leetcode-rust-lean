import Aegis.FindMaximalUncoveredRanges.Code.Funs

/-!
# Specifications of `Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges`

LeetCode problem `find-maximal-uncovered-ranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMaximalUncoveredRanges

  def cells (row : alloc.vec.Vec Std.I64) : List Int := row.val.map fun x => x.val

  def inputRows (ranges : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    ranges.val.map cells

  def outputRows (out : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
    out.val.map cells

  def ValidRange (n : Int) (r : List Int) : Prop :=
    ∃ s e : Int, r = [s, e] ∧ 0 ≤ s ∧ s ≤ n - 1 ∧ s ≤ e ∧ e ≤ n

  def InRange (R : List (List Int)) (i : Int) : Prop :=
    ∃ (j : Nat) (r : List Int) (s e : Int),
      j < R.length ∧ R[j]? = some r ∧ r[0]? = some s ∧ r[1]? = some e ∧
        s ≤ i ∧ i ≤ e

  def Covered (n : Int) (R : List (List Int)) (i : Int) : Prop :=
    0 ≤ i ∧ i < n ∧ InRange R i

  def Uncovered (n : Int) (R : List (List Int)) (i : Int) : Prop :=
    0 ≤ i ∧ i < n ∧ ¬ InRange R i

  def Row (R : List (List Int)) (k : Nat) (a b : Int) : Prop := R[k]? = some [a, b]

  def IsLeastUncovered (n : Int) (R : List (List Int)) (i : Int) : Prop :=
    Uncovered n R i ∧ ∀ i' : Int, Uncovered n R i' → i ≤ i'

  def IsGreatestUncovered (n : Int) (R : List (List Int)) (i : Int) : Prop :=
    Uncovered n R i ∧ ∀ i' : Int, Uncovered n R i' → i' ≤ i

  /-- Let out be the returned value. For a cell index i define covered(i) to mean: 0 <= i < n and there exists j with 0 <= j < len(ranges) and ranges[j][0] <= i <= ranges[j][1]. Define uncovered(i) to mean: 0 <= i < n and not covered(i). Then all of the following hold. (a) For every k with 0 <= k < len(out): len(out[k]) = 2, 0 <= out[k][0] <= out[k][1] < n, every i with out[k][0] <= i <= out[k][1] is uncovered, and (out[k][0] = 0 or covered(out[k][0]-1)) and (out[k][1] = n-1 or covered(out[k][1]+1)). (b) The intervals are strictly increasing in start: for every k with 0 <= k < len(out)-1, out[k][0] < out[k+1][0]. (c) Conversely, for every pair a,b with 0 <= a <= b < n such that every i with a <= i <= b is uncovered, and such that (a = 0 or covered(a-1)) and (b = n-1 or covered(b+1)), there is exactly one k with out[k][0] = a and out[k][1] = b.
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered, so a range ending at n covers up to n-1.) -/
  theorem spec_1 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧

        (∀ k : Nat, k < out.val.length → ∃ a b : Int,
          Row (outputRows out) k a b ∧
          0 ≤ a ∧ a ≤ b ∧ b < n.val ∧
          (∀ i : Int, a ≤ i → i ≤ b → Uncovered n.val (inputRows ranges) i) ∧
          (a = 0 ∨ Covered n.val (inputRows ranges) (a - 1)) ∧
          (b = n.val - 1 ∨ Covered n.val (inputRows ranges) (b + 1))) ∧

        (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
          Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ a < a') ∧

        (∀ a b : Int, 0 ≤ a → a ≤ b → b < n.val →
          (∀ i : Int, a ≤ i → i ≤ b → Uncovered n.val (inputRows ranges) i) →
          (a = 0 ∨ Covered n.val (inputRows ranges) (a - 1)) →
          (b = n.val - 1 ∨ Covered n.val (inputRows ranges) (b + 1)) →
          ∃! k : Nat, k < out.val.length ∧ Row (outputRows out) k a b) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧

          (∀ k : Nat, k < out.val.length → ∃ a b : Int,
            Row (outputRows out) k a b ∧
            0 ≤ a ∧ a ≤ b ∧ b < n.val ∧
            (∀ i : Int, a ≤ i → i ≤ b → Uncovered n.val (inputRows ranges) i) ∧
            (a = 0 ∨ Covered n.val (inputRows ranges) (a - 1)) ∧
            (b = n.val - 1 ∨ Covered n.val (inputRows ranges) (b + 1))) ∧

          (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
            Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ a < a') ∧

          (∀ a b : Int, 0 ≤ a → a ≤ b → b < n.val →
            (∀ i : Int, a ≤ i → i ≤ b → Uncovered n.val (inputRows ranges) i) →
            (a = 0 ∨ Covered n.val (inputRows ranges) (a - 1)) →
            (b = n.val - 1 ∨ Covered n.val (inputRows ranges) (b + 1)) →
            ∃! k : Nat, k < out.val.length ∧ Row (outputRows out) k a b)) := by
    sorry

  /-- For the returned out, every k with 0 <= k < len(out) satisfies 0 <= out[k][0] <= out[k][1] <= n-1.
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_2 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length → ∃ a b : Int,
          Row (outputRows out) k a b ∧ 0 ≤ a ∧ a ≤ b ∧ b ≤ n.val - 1) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length → ∃ a b : Int,
            Row (outputRows out) k a b ∧ 0 ≤ a ∧ a ≤ b ∧ b ≤ n.val - 1)) := by
    sorry

  /-- For the returned out, every k with 0 <= k < len(out) satisfies len(out[k]) = 2.
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_3 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length → ∃ row : alloc.vec.Vec Std.I64,
          out.val[k]? = some row ∧ row.val.length = 2) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length → ∃ row : alloc.vec.Vec Std.I64,
            out.val[k]? = some row ∧ row.val.length = 2)) := by
    sorry

  /-- For the returned out, for every k with 0 <= k < len(out) and every i with out[k][0] <= i <= out[k][1]: there is no j with 0 <= j < len(ranges) and ranges[j][0] <= i <= ranges[j][1] (that is, cell i is uncovered).
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_4 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length →
          ∀ a b : Int, Row (outputRows out) k a b →
            ∀ i : Int, a ≤ i → i ≤ b → ¬ InRange (inputRows ranges) i) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length →
            ∀ a b : Int, Row (outputRows out) k a b →
              ∀ i : Int, a ≤ i → i ≤ b → ¬ InRange (inputRows ranges) i)) := by
    sorry

  /-- For the returned out, for every k with 0 <= k < len(out): either out[k][0] = 0, or there exists j with 0 <= j < len(ranges) and ranges[j][0] <= out[k][0]-1 <= ranges[j][1].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_5 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length → ∃ a b : Int,
          Row (outputRows out) k a b ∧
            (a = 0 ∨ InRange (inputRows ranges) (a - 1))) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length → ∃ a b : Int,
            Row (outputRows out) k a b ∧
              (a = 0 ∨ InRange (inputRows ranges) (a - 1)))) := by
    sorry

  /-- For the returned out, for every k with 0 <= k < len(out): either out[k][1] = n-1, or there exists j with 0 <= j < len(ranges) and ranges[j][0] <= out[k][1]+1 <= ranges[j][1].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_6 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length → ∃ a b : Int,
          Row (outputRows out) k a b ∧
            (b = n.val - 1 ∨ InRange (inputRows ranges) (b + 1))) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length → ∃ a b : Int,
            Row (outputRows out) k a b ∧
              (b = n.val - 1 ∨ InRange (inputRows ranges) (b + 1)))) := by
    sorry

  /-- For the returned out, for every i with 0 <= i < n such that there is no j with 0 <= j < len(ranges) and ranges[j][0] <= i <= ranges[j][1] (i.e., cell i is uncovered): there exists k with 0 <= k < len(out) and out[k][0] <= i <= out[k][1].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_7 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ i : Int, 0 ≤ i → i < n.val → ¬ InRange (inputRows ranges) i →
          ∃ k : Nat, k < out.val.length ∧ ∃ a b : Int,
            Row (outputRows out) k a b ∧ a ≤ i ∧ i ≤ b) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ i : Int, 0 ≤ i → i < n.val → ¬ InRange (inputRows ranges) i →
            ∃ k : Nat, k < out.val.length ∧ ∃ a b : Int,
              Row (outputRows out) k a b ∧ a ≤ i ∧ i ≤ b)) := by
    sorry

  /-- For the returned out, and for any two distinct indices k, m with 0 <= k < len(out) and 0 <= m < len(out), the intervals [out[k][0], out[k][1]] and [out[m][0], out[m][1]] are disjoint: there is no integer i with out[k][0] <= i <= out[k][1] and out[m][0] <= i <= out[m][1].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_8 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ (k m : Nat) (a b a' b' : Int),
          k < out.val.length → m < out.val.length → k ≠ m →
          Row (outputRows out) k a b → Row (outputRows out) m a' b' →
          ¬ ∃ i : Int, a ≤ i ∧ i ≤ b ∧ a' ≤ i ∧ i ≤ b') := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ (k m : Nat) (a b a' b' : Int),
            k < out.val.length → m < out.val.length → k ≠ m →
            Row (outputRows out) k a b → Row (outputRows out) m a' b' →
            ¬ ∃ i : Int, a ≤ i ∧ i ≤ b ∧ a' ≤ i ∧ i ≤ b')) := by
    sorry

  /-- For the returned out, for every k with 0 <= k < len(out)-1: out[k][0] < out[k+1][0].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_9 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
          Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ a < a') := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
            Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ a < a')) := by
    sorry

  /-- For the returned out, for every k with 0 <= k < len(out)-1: out[k][1] + 1 < out[k+1][0].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_10 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
          Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ b + 1 < a') := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (∀ k : Nat, k < out.val.length - 1 → ∃ a b a' b' : Int,
            Row (outputRows out) k a b ∧ Row (outputRows out) (k + 1) a' b' ∧ b + 1 < a')) := by
    sorry

  /-- For the returned out: len(out) = 0 if and only if every i with 0 <= i < n is covered, i.e., for every i with 0 <= i < n there exists j with 0 <= j < len(ranges) and ranges[j][0] <= i <= ranges[j][1].
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_11 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        (out.val.length = 0 ↔ ∀ i : Int, 0 ≤ i → i < n.val → InRange (inputRows ranges) i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          (out.val.length = 0 ↔ ∀ i : Int, 0 ≤ i → i < n.val → InRange (inputRows ranges) i)) := by
    sorry

  /-- The function returns Ok r for some value r on every input satisfying the preconditions; it never fails (no overflow, out-of-bounds access, or panic occurs).
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; all computed bounds such as ranges[j][1]+1 and out[k][1]+1 are then at most 10^9+1, within i64.) -/
  theorem spec_12 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out) := by
    sorry

  /-- Suppose there is at least one uncovered cell, i.e., some i with 0 <= i < n such that no j with 0 <= j < len(ranges) has ranges[j][0] <= i <= ranges[j][1]. Then for the returned out: len(out) >= 1, out[0][0] equals the least uncovered cell index, and out[len(out)-1][1] equals the greatest uncovered cell index.
    Preconditions: 1 <= n <= 10^9; 0 <= len(ranges) <= 10^6; for every j with 0 <= j < len(ranges): len(ranges[j]) = 2, 0 <= ranges[j][0] <= n-1, and ranges[j][0] <= ranges[j][1] <= n. (The upper bound n on ranges[j][1], rather than n-1, is required by the example n = 10^9, ranges = [[0,10^9]]; only cells 0..n-1 are considered.) -/
  theorem spec_13 (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
      (hlen : (inputRows ranges).length ≤ 10 ^ 6)
      (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r)
      (hunc : ∃ i : Int, Uncovered n.val (inputRows ranges) i) :
      ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
        1 ≤ out.val.length ∧
        (∃ a b : Int, Row (outputRows out) 0 a b ∧
          IsLeastUncovered n.val (inputRows ranges) a) ∧
        (∃ a b : Int, Row (outputRows out) (out.val.length - 1) a b ∧
          IsGreatestUncovered n.val (inputRows ranges) b) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n : Std.I64) (ranges : Slice (alloc.vec.Vec Std.I64))
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10 ^ 9)
        (hlen : (inputRows ranges).length ≤ 10 ^ 6)
        (hrows : ∀ r ∈ inputRows ranges, ValidRange n.val r)
        (hunc : ∃ i : Int, Uncovered n.val (inputRows ranges) i), ∃ out : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          Aegis.FindMaximalUncoveredRanges.find_maximal_uncovered_ranges n ranges = ok out ∧
          1 ≤ out.val.length ∧
          (∃ a b : Int, Row (outputRows out) 0 a b ∧
            IsLeastUncovered n.val (inputRows ranges) a) ∧
          (∃ a b : Int, Row (outputRows out) (out.val.length - 1) a b ∧
            IsGreatestUncovered n.val (inputRows ranges) b)) := by
    sorry

  end AegisSpec.FindMaximalUncoveredRanges
