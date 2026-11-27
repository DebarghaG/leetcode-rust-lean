import Aegis.LargeGroupPositions.Code.Funs

/-!
# Specifications of `Aegis.LargeGroupPositions.large_group_positions`

LeetCode problem `positions-of-large-groups`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LargeGroupPositions

  def byteAt (s : Slice U8) (i : Int) : Nat :=
    ((s.val[i.toNat]?).map (fun b => b.val)).getD 0

  def ConstantOn (s : Slice U8) (a b : Int) : Prop :=
    ∀ k : Int, a ≤ k → k ≤ b → byteAt s k = byteAt s a

  def IsMaximalRun (s : Slice U8) (a b : Int) : Prop :=
    ConstantOn s a b ∧
      (a = 0 ∨ byteAt s (a - 1) ≠ byteAt s a) ∧
      (b + 1 = (s.val.length : Int) ∨ byteAt s (b + 1) ≠ byteAt s b)

  def IsLargeMaximalRun (s : Slice U8) (a b : Int) : Prop :=
    IsMaximalRun s a b ∧ 3 ≤ b - a + 1

  open Classical in

  noncomputable def allLargeRuns (s : Slice U8) : List (Int × Int) :=
    ((List.range s.val.length).product (List.range s.val.length)).filterMap
      (fun p =>
        if IsLargeMaximalRun s (p.1 : Int) (p.2 : Int) then
          some ((p.1 : Int), (p.2 : Int))
        else none)

  def entryInts (v : alloc.vec.Vec I64) : List Int :=
    v.val.map (fun x => x.val)

  def outPairs (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List (Option (Int × Int)) :=
    r.val.map (fun v =>
      match entryInts v with
      | [a, b] => some (a, b)
      | _ => none)

  def PairAt (r : alloc.vec.Vec (alloc.vec.Vec I64)) (j : Nat) (a b : Int) : Prop :=
    ∃ v : alloc.vec.Vec I64, r.val[j]? = some v ∧ entryInts v = [a, b]

  def TripleStart (s : Slice U8) (i : Int) : Prop :=
    0 ≤ i ∧ i + 2 < (s.val.length : Int) ∧
      byteAt s i = byteAt s (i + 1) ∧ byteAt s (i + 1) = byteAt s (i + 2)

  def TripleEnd (s : Slice U8) (i : Int) : Prop :=
    2 ≤ i ∧ i < (s.val.length : Int) ∧
      byteAt s (i - 2) = byteAt s (i - 1) ∧ byteAt s (i - 1) = byteAt s i

  /-- The function returns successfully with value r. For every j with 0 <= j < len(r), r[j] is a vector of exactly two I64 values; write r[j] = [a_j, b_j]. The list of these pairs, in the order j = 0, 1, ..., len(r)-1, is exactly the list of all pairs (a,b) of integers with 0 <= a <= b < len(s) such that b - a + 1 >= 3, s[k] = s[a] for every k with a <= k <= b, (a = 0 or s[a-1] != s[a]), and (b + 1 = len(s) or s[b+1] != s[b]); this list is ordered by increasing first component a. Thus every returned pair is a maximal constant run of length at least 3, every such run is returned, and no other pair is returned.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_1 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r ∧
        outPairs r = (allLargeRuns s).map (fun p => some p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r ∧
          outPairs r = (allLargeRuns s).map (fun p => some p)) := by
    sorry

  /-- The function returns successfully: there exists a value r such that large_group_positions s evaluates to a successful result with value r. In particular it does not fail, panic, or overflow on the given constraints.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_2 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every j with 0 <= j < len(r), len(r[j]) = 2. In other words, every produced interval is represented by exactly two I64 entries.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_3 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ j : Nat, j < r.val.length →
          ∃ v : alloc.vec.Vec I64, r.val[j]? = some v ∧ v.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ j : Nat, j < r.val.length →
            ∃ v : alloc.vec.Vec I64, r.val[j]? = some v ∧ v.val.length = 2) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every j with 0 <= j < len(r) such that len(r[j]) = 2, writing a = r[j][0] and b = r[j][1], we have 0 <= a <= b < len(s).
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_4 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ (j : Nat), j < r.val.length →
        ∀ a b : Int, PairAt r j a b → 0 ≤ a ∧ a ≤ b ∧ b < (s.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ (j : Nat), j < r.val.length →
          ∀ a b : Int, PairAt r j a b → 0 ≤ a ∧ a ≤ b ∧ b < (s.val.length : Int)) := by
    sorry

  /-- Whenever the function returns successfully with value r, for all j and k with 0 <= j < k < len(r), if len(r[j]) = 2 and len(r[k]) = 2, then r[j][0] < r[k][0]. Thus the represented intervals appear in strictly increasing order of start index.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_5 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ (j k : Nat), j < k → k < r.val.length →
        ∀ a b c d : Int, PairAt r j a b → PairAt r k c d → a < c := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ (j k : Nat), j < k → k < r.val.length →
          ∀ a b c d : Int, PairAt r j a b → PairAt r k c d → a < c) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every j with 0 <= j < len(r)-1, if len(r[j]) = 2 and len(r[j+1]) = 2, then r[j][1] < r[j+1][0]. Thus every two consecutive represented intervals are disjoint and ordered, with the end index of the earlier interval strictly less than the start index of the later interval.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_6 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ (j : Nat), j + 1 < r.val.length →
        ∀ a b c d : Int, PairAt r j a b → PairAt r (j + 1) c d → b < c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ (j : Nat), j + 1 < r.val.length →
          ∀ a b c d : Int, PairAt r j a b → PairAt r (j + 1) c d → b < c) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every j with 0 <= j < len(r) such that len(r[j]) = 2, writing a = r[j][0] and b = r[j][1], for every k with a <= k <= b we have s[k] = s[a]. Thus a returned interval lies entirely inside one constant-character run.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_7 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ (j : Nat), j < r.val.length →
        ∀ a b : Int, PairAt r j a b → ConstantOn s a b := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ (j : Nat), j < r.val.length →
          ∀ a b : Int, PairAt r j a b → ConstantOn s a b) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every j with 0 <= j < len(r) such that len(r[j]) = 2, writing a = r[j][0] and b = r[j][1], we have b - a + 1 >= 3, s[k] = s[a] for every k with a <= k <= b, (a = 0 or s[a-1] != s[a]), and (b + 1 = len(s) or s[b+1] != s[b]). Thus every returned interval is a maximal constant run whose length is at least 3.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_8 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ (j : Nat), j < r.val.length →
        ∀ a b : Int, PairAt r j a b → IsLargeMaximalRun s a b := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ (j : Nat), j < r.val.length →
          ∀ a b : Int, PairAt r j a b → IsLargeMaximalRun s a b) := by
    sorry

  /-- Whenever the function returns successfully with value r, for every a and b with 0 <= a <= b < len(s), if b - a + 1 >= 3, s[k] = s[a] for every k with a <= k <= b, (a = 0 or s[a-1] != s[a]), and (b + 1 = len(s) or s[b+1] != s[b]), then there exists j with 0 <= j < len(r) such that len(r[j]) = 2, r[j][0] = a, and r[j][1] = b. Thus every maximal constant run of length at least 3 is present in the output.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_9 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        ∀ a b : Int, 0 ≤ a → a ≤ b → b < (s.val.length : Int) →
          IsLargeMaximalRun s a b →
          ∃ j : Nat, j < r.val.length ∧ PairAt r j a b := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          ∀ a b : Int, 0 ≤ a → a ≤ b → b < (s.val.length : Int) →
            IsLargeMaximalRun s a b →
            ∃ j : Nat, j < r.val.length ∧ PairAt r j a b) := by
    sorry

  /-- Whenever the function returns successfully with value r, len(r) equals the number of maximal constant runs of s whose length is at least 3, where a maximal constant run is a pair (a,b) with 0 <= a <= b < len(s), s[k] = s[a] for all k with a <= k <= b, (a = 0 or s[a-1] != s[a]), and (b + 1 = len(s) or s[b+1] != s[b]).
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_10 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        r.val.length = (allLargeRuns s).length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          r.val.length = (allLargeRuns s).length) := by
    sorry

  /-- Whenever the function returns successfully with value r, len(r) = 0 if and only if there is no index i with 0 <= i and i + 2 < len(s) and s[i] = s[i+1] = s[i+2]. Equivalently, the output is empty exactly when s contains no three equal consecutive bytes.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_11 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        (r.val.length = 0 ↔ ¬ ∃ i : Int, TripleStart s i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          (r.val.length = 0 ↔ ¬ ∃ i : Int, TripleStart s i)) := by
    sorry

  /-- The function returns successfully with value r. If len(s) >= 3 then len(r) = 1, len(r[0]) = 2, r[0][0] = 0, and r[0][1] = len(s) - 1. If len(s) < 3 then len(r) = 0.
    Preconditions: 1 <= len(s) <= 1000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i with 0 <= i < len(s), s[i] = s[0]. -/
  theorem spec_12 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_const : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → byteAt s i = byteAt s 0) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r ∧
        (3 ≤ (s.val.length : Int) →
          r.val.length = 1 ∧ PairAt r 0 0 ((s.val.length : Int) - 1)) ∧
        ((s.val.length : Int) < 3 → r.val.length = 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_const : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) → byteAt s i = byteAt s 0), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r ∧
          (3 ≤ (s.val.length : Int) →
            r.val.length = 1 ∧ PairAt r 0 0 ((s.val.length : Int) - 1)) ∧
          ((s.val.length : Int) < 3 → r.val.length = 0)) := by
    sorry

  /-- The function returns successfully with value r and len(r) = 0. In other words, when every adjacent pair of bytes differs, all constant runs have length 1 and no large group is returned.
    Preconditions: 1 <= len(s) <= 1000, for every i with 0 <= i < len(s), 97 <= s[i] <= 122, and for every i with 0 <= i < len(s)-1, s[i] != s[i+1]. -/
  theorem spec_13 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
      (h_diff : ∀ i : Int, 0 ≤ i → i + 1 < (s.val.length : Int) →
        byteAt s i ≠ byteAt s (i + 1)) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r ∧ r.val.length = 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122)
        (h_diff : ∀ i : Int, 0 ≤ i → i + 1 < (s.val.length : Int) →
          byteAt s i ≠ byteAt s (i + 1)), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r ∧ r.val.length = 0) := by
    sorry

  /-- Whenever the function returns successfully with value r and len(r) > 0, writing a = r[0][0] (so r[0] is a two-element interval), a is the smallest integer i such that 0 <= i and i + 2 < len(s) and s[i] = s[i+1] = s[i+2]. That is, the first returned interval starts at the first position where three equal consecutive bytes begin.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_14 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        0 < r.val.length →
        ∃ a b : Int,
          PairAt r 0 a b ∧ TripleStart s a ∧ ∀ i : Int, TripleStart s i → a ≤ i := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          0 < r.val.length →
          ∃ a b : Int,
            PairAt r 0 a b ∧ TripleStart s a ∧ ∀ i : Int, TripleStart s i → a ≤ i) := by
    sorry

  /-- Whenever the function returns successfully with value r and len(r) > 0, writing b = r[len(r)-1][1] (so the last entry is a two-element interval), b is the largest integer i such that 2 <= i < len(s) and s[i-2] = s[i-1] = s[i]. That is, the last returned interval ends at the last position where three equal consecutive bytes end.
    Preconditions: 1 <= len(s) <= 1000 and for every i with 0 <= i < len(s), 97 <= s[i] <= 122. -/
  theorem spec_15 (s : Slice U8)
      (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
      (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
        97 ≤ byteAt s i ∧ byteAt s i ≤ 122) :
      ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
        Aegis.LargeGroupPositions.large_group_positions s = ok r →
        0 < r.val.length →
        ∃ a b : Int,
          PairAt r (r.val.length - 1) a b ∧ TripleEnd s b ∧
            ∀ i : Int, TripleEnd s i → i ≤ b := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Slice U8)
        (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 1000)
        (h_bytes : ∀ i : Int, 0 ≤ i → i < (s.val.length : Int) →
          97 ≤ byteAt s i ∧ byteAt s i ≤ 122), ∀ r : alloc.vec.Vec (alloc.vec.Vec I64),
          Aegis.LargeGroupPositions.large_group_positions s = ok r →
          0 < r.val.length →
          ∃ a b : Int,
            PairAt r (r.val.length - 1) a b ∧ TripleEnd s b ∧
              ∀ i : Int, TripleEnd s i → i ≤ b) := by
    sorry

  end AegisSpec.LargeGroupPositions
