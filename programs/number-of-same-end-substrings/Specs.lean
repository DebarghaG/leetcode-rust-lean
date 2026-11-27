import Aegis.SameEndSubstringCount.Code.Funs

/-!
# Specifications of `Aegis.SameEndSubstringCount.same_end_substring_count`

LeetCode problem `number-of-same-end-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SameEndSubstringCount

  def byteAt (s : Slice U8) (k : Nat) : Nat :=
    match s.val[k]? with
    | some b => b.val
    | none => 0

  def occ (s : Slice U8) (l r c : Nat) : Nat :=
    ((Finset.Icc l r).filter (fun k => byteAt s k = c)).card

  def tri (L : Nat) : Nat := L * (L + 1) / 2

  def sameEndCount (s : Slice U8) (l r : Nat) : Nat :=
    Finset.sum (Finset.Icc l r)
      (fun b => ((Finset.Icc l r).filter (fun a => a ≤ b ∧ byteAt s a = byteAt s b)).card)

  def sameEndCountStrict (s : Slice U8) (l r : Nat) : Nat :=
    Finset.sum (Finset.Icc l r)
      (fun b => ((Finset.Icc l r).filter (fun a => a < b ∧ byteAt s a = byteAt s b)).card)

  def charAgg (s : Slice U8) (l r : Nat) : Nat :=
    Finset.sum (Finset.range 256) (fun c => tri (occ s l r c))

  def qFst (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
    match queries.val[i]? with
    | some q =>
      match q.val[0]? with
      | some x => x.val
      | none => 0
    | none => 0

  def qSnd (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : Int :=
    match queries.val[i]? with
    | some q =>
      match q.val[1]? with
      | some x => x.val
      | none => 0
    | none => 0

  def qLo (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat := (qFst queries i).toNat

  def qHi (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat := (qSnd queries i).toNat

  def qLen (queries : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat := qHi queries i - qLo queries i + 1

  def ansAt (ans : alloc.vec.Vec I64) (i : Nat) : Int := (ans.val.getD i default).val

  def Precond (s : Slice U8) (queries : Slice (alloc.vec.Vec I64)) : Prop :=
    2 ≤ s.val.length ∧ s.val.length ≤ 30000 ∧
    (∀ b ∈ s.val, 97 ≤ b.val ∧ b.val ≤ 122) ∧
    1 ≤ queries.val.length ∧ queries.val.length ≤ 30000 ∧
    (∀ (i : Nat) (qd : alloc.vec.Vec I64), queries.val[i]? = some qd → qd.val.length = 2) ∧
    (∀ i, i < queries.val.length →
      0 ≤ qFst queries i ∧ qFst queries i ≤ qSnd queries i ∧ qSnd queries i < (s.val.length : Int))

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, let l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers. Then ans[i] is the number of pairs of integers (a,b) such that l_i <= a <= b <= r_i and s[a] = s[b]. Equivalently, ans[i] is the number of non-empty contiguous substrings of s[l_i..r_i] whose first and last bytes are equal.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_1 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length →
        ansAt ans i = (sameEndCount s (qLo queries i) (qHi queries i) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length →
          ansAt ans i = (sameEndCount s (qLo queries i) (qHi queries i) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, len(ans) = q = len(queries).
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_2 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ans.val.length = queries.val.length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ans.val.length = queries.val.length) := by
    sorry

  /-- same_end_substring_count(s, queries) returns a result (it does not fail) for every s and queries satisfying the preconditions.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_3 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) :
      ∃ ans : alloc.vec.Vec I64,
        Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries), ∃ ans : alloc.vec.Vec I64,
          Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, ans[i] >= r_i - l_i + 1, where l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_4 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length → (qLen queries i : Int) ≤ ansAt ans i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length → (qLen queries i : Int) ≤ ansAt ans i) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, ans[i] <= L_i*(L_i+1)/2, where L_i = r_i - l_i + 1.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_5 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length → ansAt ans i ≤ (tri (qLen queries i) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length → ansAt ans i ≤ (tri (qLen queries i) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, if s[k] = s[l_i] for every k with l_i <= k <= r_i, then ans[i] = L_i*(L_i+1)/2, where L_i = r_i - l_i + 1.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_6 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length →
        (∀ k, qLo queries i ≤ k → k ≤ qHi queries i → byteAt s k = byteAt s (qLo queries i)) →
        ansAt ans i = (tri (qLen queries i) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length →
          (∀ k, qLo queries i ≤ k → k ≤ qHi queries i → byteAt s k = byteAt s (qLo queries i)) →
          ansAt ans i = (tri (qLen queries i) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, if s[a] != s[b] for every pair l_i <= a < b <= r_i, then ans[i] = L_i, where L_i = r_i - l_i + 1.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_7 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length →
        (∀ a b, qLo queries i ≤ a → a < b → b ≤ qHi queries i → byteAt s a ≠ byteAt s b) →
        ansAt ans i = (qLen queries i : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length →
          (∀ a b, qLo queries i ≤ a → a < b → b ≤ qHi queries i → byteAt s a ≠ byteAt s b) →
          ansAt ans i = (qLen queries i : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, define f_i(c) = #{k | l_i <= k <= r_i and s[k] = c} for each byte c in 0..255. Then ans[i] = sum_{c=0}^{255} f_i(c)*(f_i(c)+1)/2.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_8 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length →
        ansAt ans i = (charAgg s (qLo queries i) (qHi queries i) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length →
          ansAt ans i = (charAgg s (qLo queries i) (qHi queries i) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, ans[i] = L_i + P_i, where L_i = r_i - l_i + 1 and P_i = #{ (a,b) | l_i <= a < b <= r_i and s[a] = s[b] }.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_9 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length →
        ansAt ans i =
          (qLen queries i : Int) +
            (sameEndCountStrict s (qLo queries i) (qHi queries i) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length →
          ansAt ans i =
            (qLen queries i : Int) +
              (sameEndCountStrict s (qLo queries i) (qHi queries i) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for all i,j with 0 <= i,j < q, if l_i <= l_j and r_j <= r_i, then ans[i] >= ans[j].
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_10 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i j, i < queries.val.length → j < queries.val.length →
        qFst queries i ≤ qFst queries j → qSnd queries j ≤ qSnd queries i →
        ansAt ans j ≤ ansAt ans i := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i j, i < queries.val.length → j < queries.val.length →
          qFst queries i ≤ qFst queries j → qSnd queries j ≤ qSnd queries i →
          ansAt ans j ≤ ansAt ans i) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with l_i < r_i, let C(a,b) for a <= b denote the number of pairs (x,y) with a <= x <= y <= b and s[x] = s[y]. Then ans[i] = C(l_i, r_i-1) + #{k | l_i <= k <= r_i and s[k] = s[r_i]}.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_11 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length → qFst queries i < qSnd queries i →
        ansAt ans i =
          (sameEndCount s (qLo queries i) (qHi queries i - 1) : Int) +
            (occ s (qLo queries i) (qHi queries i) (byteAt s (qHi queries i)) : Int) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length → qFst queries i < qSnd queries i →
          ansAt ans i =
            (sameEndCount s (qLo queries i) (qHi queries i - 1) : Int) +
              (occ s (qLo queries i) (qHi queries i) (byteAt s (qHi queries i)) : Int)) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for all i,j with 0 <= i,j < q, if for every byte c the number of k with l_i <= k <= r_i and s[k] = c equals the number of k with l_j <= k <= r_j and s[k] = c, then ans[i] = ans[j].
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_12 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i j, i < queries.val.length → j < queries.val.length →
        (∀ c, c < 256 → occ s (qLo queries i) (qHi queries i) c
          = occ s (qLo queries j) (qHi queries j) c) →
        ansAt ans i = ansAt ans j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i j, i < queries.val.length → j < queries.val.length →
          (∀ c, c < 256 → occ s (qLo queries i) (qHi queries i) c
            = occ s (qLo queries j) (qHi queries j) c) →
          ansAt ans i = ansAt ans j) := by
    sorry

  /-- Whenever same_end_substring_count(s, queries) returns a result ans, for every i with 0 <= i < q, if l_i < r_i and s[l_i] = s[r_i], then ans[i] >= L_i + 1, where L_i = r_i - l_i + 1.
    Preconditions: Let n = len(s) and q = len(queries). Preconditions: 2 <= n <= 30000; every byte of s is a lowercase English letter (ASCII code between 97 and 122 inclusive); 1 <= q <= 30000; for every i with 0 <= i < q, len(queries[i]) = 2, and if l_i = queries[i][0] and r_i = queries[i][1] as mathematical integers, then 0 <= l_i <= r_i < n. -/
  theorem spec_13 (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
      (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
      (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans) :
      ∀ i, i < queries.val.length → qFst queries i < qSnd queries i →
        byteAt s (qLo queries i) = byteAt s (qHi queries i) →
        (qLen queries i : Int) + 1 ≤ ansAt ans i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8) (queries : Slice (alloc.vec.Vec I64))
        (hpre : Precond s queries) (ans : alloc.vec.Vec I64)
        (hans : Aegis.SameEndSubstringCount.same_end_substring_count s queries = ok ans), ∀ i, i < queries.val.length → qFst queries i < qSnd queries i →
          byteAt s (qLo queries i) = byteAt s (qHi queries i) →
          (qLen queries i : Int) + 1 ≤ ansAt ans i) := by
    sorry

  end AegisSpec.SameEndSubstringCount
