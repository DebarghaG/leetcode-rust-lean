import Aegis.GetLengthOfOptimalCompression.Code.Funs

/-!
# Specifications of `Aegis.GetLengthOfOptimalCompression.get_length_of_optimal_compression`

LeetCode problem `string-compression-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.GetLengthOfOptimalCompression

  namespace AegisSpec.GetLengthOfOptimalCompression

  def digitCount (m : ℕ) : ℕ :=
    if m = 0 then 0 else (Nat.repr m).length

  def runCost (m : ℕ) : ℕ :=
    if m = 1 then 1 else 1 + digitCount m

  def uniformCost (m : ℕ) : ℕ :=
    if m = 0 then 0 else runCost m

  def clScan : List U8 → ℕ → ℕ → ℕ → ℕ
    | [], acc, _, runLen => acc + (if runLen = 0 then 0 else runCost runLen)
    | x :: xs, acc, cur, runLen =>
        if runLen = 0 then clScan xs acc x.val 1
        else if cur = x.val then clScan xs acc cur (runLen + 1)
        else clScan xs (acc + runCost runLen) x.val 1

  def cl (t : List U8) : ℕ :=
    clScan t 0 0 0

  def StrictIncreasing : List ℕ → Prop
    | [] => True
    | [_] => True
    | x :: y :: rest => x < y ∧ StrictIncreasing (y :: rest)

  def IsSubsequenceOf (t s : List U8) : Prop :=
    ∃ idx : List (Fin s.length),
      idx.length = t.length ∧
        StrictIncreasing (idx.map (fun i => i.val)) ∧
        t = idx.map (fun i => s.get i)

  def deletedAtMost (d : ℕ) (t s : List U8) : Prop :=
    IsSubsequenceOf t s ∧ s.length ≤ t.length + d

  def deletedExactly (d : ℕ) (t s : List U8) : Prop :=
    IsSubsequenceOf t s ∧ t.length = s.length - d

  def costSetAtMost (s : List U8) (d : ℕ) : Set ℕ :=
    {c | ∃ t, deletedAtMost d t s ∧ cl t = c}

  def costSetExactly (s : List U8) (d : ℕ) : Set ℕ :=
    {c | ∃ t, deletedExactly d t s ∧ cl t = c}

  noncomputable def minCostAtMost (s : List U8) (d : ℕ) : ℕ :=
    sInf (costSetAtMost s d)

  noncomputable def minCostExactly (s : List U8) (d : ℕ) : ℕ :=
    sInf (costSetExactly s d)

  /-- Let CL(t) be the run-length encoded length of a byte sequence t: CL(empty) = 0; otherwise split t into maximal contiguous runs of equal bytes, and for a run of length m contribute 1 if m = 1, and 1 + D(m) if m ≥ 2, where D(m) is the number of decimal digits of m; CL(t) is the sum over the runs. The function returns a result r and r = min { CL(t) | t is a subsequence of s obtained by deleting at most k bytes from s }. Equivalently, the minimum is over all t for which there are indices i_0 < i_1 < ... < i_{len(t)-1} in [0, len(s)) with t[j] = s[i_j] for all j, and len(t) ≥ len(s) - k; the empty sequence is allowed exactly when k = len(s).
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_1 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          r.val = (minCostAtMost s.val k.val.toNat : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            r.val = (minCostAtMost s.val k.val.toNat : ℤ)) := by
    sorry

  /-- For every s and k satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or access out of bounds.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_2 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64, get_length_of_optimal_compression s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64, get_length_of_optimal_compression s k = ok r) := by
    sorry

  /-- The function returns a result r and r ≤ len(s) - k.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_3 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          r.val ≤ (s.val.length : ℤ) - k.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            r.val ≤ (s.val.length : ℤ) - k.val) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if k = len(s).
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_4 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          (r.val = 0 ↔ k.val = (s.val.length : ℤ)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            (r.val = 0 ↔ k.val = (s.val.length : ℤ))) := by
    sorry

  /-- The function returns a result r and r = CL(s), where CL(s) is computed from the maximal contiguous runs of equal bytes in s: a run of length 1 contributes 1, and a run of length m ≥ 2 contributes 1 + D(m), where D(m) is the number of decimal digits of m.
    Preconditions: 1 ≤ len(s) ≤ 100; k = 0; for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_5 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk : k.val = 0)
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧ r.val = (cl s.val : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk : k.val = 0)
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧ r.val = (cl s.val : ℤ)) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: 1 ≤ len(s) ≤ 100; k = len(s) - 1; for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_6 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk : k.val = (s.val.length : ℤ) - 1)
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk : k.val = (s.val.length : ℤ) - 1)
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r ≤ CL(s), where CL(s) is the run-length encoded length of s: split s into maximal contiguous runs of equal bytes; a run of length 1 contributes 1, and a run of length m ≥ 2 contributes 1 + D(m), where D(m) is the number of decimal digits of m.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_7 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧ r.val ≤ (cl s.val : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧ r.val ≤ (cl s.val : ℤ)) := by
    sorry

  /-- Let r be the result of the function on s and k, and let r' be the result on s and k'. Both calls return results and r ≥ r'.
    Preconditions: 1 ≤ len(s) ≤ 100; for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122); 0 ≤ k ≤ k' ≤ len(s). -/
  theorem spec_8 (s : Slice U8) (k k' : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
      (hk0 : 0 ≤ k.val)
      (hkk' : k.val ≤ k'.val) (hk'n : k'.val ≤ (s.val.length : ℤ)) :
      ∃ r r' : I64,
        get_length_of_optimal_compression s k = ok r ∧
          get_length_of_optimal_compression s k' = ok r' ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Slice U8) (k k' : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
        (hk0 : 0 ≤ k.val)
        (hkk' : k.val ≤ k'.val) (hk'n : k'.val ≤ (s.val.length : ℤ)), ∃ r r' : I64,
          get_length_of_optimal_compression s k = ok r ∧
            get_length_of_optimal_compression s k' = ok r' ∧ r'.val ≤ r.val) := by
    sorry

  /-- Let CL(t) be the run-length encoded length of a byte sequence t as defined by maximal equal runs (run length m contributes 1 if m = 1 and 1 + D(m) if m ≥ 2, where D(m) is the number of decimal digits of m, and CL(empty) = 0). The function returns a result r and r = min { CL(t) | t is a subsequence of s with len(t) = len(s) - k }.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_9 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          r.val = (minCostExactly s.val k.val.toNat : ℤ) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            r.val = (minCostExactly s.val k.val.toNat : ℤ)) := by
    sorry

  /-- Let m = len(s) - k. The function returns a result r and: r = 0 if m = 0; r = 1 if m = 1; and r = 1 + D(m) if m ≥ 2, where D(m) is the number of decimal digits of m.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122); there is a byte c such that s[i] = c for every i with 0 ≤ i < len(s). -/
  theorem spec_10 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
      (hconst : ∃ c : U8, ∀ i : Fin s.val.length, s.val.get i = c) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          r.val = (uniformCost (s.val.length - k.val.toNat) : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
        (hconst : ∃ c : U8, ∀ i : Fin s.val.length, s.val.get i = c), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            r.val = (uniformCost (s.val.length - k.val.toNat) : ℤ)) := by
    sorry

  /-- Let r be the result of the function on s and k, and let r' be the result on s' and k. Both calls return results and r = r'.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122); f is a bijection of the set of lowercase English letters (ASCII 97 through 122) onto itself; s' is defined by s'[i] = f(s[i]) for every i with 0 ≤ i < len(s). -/
  theorem spec_11 (s s' : Slice U8) (k : I64) (f : U8 → U8)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
      (hf_maps : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 →
        97 ≤ (f c).val ∧ (f c).val ≤ 122)
      (hf_inj : ∀ c d : U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ d.val → d.val ≤ 122 →
        f c = f d → c = d)
      (hs' : s'.val = s.val.map f) :
      ∃ r r' : I64,
        get_length_of_optimal_compression s k = ok r ∧
          get_length_of_optimal_compression s' k = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s s' : Slice U8) (k : I64) (f : U8 → U8)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
        (hf_maps : ∀ c : U8, 97 ≤ c.val → c.val ≤ 122 →
          97 ≤ (f c).val ∧ (f c).val ≤ 122)
        (hf_inj : ∀ c d : U8, 97 ≤ c.val → c.val ≤ 122 → 97 ≤ d.val → d.val ≤ 122 →
          f c = f d → c = d)
        (hs' : s'.val = s.val.map f), ∃ r r' : I64,
          get_length_of_optimal_compression s k = ok r ∧
            get_length_of_optimal_compression s' k = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let CL(t) be the run-length encoded length of a byte sequence t as defined by maximal equal runs (run length m contributes 1 if m = 1 and 1 + D(m) if m ≥ 2, where D(m) is the number of decimal digits of m, and CL(empty) = 0). The function returns a result r and there exists a byte sequence t such that t is a subsequence of s obtained by deleting at most k bytes (there are indices i_0 < i_1 < ... < i_{len(t)-1} with t[j] = s[i_j] and len(t) ≥ len(s) - k) and CL(t) = r.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_12 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          ∃ t : List U8, deletedAtMost k.val.toNat t s.val ∧ r.val = (cl t : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            ∃ t : List U8, deletedAtMost k.val.toNat t s.val ∧ r.val = (cl t : ℤ)) := by
    sorry

  /-- Let CL(t) be the run-length encoded length of a byte sequence t as defined by maximal equal runs (run length m contributes 1 if m = 1 and 1 + D(m) if m ≥ 2, where D(m) is the number of decimal digits of m, and CL(empty) = 0). The function returns a result r and for every byte sequence t that is a subsequence of s obtained by deleting at most k bytes (there are indices i_0 < i_1 < ... < i_{len(t)-1} with t[j] = s[i_j] and len(t) ≥ len(s) - k), we have CL(t) ≥ r.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_13 (s : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122) :
      ∃ r : I64,
        get_length_of_optimal_compression s k = ok r ∧
          ∀ t : List U8, deletedAtMost k.val.toNat t s.val → r.val ≤ (cl t : ℤ) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122), ∃ r : I64,
          get_length_of_optimal_compression s k = ok r ∧
            ∀ t : List U8, deletedAtMost k.val.toNat t s.val → r.val ≤ (cl t : ℤ)) := by
    sorry

  /-- Let rev(s) be the byte sequence of length len(s) with rev(s)[i] = s[len(s)-1-i]. Let r be the result of the function on s and k, and let r' be the result on rev(s) and k. Both calls return results and r = r'.
    Preconditions: 1 ≤ len(s) ≤ 100; 0 ≤ k ≤ len(s); for every i with 0 ≤ i < len(s), s[i] is the ASCII code of a lowercase English letter (97 ≤ s[i] ≤ 122). -/
  theorem spec_14 (s s' : Slice U8) (k : I64)
      (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
      (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
      (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
      (hs' : s'.val = s.val.reverse) :
      ∃ r r' : I64,
        get_length_of_optimal_compression s k = ok r ∧
          get_length_of_optimal_compression s' k = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s s' : Slice U8) (k : I64)
        (hlen1 : 1 ≤ s.val.length) (hlen100 : s.val.length ≤ 100)
        (hk0 : 0 ≤ k.val) (hkn : k.val ≤ (s.val.length : ℤ))
        (hletters : ∀ i : Fin s.val.length, 97 ≤ (s.val.get i).val ∧ (s.val.get i).val ≤ 122)
        (hs' : s'.val = s.val.reverse), ∃ r r' : I64,
          get_length_of_optimal_compression s k = ok r ∧
            get_length_of_optimal_compression s' k = ok r' ∧ r.val = r'.val) := by
    sorry

  end AegisSpec.GetLengthOfOptimalCompression
