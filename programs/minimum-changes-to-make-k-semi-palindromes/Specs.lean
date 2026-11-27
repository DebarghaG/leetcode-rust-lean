import Aegis.MinimumChanges.Code.Funs

/-!
# Specifications of `Aegis.MinimumChanges.minimum_changes`

LeetCode problem `minimum-changes-to-make-k-semi-palindromes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumChanges

  def IsLowerByte (b : Aeneas.Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def AllLower (s : Aeneas.Std.Slice Aeneas.Std.U8) : Prop := ∀ b, b ∈ s.val → IsLowerByte b

  def contents (s : Aeneas.Std.Slice Aeneas.Std.U8) : List ℕ := s.val.map (fun b => b.val)

  def nparts (k : Aeneas.Std.I64) : ℕ := k.val.toNat

  def infCost : ℕ := 1000000000

  def groupLen (m d j : ℕ) : ℕ := (m - j + (d - 1)) / d

  def residueChanges (v : List ℕ) (d j : ℕ) : ℕ :=
    ((Finset.range (groupLen v.length d j / 2)).filter
      (fun t => v.getD (j + t * d) 0 ≠
        v.getD (j + (groupLen v.length d j - 1 - t) * d) 0)).card

  def changesFor (v : List ℕ) (d : ℕ) : ℕ := ∑ j ∈ Finset.range d, residueChanges v d j

  def properDivisors (m : ℕ) : List ℕ := (List.range m).filter (fun d => 1 ≤ d ∧ d ∣ m)

  def cost (v : List ℕ) : ℕ :=
    (properDivisors v.length).foldr (fun d acc => min (changesFor v d) acc) infCost

  def SemiPalindromic (v : List ℕ) : Prop :=
    ∃ d, 1 ≤ d ∧ d < v.length ∧ d ∣ v.length ∧
      ∀ j, j < d → ∀ t, t < groupLen v.length d j / 2 →
        v.getD (j + t * d) 0 = v.getD (j + (groupLen v.length d j - 1 - t) * d) 0

  def diff2 (a b : ℕ) : ℕ := if a = b then 0 else 1

  def diff3 (a c : ℕ) : ℕ := if a = c then 0 else 1

  def IsPartition (n k : ℕ) (a : ℕ → ℕ) : Prop :=
    a 0 = 0 ∧ a k = n ∧ ∀ i, i < k → a i + 2 ≤ a (i + 1)

  def part (v : List ℕ) (a : ℕ → ℕ) (i : ℕ) : List ℕ :=
    (v.drop (a i)).take (a (i + 1) - a i)

  def partitionCost (v : List ℕ) (k : ℕ) (a : ℕ → ℕ) : ℕ :=
    ∑ i ∈ Finset.range k, cost (part v a i)

  def tripleCost (v : List ℕ) (k p : ℕ) : ℕ :=
    (∑ j ∈ Finset.range p, diff2 (v.getD (2 * j) 0) (v.getD (2 * j + 1) 0))
      + diff3 (v.getD (2 * p) 0) (v.getD (2 * p + 2) 0)
      + ∑ j ∈ Finset.Icc (p + 1) (k - 1), diff2 (v.getD (2 * j + 1) 0) (v.getD (2 * j + 2) 0)

  def reverseSlice (s : Aeneas.Std.Slice Aeneas.Std.U8) : Aeneas.Std.Slice Aeneas.Std.U8 where
    leng := s.val.reverse.length
    list := Aeneas.Data.ListN.ListN.fromList s.val.reverse
    bound := by
      have h : s.val.reverse.length = s.leng := by
        simp [Aeneas.Std.Slice.val, Aeneas.Data.ListN.ListN_length]
      rw [h]; exact s.bound

  theorem contents_reverseSlice (s : Aeneas.Std.Slice Aeneas.Std.U8) :
      contents (reverseSlice s) = (contents s).reverse := by
    have h : (Aeneas.Data.ListN.ListN.fromList s.list.toList.reverse).toList
        = s.list.toList.reverse :=
      Aeneas.Data.ListN.ListN.from_to_inverse
    simp [contents, reverseSlice, Aeneas.Std.Slice.val, h, List.map_reverse]

  def DiffersAtMostOne (v w : List ℕ) : Prop := ∃ i₀, ∀ i, i ≠ i₀ → v.getD i 0 = w.getD i 0

  /-- The function returns a result r and r is the minimum over all k-partitions 0=a0<a1<...<ak=n with a_i-a_{i-1}≥2 for i=1..k of Σ_{i=1}^k cost(s[a_{i-1}..a_i]). Here, for a byte string v of length m≥2, cost(v)=min_{d|m,1≤d<m} ch(v,d), where for such d and each 0≤j<d, L_j=#{t≥0 : j+t d<m}, and ch(v,d) is the number of pairs (j,t) with 0≤j<d, 0≤t<floor(L_j/2), and v[j+t d]≠v[j+(L_j-1-t)d]. All indices are 0-based and s[a..b] is the half-open substring s[a],s[a+1],...,s[b-1].
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_1 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        (∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
          partitionCost (contents s) (nparts k) a = r.val) ∧
        (∀ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a →
          r.val ≤ partitionCost (contents s) (nparts k) a) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          (∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
            partitionCost (contents s) (nparts k) a = r.val) ∧
          (∀ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a →
            r.val ≤ partitionCost (contents s) (nparts k) a)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, overflow, or produce a failure value.
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_2 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r) := by
    sorry

  /-- The function returns a result r and 0 ≤ r ≤ floor(n/2), where n=len(s).
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_3 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          0 ≤ r.val ∧ r.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) := by
    sorry

  /-- The function returns a result r and there exists a k-partition 0=a0<a1<...<ak=n of s with a_i-a_{i-1}≥2 for all i=1..k such that Σ_{i=1}^k cost(s[a_{i-1}..a_i]) = r, where cost(v) is the minimum number of single-letter changes needed to make v semi-palindromic (v is semi-palindromic if for some divisor d with 1≤d<len(v), in each residue class modulo d the characters of v read in increasing index order form a palindrome).
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_4 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        ∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
          partitionCost (contents s) (nparts k) a = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          ∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
            partitionCost (contents s) (nparts k) a = r.val) := by
    sorry

  /-- The function returns a result r and for every k-partition 0=a0<a1<...<ak=n of s with a_i-a_{i-1}≥2 for all i=1..k, one has Σ_{i=1}^k cost(s[a_{i-1}..a_i]) ≥ r, where cost(v) is the minimum number of single-letter changes needed to make v semi-palindromic (v is semi-palindromic if for some divisor d with 1≤d<len(v), in each residue class modulo d the characters of v read in increasing index order form a palindrome).
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_5 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        ∀ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a →
          r.val ≤ partitionCost (contents s) (nparts k) a := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          ∀ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a →
            r.val ≤ partitionCost (contents s) (nparts k) a) := by
    sorry

  /-- The function returns a result r and r=0 if and only if there exists a k-partition 0=a0<a1<...<ak=n of s with a_i-a_{i-1}≥2 for all i=1..k such that every part s[a_{i-1}..a_i] is already semi-palindromic, where semi-palindromic means that for some divisor d with 1≤d<len(part), in each residue class modulo d the characters of the part read in increasing index order form a palindrome.
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_6 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        (r.val = 0 ↔ ∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
          ∀ i, i < nparts k → SemiPalindromic (part (contents s) a i)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          (r.val = 0 ↔ ∃ a : ℕ → ℕ, IsPartition s.val.length (nparts k) a ∧
            ∀ i, i < nparts k → SemiPalindromic (part (contents s) a i))) := by
    sorry

  /-- The function returns a result r and r = min_{d|n,1≤d<n} ch(s,d), where for each such d and each 0≤j<d, L_j=#{t≥0:j+t d<n}, and ch(s,d) is the number of pairs (j,t) with 0≤j<d, 0≤t<floor(L_j/2), and s[j+t d]≠s[j+(L_j-1-t)d].
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; k=1. -/
  theorem spec_7 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk : k.val = 1) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧ r.val = cost (contents s) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk : k.val = 1), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧ r.val = cost (contents s)) := by
    sorry

  /-- The function returns a result r and r = #{i : 0≤i<k and s[2i]≠s[2i+1]}.
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; n is even; k=n/2. -/
  theorem spec_8 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (heven : 2 ∣ s.val.length) (hk : nparts k = s.val.length / 2) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        r.val = ((Finset.range (nparts k)).filter
          (fun i => (contents s).getD (2 * i) 0 ≠ (contents s).getD (2 * i + 1) 0)).card := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (heven : 2 ∣ s.val.length) (hk : nparts k = s.val.length / 2), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          r.val = ((Finset.range (nparts k)).filter
            (fun i => (contents s).getD (2 * i) 0 ≠ (contents s).getD (2 * i + 1) 0)).card) := by
    sorry

  /-- If s[i]=s[0] for every 0≤i<n, then the function returns a result r and r=0.
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_9 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
      (hconst : ∀ i, i < (contents s).length → (contents s).getD i 0 = (contents s).getD 0 0) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
        (hconst : ∀ i, i < (contents s).length → (contents s).getD i 0 = (contents s).getD 0 0), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧ r.val = 0) := by
    sorry

  /-- The function returns a result r on (s,k) and the function returns the same result r on (t,k), where t is the byte string of length n with t[i]=s[n-1-i] for 0≤i<n.
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_10 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        Aegis.MinimumChanges.minimum_changes (reverseSlice s) k = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          Aegis.MinimumChanges.minimum_changes (reverseSlice s) k = ok r) := by
    sorry

  /-- Let f be any bijection from the set of lowercase ASCII bytes {97,...,122} to itself, and let t be the byte string with t[i]=f(s[i]) for all i. Then the function returns a result r on (s,k) and returns the same result r on (t,k).
    Preconditions: Let n = len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_11 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64) (f : ℕ → ℕ)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
      (hf_image : ∀ x, x ∈ Finset.Icc 97 122 → f x ∈ Finset.Icc 97 122)
      (hf_bij : ∀ y, y ∈ Finset.Icc 97 122 → ∃! x, x ∈ Finset.Icc 97 122 ∧ f x = y) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        ∃ t : Aeneas.Std.Slice Aeneas.Std.U8, contents t = (contents s).map f ∧
          Aegis.MinimumChanges.minimum_changes t k = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64) (f : ℕ → ℕ)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
        (hf_image : ∀ x, x ∈ Finset.Icc 97 122 → f x ∈ Finset.Icc 97 122)
        (hf_bij : ∀ y, y ∈ Finset.Icc 97 122 → ∃! x, x ∈ Finset.Icc 97 122 ∧ f x = y), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          ∃ t : Aeneas.Std.Slice Aeneas.Std.U8, contents t = (contents s).map f ∧
            Aegis.MinimumChanges.minimum_changes t k = ok r) := by
    sorry

  /-- Whenever the function returns result r on (s,k) and result r' on (t,k), |r-r'|≤1.
    Preconditions: Let n=len(s). s and t are byte strings of length n, all bytes in 97..122, 2≤n≤200, and 1≤k≤n/2 using integer division. The strings differ in at most one position: the set {i : s[i]≠t[i]} has size at most 1. -/
  theorem spec_12 (s t : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters_s : AllLower s) (hletters_t : AllLower t)
      (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hlen : t.val.length = s.val.length)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
      (hclose : DiffersAtMostOne (contents s) (contents t)) :
      ∀ r r', Aegis.MinimumChanges.minimum_changes s k = ok r →
        Aegis.MinimumChanges.minimum_changes t k = ok r' → |r.val - r'.val| ≤ 1 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters_s : AllLower s) (hletters_t : AllLower t)
        (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hlen : t.val.length = s.val.length)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ))
        (hclose : DiffersAtMostOne (contents s) (contents t)), ∀ r r', Aegis.MinimumChanges.minimum_changes s k = ok r →
          Aegis.MinimumChanges.minimum_changes t k = ok r' → |r.val - r'.val| ≤ 1) := by
    sorry

  /-- The function returns a result r and r = min_{0≤p<k} C_p, where C_p = Σ_{j=0}^{p-1} diff2(s[2j],s[2j+1]) + diff3(s[2p],s[2p+2]) + Σ_{j=p+1}^{k-1} diff2(s[2j+1],s[2j+2]), with diff2(a,b)=0 if a=b and 1 otherwise, and diff3(a,c)=0 if a=c and 1 otherwise.
    Preconditions: Let n=len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); n is odd; 2≤n≤200; k=(n-1)/2 using integer division. -/
  theorem spec_13 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hodd : s.val.length % 2 = 1) (hk : nparts k = (s.val.length - 1) / 2) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        (∀ p, p < nparts k → r.val ≤ tripleCost (contents s) (nparts k) p) ∧
        (∃ p, p < nparts k ∧ tripleCost (contents s) (nparts k) p = r.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hodd : s.val.length % 2 = 1) (hk : nparts k = (s.val.length - 1) / 2), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          (∀ p, p < nparts k → r.val ≤ tripleCost (contents s) (nparts k) p) ∧
          (∃ p, p < nparts k ∧ tripleCost (contents s) (nparts k) p = r.val)) := by
    sorry

  /-- The function returns a result r and r ≤ (Σ_{j=0}^{k-2} diff2(s[2j],s[2j+1])) + cost(s[2(k-1)..n]), where diff2(a,b)=0 if a=b and 1 otherwise, and cost(v) is the minimum number of single-letter changes needed to make v semi-palindromic; the last part has length n-2(k-1) and is at least 2 because k≤n/2.
    Preconditions: Let n=len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; 1 ≤ k ≤ n/2 using integer division; k is interpreted as the natural number equal to its i64 value. -/
  theorem spec_14 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        r.val ≤ ((∑ j ∈ Finset.range (nparts k - 1),
            diff2 ((contents s).getD (2 * j) 0) ((contents s).getD (2 * j + 1) 0))
          + cost (((contents s).drop (2 * (nparts k - 1))).take
              (s.val.length - 2 * (nparts k - 1)))) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ ((s.val.length / 2 : ℕ) : ℤ)), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          r.val ≤ ((∑ j ∈ Finset.range (nparts k - 1),
              diff2 ((contents s).getD (2 * j) 0) ((contents s).getD (2 * j + 1) 0))
            + cost (((contents s).drop (2 * (nparts k - 1))).take
                (s.val.length - 2 * (nparts k - 1))))) := by
    sorry

  /-- The function returns a result r and r = min_{2≤p≤n-2} (cost(s[0..p]) + cost(s[p..n])), where cost(v) is the minimum number of single-letter changes needed to make v semi-palindromic (v is semi-palindromic if for some divisor d with 1≤d<len(v), in each residue class modulo d the characters of v read in increasing index order form a palindrome).
    Preconditions: Let n=len(s). s is a slice of bytes; every byte is a lowercase English ASCII letter (97 ≤ s[i] ≤ 122 for 0 ≤ i < n); 2 ≤ n ≤ 200; k=2 (so n ≥ 4). -/
  theorem spec_15 (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
      (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
      (hn4 : 4 ≤ s.val.length) (hk : k.val = 2) :
      ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
        (∀ p, 2 ≤ p → p ≤ s.val.length - 2 →
          r.val ≤ cost ((contents s).take p) + cost ((contents s).drop p)) ∧
        (∃ p, 2 ≤ p ∧ p ≤ s.val.length - 2 ∧
          cost ((contents s).take p) + cost ((contents s).drop p) = r.val) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s : Aeneas.Std.Slice Aeneas.Std.U8) (k : Aeneas.Std.I64)
        (hletters : AllLower s) (hn2 : 2 ≤ s.val.length) (hn200 : s.val.length ≤ 200)
        (hn4 : 4 ≤ s.val.length) (hk : k.val = 2), ∃ r, Aegis.MinimumChanges.minimum_changes s k = ok r ∧
          (∀ p, 2 ≤ p → p ≤ s.val.length - 2 →
            r.val ≤ cost ((contents s).take p) + cost ((contents s).drop p)) ∧
          (∃ p, 2 ≤ p ∧ p ≤ s.val.length - 2 ∧
            cost ((contents s).take p) + cost ((contents s).drop p) = r.val)) := by
    sorry

  end AegisSpec.MinimumChanges
