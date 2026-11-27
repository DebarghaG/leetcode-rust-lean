import Aegis.FindAnagrams.Code.Funs

/-!
# Specifications of `Aegis.FindAnagrams.find_anagrams`

LeetCode problem `find-all-anagrams-in-a-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
  open Aegis.FindAnagrams

  set_option autoImplicit false

  namespace AegisSpec.FindAnagrams

  def outVals (r : List Std.I64) : List Int := r.map (fun x => x.val)

  def OccursIn (l : List Int) (i : Int) : Prop :=
    ∃ k : Nat, k < l.length ∧ l[k]? = some i

  def countByte (l : List Std.U8) (c : Std.U8) : Nat :=
    (l.filter (fun b => b.val = c.val)).length

  def IsAnagram (a b : List Std.U8) : Prop :=
    a.length = b.length ∧ ∀ c : Std.U8, countByte a c = countByte b c

  def window (l : List Std.U8) (i m : Nat) : List Std.U8 := (l.drop i).take m

  def PairwiseDistinct (l : List Int) : Prop :=
    ∀ k k' : Nat, k < l.length → k' < l.length → l[k]? = l[k']? → k = k'

  def entry (r : List Std.I64) (j : Nat) : Int := (outVals r).getD j 0

  def i64Min : Int := -((2 : Int) ^ 63)

  def i64Max : Int := (2 : Int) ^ 63

  /-- Whenever find_anagrams(s,p) returns a result r, r is a duplicate-free list whose entries are exactly the valid start indices: for every integer i with -2^63 <= i < 2^63, i occurs in r if and only if 0 <= i and i + len(p) <= len(s) and the contiguous substring of s of length len(p) starting at i, namely s[i], s[i+1], ..., s[i+len(p)-1], is an anagram of p. Here anagram of p means that the substring has length len(p) and for every byte c the number of positions j in the substring with value c equals the number of positions j in p with p[j]=c; duplicate-free means for all k,k' with 0 <= k < len(r) and 0 <= k' < len(r), r[k]=r[k'] implies k=k'; and i occurs in r means there exists k with 0 <= k < len(r) and r[k]=i.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122 (lowercase ASCII letters). -/
  theorem spec_1 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        PairwiseDistinct (outVals r.val) ∧
        ∀ i : Int, i64Min ≤ i → i < i64Max →
          (OccursIn (outVals r.val) i ↔
            0 ≤ i ∧ i + (p.val.length : Int) ≤ (s.val.length : Int) ∧
              IsAnagram (window s.val i.toNat p.val.length) p.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          PairwiseDistinct (outVals r.val) ∧
          ∀ i : Int, i64Min ≤ i → i < i64Max →
            (OccursIn (outVals r.val) i ↔
              0 ≤ i ∧ i + (p.val.length : Int) ≤ (s.val.length : Int) ∧
                IsAnagram (window s.val i.toNat p.val.length) p.val)) := by
    sorry

  /-- For every s and p satisfying the preconditions, find_anagrams(s,p) returns a result (there exists a vector v such that the call evaluates to ok v); it does not fail, overflow, or panic.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_2 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∃ v : alloc.vec.Vec Std.I64, find_anagrams s p = ok v := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∃ v : alloc.vec.Vec Std.I64, find_anagrams s p = ok v) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, for every j with 0 <= j < len(r), if 0 <= r[j] and r[j] + len(p) <= len(s), then the contiguous substring of s of length len(p) starting at r[j] is an anagram of p (same length and same multiset of bytes as p).
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_3 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        ∀ j : Nat, j < r.val.length →
          0 ≤ entry r.val j →
            entry r.val j + (p.val.length : Int) ≤ (s.val.length : Int) →
              IsAnagram (window s.val (entry r.val j).toNat p.val.length) p.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          ∀ j : Nat, j < r.val.length →
            0 ≤ entry r.val j →
              entry r.val j + (p.val.length : Int) ≤ (s.val.length : Int) →
                IsAnagram (window s.val (entry r.val j).toNat p.val.length) p.val) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, every entry r[j] with 0 <= j < len(r) satisfies 0 <= r[j] and r[j] + len(p) <= len(s).
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_4 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        ∀ j : Nat, j < r.val.length →
          0 ≤ entry r.val j ∧
            entry r.val j + (p.val.length : Int) ≤ (s.val.length : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          ∀ j : Nat, j < r.val.length →
            0 ≤ entry r.val j ∧
              entry r.val j + (p.val.length : Int) ≤ (s.val.length : Int)) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, for every integer i with 0 <= i and i + len(p) <= len(s), if the contiguous substring of s of length len(p) starting at i is an anagram of p, then i occurs in r (there exists k with 0 <= k < len(r) and r[k]=i).
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_5 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        ∀ i : Int, 0 ≤ i → i + (p.val.length : Int) ≤ (s.val.length : Int) →
          IsAnagram (window s.val i.toNat p.val.length) p.val →
            OccursIn (outVals r.val) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          ∀ i : Int, 0 ≤ i → i + (p.val.length : Int) ≤ (s.val.length : Int) →
            IsAnagram (window s.val i.toNat p.val.length) p.val →
              OccursIn (outVals r.val) i) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, the entries of r are pairwise distinct: for all k,k' with 0 <= k < len(r) and 0 <= k' < len(r), if r[k]=r[k'] then k=k'.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_6 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        PairwiseDistinct (outVals r.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          PairwiseDistinct (outVals r.val)) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, if len(p) <= len(s) then len(r) <= len(s)-len(p)+1; and if len(p) > len(s) then len(r)=0.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_7 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        (p.val.length ≤ s.val.length →
            r.val.length ≤ s.val.length - p.val.length + 1) ∧
          (s.val.length < p.val.length → r.val.length = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          (p.val.length ≤ s.val.length →
              r.val.length ≤ s.val.length - p.val.length + 1) ∧
            (s.val.length < p.val.length → r.val.length = 0)) := by
    sorry

  /-- For every byte string q such that len(q)=len(p) and for every byte c the number of positions j with q[j]=c equals the number of positions j with p[j]=c, if find_anagrams(s,p) returns r and find_anagrams(s,q) returns r', then for every integer i with -2^63 <= i < 2^63, i occurs in r if and only if i occurs in r'.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_8 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (q : Slice Std.U8)
      (hq_len : q.val.length = p.val.length)
      (hq_counts : ∀ c : Std.U8, countByte q.val c = countByte p.val c) :
      ∀ r r' : alloc.vec.Vec Std.I64,
        find_anagrams s p = ok r → find_anagrams s q = ok r' →
          ∀ i : Int, i64Min ≤ i → i < i64Max →
            (OccursIn (outVals r.val) i ↔ OccursIn (outVals r'.val) i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (q : Slice Std.U8)
        (hq_len : q.val.length = p.val.length)
        (hq_counts : ∀ c : Std.U8, countByte q.val c = countByte p.val c), ∀ r r' : alloc.vec.Vec Std.I64,
          find_anagrams s p = ok r → find_anagrams s q = ok r' →
            ∀ i : Int, i64Min ≤ i → i < i64Max →
              (OccursIn (outVals r.val) i ↔ OccursIn (outVals r'.val) i)) := by
    sorry

  /-- Whenever find_anagrams(s,p) returns r, len(r) > 0 if and only if there exists an integer i with 0 <= i and i + len(p) <= len(s) such that the contiguous substring of s of length len(p) starting at i is an anagram of p.
    Preconditions: 1 <= len(s) <= 30000, 1 <= len(p) <= 30000, all bytes of s and p are in the range 97..122. -/
  theorem spec_9 (s p : Slice Std.U8)
      (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
      (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
      (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
      (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122) :
      ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
        (0 < r.val.length ↔
          ∃ i : Int, 0 ≤ i ∧ i + (p.val.length : Int) ≤ (s.val.length : Int) ∧
            IsAnagram (window s.val i.toNat p.val.length) p.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s p : Slice Std.U8)
        (hs_len : 1 ≤ s.val.length) (hs_len_ub : s.val.length ≤ 30000)
        (hp_len : 1 ≤ p.val.length) (hp_len_ub : p.val.length ≤ 30000)
        (hs_bytes : ∀ c ∈ s.val, 97 ≤ c.val ∧ c.val ≤ 122)
        (hp_bytes : ∀ c ∈ p.val, 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : alloc.vec.Vec Std.I64, find_anagrams s p = ok r →
          (0 < r.val.length ↔
            ∃ i : Int, 0 ≤ i ∧ i + (p.val.length : Int) ≤ (s.val.length : Int) ∧
              IsAnagram (window s.val i.toNat p.val.length) p.val)) := by
    sorry

  end AegisSpec.FindAnagrams
