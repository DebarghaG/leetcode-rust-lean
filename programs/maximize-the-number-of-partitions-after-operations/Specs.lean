import Aegis.MaxPartitionsAfterOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxPartitionsAfterOperations.max_partitions_after_operations`

LeetCode problem `maximize-the-number-of-partitions-after-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Aeneas.Std.Result

open Aegis.MaxPartitionsAfterOperations

namespace AegisSpec.MaxPartitionsAfterOperations

def IsLowerByte (b : Nat) : Prop := 97 ≤ b ∧ b ≤ 122

def bytesOf (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def numDistinctAux : List Nat → List Nat → Nat
  | _, [] => 0
  | seen, x :: xs =>
      if x ∈ seen then numDistinctAux seen xs else 1 + numDistinctAux (x :: seen) xs

def numDistinct (t : List Nat) : Nat := numDistinctAux [] t

def byteAt (t : List Nat) (i : Nat) : Nat := (t[i]?).getD 0

def replaceAt (t : List Nat) (i c : Nat) : List Nat := t.set i c

def hammingDist (t s : List Nat) : Nat := (t.zip s).countP (fun p => p.1 ≠ p.2)

def Admissible (s t : List Nat) : Prop :=
  t.length = s.length ∧ (∀ b ∈ t, IsLowerByte b) ∧ hammingDist t s ≤ 1

def greedyPartsAux (q : Nat) : List Nat → List Nat → Nat
  | _, [] => 0
  | seen, x :: xs =>
      if x ∈ seen then greedyPartsAux q seen xs
      else if seen.length < q then greedyPartsAux q (x :: seen) xs
      else 1 + greedyPartsAux q [x] xs

def greedyParts (q : Nat) (t : List Nat) : Nat :=
  match t with
  | [] => 0
  | x :: xs => 1 + greedyPartsAux q [x] xs

def IsMaxGreedy (s : List Nat) (q : Nat) (r : Int) : Prop :=
  (∃ t, Admissible s t ∧ (greedyParts q t : Int) = r) ∧
    ∀ t, Admissible s t → (greedyParts q t : Int) ≤ r

def numBlocks : List Nat → Nat
  | [] => 0
  | [_] => 1
  | x :: y :: ys => (if x = y then 0 else 1) + numBlocks (y :: ys)

def maxBlockLenAux (prev : Option Nat) (cur best : Nat) : List Nat → Nat
  | [] => max best cur
  | x :: xs =>
      if prev = some x then maxBlockLenAux prev (cur + 1) best xs
      else maxBlockLenAux (some x) 1 (max best cur) xs

def maxBlockLen (t : List Nat) : Nat := maxBlockLenAux none 0 0 t

def kNat (k : Std.I64) : Nat := k.val.toNat

def IsLowerPerm (σ : Nat → Nat) : Prop :=
  (∀ b, IsLowerByte b → IsLowerByte (σ b)) ∧
    (∀ a b, IsLowerByte a → IsLowerByte b → σ a = σ b → a = b) ∧
      ∀ b, IsLowerByte b → ∃ a, IsLowerByte a ∧ σ a = b

/-- The function returns a result r and r = max { G(t,k) : t is a lowercase byte string with len(t)=len(s) and Hamming distance at most 1 from s }; here G(t,q) is the number of partitions produced by repeatedly deleting from t the longest nonempty prefix containing at most q distinct bytes, with G(empty,q)=0.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∃ r, max_partitions_after_operations s k = ok r ∧
      IsMaxGreedy (bytesOf s) (kNat k) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∃ r, max_partitions_after_operations s k = ok r ∧
      IsMaxGreedy (bytesOf s) (kNat k) r.val) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow) for every input satisfying the preconditions.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∃ r, max_partitions_after_operations s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∃ r, max_partitions_after_operations s k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r <= len(s).
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ r, max_partitions_after_operations s k = ok r →
      1 ≤ r.val ∧ r.val ≤ (s.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ r, max_partitions_after_operations s k = ok r →
      1 ≤ r.val ∧ r.val ≤ (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= G(s,k), where G(t,q) is the number of partitions produced by repeatedly deleting from t the longest nonempty prefix containing at most q distinct bytes, with G(empty,q)=0.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ r, max_partitions_after_operations s k = ok r →
      (greedyParts (kNat k) (bytesOf s) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ r, max_partitions_after_operations s k = ok r →
      (greedyParts (kNat k) (bytesOf s) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, R <= r <= R + 2, where R is the number of maximal contiguous blocks of equal bytes in s (equivalently, R = 1 + the number of indices i with 1 <= i < len(s) and s[i] != s[i-1]).
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); k = 1. -/
theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1) :
    ∀ r, max_partitions_after_operations s k = ok r →
      (numBlocks (bytesOf s) : Int) ≤ r.val ∧
        r.val ≤ (numBlocks (bytesOf s) : Int) + 2 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1), ∀ r, max_partitions_after_operations s k = ok r →
      (numBlocks (bytesOf s) : Int) ≤ r.val ∧
        r.val ≤ (numBlocks (bytesOf s) : Int) + 2) := by
  sorry

/-- Whenever the function returns a result r, r = len(s).
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); k = 1; for every i with 1 <= i < len(s), s[i] != s[i-1]. -/
theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1)
    (hne : ∀ i, 1 ≤ i → i < s.val.length →
      byteAt (bytesOf s) i ≠ byteAt (bytesOf s) (i - 1)) :
    ∀ r, max_partitions_after_operations s k = ok r → r.val = (s.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1)
    (hne : ∀ i, 1 ≤ i → i < s.val.length →
      byteAt (bytesOf s) i ≠ byteAt (bytesOf s) (i - 1)), ∀ r, max_partitions_after_operations s k = ok r → r.val = (s.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = min(len(s), 3), that is, r is the smaller of len(s) and 3.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); k = 1; for every i with 0 <= i < len(s), s[i] = s[0]. -/
theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1)
    (hconst : ∀ i, i < s.val.length → byteAt (bytesOf s) i = byteAt (bytesOf s) 0) :
    ∀ r, max_partitions_after_operations s k = ok r →
      r.val = ((min s.val.length 3 : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1)
    (hconst : ∀ i, i < s.val.length → byteAt (bytesOf s) i = byteAt (bytesOf s) 0), ∀ r, max_partitions_after_operations s k = ok r →
      r.val = ((min s.val.length 3 : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 1.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26; k >= len(s). -/
theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26)
    (hkl : (s.val.length : Int) ≤ k.val) :
    ∀ r, max_partitions_after_operations s k = ok r → r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26)
    (hkl : (s.val.length : Int) ≤ k.val), ∀ r, max_partitions_after_operations s k = ok r → r.val = 1) := by
  sorry

/-- Let r be the result returned for (s,k). For every integer k' with k <= k' <= 26, if r' is the result returned for (s,k'), then r >= r'.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_9 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ (k' : Std.I64) (r r' : Std.I64), k.val ≤ k'.val → k'.val ≤ 26 →
      max_partitions_after_operations s k = ok r →
      max_partitions_after_operations s k' = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ (k' : Std.I64) (r r' : Std.I64), k.val ≤ k'.val → k'.val ≤ 26 →
      max_partitions_after_operations s k = ok r →
      max_partitions_after_operations s k' = ok r' → r'.val ≤ r.val) := by
  sorry

/-- For every permutation f of the set of 26 lowercase ASCII byte values, if s_f is the byte string with s_f[i] = f(s[i]) for every 0 <= i < len(s), then whenever the function returns a result r on (s,k), the function returns the same result r on (s_f,k).
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_10 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ (σ : Nat → Nat) (s' : Slice Std.U8), IsLowerPerm σ →
      s'.val.map (fun b => b.val) = (s.val.map (fun b => b.val)).map σ →
      ∀ r, max_partitions_after_operations s k = ok r →
        max_partitions_after_operations s' k = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ (σ : Nat → Nat) (s' : Slice Std.U8), IsLowerPerm σ →
      s'.val.map (fun b => b.val) = (s.val.map (fun b => b.val)).map σ →
      ∀ r, max_partitions_after_operations s k = ok r →
        max_partitions_after_operations s' k = ok r) := by
  sorry

/-- The function returns a result r and there exists a lowercase byte string t with len(t)=len(s) and Hamming distance at most 1 from s such that G(t,k)=r, where G(t,q) is the number of partitions produced by repeatedly deleting from t the longest nonempty prefix containing at most q distinct bytes, with G(empty,q)=0.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_11 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∃ r, max_partitions_after_operations s k = ok r ∧
      ∃ t, Admissible (bytesOf s) t ∧ (greedyParts (kNat k) t : Int) = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∃ r, max_partitions_after_operations s k = ok r ∧
      ∃ t, Admissible (bytesOf s) t ∧ (greedyParts (kNat k) t : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, if r > G(s,k), then there exists an index i with 0 <= i < len(s) and a lowercase byte c with c != s[i] such that G(t,k)=r, where t is s with position i replaced by c and G is the greedy partition count defined by repeatedly deleting the longest nonempty prefix containing at most k distinct bytes.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_12 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ r, max_partitions_after_operations s k = ok r →
      (greedyParts (kNat k) (bytesOf s) : Int) < r.val →
      ∃ (i c : Nat), i < s.val.length ∧ IsLowerByte c ∧
        c ≠ byteAt (bytesOf s) i ∧
        (greedyParts (kNat k) (replaceAt (bytesOf s) i c) : Int) = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ r, max_partitions_after_operations s k = ok r →
      (greedyParts (kNat k) (bytesOf s) : Int) < r.val →
      ∃ (i c : Nat), i < s.val.length ∧ IsLowerByte c ∧
        c ≠ byteAt (bytesOf s) i ∧
        (greedyParts (kNat k) (replaceAt (bytesOf s) i c) : Int) = r.val) := by
  sorry

/-- Let d be the number of distinct byte values occurring in s. Whenever the function returns a result r, r = 1 if and only if d <= k.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); 1 <= k <= 26. -/
theorem spec_13 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26) :
    ∀ r, max_partitions_after_operations s k = ok r →
      (r.val = 1 ↔ numDistinct (bytesOf s) ≤ kNat k) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : 1 ≤ k.val ∧ k.val ≤ 26), ∀ r, max_partitions_after_operations s k = ok r →
      (r.val = 1 ↔ numDistinct (bytesOf s) ≤ kNat k)) := by
  sorry

/-- Let R be the number of maximal contiguous blocks of equal bytes in s, and let L be the maximum length of such a block. Whenever the function returns a result r, r = R + 2 if L >= 3, r = R + 1 if L = 2, and r = R if L = 1.
  Preconditions: len(s) is between 1 and 10000 inclusive; every byte of s is an ASCII lowercase letter (97 <= s[i] <= 122 for every 0 <= i < len(s)); k = 1. -/
theorem spec_14 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1) :
    ∀ r, max_partitions_after_operations s k = ok r →
      (3 ≤ maxBlockLen (bytesOf s) → r.val = (numBlocks (bytesOf s) : Int) + 2) ∧
      (maxBlockLen (bytesOf s) = 2 → r.val = (numBlocks (bytesOf s) : Int) + 1) ∧
      (maxBlockLen (bytesOf s) = 1 → r.val = (numBlocks (bytesOf s) : Int)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 10000)
    (hlower : ∀ b ∈ s.val, IsLowerByte b.val)
    (hk : k.val = 1), ∀ r, max_partitions_after_operations s k = ok r →
      (3 ≤ maxBlockLen (bytesOf s) → r.val = (numBlocks (bytesOf s) : Int) + 2) ∧
      (maxBlockLen (bytesOf s) = 2 → r.val = (numBlocks (bytesOf s) : Int) + 1) ∧
      (maxBlockLen (bytesOf s) = 1 → r.val = (numBlocks (bytesOf s) : Int))) := by
  sorry

end AegisSpec.MaxPartitionsAfterOperations
