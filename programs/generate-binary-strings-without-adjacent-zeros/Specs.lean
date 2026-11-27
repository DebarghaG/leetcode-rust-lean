import Aegis.ValidStrings.Code.Funs

/-!
# Specifications of `Aegis.ValidStrings.valid_strings`

LeetCode problem `generate-binary-strings-without-adjacent-zeros`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AegisSpec.ValidStrings

def IsBit (b : Std.U8) : Prop :=
  b.val = 48 ∨ b.val = 49

def ValidBinaryString (n : Nat) (s : alloc.vec.Vec Std.U8) : Prop :=
  s.val.length = n ∧
    (∀ b ∈ s.val, IsBit b) ∧
    ∀ i : Nat, s.val[i]? = some 48#u8 → s.val[i + 1]? ≠ some 48#u8

def countZeros (l : List Std.U8) : Nat :=
  l.countP (fun b => decide (b.val = 48))

def countOf (l : List (alloc.vec.Vec Std.U8)) (s : List Std.U8) : Nat :=
  l.countP (fun t => decide (t.val = s))

def revContents (s : alloc.vec.Vec Std.U8) : List Std.U8 :=
  s.val.reverse

def prefixContents (k : Nat) (s : alloc.vec.Vec Std.U8) : List Std.U8 :=
  s.val.take k

def suffixContents (k : Nat) (s : alloc.vec.Vec Std.U8) : List Std.U8 :=
  s.val.drop (s.val.length - k)

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (k + 2) => fib (k + 1) + fib k

def gen : Nat → Bool → List (List Std.U8)
  | 0, _ => [[]]
  | (k + 1), canZero =>
    (gen k true).map (fun tail => 49#u8 :: tail) ++
      (if canZero then (gen k false).map (fun tail => 48#u8 :: tail) else [])

def numValidStrings (n : Nat) : Nat :=
  (gen n true).length

/-- Whenever valid_strings(n) returns a result r, r is exactly the collection of all valid binary strings of length n, in some order. More precisely, call a byte vector s a valid binary string of length n when: len(s) = n; every byte s[i] with 0 <= i < len(s) is either 48 ('0') or 49 ('1'); and for every i with 0 <= i < len(s)-1, it is not the case that s[i] = 48 and s[i+1] = 48. Then: (1) every element s of r is a valid binary string of length n; (2) every valid binary string s of length n occurs exactly once in r, meaning there is exactly one index k with 0 <= k < len(r) and r[k] = s.
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      (∀ s ∈ r.val, ValidBinaryString n.val.toNat s) ∧
        (∀ s : alloc.vec.Vec Std.U8,
          ValidBinaryString n.val.toNat s → countOf r.val s.val = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      (∀ s ∈ r.val, ValidBinaryString n.val.toNat s) ∧
        (∀ s : alloc.vec.Vec Std.U8,
          ValidBinaryString n.val.toNat s → countOf r.val s.val = 1)) := by
  sorry

/-- valid_strings(n) returns a result r; in particular, it does not panic, overflow, or otherwise fail.
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∃ r, Aegis.ValidStrings.valid_strings n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∃ r, Aegis.ValidStrings.valid_strings n = ok r) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, len(r) = F(n+2), where F is the Fibonacci sequence defined by F(1)=1, F(2)=1, and F(k)=F(k-1)+F(k-2) for k >= 3. Equivalently, len(r) is the number of byte vectors s with len(s)=n, every byte equal to 48 or 49, and no two consecutive bytes both equal to 48.
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      r.val.length = fib (n.val.toNat + 2) ∧
        r.val.length = numValidStrings n.val.toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      r.val.length = fib (n.val.toNat + 2) ∧
        r.val.length = numValidStrings n.val.toNat) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, r has no duplicate elements: for every i and j with 0 <= i < j < len(r), r[i] != r[j].
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ i j : Nat, i < j → j < r.val.length → r.val[i]? ≠ r.val[j]? := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ i j : Nat, i < j → j < r.val.length → r.val[i]? ≠ r.val[j]?) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, every element s of r is a valid binary string of length n: len(s)=n; every byte s[i] with 0 <= i < len(s) is 48 or 49; and for every i with 0 <= i < len(s)-1, not (s[i]=48 and s[i+1]=48).
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, ValidBinaryString n.val.toNat s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, ValidBinaryString n.val.toNat s) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, every valid binary string s of length n occurs at least once in r. Here 'valid binary string of length n' means len(s)=n, every byte of s is 48 or 49, and no two consecutive bytes of s are both 48.
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s : alloc.vec.Vec Std.U8,
        ValidBinaryString n.val.toNat s → 0 < countOf r.val s.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s : alloc.vec.Vec Std.U8,
        ValidBinaryString n.val.toNat s → 0 < countOf r.val s.val) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, for every element s of r, the reverse vector rev(s), defined by len(rev(s))=len(s) and rev(s)[i]=s[len(s)-1-i] for all 0 <= i < len(s), also occurs exactly once in r.
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_7 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, countOf r.val (revContents s) = 1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, countOf r.val (revContents s) = 1) := by
  sorry

/-- Whenever valid_strings(n) returns a result r, every element s of r has at most (n+1) div 2 occurrences of the byte 48 ('0').
  Preconditions: n is an integer with 1 <= n <= 18. -/
theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18) :
    ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, countZeros s.val ≤ (n.val.toNat + 1) / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 18), ∀ r, Aegis.ValidStrings.valid_strings n = ok r →
      ∀ s ∈ r.val, countZeros s.val ≤ (n.val.toNat + 1) / 2) := by
  sorry

/-- Whenever valid_strings(n) returns a result r and valid_strings(n-1) returns a result rprev, for every element s of r, the prefix of s of length n-1 is an element of rprev, and the suffix of s of length n-1 is an element of rprev. Here the prefix of s of length k is the vector t with len(t)=k and t[i]=s[i] for 0 <= i < k; the suffix of s of length k is the vector u with len(u)=k and u[i]=s[len(s)-k+i] for 0 <= i < k.
  Preconditions: n is an integer with 2 <= n <= 18. -/
theorem spec_9 (n np : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 18)
    (hnp : np.val = n.val - 1) :
    ∀ r rprev, Aegis.ValidStrings.valid_strings n = ok r →
      Aegis.ValidStrings.valid_strings np = ok rprev →
        ∀ s ∈ r.val,
          (0 < countOf rprev.val (prefixContents (n.val.toNat - 1) s)) ∧
            (0 < countOf rprev.val (suffixContents (n.val.toNat - 1) s)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n np : Std.I64) (hn1 : 2 ≤ n.val) (hn2 : n.val ≤ 18)
    (hnp : np.val = n.val - 1), ∀ r rprev, Aegis.ValidStrings.valid_strings n = ok r →
      Aegis.ValidStrings.valid_strings np = ok rprev →
        ∀ s ∈ r.val,
          (0 < countOf rprev.val (prefixContents (n.val.toNat - 1) s)) ∧
            (0 < countOf rprev.val (suffixContents (n.val.toNat - 1) s))) := by
  sorry

end AegisSpec.ValidStrings
