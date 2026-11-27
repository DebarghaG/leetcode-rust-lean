import Aegis.PartitionString.Code.Funs

/-!
# Specifications of `Aegis.PartitionString.partition_string`

LeetCode problem `optimal-partition-of-string`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PartitionString

def contents (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

theorem contents_length (s : Slice Std.U8) : (contents s).length = s.val.length := by
  simp [contents]

def byteAt (l : List Nat) (i : Nat) : Nat := l.getD i 0

def subList (l : List Nat) (i j : Nat) : List Nat := (l.drop i).take (j - i)

def allDistinct (l : List Nat) : Prop := l.Nodup

def freq (l : List Nat) (c : Nat) : Nat := (l.filter (fun x => x = c)).length

def ceilDiv (n k : Nat) : Nat := (n + k - 1) / k

def IsCutPartition (l : List Nat) (k : Nat) (p : Nat → Nat) : Prop :=
  1 ≤ k ∧ p 0 = 0 ∧ p k = l.length ∧
    (∀ j, 1 ≤ j → j ≤ k → p (j - 1) < p j) ∧
    (∀ j, 1 ≤ j → j ≤ k → allDistinct (subList l (p (j - 1)) (p j)))

def IsMinParts (l : List Nat) (k : Nat) : Prop :=
  1 ≤ k ∧ (∃ p, IsCutPartition l k p) ∧
    ∀ k', 1 ≤ k' → (∃ p, IsCutPartition l k' p) → k ≤ k'

def IsGreedyCutPartition (l : List Nat) (k : Nat) (p : Nat → Nat) : Prop :=
  IsCutPartition l k p ∧
    ∀ j, 1 ≤ j → j < k → ∃ a, p (j - 1) ≤ a ∧ a < p j ∧ byteAt l a = byteAt l (p j)

/-- For every s satisfying the preconditions, partition_string(s) returns a result r, and r is the minimum k >= 1 for which there exist cut positions 0 = p_0 < p_1 < ... < p_k = n such that for every j with 1 <= j <= k and every a,b with p_{j-1} <= a < b < p_j, we have s[a] != s[b]. Equivalently, the k contiguous nonempty substrings s[p_{j-1}..p_j) cover s in order and each substring has all characters distinct.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122 (s consists of English lowercase letters). -/
theorem spec_1 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∃ r : Std.I64, Aegis.PartitionString.partition_string s = ok r ∧
      IsMinParts (contents s) r.val.toNat := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∃ r : Std.I64, Aegis.PartitionString.partition_string s = ok r ∧
      IsMinParts (contents s) r.val.toNat) := by
  sorry

/-- For every s satisfying the preconditions and every i,j with 0 <= i < j <= n, the call partition_string on the contiguous substring s[i..j) returns a result (it does not fail: no panic, out-of-bounds, or arithmetic overflow).
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ (i j : Nat) (t : Slice Std.U8), i < j → j ≤ n → contents t = subList (contents s) i j →
      ∃ r : Std.I64, Aegis.PartitionString.partition_string t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ (i j : Nat) (t : Slice Std.U8), i < j → j ≤ n → contents t = subList (contents s) i j →
      ∃ r : Std.I64, Aegis.PartitionString.partition_string t = ok r) := by
  sorry

/-- Whenever partition_string(s) returns a result r, 1 <= r <= n.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      1 ≤ r.val ∧ r.val ≤ (n : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      1 ≤ r.val ∧ r.val ≤ (n : Int)) := by
  sorry

/-- Whenever partition_string(s) returns a result r, r >= ceil(n / 26), where ceil(x) is the least integer greater than or equal to x.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (ceilDiv n 26 : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (ceilDiv n 26 : Int) ≤ r.val) := by
  sorry

/-- Whenever partition_string(s) returns a result r, for every byte value c, r >= freq(c), where freq(c) is the number of indices i with 0 <= i < n and s[i] = c. Equivalently, r >= max_c freq(c).
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ c : Nat, (freq (contents s) c : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ c : Nat, (freq (contents s) c : Int) ≤ r.val) := by
  sorry

/-- Whenever partition_string(s) returns a result r, there exist cut positions 0 = p_0 < p_1 < ... < p_r = n such that: (i) for every j with 1 <= j <= r, the substring s[p_{j-1}..p_j) has all characters distinct; and (ii) for every j with 1 <= j < r, there is an index a with p_{j-1} <= a < p_j and s[a] = s[p_j], so the next character after the j-th part would repeat a character already in that part.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_6 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∃ p : Nat → Nat, IsGreedyCutPartition (contents s) r.val.toNat p := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∃ p : Nat → Nat, IsGreedyCutPartition (contents s) r.val.toNat p) := by
  sorry

/-- Whenever partition_string(s) returns a result r, for every k >= 1 and every choice of cut positions 0 = q_0 < q_1 < ... < q_k = n such that each substring s[q_{j-1}..q_j) has all characters distinct, we have r <= k.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_7 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (k : Nat) (q : Nat → Nat), IsCutPartition (contents s) k q → r.val.toNat ≤ k := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (k : Nat) (q : Nat → Nat), IsCutPartition (contents s) k q → r.val.toNat ≤ k) := by
  sorry

/-- Whenever partition_string(s) returns a result r, r <= 2 if and only if either (a) for all i,j with 0 <= i < j < n, s[i] != s[j] (the whole string has all characters distinct), or (b) there exists p with 1 <= p < n such that both substrings s[0..p) and s[p..n) individually have all characters distinct.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_8 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val.toNat ≤ 2 ↔
        allDistinct (contents s) ∨
          ∃ p : Nat, 1 ≤ p ∧ p < n ∧
            allDistinct (subList (contents s) 0 p) ∧
            allDistinct (subList (contents s) p n)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val.toNat ≤ 2 ↔
        allDistinct (contents s) ∨
          ∃ p : Nat, 1 ≤ p ∧ p < n ∧
            allDistinct (subList (contents s) 0 p) ∧
            allDistinct (subList (contents s) p n))) := by
  sorry

/-- Whenever partition_string(s) returns a result r, r = 1 if and only if for all i,j with 0 <= i < j < n, s[i] != s[j].
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_9 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val = 1 ↔ allDistinct (contents s)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val = 1 ↔ allDistinct (contents s))) := by
  sorry

/-- Whenever partition_string(s) returns a result r, r = n if and only if for every i with 0 <= i < n, s[i] = s[0] (all characters of s are equal).
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val = (n : Int) ↔ ∀ i, i < n → byteAt (contents s) i = byteAt (contents s) 0) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      (r.val = (n : Int) ↔ ∀ i, i < n → byteAt (contents s) i = byteAt (contents s) 0)) := by
  sorry

/-- Whenever partition_string(s) returns a result r, for every i,j with 0 <= i < j <= n, let t be the contiguous substring s[i..j). Whenever partition_string(t) returns a result r_t, we have r_t <= r.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (i j : Nat) (t : Slice Std.U8), i < j → j ≤ n → contents t = subList (contents s) i j →
        ∀ r_t : Std.I64, Aegis.PartitionString.partition_string t = ok r_t → r_t.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (i j : Nat) (t : Slice Std.U8), i < j → j ≤ n → contents t = subList (contents s) i j →
        ∀ r_t : Std.I64, Aegis.PartitionString.partition_string t = ok r_t → r_t.val ≤ r.val) := by
  sorry

/-- Whenever partition_string(s) returns a result r, for every p with 1 <= p < n, if a = s[0..p) and b = s[p..n) and partition_string(a) returns r_a and partition_string(b) returns r_b, then r <= r_a + r_b.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_12 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (p : Nat) (a b : Slice Std.U8), 1 ≤ p → p < n →
        contents a = subList (contents s) 0 p →
        contents b = subList (contents s) p n →
        ∀ r_a r_b : Std.I64,
          Aegis.PartitionString.partition_string a = ok r_a →
          Aegis.PartitionString.partition_string b = ok r_b →
          r.val ≤ r_a.val + r_b.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ r : Std.I64, Aegis.PartitionString.partition_string s = ok r →
      ∀ (p : Nat) (a b : Slice Std.U8), 1 ≤ p → p < n →
        contents a = subList (contents s) 0 p →
        contents b = subList (contents s) p n →
        ∀ r_a r_b : Std.I64,
          Aegis.PartitionString.partition_string a = ok r_a →
          Aegis.PartitionString.partition_string b = ok r_b →
          r.val ≤ r_a.val + r_b.val) := by
  sorry

/-- Whenever partition_string(s) returns a result r_s and partition_string(t) returns a result r_t, we have r_s = r_t.
  Preconditions: len(s) = len(t) = n, 1 <= n <= 100000, all bytes of s and t are in 97..122, and for all i,j with 0 <= i < n and 0 <= j < n, s[i] = s[j] if and only if t[i] = t[j]. -/
theorem spec_13 (s t : Slice Std.U8) (n : Nat)
    (hs : s.val.length = n) (ht : t.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (halls : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122)
    (hallt : ∀ i, i < n → 97 ≤ byteAt (contents t) i ∧ byteAt (contents t) i ≤ 122)
    (hpat : ∀ i j, i < n → j < n →
      (byteAt (contents s) i = byteAt (contents s) j ↔
        byteAt (contents t) i = byteAt (contents t) j)) :
    ∀ r_s r_t : Std.I64,
      Aegis.PartitionString.partition_string s = ok r_s →
      Aegis.PartitionString.partition_string t = ok r_t → r_s.val = r_t.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice Std.U8) (n : Nat)
    (hs : s.val.length = n) (ht : t.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (halls : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122)
    (hallt : ∀ i, i < n → 97 ≤ byteAt (contents t) i ∧ byteAt (contents t) i ≤ 122)
    (hpat : ∀ i j, i < n → j < n →
      (byteAt (contents s) i = byteAt (contents s) j ↔
        byteAt (contents t) i = byteAt (contents t) j)), ∀ r_s r_t : Std.I64,
      Aegis.PartitionString.partition_string s = ok r_s →
      Aegis.PartitionString.partition_string t = ok r_t → r_s.val = r_t.val) := by
  sorry

/-- Whenever partition_string(s) returns a result r, let rev(s) be the byte slice of length n with rev(s)[i] = s[n-1-i] for every i with 0 <= i < n. Whenever partition_string(rev(s)) returns a result r_rev, we have r_rev = r.
  Preconditions: len(s) = n, 1 <= n <= 100000, and for every i with 0 <= i < n, 97 <= s[i] <= 122. -/
theorem spec_14 (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122) :
    ∀ (t : Slice Std.U8), contents t = (contents s).reverse →
      ∀ r r_rev : Std.I64,
        Aegis.PartitionString.partition_string s = ok r →
        Aegis.PartitionString.partition_string t = ok r_rev → r_rev.val = r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8) (n : Nat)
    (hn : s.val.length = n) (hpos : 1 ≤ n) (hle : n ≤ 100000)
    (hall : ∀ i, i < n → 97 ≤ byteAt (contents s) i ∧ byteAt (contents s) i ≤ 122), ∀ (t : Slice Std.U8), contents t = (contents s).reverse →
      ∀ r r_rev : Std.I64,
        Aegis.PartitionString.partition_string s = ok r →
        Aegis.PartitionString.partition_string t = ok r_rev → r_rev.val = r.val) := by
  sorry

end AegisSpec.PartitionString
