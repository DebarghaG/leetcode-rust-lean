import Aegis.EqualCountSubstrings.Code.Funs

/-!
# Specifications of `Aegis.EqualCountSubstrings.equal_count_substrings`

LeetCode problem `number-of-equal-count-substrings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.EqualCountSubstrings

namespace AegisSpec.EqualCountSubstrings

def countOf (l : List Std.U8) (c : Std.U8) : Nat := (l.filter (fun x => x = c)).length

def subList (l : List Std.U8) (i j : Nat) : List Std.U8 := (l.drop i).take (j + 1 - i)

def EqualCount (cnt : Int) (l : List Std.U8) : Prop :=
  ∀ c : Std.U8, c ∈ l → (countOf l c : Int) = cnt

def AtMostOnce (l : List Std.U8) : Prop := ∀ c : Std.U8, countOf l c ≤ 1

def ConstantRun (l : List Std.U8) (i cnt : Nat) : Prop :=
  ∃ c : Std.U8, (l.drop i).take cnt = List.replicate cnt c

def indexPairs (n : Nat) : Finset (Nat × Nat) :=
  ((Finset.range n).product (Finset.range n)).filter (fun p : Nat × Nat => p.1 ≤ p.2)

noncomputable def equalCountSubstringCount (l : List Std.U8) (cnt : Int) : Nat :=
  open Classical in
  ((indexPairs l.length).filter (fun p : Nat × Nat => EqualCount cnt (subList l p.1 p.2))).card

noncomputable def distinctSubstringCount (l : List Std.U8) : Nat :=
  open Classical in
  ((indexPairs l.length).filter (fun p : Nat × Nat => AtMostOnce (subList l p.1 p.2))).card

noncomputable def multipleLengthSubstringCount (l : List Std.U8) (cnt : Nat) : Nat :=
  open Classical in
  ((indexPairs l.length).filter (fun p : Nat × Nat =>
    ∃ m : Nat, 1 ≤ m ∧ p.2 + 1 - p.1 = cnt * m)).card

noncomputable def constantRunCount (l : List Std.U8) (cnt : Nat) : Nat :=
  open Classical in
  ((Finset.range (l.length + 1)).filter (fun i : Nat =>
    i + cnt ≤ l.length ∧ ConstantRun l i cnt)).card

/-- Under these preconditions the function returns a result r (it does not fail), and r is exactly the number of pairs of indices (i,j) with 0 <= i <= j < len(s) for which the substring s[i..j] is equal-count. A non-empty substring s[i..j] is equal-count when, for every byte c with 97 <= c <= 122, if c occurs among s[i],...,s[j] (i.e. there exists k with i <= k <= j and s[k]=c), then the number of k with i <= k <= j and s[k]=c is exactly count. Equivalently, every distinct letter present in the substring appears exactly count times in it.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122 (s is a lowercase ASCII byte string). -/
theorem spec_1 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      r.val = (equalCountSubstringCount s.val count.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      r.val = (equalCountSubstringCount s.val count.val : Int)) := by
  sorry

/-- Under these preconditions, the function returns an ok result (Result.ok) for every input satisfying the preconditions; it does not fail, panic, overflow, or return an error.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_2 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∃ r : Std.I64, equal_count_substrings s count = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∃ r : Std.I64, equal_count_substrings s count = ok r) := by
  sorry

/-- Whenever the function returns a result r under these preconditions, 0 <= r <= len(s) * (len(s) + 1) / 2. The upper bound is the total number of non-empty contiguous substrings of s.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_3 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length : Int) * ((s.val.length : Int) + 1)) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∀ r : Std.I64, equal_count_substrings s count = ok r →
      0 ≤ r.val ∧ r.val ≤ ((s.val.length : Int) * ((s.val.length : Int) + 1)) / 2) := by
  sorry

/-- Under these preconditions, the function returns a result r, and r = 0 if and only if there is no pair of indices (i,j) with 0 <= i <= j < len(s) such that s[i..j] is equal-count. Here equal-count means that every distinct byte occurring in s[i..j] occurs in it exactly count times.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_4 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i j : Nat),
        i ≤ j ∧ j < s.val.length ∧ EqualCount count.val (subList s.val i j)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      (r.val = 0 ↔ ¬ ∃ (i j : Nat),
        i ≤ j ∧ j < s.val.length ∧ EqualCount count.val (subList s.val i j))) := by
  sorry

/-- Whenever the function returns a result r under these preconditions and r > 0, there exist indices i,j with 0 <= i <= j < len(s) such that s[i..j] is equal-count, meaning that every distinct byte occurring in s[i..j] occurs in it exactly count times.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_5 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r → 0 < r.val →
      ∃ (i j : Nat), i ≤ j ∧ j < s.val.length ∧ EqualCount count.val (subList s.val i j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∀ r : Std.I64, equal_count_substrings s count = ok r → 0 < r.val →
      ∃ (i j : Nat), i ≤ j ∧ j < s.val.length ∧ EqualCount count.val (subList s.val i j)) := by
  sorry

/-- Under these preconditions, the function returns a result r and r = 0.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122; for every byte c with 97 <= c <= 122, the number of indices k with 0 <= k < len(s) and s[k] = c is less than count. -/
theorem spec_6 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_counts : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → (countOf s.val c : Int) < count.val) :
    ∃ r : Std.I64, equal_count_substrings s count = ok r ∧ r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_counts : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → (countOf s.val c : Int) < count.val), ∃ r : Std.I64, equal_count_substrings s count = ok r ∧ r.val = 0) := by
  sorry

/-- Whenever the function returns a result r under these preconditions, r equals the number of pairs (i,j) with 0 <= i <= j < len(s) such that no byte value occurs more than once in s[i..j]; explicitly, for every byte c, the number of k with i <= k <= j and s[k] = c is at most 1.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122; count = 1. -/
theorem spec_7 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_count_one : count.val = 1) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val = (distinctSubstringCount s.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_count_one : count.val = 1), ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val = (distinctSubstringCount s.val : Int)) := by
  sorry

/-- Under these preconditions, the function returns a result r equal to max(0, len(s) - count + 1). Equivalently, r = len(s) - count + 1 when count <= len(s), and r = 0 when count > len(s).
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122; there exists a byte c with 97 <= c <= 122 such that s[k] = c for every k with 0 <= k < len(s). -/
theorem spec_8 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_const : ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧
      ∀ (k : Nat) (hk : k < s.val.length), s.val[k] = c) :
    ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      r.val = max 0 ((s.val.length : Int) - count.val + 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_const : ∃ c : Std.U8, 97 ≤ c.val ∧ c.val ≤ 122 ∧
      ∀ (k : Nat) (hk : k < s.val.length), s.val[k] = c), ∃ r : Std.I64, equal_count_substrings s count = ok r ∧
      r.val = max 0 ((s.val.length : Int) - count.val + 1)) := by
  sorry

/-- Whenever the function returns a result r under these preconditions, r equals the number of indices i with 0 <= i and i + count <= len(s) such that all bytes s[i], s[i+1], ..., s[i+count-1] are equal to one another (there is a byte c with s[i+t] = c for every t with 0 <= t < count).
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122; 2 * count > len(s). -/
theorem spec_9 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_tight : 2 * count.val > (s.val.length : Int)) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val = (constantRunCount s.val count.val.toNat : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_tight : 2 * count.val > (s.val.length : Int)), ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val = (constantRunCount s.val count.val.toNat : Int)) := by
  sorry

/-- For every permutation pi of the set of byte values {97,98,...,122}, let t be the byte slice with len(t)=len(s) and t[k]=pi(s[k]) for every k with 0 <= k < len(s). If the function returns r on (s,count) and r' on (t,count), then r = r'.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_10 (s : Slice Std.U8) (count : Std.I64) (π : Std.U8 → Std.U8)
    (t : Slice Std.U8)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (hπ_maps : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      97 ≤ (π c).val ∧ (π c).val ≤ 122)
    (hπ_inj : ∀ c d : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      97 ≤ d.val → d.val ≤ 122 → π c = π d → c = d)
    (ht : t.val = s.val.map π) :
    ∀ r r' : Std.I64, equal_count_substrings s count = ok r →
      equal_count_substrings t count = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64) (π : Std.U8 → Std.U8)
    (t : Slice Std.U8)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (hπ_maps : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      97 ≤ (π c).val ∧ (π c).val ≤ 122)
    (hπ_inj : ∀ c d : Std.U8, 97 ≤ c.val → c.val ≤ 122 →
      97 ≤ d.val → d.val ≤ 122 → π c = π d → c = d)
    (ht : t.val = s.val.map π), ∀ r r' : Std.I64, equal_count_substrings s count = ok r →
      equal_count_substrings t count = ok r' → r = r') := by
  sorry

/-- Let t be the byte slice with len(t)=len(s) and t[k]=s[len(s)-1-k] for every k with 0 <= k < len(s). If the function returns r on (s,count) and r' on (t,count), then r = r'.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_11 (s : Slice Std.U8) (count : Std.I64) (t : Slice Std.U8)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (ht : t.val = s.val.reverse) :
    ∀ r r' : Std.I64, equal_count_substrings s count = ok r →
      equal_count_substrings t count = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64) (t : Slice Std.U8)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (ht : t.val = s.val.reverse), ∀ r r' : Std.I64, equal_count_substrings s count = ok r →
      equal_count_substrings t count = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r under these preconditions, r >= 1.
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122; for every byte c with 97 <= c <= 122, if c occurs in s (there exists k with 0 <= k < len(s) and s[k]=c), then the number of k with 0 <= k < len(s) and s[k]=c is exactly count. -/
theorem spec_12 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_exact : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → c ∈ s.val →
      (countOf s.val c : Int) = count.val) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r → 1 ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122)
    (h_exact : ∀ c : Std.U8, 97 ≤ c.val → c.val ≤ 122 → c ∈ s.val →
      (countOf s.val c : Int) = count.val), ∀ r : Std.I64, equal_count_substrings s count = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r under these preconditions, r <= M, where M is the number of pairs (i,j) with 0 <= i <= j < len(s) such that j - i + 1 is a positive multiple of count (i.e. j - i + 1 = count * m for some integer m with m >= 1).
  Preconditions: 1 <= len(s) <= 30000; 1 <= count <= 30000; for every k with 0 <= k < len(s), 97 <= s[k] <= 122. -/
theorem spec_13 (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122) :
    ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val ≤ (multipleLengthSubstringCount s.val count.val.toNat : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8) (count : Std.I64)
    (h_len_lo : 1 ≤ s.val.length) (h_len_hi : s.val.length ≤ 30000)
    (h_count_lo : 1 ≤ count.val) (h_count_hi : count.val ≤ 30000)
    (h_bytes : ∀ (k : Nat) (hk : k < s.val.length),
      97 ≤ (s.val[k]).val ∧ (s.val[k]).val ≤ 122), ∀ r : Std.I64, equal_count_substrings s count = ok r →
      r.val ≤ (multipleLengthSubstringCount s.val count.val.toNat : Int)) := by
  sorry

end AegisSpec.EqualCountSubstrings
