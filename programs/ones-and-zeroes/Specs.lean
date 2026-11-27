import Aegis.FindMaxForm.Code.Funs

/-!
# Specifications of `Aegis.FindMaxForm.find_max_form`

LeetCode problem `ones-and-zeroes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaxForm

def IsBit (b : U8) : Prop := b = 48#u8 ∨ b = 49#u8

def IsBinaryString (s : alloc.vec.Vec U8) : Prop :=
  1 ≤ s.val.length ∧ s.val.length ≤ 100 ∧ ∀ b ∈ s.val, IsBit b

def zerosOf (s : alloc.vec.Vec U8) : Nat := s.val.countP (fun b => b = 48#u8)

def onesOf (s : alloc.vec.Vec U8) : Nat := s.val.countP (fun b => b = 49#u8)

def zerosAt (strs : Slice (alloc.vec.Vec U8)) (i : Nat) : Nat :=
  match strs.val[i]? with
  | some s => zerosOf s
  | none => 0

def onesAt (strs : Slice (alloc.vec.Vec U8)) (i : Nat) : Nat :=
  match strs.val[i]? with
  | some s => onesOf s
  | none => 0

def zerosSum (strs : Slice (alloc.vec.Vec U8)) (S : Finset Nat) : Nat :=
  S.sum (fun i => zerosAt strs i)

def onesSum (strs : Slice (alloc.vec.Vec U8)) (S : Finset Nat) : Nat :=
  S.sum (fun i => onesAt strs i)

def InIndexRange (strs : Slice (alloc.vec.Vec U8)) (S : Finset Nat) : Prop :=
  ∀ i ∈ S, i < strs.val.length

def ValidSubset (strs : Slice (alloc.vec.Vec U8)) (m n : Int) (S : Finset Nat) : Prop :=
  InIndexRange strs S ∧ (zerosSum strs S : Int) ≤ m ∧ (onesSum strs S : Int) ≤ n

def totalZeros (strs : Slice (alloc.vec.Vec U8)) : Nat :=
  (Finset.range strs.val.length).sum (fun i => zerosAt strs i)

def totalOnes (strs : Slice (alloc.vec.Vec U8)) : Nat :=
  (Finset.range strs.val.length).sum (fun i => onesAt strs i)

def fittingCount (strs : Slice (alloc.vec.Vec U8)) (m n : Int) : Nat :=
  ((Finset.range strs.val.length).filter
    (fun i => (zerosAt strs i : Int) ≤ m ∧ (onesAt strs i : Int) ≤ n)).card

def firstByteCount (strs : Slice (alloc.vec.Vec U8)) (b : U8) : Nat :=
  ((Finset.range strs.val.length).filter
    (fun i => (strs.val[i]?).bind (fun s => s.val[0]?) = some b)).card

def prefixSum (L : List Nat) (k : Nat) : Nat := (L.take k).sum

def maxPrefixK (L : List Nat) (m : Int) : Nat :=
  (List.range (L.length + 1)).foldl
    (fun best k => if (prefixSum L k : Int) ≤ m then max best k else best) 0

def IsSortedLengths (strs : Slice (alloc.vec.Vec U8)) (L : List Nat) : Prop :=
  L.Perm (strs.val.map (fun s => s.val.length)) ∧ L.Pairwise (fun a b => a ≤ b)

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. A subset of positions is a set S of integers such that 0 <= i < len(strs) for every i in S, with no duplicates. Call S valid if sum_{i in S} z(strs[i]) <= m and sum_{i in S} o(strs[i]) <= n. The function returns a result r and: (1) 0 <= r <= len(strs); (2) there exists a valid subset S with |S| = r; (3) for every valid subset S, |S| <= r. Equivalently, r is the maximum cardinality of a valid subset of positions; the empty subset is allowed and has size 0.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_1 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (strs.val.length : Int) ∧
      (∃ S : Finset Nat, ValidSubset strs m.val n.val S ∧ (S.card : Int) = r.val) ∧
      (∀ S : Finset Nat, ValidSubset strs m.val n.val S → (S.card : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (strs.val.length : Int) ∧
      (∃ S : Finset Nat, ValidSubset strs m.val n.val S ∧ (S.card : Int) = r.val) ∧
      (∀ S : Finset Nat, ValidSubset strs m.val n.val S → (S.card : Int) ≤ r.val)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, panic, or access memory out of bounds.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_2 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= min(len(strs), m+n).
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_3 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      0 ≤ r.val ∧ r.val ≤ min (strs.val.length : Int) (m.val + n.val) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      0 ≤ r.val ∧ r.val ≤ min (strs.val.length : Int) (m.val + n.val)) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. The function returns a result r and there exists a set S of indices, with 0 <= i < len(strs) for every i in S, such that |S| = r, sum_{i in S} z(strs[i]) <= m, and sum_{i in S} o(strs[i]) <= n.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_4 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      ∃ S : Finset Nat, ValidSubset strs m.val n.val S ∧ (S.card : Int) = r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      ∃ S : Finset Nat, ValidSubset strs m.val n.val S ∧ (S.card : Int) = r.val) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. The function returns a result r and for every set S of indices with 0 <= i < len(strs) for all i in S, if sum_{i in S} z(strs[i]) <= m and sum_{i in S} o(strs[i]) <= n, then |S| <= r.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_5 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      ∀ S : Finset Nat, ValidSubset strs m.val n.val S → (S.card : Int) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      ∀ S : Finset Nat, ValidSubset strs m.val n.val S → (S.card : Int) ≤ r.val) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. If sum_{i=0}^{len(strs)-1} z(strs[i]) <= m and sum_{i=0}^{len(strs)-1} o(strs[i]) <= n, then the function returns r = len(strs).
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_6 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hz : (totalZeros strs : Int) ≤ m.val) (ho : (totalOnes strs : Int) ≤ n.val) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = (strs.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hz : (totalZeros strs : Int) ≤ m.val) (ho : (totalOnes strs : Int) ≤ n.val), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = (strs.val.length : Int)) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. If for every i with 0 <= i < len(strs), either z(strs[i]) > m or o(strs[i]) > n, then the function returns r = 0.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_7 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hbig : ∀ i : Nat, i < strs.val.length →
      m.val < (zerosAt strs i : Int) ∨ n.val < (onesAt strs i : Int)) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hbig : ∀ i : Nat, i < strs.val.length →
      m.val < (zerosAt strs i : Int) ∨ n.val < (onesAt strs i : Int)), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 0) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. If len(strs) = 1, then the function returns r = 1 when z(strs[0]) <= m and o(strs[0]) <= n, and returns r = 0 otherwise.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_8 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (h1 : strs.val.length = 1) :
    (((zerosAt strs 0 : Int) ≤ m.val ∧ (onesAt strs 0 : Int) ≤ n.val) →
        ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 1) ∧
      (¬ ((zerosAt strs 0 : Int) ≤ m.val ∧ (onesAt strs 0 : Int) ≤ n.val) →
        ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (h1 : strs.val.length = 1), (((zerosAt strs 0 : Int) ≤ m.val ∧ (onesAt strs 0 : Int) ≤ n.val) →
        ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 1) ∧
      (¬ ((zerosAt strs 0 : Int) ≤ m.val ∧ (onesAt strs 0 : Int) ≤ n.val) →
        ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ r.val = 0)) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. Let F be the number of indices i with 0 <= i < len(strs) such that z(strs[i]) <= m and o(strs[i]) <= n. The function returns a result r with r <= F.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_9 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val ≤ (fittingCount strs m.val n.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val ≤ (fittingCount strs m.val n.val : Int)) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. If there exists an index i with 0 <= i < len(strs) such that z(strs[i]) <= m and o(strs[i]) <= n, then the function returns a result r with r >= 1.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_10 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hex : ∃ i : Nat, i < strs.val.length ∧ (zerosAt strs i : Int) ≤ m.val ∧
      (onesAt strs i : Int) ≤ n.val) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hex : ∃ i : Nat, i < strs.val.length ∧ (zerosAt strs i : Int) ≤ m.val ∧
      (onesAt strs i : Int) ≤ n.val), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- Suppose every string in strs has length 1. Let c0 be the number of indices i with strs[i][0] = 48, and let c1 be the number of indices i with strs[i][0] = 49. Then the function returns r = min(c0, m) + min(c1, n), where c0 and c1 are compared with m and n as ordinary integers.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_11 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (h1 : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → s.val.length = 1) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = min (firstByteCount strs 48#u8 : Int) m.val +
        min (firstByteCount strs 49#u8 : Int) n.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (h1 : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → s.val.length = 1), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = min (firstByteCount strs 48#u8 : Int) m.val +
        min (firstByteCount strs 49#u8 : Int) n.val) := by
  sorry

/-- Suppose every byte of every string in strs is 48, so each strs[i] consists only of '0's. Let L_0, L_1, ..., L_{len(strs)-1} be the values len(strs[i]) sorted in nondecreasing order. Then the function returns r = max { k | 0 <= k <= len(strs) and sum_{j=0}^{k-1} L_j <= m }, where the empty sum for k=0 is 0.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_12 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hzero : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s →
      ∀ b ∈ s.val, b = 48#u8)
    (L : List Nat) (hL : IsSortedLengths strs L) :
    ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = (maxPrefixK L m.val : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hzero : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s →
      ∀ b ∈ s.val, b = 48#u8)
    (L : List Nat) (hL : IsSortedLengths strs L), ∃ r : I64, Aegis.FindMaxForm.find_max_form strs m n = ok r ∧
      r.val = (maxPrefixK L m.val : Int)) := by
  sorry

/-- For any bijection pi of {0, 1, ..., len(strs)-1}, let strs' be the slice of length len(strs) with strs'[i] = strs[pi(i)] for every i. Then the function returns the same result on strs' and on strs: find_max_form(strs', m, n) = find_max_form(strs, m, n).
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_13 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (strs' : Slice (alloc.vec.Vec U8)) (hperm : strs'.val.Perm strs.val) :
    Aegis.FindMaxForm.find_max_form strs' m n = Aegis.FindMaxForm.find_max_form strs m n := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (strs' : Slice (alloc.vec.Vec U8)) (hperm : strs'.val.Perm strs.val), Aegis.FindMaxForm.find_max_form strs' m n = Aegis.FindMaxForm.find_max_form strs m n) := by
  sorry

/-- Let r be the result on (strs, m, n). For any integers m' and n' with 1 <= m' <= 100, 1 <= n' <= 100, m' >= m, and n' >= n, if r' is the result on (strs, m', n'), then r' >= r.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_14 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (m' n' : I64) (hm' : 1 ≤ m'.val ∧ m'.val ≤ 100) (hn' : 1 ≤ n'.val ∧ n'.val ≤ 100)
    (hmm' : m.val ≤ m'.val) (hnn' : n.val ≤ n'.val) (r r' : I64)
    (hr : Aegis.FindMaxForm.find_max_form strs m n = ok r)
    (hr' : Aegis.FindMaxForm.find_max_form strs m' n' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (m' n' : I64) (hm' : 1 ≤ m'.val ∧ m'.val ≤ 100) (hn' : 1 ≤ n'.val ∧ n'.val ≤ 100)
    (hmm' : m.val ≤ m'.val) (hnn' : n.val ≤ n'.val) (r r' : I64)
    (hr : Aegis.FindMaxForm.find_max_form strs m n = ok r)
    (hr' : Aegis.FindMaxForm.find_max_form strs m' n' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let z(s) be the number of indices j with 0 <= j < len(s) and s[j] = 48, and let o(s) be the number of indices j with 0 <= j < len(s) and s[j] = 49. Suppose len(strs) >= 2 and fix an index i with 0 <= i < len(strs) such that z(strs[i]) > m or o(strs[i]) > n. Let strs' be the slice obtained from strs by deleting position i, so len(strs') = len(strs)-1 and strs'[j] = strs[j] for j < i and strs'[j] = strs[j+1] for j >= i. Then the function returns the same result on strs' and on strs.
  Preconditions: The slice strs satisfies 1 <= len(strs) <= 600. For every i with 0 <= i < len(strs), the vector strs[i] satisfies 1 <= len(strs[i]) <= 100 and every byte of strs[i] is either 48 ('0') or 49 ('1'). The integers m and n satisfy 1 <= m <= 100 and 1 <= n <= 100. -/
theorem spec_15 (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hlen2 : 2 ≤ strs.val.length)
    (i : Nat) (hi : i < strs.val.length)
    (hbig : m.val < (zerosAt strs i : Int) ∨ n.val < (onesAt strs i : Int))
    (strs' : Slice (alloc.vec.Vec U8))
    (hlen' : strs'.val.length = strs.val.length - 1)
    (hbefore : ∀ j : Nat, j < i → strs'.val[j]? = strs.val[j]?)
    (hafter : ∀ j : Nat, i ≤ j → strs'.val[j]? = strs.val[j + 1]?) :
    Aegis.FindMaxForm.find_max_form strs' m n = Aegis.FindMaxForm.find_max_form strs m n := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec U8)) (m n : I64)
    (hlen : 1 ≤ strs.val.length ∧ strs.val.length ≤ 600)
    (hstrs : ∀ (i : Nat) (s : alloc.vec.Vec U8), strs.val[i]? = some s → IsBinaryString s)
    (hm : 1 ≤ m.val ∧ m.val ≤ 100) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (hlen2 : 2 ≤ strs.val.length)
    (i : Nat) (hi : i < strs.val.length)
    (hbig : m.val < (zerosAt strs i : Int) ∨ n.val < (onesAt strs i : Int))
    (strs' : Slice (alloc.vec.Vec U8))
    (hlen' : strs'.val.length = strs.val.length - 1)
    (hbefore : ∀ j : Nat, j < i → strs'.val[j]? = strs.val[j]?)
    (hafter : ∀ j : Nat, i ≤ j → strs'.val[j]? = strs.val[j + 1]?), Aegis.FindMaxForm.find_max_form strs' m n = Aegis.FindMaxForm.find_max_form strs m n) := by
  sorry

end AegisSpec.FindMaxForm
