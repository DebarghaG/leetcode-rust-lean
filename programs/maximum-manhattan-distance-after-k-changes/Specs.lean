import Aegis.MaxDistance.Code.Funs

/-!
# Specifications of `Aegis.MaxDistance.max_distance`

LeetCode problem `maximum-manhattan-distance-after-k-changes`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxDistance

def DirByte (c : U8) : Prop :=
  c.val = 78 ∨ c.val = 83 ∨ c.val = 69 ∨ c.val = 87

def countOf (b : ℕ) : List U8 → ℕ
  | [] => 0
  | c :: cs => (if c.val = b then 1 else 0) + countOf b cs

def dist (l : List U8) : ℤ :=
  |(countOf 69 l : ℤ) - (countOf 87 l : ℤ)| + |(countOf 78 l : ℤ) - (countOf 83 l : ℤ)|

noncomputable def maxOver (N : ℕ) (f : ℕ → ℤ) : ℤ :=
  (Finset.range (N + 1)).sup' ⟨0, by simp⟩ f

noncomputable def specValue (l : List U8) (k : ℤ) : ℤ :=
  maxOver l.length (fun m => min (m : ℤ) (dist (l.take m) + 2 * k))

noncomputable def maxPlainDist (l : List U8) : ℤ :=
  maxOver l.length (fun m => dist (l.take m))

def diffCount : List U8 → List U8 → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | a :: al, b :: bl => (if a = b then 0 else 1) + diffCount al bl

def sliceOfList (l : List U8) (h : l.length ≤ Aeneas.Std.Usize.max) : Slice U8 :=
  ⟨l.length, Aeneas.Data.ListN.ListN.fromList l, h⟩

theorem sliceOfList_val (l : List U8) (h : l.length ≤ Aeneas.Std.Usize.max) :
    (sliceOfList l h).val = l := by
  exact Aeneas.Data.ListN.ListN.from_to_inverse

theorem slice_val_length (s : Slice U8) : s.val.length = s.leng :=
  Aeneas.Data.ListN.ListN_length s.list

def rotByte (c : U8) : U8 :=
  if c.val = 78 then 69#u8
  else if c.val = 69 then 83#u8
  else if c.val = 83 then 87#u8
  else if c.val = 87 then 78#u8
  else c

def rot (s : Slice U8) : Slice U8 :=
  sliceOfList (s.val.map rotByte) (by
    simp only [List.length_map, slice_val_length]
    exact s.bound)

theorem rot_val (s : Slice U8) : (rot s).val = s.val.map rotByte := by
  simp [rot, sliceOfList_val]

def flipByte (c : U8) : U8 :=
  if c.val = 78 then 83#u8 else if c.val = 83 then 78#u8 else c

def flip (s : Slice U8) : Slice U8 :=
  sliceOfList (s.val.map flipByte) (by
    simp only [List.length_map, slice_val_length]
    exact s.bound)

theorem flip_val (s : Slice U8) : (flip s).val = s.val.map flipByte := by
  simp [flip, sliceOfList_val]

/-- Whenever the preconditions hold, the function returns a result r and r = max over all integers m with 0 <= m <= n of min(m, |E_m - W_m| + |N_m - S_m| + 2*k), where for each m, E_m, W_m, N_m, S_m are the numbers of bytes 'E', 'W', 'N', 'S' among the first m bytes s[0],...,s[m-1] (all four counts are 0 for m=0), and min denotes the smaller integer. This is the largest Manhattan distance from the origin attainable after changing at most k characters of s to any of 'N','S','E','W' and performing the changed moves in order, at some time after processing a prefix of length m (including m=0, whose distance is 0).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_1 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∃ r : I64, Aegis.MaxDistance.max_distance s k = ok r ∧ r.val = specValue s.val k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∃ r : I64, Aegis.MaxDistance.max_distance s k = ok r ∧ r.val = specValue s.val k.val) := by
  sorry

/-- Whenever the preconditions hold, the function returns a result r; in particular, it does not fail because of integer overflow, out-of-bounds indexing, or a panic on any valid input.
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_2 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∃ r : I64, Aegis.MaxDistance.max_distance s k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∃ r : I64, Aegis.MaxDistance.max_distance s k = ok r) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, 0 <= r.
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_3 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r → 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r <= n = len(s).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_4 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r → r.val ≤ (s.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r → r.val ≤ (s.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r >= min(n, 2*k).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_5 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      min (s.val.length : ℤ) (2 * k.val) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      min (s.val.length : ℤ) (2 * k.val) ≤ r.val) := by
  sorry

/-- For every integer m with 0 <= m <= n, let E_m, W_m, N_m, S_m be the numbers of 'E','W','N','S' among s[0],...,s[m-1] (all zero for m=0). Whenever the function returns a result r under the preconditions, r >= min(m, |E_m - W_m| + |N_m - S_m| + 2*k).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_6 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∀ m : ℕ, m ≤ s.val.length →
        min (m : ℤ) (dist (s.val.take m) + 2 * k.val) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∀ m : ℕ, m ≤ s.val.length →
        min (m : ℤ) (dist (s.val.take m) + 2 * k.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, there exist an integer m with 0 <= m <= n and a byte string t of length n whose bytes are all in {'N','S','E','W'} such that t differs from s in at most k positions and |E'_m - W'_m| + |N'_m - S'_m| = r, where E'_m, W'_m, N'_m, S'_m are the numbers of 'E','W','N','S' among t[0],...,t[m-1] (all zero for m=0).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_7 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∃ (m : ℕ) (t : Slice U8),
        m ≤ s.val.length ∧ t.val.length = s.val.length ∧
        (∀ c ∈ t.val, DirByte c) ∧ (diffCount t.val s.val : ℤ) ≤ k.val ∧
        dist (t.val.take m) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∃ (m : ℕ) (t : Slice U8),
        m ≤ s.val.length ∧ t.val.length = s.val.length ∧
        (∀ c ∈ t.val, DirByte c) ∧ (diffCount t.val s.val : ℤ) ≤ k.val ∧
        dist (t.val.take m) = r.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, for every integer m with 0 <= m <= n and every byte string t of length n whose bytes are all in {'N','S','E','W'} and which differs from s in at most k positions, |E'_m - W'_m| + |N'_m - S'_m| <= r, where E'_m, W'_m, N'_m, S'_m are the numbers of 'E','W','N','S' among t[0],...,t[m-1] (all zero for m=0).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_8 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∀ (m : ℕ) (t : Slice U8), m ≤ s.val.length → t.val.length = s.val.length →
        (∀ c ∈ t.val, DirByte c) → (diffCount t.val s.val : ℤ) ≤ k.val →
        dist (t.val.take m) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      ∀ (m : ℕ) (t : Slice U8), m ≤ s.val.length → t.val.length = s.val.length →
        (∀ c ∈ t.val, DirByte c) → (diffCount t.val s.val : ℤ) ≤ k.val →
        dist (t.val.take m) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, r = n if and only if min(E_n, W_n) + min(N_n, S_n) <= k, where E_n, W_n, N_n, S_n are the total numbers of 'E','W','N','S' in the whole string s.
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_9 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      (r.val = (s.val.length : ℤ) ↔
        ((min (countOf 69 s.val) (countOf 87 s.val) +
            min (countOf 78 s.val) (countOf 83 s.val) : ℕ) : ℤ) ≤ k.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      (r.val = (s.val.length : ℤ) ↔
        ((min (countOf 69 s.val) (countOf 87 s.val) +
            min (countOf 78 s.val) (countOf 83 s.val) : ℕ) : ℤ) ≤ k.val)) := by
  sorry

/-- Both calls max_distance(s, k1) and max_distance(s, k2) return results r1 and r2, and r1 <= r2.
  Preconditions: Let n = len(s). We have 1 <= n <= 100000, every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'), and k1 and k2 are integers with 0 <= k1 <= k2 <= n. -/
theorem spec_10 (s : Slice U8) (k1 k2 : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∃ r1 r2 : I64,
      Aegis.MaxDistance.max_distance s k1 = ok r1 ∧
      Aegis.MaxDistance.max_distance s k2 = ok r2 ∧ r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice U8) (k1 k2 : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2 : k2.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∃ r1 r2 : I64,
      Aegis.MaxDistance.max_distance s k1 = ok r1 ∧
      Aegis.MaxDistance.max_distance s k2 = ok r2 ∧ r1.val ≤ r2.val) := by
  sorry

/-- Define rot(s) by replacing each byte as follows: 'N' -> 'E', 'E' -> 'S', 'S' -> 'W', and 'W' -> 'N'. Then max_distance(rot(s), k) returns the same result as max_distance(s, k).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_11 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    Aegis.MaxDistance.max_distance (rot s) k = Aegis.MaxDistance.max_distance s k := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), Aegis.MaxDistance.max_distance (rot s) k = Aegis.MaxDistance.max_distance s k) := by
  sorry

/-- Define flip(s) by replacing 'N' with 'S', 'S' with 'N', and leaving 'E' and 'W' unchanged. Then max_distance(flip(s), k) returns the same result as max_distance(s, k).
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_12 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    Aegis.MaxDistance.max_distance (flip s) k = Aegis.MaxDistance.max_distance s k := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), Aegis.MaxDistance.max_distance (flip s) k = Aegis.MaxDistance.max_distance s k) := by
  sorry

/-- Both calls max_distance(s, k) and max_distance(t, k) return results r_s and r_t, and r_s <= r_t.
  Preconditions: Let s and t be strings satisfying the byte precondition (only 'N','S','E','W') with 1 <= len(s) <= len(t) <= 100000, and let k be an integer with 0 <= k <= len(s). Suppose s[i] = t[i] for every i with 0 <= i < len(s), so s is a prefix of t. -/
theorem spec_13 (s t : Slice U8) (k : I64)
    (hs1 : 1 ≤ s.val.length) (hst : s.val.length ≤ t.val.length)
    (ht2 : t.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hsbytes : ∀ c ∈ s.val, DirByte c) (htbytes : ∀ c ∈ t.val, DirByte c)
    (hpre : ∀ i : ℕ, i < s.val.length → t.val[i]? = s.val[i]?) :
    ∃ rs rt : I64,
      Aegis.MaxDistance.max_distance s k = ok rs ∧
      Aegis.MaxDistance.max_distance t k = ok rt ∧ rs.val ≤ rt.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice U8) (k : I64)
    (hs1 : 1 ≤ s.val.length) (hst : s.val.length ≤ t.val.length)
    (ht2 : t.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hsbytes : ∀ c ∈ s.val, DirByte c) (htbytes : ∀ c ∈ t.val, DirByte c)
    (hpre : ∀ i : ℕ, i < s.val.length → t.val[i]? = s.val[i]?), ∃ rs rt : I64,
      Aegis.MaxDistance.max_distance s k = ok rs ∧
      Aegis.MaxDistance.max_distance t k = ok rt ∧ rs.val ≤ rt.val) := by
  sorry

/-- Whenever the function returns a result r under the preconditions, let A0 = max over all integers m with 0 <= m <= n of (|E_m - W_m| + |N_m - S_m|), where E_m, W_m, N_m, S_m are the numbers of 'E','W','N','S' among the original first m bytes of s. Then r <= A0 + 2*k.
  Preconditions: Let n = len(s). The input satisfies 1 <= n <= 100000, 0 <= k <= n, and every byte of s is one of the ASCII codes 78 ('N'), 83 ('S'), 69 ('E'), 87 ('W'). -/
theorem spec_14 (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c) :
    ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      r.val ≤ maxPlainDist s.val + 2 * k.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice U8) (k : I64)
    (hn1 : 1 ≤ s.val.length) (hn2 : s.val.length ≤ 100000)
    (hk1 : 0 ≤ k.val) (hk2 : k.val ≤ (s.val.length : ℤ))
    (hbytes : ∀ c ∈ s.val, DirByte c), ∀ r : I64, Aegis.MaxDistance.max_distance s k = ok r →
      r.val ≤ maxPlainDist s.val + 2 * k.val) := by
  sorry

end AegisSpec.MaxDistance
