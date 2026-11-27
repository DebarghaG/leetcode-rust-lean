import Aegis.NumberOfSubstrings.Code.Funs

/-!
# Specifications of `Aegis.NumberOfSubstrings.number_of_substrings`

LeetCode problem `count-substrings-with-k-frequency-characters-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumberOfSubstrings

abbrev number_of_substrings := Aegis.NumberOfSubstrings.number_of_substrings

def byteAt (s : Slice Std.U8) (t : Nat) : Nat :=
  ((s.val[t]?).map (fun b => b.val)).getD 0

def windowValues (s : Slice Std.U8) (i j : Nat) : Finset Nat :=
  (Finset.Icc i j).image (fun t => byteAt s t)

def windowCount (s : Slice Std.U8) (c i j : Nat) : Nat :=
  ((Finset.Icc i j).filter (fun t => byteAt s t = c)).card

def countOcc (s : Slice Std.U8) (c : Nat) : Nat :=
  (s.val.filter (fun b => b.val == c)).length

abbrev windowHasK (s : Slice Std.U8) (k : Int) (i j : Nat) : Prop :=
  ∃ c ∈ windowValues s i j, k ≤ (windowCount s c i j : Int)

def countSubstrings (s : Slice Std.U8) (k : Int) : Int :=
  ((((Finset.range s.val.length).product (Finset.range s.val.length)).filter
      (fun p => p.1 ≤ p.2 ∧ windowHasK s k p.1 p.2)).card : Int)

def maxOcc (s : Slice Std.U8) : Nat :=
  ((s.val.map (fun b => b.val)).toFinset).sup (fun c => countOcc s c)

def excessSum (s : Slice Std.U8) (k : Int) : Int :=
  ((s.val.map (fun b => b.val)).toFinset).sum
    (fun c => max 0 ((countOcc s c : Int) - k + 1))

/-- Whenever the function returns a result res, res equals the number of pairs (i,j) of integers such that 0 <= i <= j < len(s) and there exists a byte c with #{t | i <= t <= j and s[t] = c} >= k. Equivalently, res is the number of nonempty contiguous substrings s[i..j] (inclusive, 0-indexed) in which some character occurs at least k times within that substring.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). -/
theorem spec_1 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res → res.val = countSubstrings s k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res → res.val = countSubstrings s k.val) := by
  sorry

/-- The function returns a result res and does not fail (no arithmetic overflow, index out of bounds, or panic) for every input satisfying the preconditions.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). -/
theorem spec_2 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)) :
    ∃ res : Std.I64, number_of_substrings s k = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)), ∃ res : Std.I64, number_of_substrings s k = ok res) := by
  sorry

/-- Whenever the function returns a result res, res <= (len(s)-k+1)*(len(s)-k+2)/2.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). -/
theorem spec_3 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val ≤ ((s.val.length : Int) - k.val + 1) * ((s.val.length : Int) - k.val + 2) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val ≤ ((s.val.length : Int) - k.val + 1) * ((s.val.length : Int) - k.val + 2) / 2) := by
  sorry

/-- Whenever the function returns a result res, res = len(s)*(len(s)+1)/2.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with k = 1; note this already implies 1 <= k <= len(s). -/
theorem spec_4 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : k.val = 1) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val = (s.val.length : Int) * ((s.val.length : Int) + 1) / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : k.val = 1), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val = (s.val.length : Int) * ((s.val.length : Int) + 1) / 2) := by
  sorry

/-- Whenever the function returns a result res, res = 1 if for all t with 0 <= t < len(s) we have s[t] = s[0], and res = 0 otherwise.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with k = len(s). -/
theorem spec_5 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : k.val = (s.val.length : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        ((∀ t, t < s.val.length → byteAt s t = byteAt s 0) → res.val = 1) ∧
        ((¬ ∀ t, t < s.val.length → byteAt s t = byteAt s 0) → res.val = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : k.val = (s.val.length : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        ((∀ t, t < s.val.length → byteAt s t = byteAt s 0) → res.val = 1) ∧
        ((¬ ∀ t, t < s.val.length → byteAt s t = byteAt s 0) → res.val = 0)) := by
  sorry

/-- Whenever the function returns a result res, res = (len(s)-k+1)*(len(s)-k+2)/2.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s); there exists a byte c such that s[t] = c for every 0 <= t < len(s). -/
theorem spec_6 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hconst : ∃ c : Nat, ∀ t, t < s.val.length → byteAt s t = c) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val = ((s.val.length : Int) - k.val + 1) * ((s.val.length : Int) - k.val + 2) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hconst : ∃ c : Nat, ∀ t, t < s.val.length → byteAt s t = c), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        res.val = ((s.val.length : Int) - k.val + 1) * ((s.val.length : Int) - k.val + 2) / 2) := by
  sorry

/-- Whenever the function returns a result res, res = 0.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 2 <= k <= len(s); for all i,j with 0 <= i < j < len(s), s[i] != s[j]. -/
theorem spec_7 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 2 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hdistinct : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res → res.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 2 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hdistinct : ∀ i j, i < j → j < s.val.length → byteAt s i ≠ byteAt s j), ∀ res : Std.I64,
      number_of_substrings s k = ok res → res.val = 0) := by
  sorry

/-- Whenever the function returns a result res, res > 0 if and only if there exists a byte c such that #{t | 0 <= t < len(s) and s[t] = c} >= k.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). -/
theorem spec_8 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        (0 < res.val ↔ ∃ c : Nat, k.val ≤ (countOcc s c : Int)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        (0 < res.val ↔ ∃ c : Nat, k.val ≤ (countOcc s c : Int))) := by
  sorry

/-- Whenever the function returns a result res, if M >= k then res >= M - k + 1.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). Let M = max over bytes c of #{t | 0 <= t < len(s) and s[t] = c}. -/
theorem spec_9 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hM : k.val ≤ (maxOcc s : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        (maxOcc s : Int) - k.val + 1 ≤ res.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hM : k.val ≤ (maxOcc s : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res →
        (maxOcc s : Int) - k.val + 1 ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res1 for the input (s,k1) and a result res2 for the input (s,k2), res2 <= res1.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k1 and k2 are 64-bit integers with 1 <= k1 <= k2 <= len(s). -/
theorem spec_10 (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk1 : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (s.val.length : Int)) :
    ∀ res1 res2 : Std.I64,
      number_of_substrings s k1 = ok res1 →
        number_of_substrings s k2 = ok res2 → res2.val ≤ res1.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8) (k1 k2 : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk1 : 1 ≤ k1.val)
    (hk12 : k1.val ≤ k2.val)
    (hk2 : k2.val ≤ (s.val.length : Int)), ∀ res1 res2 : Std.I64,
      number_of_substrings s k1 = ok res1 →
        number_of_substrings s k2 = ok res2 → res2.val ≤ res1.val) := by
  sorry

/-- Whenever the function returns a result res for the input (s,k) and a result res' for the input (t,k), res = res'.
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). Let n = len(s) and let t be the byte string with len(t) = n and t[u] = s[n-1-u] for all 0 <= u < n. -/
theorem spec_11 (s t : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ u, u < s.val.length → 97 ≤ byteAt s u ∧ byteAt s u ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hlen_t : t.val.length = s.val.length)
    (ht : ∀ u, u < t.val.length → byteAt t u = byteAt s (s.val.length - 1 - u)) :
    ∀ res res' : Std.I64,
      number_of_substrings s k = ok res →
        number_of_substrings t k = ok res' → res.val = res'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ u, u < s.val.length → 97 ≤ byteAt s u ∧ byteAt s u ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hlen_t : t.val.length = s.val.length)
    (ht : ∀ u, u < t.val.length → byteAt t u = byteAt s (s.val.length - 1 - u)), ∀ res res' : Std.I64,
      number_of_substrings s k = ok res →
        number_of_substrings t k = ok res' → res.val = res'.val) := by
  sorry

/-- Let f(c) = #{t | 0 <= t < len(s) and s[t] = c} for each byte c. Whenever the function returns a result res, res >= sum over all bytes c of max(0, f(c) - k + 1).
  Preconditions: len(s) is an integer with 1 <= len(s) <= 3000; every byte s[t] for 0 <= t < len(s) is an ASCII lowercase letter (97 <= s[t] <= 122); k is a 64-bit integer with 1 <= k <= len(s). -/
theorem spec_12 (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)) :
    ∀ res : Std.I64,
      number_of_substrings s k = ok res → excessSum s k.val ≤ res.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8) (k : Std.I64)
    (hlen : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlower : ∀ t, t < s.val.length → 97 ≤ byteAt s t ∧ byteAt s t ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int)), ∀ res : Std.I64,
      number_of_substrings s k = ok res → excessSum s k.val ≤ res.val) := by
  sorry

/-- Whenever the function returns a result res for the input (s,k) and a result res' for the input (t,k), res <= res'.
  Preconditions: len(s) and len(t) are integers with 1 <= len(s) <= len(t) <= 3000; every byte of s and t is an ASCII lowercase letter; k is a 64-bit integer with 1 <= k <= len(s); and t[u] = s[u] for all 0 <= u < len(s) (so s is a prefix of t). -/
theorem spec_13 (s t : Slice Std.U8) (k : Std.I64)
    (hlen_s : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlen_t : 1 ≤ t.val.length ∧ t.val.length ≤ 3000)
    (hlen_le : s.val.length ≤ t.val.length)
    (hlower_s : ∀ u, u < s.val.length → 97 ≤ byteAt s u ∧ byteAt s u ≤ 122)
    (hlower_t : ∀ u, u < t.val.length → 97 ≤ byteAt t u ∧ byteAt t u ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hprefix : ∀ u, u < s.val.length → byteAt t u = byteAt s u) :
    ∀ res res' : Std.I64,
      number_of_substrings s k = ok res →
        number_of_substrings t k = ok res' → res.val ≤ res'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s t : Slice Std.U8) (k : Std.I64)
    (hlen_s : 1 ≤ s.val.length ∧ s.val.length ≤ 3000)
    (hlen_t : 1 ≤ t.val.length ∧ t.val.length ≤ 3000)
    (hlen_le : s.val.length ≤ t.val.length)
    (hlower_s : ∀ u, u < s.val.length → 97 ≤ byteAt s u ∧ byteAt s u ≤ 122)
    (hlower_t : ∀ u, u < t.val.length → 97 ≤ byteAt t u ∧ byteAt t u ≤ 122)
    (hk : 1 ≤ k.val ∧ k.val ≤ (s.val.length : Int))
    (hprefix : ∀ u, u < s.val.length → byteAt t u = byteAt s u), ∀ res res' : Std.I64,
      number_of_substrings s k = ok res →
        number_of_substrings t k = ok res' → res.val ≤ res'.val) := by
  sorry

end AegisSpec.NumberOfSubstrings
