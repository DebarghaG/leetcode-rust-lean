import Aegis.CountTriplets.Code.Funs

/-!
# Specifications of `Aegis.CountTriplets.count_triplets`

LeetCode problem `count-triplets-that-can-form-two-arrays-of-equal-xor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountTriplets

def values (arr : Slice Std.I64) : List Int := arr.val.map (fun x => x.val)

def xorInt (a b : Int) : Int := Int.ofNat (a.toNat ^^^ b.toNat)

def xorRange (l : List Int) (i k : Nat) : Int := ((l.drop i).take (k - i)).foldr xorInt 0

def prefixXor (l : List Int) (t : Nat) : Int := xorRange l 0 t

def tripleSet (l : List Int) : Finset (Nat × Nat × Nat) :=
  ((Finset.range l.length) ×ˢ ((Finset.range l.length) ×ˢ (Finset.range l.length))).filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 ≤ p.2.2 ∧
      xorRange l p.1 p.2.1 = xorRange l p.2.1 (p.2.2 + 1))

def zeroXorPairs (l : List Int) : Finset (Nat × Nat) :=
  ((Finset.range l.length) ×ˢ (Finset.range l.length)).filter
    (fun p => p.1 < p.2 ∧ xorRange l p.1 (p.2 + 1) = 0)

def zeroXorPairSum (l : List Int) : Int :=
  ∑ p ∈ zeroXorPairs l, ((p.2 : Int) - (p.1 : Int))

def equalPrefixPairs (l : List Int) : Finset (Nat × Nat) :=
  ((Finset.range (l.length + 1)) ×ˢ (Finset.range (l.length + 1))).filter
    (fun p => p.1 < p.2 ∧ prefixXor l p.1 = prefixXor l p.2)

def equalPrefixPairSum (l : List Int) : Int :=
  ∑ p ∈ equalPrefixPairs l, ((p.2 : Int) - (p.1 : Int) - 1)

def evenBlockSum (n : Nat) : Int :=
  ∑ s ∈ (Finset.range (n + 1)).filter (fun s => s % 2 = 0 ∧ 2 ≤ s),
    (((s : Int) - 1) * ((n : Int) - (s : Int) + 1))

def revSlice (arr : Slice Std.I64) : Slice Std.I64 :=
  Slice.from arr.val.reverse (by simp)

/-- Whenever the function returns a result r, r is the number of integer triples (i,j,k) such that 0 <= i < j <= k < n and arr[i] ^ arr[i+1] ^ ... ^ arr[j-1] = arr[j] ^ arr[j+1] ^ ... ^ arr[k], where ^ denotes bitwise exclusive-or. Equivalently, r is the cardinality of the set of all such triples.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and for every t with 0 <= t < n, arr[t] is an integer with 1 <= arr[t] <= 10^8. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_1 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000) :
    ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = ((tripleSet (values arr)).card : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000), ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = ((tripleSet (values arr)).card : Int)) := by
  sorry

/-- The function returns a result r on every input satisfying the preconditions; in particular, it does not overflow, access outside the slice, or panic.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and for every t with 0 <= t < n, arr[t] is an integer with 1 <= arr[t] <= 10^8. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_2 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000) :
    ∃ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000), ∃ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = sum over all integer pairs (i,k) with 0 <= i < k < n and arr[i] ^ arr[i+1] ^ ... ^ arr[k] = 0 of (k - i). If there is no such pair, the sum is 0.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and for every t with 0 <= t < n, arr[t] is an integer with 1 <= arr[t] <= 10^8. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_3 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000) :
    ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = zeroXorPairSum (values arr) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000), ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = zeroXorPairSum (values arr)) := by
  sorry

/-- Let P[0] = 0 and, for 1 <= t <= n, let P[t] = arr[0] ^ arr[1] ^ ... ^ arr[t-1]. Whenever the function returns a result r, r = sum over all integer pairs (a,b) with 0 <= a < b <= n and P[a] = P[b] of (b - a - 1). Pairs with b = a + 1 contribute 0; if there is no such pair, the sum is 0.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and for every t with 0 <= t < n, arr[t] is an integer with 1 <= arr[t] <= 10^8. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_4 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000) :
    ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = equalPrefixPairSum (values arr) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000), ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = equalPrefixPairSum (values arr)) := by
  sorry

/-- Let rev be the slice of length n defined by rev[t] = arr[n-1-t] for 0 <= t < n. Whenever count_triplets(arr) returns r and count_triplets(rev) returns r', we have r = r'.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and for every t with 0 <= t < n, arr[t] is an integer with 1 <= arr[t] <= 10^8. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_5 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000) :
    ∀ r r' : Std.I64,
      Aegis.CountTriplets.count_triplets arr = ok r →
      Aegis.CountTriplets.count_triplets (revSlice arr) = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hentries : ∀ (t : Nat) (ht : t < arr.val.length),
      1 ≤ (arr.val.get ⟨t, ht⟩).val ∧ (arr.val.get ⟨t, ht⟩).val ≤ 100000000), ∀ r r' : Std.I64,
      Aegis.CountTriplets.count_triplets arr = ok r →
      Aegis.CountTriplets.count_triplets (revSlice arr) = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, r = sum over all even integers s with 2 <= s <= n of (s - 1) * (n - s + 1). If no such even s exists, the sum is 0.
  Preconditions: Let n = len(arr). The slice arr is 0-indexed and satisfies 1 <= n <= 300, and there is an integer c with 1 <= c <= 10^8 such that arr[t] = c for every t with 0 <= t < n. All arithmetic in this specification is exact mathematical integer arithmetic. -/
theorem spec_6 (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hconst : ∃ c : Int, 1 ≤ c ∧ c ≤ 100000000 ∧
      ∀ (t : Nat) (ht : t < arr.val.length), (arr.val.get ⟨t, ht⟩).val = c) :
    ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = evenBlockSum arr.val.length := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64)
    (hlen_pos : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 300)
    (hconst : ∃ c : Int, 1 ≤ c ∧ c ≤ 100000000 ∧
      ∀ (t : Nat) (ht : t < arr.val.length), (arr.val.get ⟨t, ht⟩).val = c), ∀ r : Std.I64, Aegis.CountTriplets.count_triplets arr = ok r →
      r.val = evenBlockSum arr.val.length) := by
  sorry

end AegisSpec.CountTriplets
