import Aegis.GetStrongest.Code.Funs

/-!
# Specifications of `Aegis.GetStrongest.get_strongest`

LeetCode problem `the-k-strongest-values-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.GetStrongest

set_option autoImplicit false

def i64Vals (l : List Std.I64) : List ℤ := l.map fun a => a.val

def arrVals (arr : Slice Std.I64) : List ℤ := i64Vals arr.val

def vecVals (r : alloc.vec.Vec Std.I64) : List ℤ := i64Vals r.val

def sortedVals (arr : Slice Std.I64) : List ℤ := (arrVals arr).insertionSort (· ≤ ·)

def medianIndex (arr : Slice Std.I64) : ℕ := (arr.val.length - 1) / 2

def medianVal (arr : Slice Std.I64) : ℤ := (sortedVals arr).getD (medianIndex arr) 0

def dist (m x : ℤ) : ℤ := |x - m|

def strengthLe (m x y : ℤ) : Prop := dist m y < dist m x ∨ (dist m x = dist m y ∧ y ≤ x)

def stronger (m x y : ℤ) : Prop := dist m y < dist m x ∨ (dist m x = dist m y ∧ y < x)

def countOcc (l : List ℤ) (v : ℤ) : ℕ := (l.filter fun a => a = v).length

def listMin (l : List ℤ) : ℤ := l.foldr min (l.headD 0)

def listMax (l : List ℤ) : ℤ := l.foldr max (l.headD 0)

def kNat (k : Std.I64) : ℕ := k.val.toNat

/-- Let s be the nondecreasing sorted list of the n values arr[0],...,arr[n-1], and let m = s[(n-1) div 2], where div denotes floor division. For any value x let d(x)=|x-m|. Let L be any list formed from all n occurrences of the input values by arranging them so that whenever an occurrence of x precedes an occurrence of y, either d(x)>d(y), or d(x)=d(y) and x>=y. Whenever get_strongest(arr,k) returns a result r, r is a permutation of the first k entries of L. Equivalently, r has exactly the multiset of the k strongest occurrences of arr under the strength order: greater d first, and for equal d greater value first.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_1 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ (L : List ℤ), (arrVals arr).Perm L → L.Pairwise (strengthLe (medianVal arr)) →
      ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
        (vecVals r).Perm (L.take (kNat k)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ (L : List ℤ), (arrVals arr).Perm L → L.Pairwise (strengthLe (medianVal arr)) →
      ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
        (vecVals r).Perm (L.take (kNat k))) := by
  sorry

/-- For every arr and k satisfying the preconditions, get_strongest(arr,k) returns a normal result r. In particular, it does not fail, panic, go out of bounds, or overflow during the computation.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_2 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r, len(r) equals k, where k is interpreted as its non-negative integer value.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_3 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      r.val.length = kNat k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      r.val.length = kNat k) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r, for every integer value v, the number of occurrences of v in r is at most the number of occurrences of v in arr.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_4 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ v : ℤ, countOcc (vecVals r) v ≤ countOcc (arrVals arr) v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ v : ℤ, countOcc (vecVals r) v ≤ countOcc (arrVals arr) v) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r, there exists an injective function f from {0,1,...,k-1} to {0,1,...,n-1} such that r[i] = arr[f(i)] for every i with 0 <= i < k. Thus each output occurrence is witnessed by a distinct input occurrence.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_5 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∃ f : Fin (kNat k) → Fin arr.val.length, Function.Injective f ∧
        ∀ i : Fin (kNat k),
          (r.val[i.val]?).map (fun a => a.val) = some ((arr.val.get (f i)).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∃ f : Fin (kNat k) → Fin arr.val.length, Function.Injective f ∧
        ∀ i : Fin (kNat k),
          (r.val[i.val]?).map (fun a => a.val) = some ((arr.val.get (f i)).val)) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r, for every i with 0 <= i < len(r), min(arr) <= r[i] <= max(arr), where min(arr) and max(arr) are the minimum and maximum of the n input values.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_6 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ (i : ℕ) (hi : i < r.val.length),
        listMin (arrVals arr) ≤ (r.val.get ⟨i, hi⟩).val ∧
          (r.val.get ⟨i, hi⟩).val ≤ listMax (arrVals arr) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ (i : ℕ) (hi : i < r.val.length),
        listMin (arrVals arr) ≤ (r.val.get ⟨i, hi⟩).val ∧
          (r.val.get ⟨i, hi⟩).val ≤ listMax (arrVals arr)) := by
  sorry

/-- Let s be the nondecreasing sorted list of arr, let m = s[(n-1) div 2], and for a value x let d(x)=|x-m|. Whenever get_strongest(arr,k) returns r, for any integers x and y such that x is strictly stronger than y (that is, d(x)>d(y), or d(x)=d(y) and x>y), if y occurs at least once in r, then x occurs in r exactly as many times as x occurs in arr.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. -/
theorem spec_7 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ x y : ℤ, stronger (medianVal arr) x y → 0 < countOcc (vecVals r) y →
        countOcc (vecVals r) x = countOcc (arrVals arr) x := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, Aegis.GetStrongest.get_strongest arr k = ok r →
      ∀ x y : ℤ, stronger (medianVal arr) x y → 0 < countOcc (vecVals r) y →
        countOcc (vecVals r) x = countOcc (arrVals arr) x) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r and get_strongest(arr',k) returns r', r' is a permutation of r.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. Let arr' be any list of length n that is a permutation of arr. -/
theorem spec_8 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ arr' : Slice Std.I64, (arrVals arr').Perm (arrVals arr) →
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.GetStrongest.get_strongest arr k = ok r →
          Aegis.GetStrongest.get_strongest arr' k = ok r' → (vecVals r').Perm (vecVals r) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ arr' : Slice Std.I64, (arrVals arr').Perm (arrVals arr) →
      ∀ (r r' : alloc.vec.Vec Std.I64),
        Aegis.GetStrongest.get_strongest arr k = ok r →
          Aegis.GetStrongest.get_strongest arr' k = ok r' → (vecVals r').Perm (vecVals r)) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r and get_strongest(arr',k) returns r', r' is a permutation of the list obtained from r by adding c to each of its k entries.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. Let c be an integer and let arr' be the list of length n with arr'[i]=arr[i]+c for every i. Assume -100000 <= arr'[i] <= 100000 for every i. -/
theorem spec_9 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ (c : ℤ) (arr' : Slice Std.I64),
      arrVals arr' = (arrVals arr).map (fun a => a + c) →
        (∀ x ∈ arr'.val, -100000 ≤ x.val ∧ x.val ≤ 100000) →
          ∀ (r r' : alloc.vec.Vec Std.I64),
            Aegis.GetStrongest.get_strongest arr k = ok r →
              Aegis.GetStrongest.get_strongest arr' k = ok r' →
                (vecVals r').Perm ((vecVals r).map (fun a => a + c)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ (c : ℤ) (arr' : Slice Std.I64),
      arrVals arr' = (arrVals arr).map (fun a => a + c) →
        (∀ x ∈ arr'.val, -100000 ≤ x.val ∧ x.val ≤ 100000) →
          ∀ (r r' : alloc.vec.Vec Std.I64),
            Aegis.GetStrongest.get_strongest arr k = ok r →
              Aegis.GetStrongest.get_strongest arr' k = ok r' →
                (vecVals r').Perm ((vecVals r).map (fun a => a + c))) := by
  sorry

/-- Whenever get_strongest(arr,k) returns r and get_strongest(arr',k) returns r', r' is a permutation of the list obtained from r by multiplying each of its k entries by c.
  Preconditions: Let n = len(arr). Assume 1 <= n <= 100000, 1 <= k <= n, and for every i with 0 <= i < n, -100000 <= arr[i] <= 100000. Let c be an integer with c>0 and let arr' be the list of length n with arr'[i]=c*arr[i] for every i. Assume -100000 <= arr'[i] <= 100000 for every i. -/
theorem spec_10 (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ (c : ℤ), 0 < c → ∀ arr' : Slice Std.I64,
      arrVals arr' = (arrVals arr).map (fun a => c * a) →
        (∀ x ∈ arr'.val, -100000 ≤ x.val ∧ x.val ≤ 100000) →
          ∀ (r r' : alloc.vec.Vec Std.I64),
            Aegis.GetStrongest.get_strongest arr k = ok r →
              Aegis.GetStrongest.get_strongest arr' k = ok r' →
                (vecVals r').Perm ((vecVals r).map (fun a => c * a)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
    (hn_pos : 1 ≤ arr.val.length) (hn_le : arr.val.length ≤ 100000)
    (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ (arr.val.length : ℤ))
    (hval : ∀ x ∈ arr.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ (c : ℤ), 0 < c → ∀ arr' : Slice Std.I64,
      arrVals arr' = (arrVals arr).map (fun a => c * a) →
        (∀ x ∈ arr'.val, -100000 ≤ x.val ∧ x.val ≤ 100000) →
          ∀ (r r' : alloc.vec.Vec Std.I64),
            Aegis.GetStrongest.get_strongest arr k = ok r →
              Aegis.GetStrongest.get_strongest arr' k = ok r' →
                (vecVals r').Perm ((vecVals r).map (fun a => c * a))) := by
  sorry

end AegisSpec.GetStrongest
