import Aegis.FindClosestElements.Code.Funs

/-!
# Specifications of `Aegis.FindClosestElements.find_closest_elements`

LeetCode problem `find-k-closest-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aeneas.Std.Result

namespace AegisSpec.FindClosestElements

def slvals (s : Slice Std.I64) : List ℤ := s.val.map (fun v => v.val)

def vecvals (v : alloc.vec.Vec Std.I64) : List ℤ := v.val.map (fun w => w.val)

def lenI (l : List ℤ) : ℤ := (l.length : ℤ)

def Sorted (l : List ℤ) : Prop :=
  ∀ (i j : ℕ), i < j → (hi : i < l.length) → (hj : j < l.length) → l[i] ≤ l[j]

def InRange (l : List ℤ) : Prop :=
  ∀ (i : ℕ) (hi : i < l.length), -10000 ≤ l[i] ∧ l[i] ≤ 10000

def countOf (l : List ℤ) (v : ℤ) : ℕ := (l.filter fun w => w = v).length

def absDiff (t x : ℤ) : ℕ := (t - x).natAbs

def keyLe (x a b : ℤ) : Prop :=
  absDiff a x < absDiff b x ∨ (absDiff a x = absDiff b x ∧ a ≤ b)

instance decidableKeyLe (x a b : ℤ) : Decidable (keyLe x a b) := by
  unfold keyLe
  infer_instance

/-- Let key(t) = (|t - x|, t), compared lexicographically. Let cnt_r(v) be the number of indices i with 0 <= i < len(r) and r[i] = v, and let cnt_arr(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v. The function returns a result r such that: (1) len(r) = k; (2) r is nondecreasing, i.e. r[i] <= r[j] for all 0 <= i < j < len(r); (3) cnt_r(v) <= cnt_arr(v) for every integer v; and (4) for all integers a,b, if cnt_r(a) > 0 and cnt_r(b) < cnt_arr(b), then key(a) <= key(b).
  Preconditions: arr is sorted in nondecreasing order (for every i,j with 0 <= i < j < len(arr), arr[i] <= arr[j]); len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; -10000 <= arr[i] <= 10000 for every 0 <= i < len(arr); and -10000 <= x <= 10000. -/
theorem spec_1 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindClosestElements.find_closest_elements arr k x = ok r ∧
      lenI (vecvals r) = k.val ∧
      Sorted (vecvals r) ∧
      (∀ v : ℤ, countOf (vecvals r) v ≤ countOf (slvals arr) v) ∧
      (∀ a b : ℤ, 0 < countOf (vecvals r) a →
        countOf (vecvals r) b < countOf (slvals arr) b → keyLe x.val a b) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindClosestElements.find_closest_elements arr k x = ok r ∧
      lenI (vecvals r) = k.val ∧
      Sorted (vecvals r) ∧
      (∀ v : ℤ, countOf (vecvals r) v ≤ countOf (slvals arr) v) ∧
      (∀ a b : ℤ, 0 < countOf (vecvals r) a →
        countOf (vecvals r) b < countOf (slvals arr) b → keyLe x.val a b)) := by
  sorry

/-- Under the preconditions, the function returns a result r; it does not fail, panic, overflow, or get stuck.
  Preconditions: arr is sorted in nondecreasing order (for every i,j with 0 <= i < j < len(arr), arr[i] <= arr[j]); len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; -10000 <= arr[i] <= 10000 for every 0 <= i < len(arr); and -10000 <= x <= 10000. -/
theorem spec_2 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindClosestElements.find_closest_elements arr k x = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.FindClosestElements.find_closest_elements arr k x = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = k.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_3 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    lenI (vecvals r) = k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), lenI (vecvals r) = k.val) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i < j < len(r), r[i] <= r[j].
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_4 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    Sorted (vecvals r) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), Sorted (vecvals r)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of occurrences of v in r is at most the number of occurrences of v in arr.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_5 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∀ v : ℤ, countOf (vecvals r) v ≤ countOf (slvals arr) v := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∀ v : ℤ, countOf (vecvals r) v ≤ countOf (slvals arr) v) := by
  sorry

/-- Whenever the function returns a result r, for every integer a that occurs at least once in r and every integer b that occurs fewer times in r than in arr, we have |a - x| < |b - x|, or |a - x| = |b - x| and a <= b.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_6 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∀ a b : ℤ, 0 < countOf (vecvals r) a →
      countOf (vecvals r) b < countOf (slvals arr) b → keyLe x.val a b := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∀ a b : ℤ, 0 < countOf (vecvals r) a →
      countOf (vecvals r) b < countOf (slvals arr) b → keyLe x.val a b) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer s with 0 <= s <= len(arr) - k such that r is exactly the length-k sequence arr[s], arr[s+1], ..., arr[s+k-1]; in particular len(r) = k and r[i] = arr[s+i] for all 0 <= i < k.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_7 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∃ s : ℕ,
      s + k.val.toNat ≤ (slvals arr).length ∧
      vecvals r = ((slvals arr).drop s).take k.val.toNat ∧
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat → (vecvals r)[i]? = (slvals arr)[s + i]?) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∃ s : ℕ,
      s + k.val.toNat ≤ (slvals arr).length ∧
      vecvals r = ((slvals arr).drop s).take k.val.toNat ∧
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat → (vecvals r)[i]? = (slvals arr)[s + i]?)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v that occurs at least once in r, every integer u with |u - x| < |v - x| occurs equally many times in r and in arr.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_8 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∀ v u : ℤ, 0 < countOf (vecvals r) v → absDiff u x.val < absDiff v x.val →
      countOf (vecvals r) u = countOf (slvals arr) u := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∀ v u : ℤ, 0 < countOf (vecvals r) v → absDiff u x.val < absDiff v x.val →
      countOf (vecvals r) u = countOf (slvals arr) u) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), arr[0] <= r[i] <= arr[len(arr)-1].
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_9 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∀ (i : ℕ) (hi : i < (vecvals r).length),
      (slvals arr)[0] ≤ (vecvals r)[i] ∧ (vecvals r)[i] ≤ (slvals arr)[(slvals arr).length - 1] := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∀ (i : ℕ) (hi : i < (vecvals r).length),
      (slvals arr)[0] ≤ (vecvals r)[i] ∧ (vecvals r)[i] ≤ (slvals arr)[(slvals arr).length - 1]) := by
  sorry

/-- Whenever the function returns a result r, if x <= arr[0], then len(r) = k and r[i] = arr[i] for every i with 0 <= i < k.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_10 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    x.val ≤ (slvals arr)[0] →
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat → (vecvals r)[i]? = (slvals arr)[i]?) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), x.val ≤ (slvals arr)[0] →
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat → (vecvals r)[i]? = (slvals arr)[i]?)) := by
  sorry

/-- Whenever the function returns a result r, if x >= arr[len(arr)-1], then len(r) = k and r[i] = arr[len(arr)-k+i] for every i with 0 <= i < k.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_11 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    (slvals arr)[(slvals arr).length - 1] ≤ x.val →
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        (vecvals r)[i]? = (slvals arr)[(slvals arr).length - k.val.toNat + i]?) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), (slvals arr)[(slvals arr).length - 1] ≤ x.val →
      lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        (vecvals r)[i]? = (slvals arr)[(slvals arr).length - k.val.toNat + i]?)) := by
  sorry

/-- Consider two calls with the same arr and k, using x = x1 and x = x2. If the first call returns r1 and the second returns r2, then len(r1) = len(r2) = k and for every i with 0 <= i < k, r1[i] <= r2[i].
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values satisfy -10000 <= arr[i] <= 10000; and x1 <= x2 both satisfy -10000 <= x1,x2 <= 10000. -/
theorem spec_12 (arr : Slice Std.I64) (k x1 x2 : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx1 : -10000 ≤ x1.val ∧ x1.val ≤ 10000)
    (hx2 : -10000 ≤ x2.val ∧ x2.val ≤ 10000)
    (hx12 : x1.val ≤ x2.val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hres1 : Aegis.FindClosestElements.find_closest_elements arr k x1 = ok r1)
    (hres2 : Aegis.FindClosestElements.find_closest_elements arr k x2 = ok r2) :
    lenI (vecvals r1) = k.val ∧ lenI (vecvals r2) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        ∃ a b : ℤ, (vecvals r1)[i]? = some a ∧ (vecvals r2)[i]? = some b ∧ a ≤ b) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x1 x2 : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx1 : -10000 ≤ x1.val ∧ x1.val ≤ 10000)
    (hx2 : -10000 ≤ x2.val ∧ x2.val ≤ 10000)
    (hx12 : x1.val ≤ x2.val)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hres1 : Aegis.FindClosestElements.find_closest_elements arr k x1 = ok r1)
    (hres2 : Aegis.FindClosestElements.find_closest_elements arr k x2 = ok r2), lenI (vecvals r1) = k.val ∧ lenI (vecvals r2) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        ∃ a b : ℤ, (vecvals r1)[i]? = some a ∧ (vecvals r2)[i]? = some b ∧ a ≤ b)) := by
  sorry

/-- If the call on (arr,k,x) returns r and the call on (arr2,k,x2) returns r2, then len(r2) = len(r) = k and r2[i] = r[i] + t for every i with 0 <= i < k.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. Let t be an integer, arr2 a slice of the same length with arr2[i] = arr[i] + t for all i, and x2 = x + t; suppose both (arr,k,x) and (arr2,k,x2) satisfy the preconditions and no i64 overflow occurs in these additions. -/
theorem spec_13 (arr arr2 : Slice Std.I64) (k x x2 : Std.I64) (t : ℤ)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hshift_len : (slvals arr2).length = (slvals arr).length)
    (hshift : ∀ (i : ℕ) (hi : i < (slvals arr).length) (hi2 : i < (slvals arr2).length),
      (slvals arr2)[i] = (slvals arr)[i] + t)
    (hx2 : x2.val = x.val + t)
    (hsorted2 : Sorted (slvals arr2))
    (hrange2 : InRange (slvals arr2))
    (hx2_range : -10000 ≤ x2.val ∧ x2.val ≤ 10000)
    (r r2 : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r)
    (hres2 : Aegis.FindClosestElements.find_closest_elements arr2 k x2 = ok r2) :
    (vecvals r2).length = (vecvals r).length ∧ lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        ∃ a b : ℤ, (vecvals r)[i]? = some a ∧ (vecvals r2)[i]? = some b ∧ b = a + t) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (arr arr2 : Slice Std.I64) (k x x2 : Std.I64) (t : ℤ)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (hshift_len : (slvals arr2).length = (slvals arr).length)
    (hshift : ∀ (i : ℕ) (hi : i < (slvals arr).length) (hi2 : i < (slvals arr2).length),
      (slvals arr2)[i] = (slvals arr)[i] + t)
    (hx2 : x2.val = x.val + t)
    (hsorted2 : Sorted (slvals arr2))
    (hrange2 : InRange (slvals arr2))
    (hx2_range : -10000 ≤ x2.val ∧ x2.val ≤ 10000)
    (r r2 : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r)
    (hres2 : Aegis.FindClosestElements.find_closest_elements arr2 k x2 = ok r2), (vecvals r2).length = (vecvals r).length ∧ lenI (vecvals r) = k.val ∧
      (∀ i : ℕ, i < k.val.toNat →
        ∃ a b : ℤ, (vecvals r)[i]? = some a ∧ (vecvals r2)[i]? = some b ∧ b = a + t)) := by
  sorry

/-- Whenever the function returns a result r, there exist k distinct indices p_0, p_1, ..., p_{k-1} with 0 <= p_j < len(arr) such that r is the nondecreasing rearrangement of the sequence arr[p_0], arr[p_1], ..., arr[p_{k-1}]; equivalently, len(r) = k and the multiset of values of r equals the multiset of values at those k array positions.
  Preconditions: arr is sorted in nondecreasing order; len(arr) >= 1; 1 <= k <= len(arr); len(arr) <= 10000; values and x satisfy -10000 <= arr[i], x <= 10000. -/
theorem spec_14 (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r) :
    ∃ p : List (Fin (slvals arr).length),
      p.length = k.val.toNat ∧ p.Nodup ∧ lenI (vecvals r) = k.val ∧
      (∀ v : ℤ,
        countOf (vecvals r) v = countOf (p.map fun i => (slvals arr).get i) v) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (arr : Slice Std.I64) (k x : Std.I64)
    (hsorted : Sorted (slvals arr))
    (hlen : 1 ≤ (slvals arr).length)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ lenI (slvals arr))
    (hlen_max : (slvals arr).length ≤ 10000)
    (hrange : InRange (slvals arr))
    (hx : -10000 ≤ x.val ∧ x.val ≤ 10000)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.FindClosestElements.find_closest_elements arr k x = ok r), ∃ p : List (Fin (slvals arr).length),
      p.length = k.val.toNat ∧ p.Nodup ∧ lenI (vecvals r) = k.val ∧
      (∀ v : ℤ,
        countOf (vecvals r) v = countOf (p.map fun i => (slvals arr).get i) v)) := by
  sorry

end AegisSpec.FindClosestElements
