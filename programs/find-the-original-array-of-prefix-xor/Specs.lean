import Aegis.FindArray.Code.Funs

/-!
# Specifications of `Aegis.FindArray.find_array`

LeetCode problem `find-the-original-array-of-prefix-xor`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindArray

  def xorInt (a b : Int) : Int := ((a.toNat ^^^ b.toNat : Nat) : Int)

  def nth (l : List Int) (i : Nat) : Int := l.getD i 0

  def xorPrefix (l : List Int) : Nat → Int
    | 0 => nth l 0
    | n + 1 => xorInt (xorPrefix l n) (nth l (n + 1))

  def sliceVals (s : Slice I64) : List Int := s.val.map (fun x => x.val)

  def vecVals (v : alloc.vec.Vec I64) : List Int := v.val.map (fun x => x.val)

  /-- Whenever find_array(pref) returns a result r, len(r) = n and, for every i with 0 <= i < n, xor(r[0..i]) = pref[i], where xor(r[0..i]) denotes the bitwise xor r[0] bitwise-xor r[1] bitwise-xor ... bitwise-xor r[i]. For i = 0 this means xor(r[0..0]) = r[0].
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_1 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        (vecVals r).length = (sliceVals pref).length ∧
          (∀ i, i < (sliceVals pref).length →
            xorPrefix (vecVals r) i = nth (sliceVals pref) i) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          (vecVals r).length = (sliceVals pref).length ∧
            (∀ i, i < (sliceVals pref).length →
              xorPrefix (vecVals r) i = nth (sliceVals pref) i)) := by
    sorry

  /-- For every pref satisfying the preconditions, find_array(pref) returns a result. It does not fail: there is no panic, no out-of-bounds access, and no arithmetic overflow.
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_2 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∃ r, Aegis.FindArray.find_array pref = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∃ r, Aegis.FindArray.find_array pref = ok r) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every i with 0 <= i < n, if i = 0 then r[i] = pref[0], and if i > 0 then r[i] = pref[i] bitwise-xor pref[i-1].
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_3 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ i, i < (sliceVals pref).length →
          (i = 0 → nth (vecVals r) i = nth (sliceVals pref) 0) ∧
          (0 < i → nth (vecVals r) i =
            xorInt (nth (sliceVals pref) i) (nth (sliceVals pref) (i - 1))) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ i, i < (sliceVals pref).length →
            (i = 0 → nth (vecVals r) i = nth (sliceVals pref) 0) ∧
            (0 < i → nth (vecVals r) i =
              xorInt (nth (sliceVals pref) i) (nth (sliceVals pref) (i - 1)))) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every i with 2 <= i < n, (r[i] bitwise-xor r[i-1]) = (pref[i] bitwise-xor pref[i-2]).
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_4 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ i, 2 ≤ i → i < (sliceVals pref).length →
          xorInt (nth (vecVals r) i) (nth (vecVals r) (i - 1)) =
            xorInt (nth (sliceVals pref) i) (nth (sliceVals pref) (i - 2)) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ i, 2 ≤ i → i < (sliceVals pref).length →
            xorInt (nth (vecVals r) i) (nth (vecVals r) (i - 1)) =
              xorInt (nth (sliceVals pref) i) (nth (sliceVals pref) (i - 2))) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every i with 0 <= i < n, 0 <= r[i] <= 1048575, that is, r[i] <= 2^20 - 1.
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_5 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (vecVals r) i ∧ nth (vecVals r) i ≤ 1048575 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ i, i < (sliceVals pref).length →
            0 ≤ nth (vecVals r) i ∧ nth (vecVals r) i ≤ 1048575) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every array q of length n of 64-bit integers such that xor(q[0..i]) = pref[i] for every i with 0 <= i < n, it holds that q[i] = r[i] for every i with 0 <= i < n.
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_6 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ q : alloc.vec.Vec I64, (vecVals q).length = (sliceVals pref).length →
          (∀ i, i < (sliceVals pref).length →
            xorPrefix (vecVals q) i = nth (sliceVals pref) i) →
          ∀ i, i < (sliceVals pref).length → nth (vecVals q) i = nth (vecVals r) i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ q : alloc.vec.Vec I64, (vecVals q).length = (sliceVals pref).length →
            (∀ i, i < (sliceVals pref).length →
              xorPrefix (vecVals q) i = nth (sliceVals pref) i) →
            ∀ i, i < (sliceVals pref).length → nth (vecVals q) i = nth (vecVals r) i) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every i with 1 <= i < n, if pref[i] = pref[i-1], then r[i] = 0.
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_7 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ i, 1 ≤ i → i < (sliceVals pref).length →
          nth (sliceVals pref) i = nth (sliceVals pref) (i - 1) → nth (vecVals r) i = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ i, 1 ≤ i → i < (sliceVals pref).length →
            nth (sliceVals pref) i = nth (sliceVals pref) (i - 1) → nth (vecVals r) i = 0) := by
    sorry

  /-- Whenever find_array(pref) returns a result r, for every i with 1 <= i < n, r[i] bitwise-xor pref[i-1] = pref[i].
    Preconditions: Let n = len(pref). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= pref[i] <= 1000000. -/
  theorem spec_8 (pref : Slice I64)
      (hn_lo : 1 ≤ (sliceVals pref).length)
      (hn_hi : (sliceVals pref).length ≤ 100000)
      (hbnd : ∀ i, i < (sliceVals pref).length →
        0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000) :
      ∀ r, Aegis.FindArray.find_array pref = ok r →
        ∀ i, 1 ≤ i → i < (sliceVals pref).length →
          xorInt (nth (vecVals r) i) (nth (sliceVals pref) (i - 1)) =
            nth (sliceVals pref) i := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (pref : Slice I64)
        (hn_lo : 1 ≤ (sliceVals pref).length)
        (hn_hi : (sliceVals pref).length ≤ 100000)
        (hbnd : ∀ i, i < (sliceVals pref).length →
          0 ≤ nth (sliceVals pref) i ∧ nth (sliceVals pref) i ≤ 1000000), ∀ r, Aegis.FindArray.find_array pref = ok r →
          ∀ i, 1 ≤ i → i < (sliceVals pref).length →
            xorInt (nth (vecVals r) i) (nth (sliceVals pref) (i - 1)) =
              nth (sliceVals pref) i) := by
    sorry

  end AegisSpec.FindArray
