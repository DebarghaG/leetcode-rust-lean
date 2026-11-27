import Aegis.Decode.Code.Funs

/-!
# Specifications of `Aegis.Decode.decode`

LeetCode problem `decode-xored-permutation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Decode

  def xorInt (a b : Int) : Int := (BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 b).toInt

  def xorAll (l : List Int) : Int := l.foldr xorInt 0

  def sumAll (l : List Int) : Int := l.foldr (· + ·) 0

  def vals (l : List I64) : List Int := l.map (fun x => x.val)

  def valAt (l : List I64) (i : Nat) : Int := (l.getD i 0#i64).val

  def oneTo (n : Nat) : List Int := (List.range n).map (fun k => (k : Int) + 1)

  def IsPermOf (l : List Int) (n : Nat) : Prop := l.Perm (oneTo n)

  def adjacentXor (l : List Int) : List Int :=
    (l.zip l.tail).map (fun q => xorInt q.1 q.2)

  def Encodes (e p : List Int) : Prop := adjacentXor p = e

  def xorOddPos (l : List Int) : Int :=
    xorAll ((List.range l.length).filterMap
      (fun i => if i % 2 = 1 then l[i]? else none))

  /-- The function returns a result r (a vector of i64) such that: (1) len(r) = n, where n = len(encoded) + 1; (2) r is a permutation of the integers 1, 2, ..., n, meaning each integer from 1 to n appears exactly once in r; (3) for every i with 0 <= i < len(encoded), encoded[i] = r[i] XOR r[i+1].
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, len(encoded) < 10^5 - 1, and there exists a unique permutation p of {1,2,...,n} such that for every i with 0 <= i < len(encoded), encoded[i] = p[i] XOR p[i+1]. -/
  theorem spec_1 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        r.val.length = encoded.val.length + 1 ∧
        IsPermOf (vals r.val) (encoded.val.length + 1) ∧
        Encodes (vals encoded.val) (vals r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          r.val.length = encoded.val.length + 1 ∧
          IsPermOf (vals r.val) (encoded.val.length + 1) ∧
          Encodes (vals encoded.val) (vals r.val)) := by
    sorry

  /-- The function returns a result r with len(r) = len(encoded) + 1.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_2 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        r.val.length = encoded.val.length + 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          r.val.length = encoded.val.length + 1) := by
    sorry

  /-- For every index i with 0 <= i < len(r), 1 <= r[i] <= n, where n = len(encoded) + 1.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_3 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        ∀ i : Nat, i < r.val.length →
          1 ≤ valAt r.val i ∧ valAt r.val i ≤ (encoded.val.length : Int) + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          ∀ i : Nat, i < r.val.length →
            1 ≤ valAt r.val i ∧ valAt r.val i ≤ (encoded.val.length : Int) + 1) := by
    sorry

  /-- For every pair of indices i and j with 0 <= i < j < len(r), r[i] != r[j].
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_4 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        ∀ i j : Nat, i < j → j < r.val.length → valAt r.val i ≠ valAt r.val j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          ∀ i j : Nat, i < j → j < r.val.length → valAt r.val i ≠ valAt r.val j) := by
    sorry

  /-- For every integer v with 1 <= v <= n, there exists an index i with 0 <= i < len(r) such that r[i] = v.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_5 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        ∀ v : Int, 1 ≤ v → v ≤ (encoded.val.length : Int) + 1 →
          ∃ i : Nat, i < r.val.length ∧ valAt r.val i = v := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          ∀ v : Int, 1 ≤ v → v ≤ (encoded.val.length : Int) + 1 →
            ∃ i : Nat, i < r.val.length ∧ valAt r.val i = v) := by
    sorry

  /-- For every i with 0 <= i < len(encoded), encoded[i] = r[i] XOR r[i+1].
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_6 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        ∀ i : Nat, i < encoded.val.length →
          valAt encoded.val i = xorInt (valAt r.val i) (valAt r.val (i + 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          ∀ i : Nat, i < encoded.val.length →
            valAt encoded.val i = xorInt (valAt r.val i) (valAt r.val (i + 1))) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail, panic, or overflow) and r is a vector of i64.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_7 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64, Aegis.Decode.decode encoded = ok r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64, Aegis.Decode.decode encoded = ok r) := by
    sorry

  /-- The sum of all elements of r equals n*(n+1)/2, where n = len(encoded) + 1.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_8 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        sumAll (vals r.val) =
          ((encoded.val.length : Int) + 1) * ((encoded.val.length : Int) + 2) / 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          sumAll (vals r.val) =
            ((encoded.val.length : Int) + 1) * ((encoded.val.length : Int) + 2) / 2) := by
    sorry

  /-- The bitwise XOR of all elements of r, i.e., r[0] XOR r[1] XOR ... XOR r[n-1], equals the bitwise XOR of the integers 1, 2, ..., n.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_9 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        xorAll (vals r.val) = xorAll (oneTo (encoded.val.length + 1)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          xorAll (vals r.val) = xorAll (oneTo (encoded.val.length + 1))) := by
    sorry

  /-- The bitwise XOR of all elements of encoded, i.e., encoded[0] XOR encoded[1] XOR ... XOR encoded[n-2], equals r[0] XOR r[n-1].
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_10 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        xorAll (vals encoded.val) =
          xorInt (valAt r.val 0) (valAt r.val encoded.val.length) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          xorAll (vals encoded.val) =
            xorInt (valAt r.val 0) (valAt r.val encoded.val.length)) := by
    sorry

  /-- r[0] = (1 XOR 2 XOR ... XOR n) XOR (encoded[1] XOR encoded[3] XOR ... XOR encoded[n-2]), where the second XOR is over all odd indices of encoded.
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_11 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        valAt r.val 0 =
          xorInt (xorAll (oneTo (encoded.val.length + 1))) (xorOddPos (vals encoded.val)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          valAt r.val 0 =
            xorInt (xorAll (oneTo (encoded.val.length + 1))) (xorOddPos (vals encoded.val))) := by
    sorry

  /-- r[n-1] = r[0] XOR (encoded[0] XOR encoded[1] XOR ... XOR encoded[n-2]).
    Preconditions: Let n = len(encoded) + 1. Assume len(encoded) >= 2, len(encoded) is even, and the input is a valid encoding as described in spec_1. -/
  theorem spec_12 (encoded : Slice I64)
      (hlen : 2 ≤ encoded.val.length)
      (heven : encoded.val.length % 2 = 0)
      (hbound : encoded.val.length < 10 ^ 5 - 1)
      (hvalid : ∃! p : List Int,
        IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p) :
      ∃ r : alloc.vec.Vec I64,
        Aegis.Decode.decode encoded = ok r ∧
        valAt r.val encoded.val.length =
          xorInt (valAt r.val 0) (xorAll (vals encoded.val)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (encoded : Slice I64)
        (hlen : 2 ≤ encoded.val.length)
        (heven : encoded.val.length % 2 = 0)
        (hbound : encoded.val.length < 10 ^ 5 - 1)
        (hvalid : ∃! p : List Int,
          IsPermOf p (encoded.val.length + 1) ∧ Encodes (vals encoded.val) p), ∃ r : alloc.vec.Vec I64,
          Aegis.Decode.decode encoded = ok r ∧
          valAt r.val encoded.val.length =
            xorInt (valAt r.val 0) (xorAll (vals encoded.val))) := by
    sorry

  end AegisSpec.Decode
