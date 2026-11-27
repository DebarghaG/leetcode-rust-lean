import Aegis.Decode.Code.Funs

/-!
# Specifications of `Aegis.Decode.decode`

LeetCode problem `decode-xored-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.Decode

  namespace AegisSpec.Decode

  def xorInt (a b : Int) : Int := ((BitVec.ofInt 64 a) ^^^ (BitVec.ofInt 64 b)).toInt

  def xorList (init : Int) (l : List Std.I64) : Int :=
    l.foldl (fun acc x => xorInt acc x.val) init

  def prefixXor (first : Int) (l : List Std.I64) (i : Nat) : Int :=
    xorList first (l.take i)

  def segXor (l : List Std.I64) (i j : Nat) : Int :=
    xorList 0 ((l.drop i).take (j - i))

  def ivals (l : List Std.I64) : List Int := l.map (fun x => x.val)

  def vals (v : alloc.vec.Vec Std.I64) : List Int := ivals v.val

  /-- The function returns a result r (it does not fail). The vector r has length len(encoded)+1. Its first element is r[0] = first. For every i with 0 <= i < len(encoded), the next element is r[i+1] = r[i] XOR encoded[i]. Equivalently, r satisfies r[0] = first and encoded[i] = r[i] XOR r[i+1] for every 0 <= i < len(encoded).
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_1 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∃ r : alloc.vec.Vec Std.I64,
        decode encoded first = ok r ∧
        r.val.length = encoded.val.length + 1 ∧
        (vals r)[0]? = some first.val ∧
        (∀ i (hi : i < encoded.val.length), ∃ a b : Int,
          (vals r)[i]? = some a ∧
          (vals r)[i + 1]? = some b ∧
          b = xorInt a (encoded.val[i]'hi).val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64,
          decode encoded first = ok r ∧
          r.val.length = encoded.val.length + 1 ∧
          (vals r)[0]? = some first.val ∧
          (∀ i (hi : i < encoded.val.length), ∃ a b : Int,
            (vals r)[i]? = some a ∧
            (vals r)[i + 1]? = some b ∧
            b = xorInt a (encoded.val[i]'hi).val)) := by
    sorry

  /-- For every encoded and first satisfying the preconditions, decode returns a result r; it never panics, overflows, or accesses an out-of-bounds index.
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_2 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∃ r : alloc.vec.Vec Std.I64, decode encoded first = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∃ r : alloc.vec.Vec Std.I64, decode encoded first = ok r) := by
    sorry

  /-- Whenever decode returns a result r, len(r) = len(encoded) + 1. Consequently, since len(encoded) >= 1, r has at least two elements.
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_3 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        r.val.length = encoded.val.length + 1 ∧ 2 ≤ r.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          r.val.length = encoded.val.length + 1 ∧ 2 ≤ r.val.length) := by
    sorry

  /-- Whenever decode returns a result r, for every i with 0 <= i <= len(encoded), the integer value of r[i] satisfies 0 <= r[i] <= 131071 (that is, 0 <= r[i] <= 2^17 - 1).
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_4 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ i (hi : i ≤ encoded.val.length), ∃ x : Int,
          (vals r)[i]? = some x ∧ 0 ≤ x ∧ x ≤ 131071 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ i (hi : i ≤ encoded.val.length), ∃ x : Int,
            (vals r)[i]? = some x ∧ 0 ≤ x ∧ x ≤ 131071) := by
    sorry

  /-- Whenever decode returns a result r, for every i with 0 <= i < len(encoded), r[i] XOR r[i+1] = encoded[i].
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_5 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ i (hi : i < encoded.val.length), ∃ a b : Int,
          (vals r)[i]? = some a ∧
          (vals r)[i + 1]? = some b ∧
          xorInt a b = (encoded.val[i]'hi).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ i (hi : i < encoded.val.length), ∃ a b : Int,
            (vals r)[i]? = some a ∧
            (vals r)[i + 1]? = some b ∧
            xorInt a b = (encoded.val[i]'hi).val) := by
    sorry

  /-- Whenever decode returns a result r, for every i with 0 <= i <= len(encoded), r[i] = first XOR encoded[0] XOR encoded[1] XOR ... XOR encoded[i-1], where the empty XOR (when i = 0) is 0. In other words, r[i] is the XOR of first with the prefix encoded[0..i-1].
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_6 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ i (hi : i ≤ encoded.val.length), ∃ x : Int,
          (vals r)[i]? = some x ∧ x = prefixXor first.val encoded.val i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ i (hi : i ≤ encoded.val.length), ∃ x : Int,
            (vals r)[i]? = some x ∧ x = prefixXor first.val encoded.val i) := by
    sorry

  /-- Whenever decode returns a result r, r[0] XOR r[len(encoded)] = encoded[0] XOR encoded[1] XOR ... XOR encoded[len(encoded)-1] (the XOR of all entries of encoded).
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_7 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∃ a b : Int,
          (vals r)[0]? = some a ∧
          (vals r)[encoded.val.length]? = some b ∧
          xorInt a b = xorList 0 encoded.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∃ a b : Int,
            (vals r)[0]? = some a ∧
            (vals r)[encoded.val.length]? = some b ∧
            xorInt a b = xorList 0 encoded.val) := by
    sorry

  /-- Whenever decode returns a result r, for every sequence a of 64-bit integers with len(a) = len(encoded)+1, a[0] = first, and a[i] XOR a[i+1] = encoded[i] for every 0 <= i < len(encoded), we have a[i] = r[i] for every 0 <= i <= len(encoded). Thus r is the unique solution.
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_8 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ a : List Std.I64,
          a.length = encoded.val.length + 1 →
          a[0]? = some first →
          (∀ i (hi : i < encoded.val.length), ∃ x y : Int,
            (ivals a)[i]? = some x ∧
            (ivals a)[i + 1]? = some y ∧
            xorInt x y = (encoded.val[i]'hi).val) →
          ∀ i (hi : i ≤ encoded.val.length), ∀ x y : Int,
            (ivals a)[i]? = some x → (vals r)[i]? = some y → x = y := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ a : List Std.I64,
            a.length = encoded.val.length + 1 →
            a[0]? = some first →
            (∀ i (hi : i < encoded.val.length), ∃ x y : Int,
              (ivals a)[i]? = some x ∧
              (ivals a)[i + 1]? = some y ∧
              xorInt x y = (encoded.val[i]'hi).val) →
            ∀ i (hi : i ≤ encoded.val.length), ∀ x y : Int,
              (ivals a)[i]? = some x → (vals r)[i]? = some y → x = y) := by
    sorry

  /-- Whenever decode returns a result r and len(encoded) = 1, r is exactly the two-element vector [first, first XOR encoded[0]].
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_9 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        (hlen_one : encoded.val.length = 1) →
        vals r = [first.val, xorInt first.val (encoded.val[0]'(by omega)).val] := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          (hlen_one : encoded.val.length = 1) →
          vals r = [first.val, xorInt first.val (encoded.val[0]'(by omega)).val]) := by
    sorry

  /-- Whenever decode returns a result r and encoded[i] = 0 for every 0 <= i < len(encoded), then r[i] = first for every 0 <= i <= len(encoded).
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_10 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        (∀ i (hi : i < encoded.val.length), (encoded.val[i]'hi).val = 0) →
        ∀ i (hi : i ≤ encoded.val.length), (vals r)[i]? = some first.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          (∀ i (hi : i < encoded.val.length), (encoded.val[i]'hi).val = 0) →
          ∀ i (hi : i ≤ encoded.val.length), (vals r)[i]? = some first.val) := by
    sorry

  /-- Whenever decode returns a result r and first = 0, then r[0] = 0 and for every i with 1 <= i <= len(encoded), r[i] = encoded[0] XOR encoded[1] XOR ... XOR encoded[i-1] (the XOR of the prefix of encoded of length i).
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_11 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        first.val = 0 →
        (vals r)[0]? = some 0 ∧
        (∀ i (hi_lo : 1 ≤ i) (hi_hi : i ≤ encoded.val.length),
          (vals r)[i]? = some (prefixXor 0 encoded.val i)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          first.val = 0 →
          (vals r)[0]? = some 0 ∧
          (∀ i (hi_lo : 1 ≤ i) (hi_hi : i ≤ encoded.val.length),
            (vals r)[i]? = some (prefixXor 0 encoded.val i))) := by
    sorry

  /-- Whenever decode returns a result r, for every i with 0 <= i < len(encoded), r[i] = r[i+1] if and only if encoded[i] = 0.
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_12 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ i (hi : i < encoded.val.length),
          ((∃ a b : Int,
              (vals r)[i]? = some a ∧
              (vals r)[i + 1]? = some b ∧
              a = b) ↔
            (encoded.val[i]'hi).val = 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ i (hi : i < encoded.val.length),
            ((∃ a b : Int,
                (vals r)[i]? = some a ∧
                (vals r)[i + 1]? = some b ∧
                a = b) ↔
              (encoded.val[i]'hi).val = 0)) := by
    sorry

  /-- Whenever decode returns a result r, for every i and j with 0 <= i <= j <= len(encoded), r[i] XOR r[j] = encoded[i] XOR encoded[i+1] XOR ... XOR encoded[j-1], where the empty XOR (when i = j) is 0. This general pairwise relation subsumes the endpoint case of spec_7 and the adjacent case of spec_5.
    Preconditions: encoded is a slice of 64-bit integers with 1 <= len(encoded) <= 9999, and for every i with 0 <= i < len(encoded), 0 <= encoded[i] <= 100000. first is a 64-bit integer with 0 <= first <= 100000. XOR denotes bitwise exclusive-or on 64-bit integers; on these non-negative values it agrees with ordinary non-negative integer XOR. -/
  theorem spec_13 (encoded : Slice Std.I64) (first : Std.I64)
      (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
      (henc : ∀ i (hi : i < encoded.val.length),
        0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
      (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000) :
      ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
        ∀ i j (hij : i ≤ j) (hj : j ≤ encoded.val.length), ∃ a b : Int,
          (vals r)[i]? = some a ∧
          (vals r)[j]? = some b ∧
          xorInt a b = segXor encoded.val i j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (encoded : Slice Std.I64) (first : Std.I64)
        (hlen_lo : 1 ≤ encoded.val.length) (hlen_hi : encoded.val.length ≤ 9999)
        (henc : ∀ i (hi : i < encoded.val.length),
          0 ≤ (encoded.val[i]'hi).val ∧ (encoded.val[i]'hi).val ≤ 100000)
        (hfirst_lo : 0 ≤ first.val) (hfirst_hi : first.val ≤ 100000), ∀ r : alloc.vec.Vec Std.I64, decode encoded first = ok r →
          ∀ i j (hij : i ≤ j) (hj : j ≤ encoded.val.length), ∃ a b : Int,
            (vals r)[i]? = some a ∧
            (vals r)[j]? = some b ∧
            xorInt a b = segXor encoded.val i j) := by
    sorry

  end AegisSpec.Decode
