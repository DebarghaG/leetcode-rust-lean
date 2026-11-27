import Aegis.ArrayStringsAreEqual.Code.Funs

/-!
# Specifications of `Aegis.ArrayStringsAreEqual.array_strings_are_equal`

LeetCode problem `check-if-two-string-arrays-are-equivalent`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ArrayStringsAreEqual

  open Aegis.ArrayStringsAreEqual

  def IsLowerByte (b : Std.U8) : Prop := 97 ≤ b.val ∧ b.val ≤ 122

  def ValidWord (v : alloc.vec.Vec Std.U8) : Prop :=
    1 ≤ v.val.length ∧ v.val.length ≤ 1000 ∧ ∀ b ∈ v.val, IsLowerByte b

  def totalLen (w : Slice (alloc.vec.Vec Std.U8)) : Nat :=
    (w.val.map fun v => v.val.length).sum

  def concat (w : Slice (alloc.vec.Vec Std.U8)) : List Std.U8 :=
    w.val.flatMap fun v => v.val

  def Valid (w : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    1 ≤ w.val.length ∧ w.val.length ≤ 1000 ∧
    (∀ v ∈ w.val, ValidWord v) ∧ totalLen w ≤ 1000

  def IsAppend (s t r : Slice (alloc.vec.Vec Std.U8)) : Prop :=
    r.val = s.val ++ t.val

  /-- The function returns a result r, and r = true if and only if concat(word1) and concat(word2) are equal as byte sequences: len(concat(word1)) = len(concat(word2)) and for every k with 0 <= k < len(concat(word1)), concat(word1)[k] = concat(word2)[k]. Equivalently, r = true iff concat(word1) = concat(word2); and r = false iff concat(word1) != concat(word2). Here concat(w) is the byte sequence obtained by concatenating w[0], w[1], ..., w[len(w)-1] in that order.
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(word1) and Valid(word2). -/
  theorem spec_1 (word1 word2 : Slice (alloc.vec.Vec Std.U8))
      (h1 : Valid word1) (h2 : Valid word2) :
      ∃ r, array_strings_are_equal word1 word2 = ok r ∧
        (r = true ↔ concat word1 = concat word2) ∧
        (r = false ↔ concat word1 ≠ concat word2) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (word1 word2 : Slice (alloc.vec.Vec Std.U8))
        (h1 : Valid word1) (h2 : Valid word2), ∃ r, array_strings_are_equal word1 word2 = ok r ∧
          (r = true ↔ concat word1 = concat word2) ∧
          (r = false ↔ concat word1 ≠ concat word2)) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, or panic) on every input satisfying the preconditions.
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(word1) and Valid(word2). -/
  theorem spec_2 (word1 word2 : Slice (alloc.vec.Vec Std.U8))
      (h1 : Valid word1) (h2 : Valid word2) :
      ∃ r, array_strings_are_equal word1 word2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (word1 word2 : Slice (alloc.vec.Vec Std.U8))
        (h1 : Valid word1) (h2 : Valid word2), ∃ r, array_strings_are_equal word1 word2 = ok r) := by
    sorry

  /-- Let r1 be the result of the call on (a, b) and r2 the result of the call on (b, a). If both calls return results, then r1 = r2. (Under the preconditions both calls return results, so the function is symmetric in its two arguments.)
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a) and Valid(b). -/
  theorem spec_3 (a b : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) :
      ∀ r1 r2, array_strings_are_equal a b = ok r1 →
        array_strings_are_equal b a = ok r2 → r1 = r2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (a b : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b), ∀ r1 r2, array_strings_are_equal a b = ok r1 →
          array_strings_are_equal b a = ok r2 → r1 = r2) := by
    sorry

  /-- If the call on (a, b) returns true and the call on (b, c) returns true, then the call on (a, c) returns true.
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(b), and Valid(c). -/
  theorem spec_4 (a b c : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) (hc : Valid c) :
      array_strings_are_equal a b = ok true →
      array_strings_are_equal b c = ok true →
      array_strings_are_equal a c = ok true := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (a b c : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b) (hc : Valid c), array_strings_are_equal a b = ok true →
        array_strings_are_equal b c = ok true →
        array_strings_are_equal a c = ok true) := by
    sorry

  /-- If concat(a) = concat(a') and concat(b) = concat(b'), then the result of the call on (a, b) equals the result of the call on (a', b'). Both calls return results under the preconditions.
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(a'), Valid(b), and Valid(b'). -/
  theorem spec_5 (a a' b b' : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (ha' : Valid a') (hb : Valid b) (hb' : Valid b')
      (hA : concat a = concat a') (hB : concat b = concat b') :
      ∀ r1 r2, array_strings_are_equal a b = ok r1 →
        array_strings_are_equal a' b' = ok r2 → r1 = r2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a a' b b' : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (ha' : Valid a') (hb : Valid b) (hb' : Valid b')
        (hA : concat a = concat a') (hB : concat b = concat b'), ∀ r1 r2, array_strings_are_equal a b = ok r1 →
          array_strings_are_equal a' b' = ok r2 → r1 = r2) := by
    sorry

  /-- The result of the call on (c++a, c++b) equals the result of the call on (a, b).
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(b), Valid(c), Valid(c++a), and Valid(c++b), where c++a is the slice obtained by concatenating c and a (all elements of c followed by all elements of a). -/
  theorem spec_6 (a b c ca cb : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) (hc : Valid c)
      (hca : Valid ca) (hcb : Valid cb)
      (hca' : IsAppend c a ca) (hcb' : IsAppend c b cb) :
      ∀ r1 r2, array_strings_are_equal ca cb = ok r1 →
        array_strings_are_equal a b = ok r2 → r1 = r2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b c ca cb : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b) (hc : Valid c)
        (hca : Valid ca) (hcb : Valid cb)
        (hca' : IsAppend c a ca) (hcb' : IsAppend c b cb), ∀ r1 r2, array_strings_are_equal ca cb = ok r1 →
          array_strings_are_equal a b = ok r2 → r1 = r2) := by
    sorry

  /-- The result of the call on (a++c, b++c) equals the result of the call on (a, b).
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(b), Valid(c), Valid(a++c), and Valid(b++c), where a++c is the slice obtained by concatenating a and c. -/
  theorem spec_7 (a b c ac bc : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) (hc : Valid c)
      (hac : Valid ac) (hbc : Valid bc)
      (hac' : IsAppend a c ac) (hbc' : IsAppend b c bc) :
      ∀ r1 r2, array_strings_are_equal ac bc = ok r1 →
        array_strings_are_equal a b = ok r2 → r1 = r2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b c ac bc : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b) (hc : Valid c)
        (hac : Valid ac) (hbc : Valid bc)
        (hac' : IsAppend a c ac) (hbc' : IsAppend b c bc), ∀ r1 r2, array_strings_are_equal ac bc = ok r1 →
          array_strings_are_equal a b = ok r2 → r1 = r2) := by
    sorry

  /-- If the call on (a, b) returns true, then for every such c and d, the result of the call on (a++c, b++d) equals the result of the call on (c, d).
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(b), Valid(c), Valid(d), Valid(a++c), and Valid(b++d). -/
  theorem spec_8 (a b c d ac bd : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d)
      (hac : Valid ac) (hbd : Valid bd)
      (hac' : IsAppend a c ac) (hbd' : IsAppend b d bd)
      (h : array_strings_are_equal a b = ok true) :
      ∀ r1 r2, array_strings_are_equal ac bd = ok r1 →
        array_strings_are_equal c d = ok r2 → r1 = r2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b c d ac bd : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d)
        (hac : Valid ac) (hbd : Valid bd)
        (hac' : IsAppend a c ac) (hbd' : IsAppend b d bd)
        (h : array_strings_are_equal a b = ok true), ∀ r1 r2, array_strings_are_equal ac bd = ok r1 →
          array_strings_are_equal c d = ok r2 → r1 = r2) := by
    sorry

  /-- If the call on (a, b) returns true, then for every such c and d, the result of the call on (c++a, d++b) equals the result of the call on (c, d).
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a), Valid(b), Valid(c), Valid(d), Valid(c++a), and Valid(d++b). -/
  theorem spec_9 (a b c d ca db : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d)
      (hca : Valid ca) (hdb : Valid db)
      (hca' : IsAppend c a ca) (hdb' : IsAppend d b db)
      (h : array_strings_are_equal a b = ok true) :
      ∀ r1 r2, array_strings_are_equal ca db = ok r1 →
        array_strings_are_equal c d = ok r2 → r1 = r2 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b c d ca db : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b) (hc : Valid c) (hd : Valid d)
        (hca : Valid ca) (hdb : Valid db)
        (hca' : IsAppend c a ca) (hdb' : IsAppend d b db)
        (h : array_strings_are_equal a b = ok true), ∀ r1 r2, array_strings_are_equal ca db = ok r1 →
          array_strings_are_equal c d = ok r2 → r1 = r2) := by
    sorry

  /-- If the call on (a, b) returns false, then there exists an array c with Valid(c) such that the result of the call on (a, c) differs from the result of the call on (b, c). (For instance, c = a works.)
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a) and Valid(b). -/
  theorem spec_10 (a b : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b)
      (h : array_strings_are_equal a b = ok false) :
      ∃ c, Valid c ∧ ∃ r1 r2,
        array_strings_are_equal a c = ok r1 ∧
        array_strings_are_equal b c = ok r2 ∧ r1 ≠ r2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b)
        (h : array_strings_are_equal a b = ok false), ∃ c, Valid c ∧ ∃ r1 r2,
          array_strings_are_equal a c = ok r1 ∧
          array_strings_are_equal b c = ok r2 ∧ r1 ≠ r2) := by
    sorry

  /-- The total length of concat(a) is sum_{i=0}^{len(a)-1} len(a[i]) and the total length of concat(b) is sum_{j=0}^{len(b)-1} len(b[j]); each of these sums is at most 1000. If the call on (a, b) returns true, then these two total lengths are equal.
    Preconditions: Let Valid(w) mean: 1 <= len(w) <= 1000; for every i with 0 <= i < len(w), 1 <= len(w[i]) <= 1000 and every byte of w[i] is a lowercase ASCII letter (97 <= byte <= 122); and sum_{i=0}^{len(w)-1} len(w[i]) <= 1000. Assume Valid(a) and Valid(b). -/
  theorem spec_11 (a b : Slice (alloc.vec.Vec Std.U8))
      (ha : Valid a) (hb : Valid b) :
      (concat a).length = totalLen a ∧
      (concat b).length = totalLen b ∧
      totalLen a ≤ 1000 ∧
      totalLen b ≤ 1000 ∧
      (array_strings_are_equal a b = ok true →
        (concat a).length = (concat b).length) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (a b : Slice (alloc.vec.Vec Std.U8))
        (ha : Valid a) (hb : Valid b), (concat a).length = totalLen a ∧
        (concat b).length = totalLen b ∧
        totalLen a ≤ 1000 ∧
        totalLen b ≤ 1000 ∧
        (array_strings_are_equal a b = ok true →
          (concat a).length = (concat b).length)) := by
    sorry

  end AegisSpec.ArrayStringsAreEqual
