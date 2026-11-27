import Aegis.IsValid.Code.Funs

/-!
# Specifications of `Aegis.IsValid.is_valid`

LeetCode problem `check-if-word-is-valid-after-substitutions`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsValid

def bytes (s : Slice Std.U8) : List Nat := s.val.map (fun b => b.val)

def byteAt (s : Slice Std.U8) (i : Nat) : Option Nat := (bytes s)[i]?

def abcBytes (s : Slice Std.U8) : Prop :=
  ∀ i : Nat, i < s.val.length →
    byteAt s i = some 97 ∨ byteAt s i = some 98 ∨ byteAt s i = some 99

def countOf (u : List Nat) (x : Nat) : Nat := u.countP (fun y => y == x)

def countPrefix (s : Slice Std.U8) (i x : Nat) : Nat := countOf ((bytes s).take i) x

def countSuffix (s : Slice Std.U8) (i x : Nat) : Nat := countOf ((bytes s).drop i) x

def insertStep (u v : List Nat) (p : Nat) : Prop :=
  p ≤ u.length ∧ v = u.take p ++ [97, 98, 99] ++ u.drop p

def InsertionValid (u : List Nat) : Prop :=
  ∃ n : Nat, ∃ us : Nat → List Nat,
    us 0 = [] ∧ us n = u ∧ ∀ k : Nat, k < n → ∃ p : Nat, insertStep (us k) (us (k + 1)) p

def deleteStep (u v : List Nat) (i : Nat) : Prop :=
  i + 3 ≤ u.length ∧ u[i]? = some 97 ∧ u[i + 1]? = some 98 ∧ u[i + 2]? = some 99 ∧
    v = u.take i ++ u.drop (i + 3)

def ReductionValid (u : List Nat) : Prop :=
  ∃ n : Nat, ∃ us : Nat → List Nat,
    us 0 = u ∧ us n = [] ∧ ∀ k : Nat, k < n → ∃ i : Nat, deleteStep (us k) (us (k + 1)) i

def endsWithABC (st : List Nat) : Prop :=
  3 ≤ st.length ∧ st.drop (st.length - 3) = [97, 98, 99]

def stripRev : List Nat → List Nat
  | 99 :: 98 :: 97 :: rest => stripRev rest
  | l => l

def stripAll (st : List Nat) : List Nat := (stripRev st.reverse).reverse

def pushStrip (st : List Nat) (x : Nat) : List Nat := stripAll (st ++ [x])

def stackFold (u : List Nat) : List Nat := u.foldl pushStrip []

def StackAccepts (u : List Nat) : Prop := stackFold u = []

/-- Whenever is_valid(s) returns Result.ok r, r = true if and only if s is valid, where a byte string u is valid exactly when there exist n >= 0 and byte strings u_0, ..., u_n such that u_0 is empty, u_n = u, and for every k with 0 <= k < n there is an insertion position p with 0 <= p <= len(u_k) and u_{k+1} = u_k[0..p] ++ [97,98,99] ++ u_k[p..len(u_k)].
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
theorem spec_1 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ InsertionValid (bytes s)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ InsertionValid (bytes s))) := by
  sorry

/-- The call is_valid(s) returns a result of the form Result.ok r for some Boolean r; it does not fail, panic, overflow, or go out of bounds.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
theorem spec_2 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    ∃ r : Bool, Aegis.IsValid.is_valid s = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), ∃ r : Bool, Aegis.IsValid.is_valid s = ok r) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then there exists an integer k >= 0 with len(s) = 3*k.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_3 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true → ∃ k : Nat, s.val.length = 3 * k := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true → ∃ k : Nat, s.val.length = 3 * k) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then the number of indices i with 0 <= i < len(s) and s[i] = 97 is equal to the number of indices i with 0 <= i < len(s) and s[i] = 98, and this number is also equal to the number of indices i with 0 <= i < len(s) and s[i] = 99.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_4 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true →
      countOf (bytes s) 97 = countOf (bytes s) 98 ∧
        countOf (bytes s) 97 = countOf (bytes s) 99 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true →
      countOf (bytes s) 97 = countOf (bytes s) 98 ∧
        countOf (bytes s) 97 = countOf (bytes s) 99) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then for every i with 0 <= i <= len(s), if A_i, B_i, C_i are respectively the numbers of j with 0 <= j < i and s[j] = 97, 98, 99, then A_i >= B_i and B_i >= C_i.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_5 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true →
      ∀ i : Nat, i ≤ s.val.length →
        countPrefix s i 97 ≥ countPrefix s i 98 ∧
          countPrefix s i 98 ≥ countPrefix s i 99 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true →
      ∀ i : Nat, i ≤ s.val.length →
        countPrefix s i 97 ≥ countPrefix s i 98 ∧
          countPrefix s i 98 ≥ countPrefix s i 99) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then for every i with 0 <= i <= len(s), if A_i, B_i, C_i are respectively the numbers of j with i <= j < len(s) and s[j] = 97, 98, 99, then C_i >= B_i and B_i >= A_i.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_6 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true →
      ∀ i : Nat, i ≤ s.val.length →
        countSuffix s i 99 ≥ countSuffix s i 98 ∧
          countSuffix s i 98 ≥ countSuffix s i 97 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true →
      ∀ i : Nat, i ≤ s.val.length →
        countSuffix s i 99 ≥ countSuffix s i 98 ∧
          countSuffix s i 98 ≥ countSuffix s i 97) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then s[0] = 97.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_7 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true → byteAt s 0 = some 97 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true → byteAt s 0 = some 97) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then s[len(s)-1] = 99.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_8 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true → byteAt s (s.val.length - 1) = some 99 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true → byteAt s (s.val.length - 1) = some 99) := by
  sorry

/-- If is_valid(s) returns Result.ok true, then there exist n >= 0 and byte strings u_0, ..., u_n such that u_0 = s, u_n is empty, and for every k with 0 <= k < n there is an index i with 0 <= i <= len(u_k)-3, u_k[i] = 97, u_k[i+1] = 98, u_k[i+2] = 99, and u_{k+1} = u_k[0..i] ++ u_k[i+3..len(u_k)].
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_9 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true → ReductionValid (bytes s) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true → ReductionValid (bytes s)) := by
  sorry

/-- For every p with 0 <= p <= len(s), let s' = s[0..p] ++ [97,98,99] ++ s[p..len(s)]. Whenever is_valid(s) returns Result.ok true, is_valid(s') returns Result.ok true.
  Preconditions: 1 <= len(s) <= 19997; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_10 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 19997)
    (habc : abcBytes s) :
    ∀ p : Nat, p ≤ s.val.length →
      ∀ s' : Slice Std.U8,
        bytes s' = (bytes s).take p ++ [97, 98, 99] ++ (bytes s).drop p →
          Aegis.IsValid.is_valid s = ok true → Aegis.IsValid.is_valid s' = ok true := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 19997)
    (habc : abcBytes s), ∀ p : Nat, p ≤ s.val.length →
      ∀ s' : Slice Std.U8,
        bytes s' = (bytes s).take p ++ [97, 98, 99] ++ (bytes s).drop p →
          Aegis.IsValid.is_valid s = ok true → Aegis.IsValid.is_valid s' = ok true) := by
  sorry

/-- For every i with 0 <= i <= len(s)-3 such that s[i] = 97, s[i+1] = 98, and s[i+2] = 99, let t_i = s[0..i] ++ s[i+3..len(s)]. Whenever is_valid(s) returns Result.ok r_s and is_valid(t_i) returns Result.ok r_t, we have r_s = r_t.
  Preconditions: 1 <= len(s) <= 20000; for every j with 0 <= j < len(s), s[j] is 97, 98, or 99; len(s) >= 4. -/
theorem spec_11 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) (hlen4 : 4 ≤ s.val.length) :
    ∀ i : Nat, i + 3 ≤ s.val.length →
      byteAt s i = some 97 → byteAt s (i + 1) = some 98 → byteAt s (i + 2) = some 99 →
        ∀ t : Slice Std.U8,
          bytes t = (bytes s).take i ++ (bytes s).drop (i + 3) →
            ∀ r_s r_t : Bool, Aegis.IsValid.is_valid s = ok r_s →
              Aegis.IsValid.is_valid t = ok r_t → r_s = r_t := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) (hlen4 : 4 ≤ s.val.length), ∀ i : Nat, i + 3 ≤ s.val.length →
      byteAt s i = some 97 → byteAt s (i + 1) = some 98 → byteAt s (i + 2) = some 99 →
        ∀ t : Slice Std.U8,
          bytes t = (bytes s).take i ++ (bytes s).drop (i + 3) →
            ∀ r_s r_t : Bool, Aegis.IsValid.is_valid s = ok r_s →
              Aegis.IsValid.is_valid t = ok r_t → r_s = r_t) := by
  sorry

/-- If is_valid(s) returns Result.ok true and len(s) > 0, then there exists an index i with 0 <= i <= len(s)-3 such that s[i] = 97, s[i+1] = 98, s[i+2] = 99, and the byte string t = s[0..i] ++ s[i+3..len(s)] is valid, where valid means obtainable from the empty string by zero or more insertions of [97,98,99] at arbitrary positions.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97, 98, or 99. -/
theorem spec_12 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    Aegis.IsValid.is_valid s = ok true → 0 < s.val.length →
      ∃ i : Nat, i + 3 ≤ s.val.length ∧ byteAt s i = some 97 ∧
        byteAt s (i + 1) = some 98 ∧ byteAt s (i + 2) = some 99 ∧
          InsertionValid ((bytes s).take i ++ (bytes s).drop (i + 3)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), Aegis.IsValid.is_valid s = ok true → 0 < s.val.length →
      ∃ i : Nat, i + 3 ≤ s.val.length ∧ byteAt s i = some 97 ∧
        byteAt s (i + 1) = some 98 ∧ byteAt s (i + 2) = some 99 ∧
          InsertionValid ((bytes s).take i ++ (bytes s).drop (i + 3))) := by
  sorry

/-- Whenever is_valid(s) returns Result.ok r, r = true if and only if there exist n >= 0 and byte strings u_0, ..., u_n such that u_0 = s, u_n is empty, and for every k with 0 <= k < n there is an index i with 0 <= i <= len(u_k)-3, u_k[i] = 97, u_k[i+1] = 98, u_k[i+2] = 99, and u_{k+1} = u_k[0..i] ++ u_k[i+3..len(u_k)].
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
theorem spec_13 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ ReductionValid (bytes s)) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ ReductionValid (bytes s))) := by
  sorry

/-- Whenever is_valid(s) returns Result.ok r, r = true if and only if the following computation leaves an empty stack: start with an empty byte string st; for j = 0, ..., len(s)-1 in order, append s[j] to st and then, while len(st) >= 3 and the last three bytes of st are [97,98,99], remove those three bytes from st; after processing all bytes, st is empty.
  Preconditions: 1 <= len(s) <= 20000; for every i with 0 <= i < len(s), s[i] is 97 ('a'), 98 ('b'), or 99 ('c'). -/
theorem spec_14 (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s) :
    ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ StackAccepts (bytes s)) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (s : Slice Std.U8)
    (hlen_lo : 1 ≤ s.val.length) (hlen_hi : s.val.length ≤ 20000)
    (habc : abcBytes s), ∀ r : Bool, Aegis.IsValid.is_valid s = ok r →
      (r = true ↔ StackAccepts (bytes s))) := by
  sorry

end AegisSpec.IsValid
