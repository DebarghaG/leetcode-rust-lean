import Aegis.FindLuSlength.Code.Funs

/-!
# Specifications of `Aegis.FindLuSlength.find_lu_slength`

LeetCode problem `longest-uncommon-subsequence-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindLuSlength (find_lu_slength)

namespace AegisSpec.FindLuSlength

abbrev ByteString := List Std.U8

def Sub (x y : ByteString) : Prop :=
  ∃ p : Fin x.length → Fin y.length,
    (∀ a b : Fin x.length, a < b → p a < p b) ∧ ∀ t : Fin x.length, x.get t = y.get (p t)

def Good (strs : List (alloc.vec.Vec Std.U8)) (i : Nat) (hi : i < strs.length) : Prop :=
  ∀ (j : Nat) (hj : j < strs.length), j ≠ i → ¬ Sub (strs[i]).val (strs[j]).val

def Uncommon (strs : List (alloc.vec.Vec Std.U8)) (x : ByteString) : Prop :=
  ∃ (i : Nat) (hi : i < strs.length), Sub x (strs[i]).val ∧
    ∀ (j : Nat) (hj : j < strs.length), Sub x (strs[j]).val → j = i

def maxLen (strs : List (alloc.vec.Vec Std.U8)) : Nat :=
  (strs.map (fun s => s.val.length)).foldr max 0

/-- The function returns a result r and: if no index i with 0 <= i < n is good, then r = -1; if at least one index is good, then r = max{ len(strs[i]) | 0 <= i < n and i is good }. Equivalently, r = -1 exactly when no uncommon subsequence exists, and otherwise r is the largest length of an uncommon subsequence, where a byte string x is an uncommon subsequence when there is exactly one index i with 0 <= i < n and Sub(x, strs[i]).
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_1 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : Std.I64,
      find_lu_slength strs = ok r ∧

      ((∀ (i : Nat) (hi : i < strs.val.length), ¬ Good strs.val i hi) ↔ r.val = -1) ∧

      (∀ (i : Nat) (hi : i < strs.val.length),
        Good strs.val i hi → ((strs.val[i]).val.length : Int) ≤ r.val) ∧

      ((∃ (i : Nat) (hi : i < strs.val.length), Good strs.val i hi) →
        ∃ (i : Nat) (hi : i < strs.val.length),
          Good strs.val i hi ∧ r.val = ((strs.val[i]).val.length : Int)) ∧

      ((∃ x : ByteString, Uncommon strs.val x) ↔ r.val ≠ -1) ∧
      (∀ x : ByteString, Uncommon strs.val x → (x.length : Int) ≤ r.val) ∧
      ((∃ x : ByteString, Uncommon strs.val x) →
        ∃ x : ByteString, Uncommon strs.val x ∧ r.val = (x.length : Int)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64,
      find_lu_slength strs = ok r ∧

      ((∀ (i : Nat) (hi : i < strs.val.length), ¬ Good strs.val i hi) ↔ r.val = -1) ∧

      (∀ (i : Nat) (hi : i < strs.val.length),
        Good strs.val i hi → ((strs.val[i]).val.length : Int) ≤ r.val) ∧

      ((∃ (i : Nat) (hi : i < strs.val.length), Good strs.val i hi) →
        ∃ (i : Nat) (hi : i < strs.val.length),
          Good strs.val i hi ∧ r.val = ((strs.val[i]).val.length : Int)) ∧

      ((∃ x : ByteString, Uncommon strs.val x) ↔ r.val ≠ -1) ∧
      (∀ x : ByteString, Uncommon strs.val x → (x.length : Int) ≤ r.val) ∧
      ((∃ x : ByteString, Uncommon strs.val x) →
        ∃ x : ByteString, Uncommon strs.val x ∧ r.val = (x.length : Int))) := by
  sorry

/-- The function returns some result r : I64; it does not fail.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_2 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∃ r : Std.I64, find_lu_slength strs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∃ r : Std.I64, find_lu_slength strs = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 1 <= r <= maxLen.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_3 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (maxLen strs.val : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r →
      r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (maxLen strs.val : Int))) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < n such that r = len(strs[i]).
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_4 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < strs.val.length), r.val = ((strs.val[i]).val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < strs.val.length), r.val = ((strs.val[i]).val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists an index i with 0 <= i < n such that i is good and r = len(strs[i]).
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_5 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < strs.val.length),
        Good strs.val i hi ∧ r.val = ((strs.val[i]).val.length : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ (i : Nat) (hi : i < strs.val.length),
        Good strs.val i hi ∧ r.val = ((strs.val[i]).val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if for every index i with 0 <= i < n there exists an index j with 0 <= j < n, j != i, such that Sub(strs[i], strs[j]).
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_6 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r →
      (r.val = -1 ↔
        ∀ (i : Nat) (hi : i < strs.val.length),
          ∃ (j : Nat) (hj : j < strs.val.length),
            j ≠ i ∧ Sub (strs.val[i]).val (strs.val[j]).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r →
      (r.val = -1 ↔
        ∀ (i : Nat) (hi : i < strs.val.length),
          ∃ (j : Nat) (hj : j < strs.val.length),
            j ≠ i ∧ Sub (strs.val[i]).val (strs.val[j]).val)) := by
  sorry

/-- Whenever the function returns a result r, for every byte string x, if there is exactly one index i with 0 <= i < n such that Sub(x, strs[i]), then r != -1 and len(x) <= r.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_7 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r →
      ∀ x : ByteString, Uncommon strs.val x → r.val ≠ -1 ∧ (x.length : Int) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r →
      ∀ x : ByteString, Uncommon strs.val x → r.val ≠ -1 ∧ (x.length : Int) ≤ r.val) := by
  sorry

/-- If there exists an index i with 0 <= i < n such that len(strs[i]) = maxLen and strs[i] != strs[j] for every j with 0 <= j < n and j != i, then the function returns a result r and r = maxLen.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_8 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    (∃ (i : Nat) (hi : i < strs.val.length),
        (strs.val[i]).val.length = maxLen strs.val ∧
          ∀ (j : Nat) (hj : j < strs.val.length),
            j ≠ i → (strs.val[j]).val ≠ (strs.val[i]).val) →
      ∃ r : Std.I64, find_lu_slength strs = ok r ∧ r.val = (maxLen strs.val : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), (∃ (i : Nat) (hi : i < strs.val.length),
        (strs.val[i]).val.length = maxLen strs.val ∧
          ∀ (j : Nat) (hj : j < strs.val.length),
            j ≠ i → (strs.val[j]).val ≠ (strs.val[i]).val) →
      ∃ r : Std.I64, find_lu_slength strs = ok r ∧ r.val = (maxLen strs.val : Int)) := by
  sorry

/-- If for every index i with 0 <= i < n and len(strs[i]) = maxLen there exists an index j with 0 <= j < n, j != i, such that strs[j] = strs[i], then whenever the function returns a result r, either r = -1 or r < maxLen.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_9 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    (∀ (i : Nat) (hi : i < strs.val.length), (strs.val[i]).val.length = maxLen strs.val →
        ∃ (j : Nat) (hj : j < strs.val.length),
          j ≠ i ∧ (strs.val[j]).val = (strs.val[i]).val) →
      ∀ r : Std.I64, find_lu_slength strs = ok r →
        r.val = -1 ∨ r.val < (maxLen strs.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), (∀ (i : Nat) (hi : i < strs.val.length), (strs.val[i]).val.length = maxLen strs.val →
        ∃ (j : Nat) (hj : j < strs.val.length),
          j ≠ i ∧ (strs.val[j]).val = (strs.val[i]).val) →
      ∀ r : Std.I64, find_lu_slength strs = ok r →
        r.val = -1 ∨ r.val < (maxLen strs.val : Int)) := by
  sorry

/-- If there exist indices i and j with 0 <= i < n, 0 <= j < n, i != j, strs[i] = strs[j], and for every k with 0 <= k < n we have Sub(strs[k], strs[i]), then the function returns a result r and r = -1.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_10 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    (∃ (i : Nat) (hi : i < strs.val.length) (j : Nat) (hj : j < strs.val.length),
        i ≠ j ∧ (strs.val[i]).val = (strs.val[j]).val ∧
          ∀ (k : Nat) (hk : k < strs.val.length), Sub (strs.val[k]).val (strs.val[i]).val) →
      ∃ r : Std.I64, find_lu_slength strs = ok r ∧ r.val = -1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), (∃ (i : Nat) (hi : i < strs.val.length) (j : Nat) (hj : j < strs.val.length),
        i ≠ j ∧ (strs.val[i]).val = (strs.val[j]).val ∧
          ∀ (k : Nat) (hk : k < strs.val.length), Sub (strs.val[k]).val (strs.val[i]).val) →
      ∃ r : Std.I64, find_lu_slength strs = ok r ∧ r.val = -1) := by
  sorry

/-- If n = 2, then the function returns a result r and: r = -1 if strs[0] = strs[1]; otherwise r = max(len(strs[0]), len(strs[1])).
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_11 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122)
    (h2 : strs.val.length = 2) :
    ∃ r : Std.I64,
      find_lu_slength strs = ok r ∧
      ((strs.val[0]).val = (strs.val[1]).val → r.val = -1) ∧
      ((strs.val[0]).val ≠ (strs.val[1]).val →
        r.val = ((max (strs.val[0]).val.length (strs.val[1]).val.length) : Int)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122)
    (h2 : strs.val.length = 2), ∃ r : Std.I64,
      find_lu_slength strs = ok r ∧
      ((strs.val[0]).val = (strs.val[1]).val → r.val = -1) ∧
      ((strs.val[0]).val ≠ (strs.val[1]).val →
        r.val = ((max (strs.val[0]).val.length (strs.val[1]).val.length) : Int))) := by
  sorry

/-- Let strs' be any slice of length n such that there is a bijection p from {0, ..., n-1} to itself with strs'[k] = strs[p(k)] for every 0 <= k < n (so strs' is a permutation of strs). Whenever find_lu_slength strs returns r and find_lu_slength strs' returns r', we have r = r'.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_12 (strs strs' : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122)
    (hlen' : strs'.val.length = strs.val.length)
    (p : Equiv.Perm (Fin strs.val.length))
    (hperm : ∀ (k : Nat) (hk : k < strs.val.length),
      (strs'.val[k]).val = (strs.val.get (p ⟨k, hk⟩)).val) :
    ∀ (r r' : Std.I64),
      find_lu_slength strs = ok r → find_lu_slength strs' = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (strs strs' : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122)
    (hlen' : strs'.val.length = strs.val.length)
    (p : Equiv.Perm (Fin strs.val.length))
    (hperm : ∀ (k : Nat) (hk : k < strs.val.length),
      (strs'.val[k]).val = (strs.val.get (p ⟨k, hk⟩)).val), ∀ (r r' : Std.I64),
      find_lu_slength strs = ok r → find_lu_slength strs' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exists a byte string x such that there is exactly one index i with 0 <= i < n and Sub(x, strs[i]), and len(x) = r.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_13 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ x : ByteString, Uncommon strs.val x ∧ r.val = (x.length : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r → r.val ≠ -1 →
      ∃ x : ByteString, Uncommon strs.val x ∧ r.val = (x.length : Int)) := by
  sorry

/-- Whenever the function returns a result r with r = -1, for every byte string x, the number of indices i with 0 <= i < n and Sub(x, strs[i]) is not equal to 1.
  Preconditions: Let n = len(strs). We assume 2 <= n <= 50. For every i with 0 <= i < n, len(strs[i]) is between 1 and 10 and every byte of strs[i] is an ASCII lowercase letter (its integer code c satisfies 97 <= c <= 122). Write Sub(x,y) to mean that x is a subsequence of y: there exist indices 0 <= p_0 < p_1 < ... < p_{len(x)-1} < len(y) such that x[t] = y[p_t] for every 0 <= t < len(x); the empty string is a subsequence of every string. For 0 <= i < n, call i good when for every j with 0 <= j < n and j != i, Sub(strs[i], strs[j]) is false. Let maxLen = max_{0 <= i < n} len(strs[i]). -/
theorem spec_14 (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122) :
    ∀ r : Std.I64, find_lu_slength strs = ok r → r.val = -1 →
      ∀ x : ByteString, ¬ Uncommon strs.val x := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (strs : Slice (alloc.vec.Vec Std.U8))
    (hlen : 2 ≤ strs.val.length ∧ strs.val.length ≤ 50)
    (hentry : ∀ (i : Nat) (hi : i < strs.val.length),
      1 ≤ (strs.val[i]).val.length ∧ (strs.val[i]).val.length ≤ 10)
    (hbyte : ∀ (i : Nat) (hi : i < strs.val.length) (c : Std.U8),
      c ∈ (strs.val[i]).val → 97 ≤ c.val ∧ c.val ≤ 122), ∀ r : Std.I64, find_lu_slength strs = ok r → r.val = -1 →
      ∀ x : ByteString, ¬ Uncommon strs.val x) := by
  sorry

end AegisSpec.FindLuSlength
