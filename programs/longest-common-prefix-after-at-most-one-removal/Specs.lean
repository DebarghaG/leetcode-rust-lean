import Aegis.LongestCommonPrefix.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonPrefix.longest_common_prefix`

LeetCode problem `longest-common-prefix-after-at-most-one-removal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.LongestCommonPrefix

  def IsLowerByte (x : U8) : Prop := 97 ≤ x.val ∧ x.val ≤ 122

  def AllLowerBytes (l : List U8) : Prop := ∀ x ∈ l, IsLowerByte x

  def Pre (s t : Slice U8) : Prop :=
    1 ≤ s.leng ∧ 1 ≤ t.leng ∧ s.leng ≤ 100000 ∧ t.leng ≤ 100000 ∧
      AllLowerBytes s.val ∧ AllLowerBytes t.val

  def AgreeBelow (a b : List U8) (L : ℕ) : Prop := ∀ j, j < L → a[j]? = b[j]?

  def IsPrefixLen (a b : List U8) (L : ℕ) : Prop :=
    L ≤ a.length ∧ L ≤ b.length ∧ AgreeBelow a b L

  instance (a b : List U8) : DecidablePred (IsPrefixLen a b) :=
    fun L => by unfold IsPrefixLen AgreeBelow; infer_instance

  def lcpLen (a b : List U8) : ℕ :=
    Nat.findGreatest (IsPrefixLen a b) (min a.length b.length)

  def applyDel (s : List U8) : Option ℕ → List U8
    | none => s
    | some d => s.eraseIdx d

  def DelValidLt (n : ℕ) (D : Option ℕ) : Prop :=
    D = none ∨ ∃ d, D = some d ∧ d < n

  def DelValidLe (n : ℕ) (D : Option ℕ) : Prop :=
    D = none ∨ ∃ d, D = some d ∧ d ≤ n

  def deletions (s : List U8) : List (List U8) :=
    s :: (List.range s.length).map (fun d => s.eraseIdx d)

  def maxLcpOverDeletions (s t : List U8) : ℕ :=
    ((deletions s).map (fun a => lcpLen a t)).foldr max 0

  def ShiftMatch (a b : List U8) (p L : ℕ) : Prop :=
    L ≤ a.length - (p + 1) ∧ L ≤ b.length - p ∧ ∀ j, j < L → a[p + 1 + j]? = b[p + j]?

  instance (a b : List U8) (p : ℕ) : DecidablePred (ShiftMatch a b p) :=
    fun L => by unfold ShiftMatch; infer_instance

  def shiftLen (a b : List U8) (p : ℕ) : ℕ :=
    Nat.findGreatest (ShiftMatch a b p) (min (a.length - (p + 1)) (b.length - p))

  /-- Whenever the function returns a result r, r is exactly the maximum, over all deletion choices D, of the longest common prefix length of s_D and t, where a deletion choice D is either no deletion (so s_D = s and len(s_D) = len(s)) or deletion of one index d with 0 <= d < len(s) (so len(s_D) = len(s) - 1, s_D[j] = s[j] for 0 <= j < d, and s_D[j] = s[j+1] for d <= j < len(s)-1). For a byte slice a, its longest common prefix with t is the largest L such that 0 <= L <= len(a), 0 <= L <= len(t), and a[j] = t[j] for every 0 <= j < L.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_1 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      r.val = (maxLcpOverDeletions s.val t.val : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), r.val = (maxLcpOverDeletions s.val t.val : ℤ)) := by
    sorry

  /-- On every input satisfying the preconditions, the function returns a result r; it does not panic, access out of bounds, or overflow the i64 result type.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_2 (s t : Slice U8) (hpre : Pre s t) :
      ∃ r : I64, Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t), ∃ r : I64, Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= min(len(s), len(t)).
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_3 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      0 ≤ r.val ∧ r.val ≤ ((min s.leng t.leng : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), 0 ≤ r.val ∧ r.val ≤ ((min s.leng t.leng : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a deletion choice D, either no deletion or deletion of one index d with 0 <= d < len(s), such that, writing s_D for s with that deletion applied, r <= len(s_D), r <= len(t), and s_D[j] = t[j] for every 0 <= j < r.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_4 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      ∃ D : Option ℕ,
        DelValidLt s.leng D ∧
          r.val ≤ (((applyDel s.val D).length : ℕ) : ℤ) ∧
            r.val ≤ ((t.leng : ℕ) : ℤ) ∧
              ∀ j : ℕ, (j : ℤ) < r.val → (applyDel s.val D)[j]? = t.val[j]? := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), ∃ D : Option ℕ,
          DelValidLt s.leng D ∧
            r.val ≤ (((applyDel s.val D).length : ℕ) : ℤ) ∧
              r.val ≤ ((t.leng : ℕ) : ℤ) ∧
                ∀ j : ℕ, (j : ℤ) < r.val → (applyDel s.val D)[j]? = t.val[j]?) := by
    sorry

  /-- Whenever the function returns a result r, for every deletion choice D, either no deletion or deletion of one index d with 0 <= d < len(s), and every integer L with r < L <= min(len(s_D), len(t)), there exists an index j with 0 <= j < L such that s_D[j] != t[j], where s_D is s with the deletion D applied.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_5 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      ∀ D : Option ℕ,
        DelValidLt s.leng D →
          ∀ L : ℕ,
            r.val < (L : ℤ) →
              (L : ℤ) ≤ (((applyDel s.val D).length : ℕ) : ℤ) →
                (L : ℤ) ≤ ((t.leng : ℕ) : ℤ) →
                  ∃ j : ℕ, j < L ∧ (applyDel s.val D)[j]? ≠ t.val[j]? := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), ∀ D : Option ℕ,
          DelValidLt s.leng D →
            ∀ L : ℕ,
              r.val < (L : ℤ) →
                (L : ℤ) ≤ (((applyDel s.val D).length : ℕ) : ℤ) →
                  (L : ℤ) ≤ ((t.leng : ℕ) : ℤ) →
                    ∃ j : ℕ, j < L ∧ (applyDel s.val D)[j]? ≠ t.val[j]?) := by
    sorry

  /-- Whenever the function returns a result r, r >= p, where p is the standard longest common prefix length of s and t: the largest L such that 0 <= L <= min(len(s), len(t)) and s[j] = t[j] for every 0 <= j < L.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_6 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      (lcpLen s.val t.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), (lcpLen s.val t.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let p be the standard longest common prefix length of s and t: the largest L such that 0 <= L <= min(len(s), len(t)) and s[j] = t[j] for every 0 <= j < L. If p = min(len(s), len(t)), then r = min(len(s), len(t)).
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_7 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hp : lcpLen s.val t.val = min s.leng t.leng) :
      r.val = ((min s.leng t.leng : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hp : lcpLen s.val t.val = min s.leng t.leng), r.val = ((min s.leng t.leng : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let p be the standard longest common prefix length of s and t: the largest L such that 0 <= L <= min(len(s), len(t)) and s[j] = t[j] for every 0 <= j < L. If p < min(len(s), len(t)) and (p+1 = len(s) or (p+1 < len(s) and s[p+1] != t[p])), then r = p.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_8 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hp : lcpLen s.val t.val < min s.leng t.leng)
      (hcond :
        lcpLen s.val t.val + 1 = s.leng ∨
          (lcpLen s.val t.val + 1 < s.leng ∧
            s.val[lcpLen s.val t.val + 1]? ≠ t.val[lcpLen s.val t.val]?)) :
      r.val = (lcpLen s.val t.val : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hp : lcpLen s.val t.val < min s.leng t.leng)
        (hcond :
          lcpLen s.val t.val + 1 = s.leng ∨
            (lcpLen s.val t.val + 1 < s.leng ∧
              s.val[lcpLen s.val t.val + 1]? ≠ t.val[lcpLen s.val t.val]?)), r.val = (lcpLen s.val t.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, let p be the standard longest common prefix length of s and t: the largest L such that 0 <= L <= min(len(s), len(t)) and s[j] = t[j] for every 0 <= j < L. If p < min(len(s), len(t)), p+1 < len(s), and s[p+1] = t[p], then r >= p+1.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_9 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hp : lcpLen s.val t.val < min s.leng t.leng)
      (h1 : lcpLen s.val t.val + 1 < s.leng)
      (h2 : s.val[lcpLen s.val t.val + 1]? = t.val[lcpLen s.val t.val]?) :
      (lcpLen s.val t.val : ℤ) + 1 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hp : lcpLen s.val t.val < min s.leng t.leng)
        (h1 : lcpLen s.val t.val + 1 < s.leng)
        (h2 : s.val[lcpLen s.val t.val + 1]? = t.val[lcpLen s.val t.val]?), (lcpLen s.val t.val : ℤ) + 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) = 1, then r = 1 if s[0] = t[0], and r = 0 otherwise.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_10 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hs : s.leng = 1) :
      r.val = if s.val[0]? = t.val[0]? then (1 : ℤ) else 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hs : s.leng = 1), r.val = if s.val[0]? = t.val[0]? then (1 : ℤ) else 0) := by
    sorry

  /-- Whenever the function returns a result r, if len(t) = 1, then r = 1 if s[0] = t[0] or (len(s) >= 2 and s[1] = t[0]), and r = 0 otherwise.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_11 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (ht : t.leng = 1) :
      r.val = if s.val[0]? = t.val[0]? ∨ (2 ≤ s.leng ∧ s.val[1]? = t.val[0]?)
        then (1 : ℤ) else 0 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (ht : t.leng = 1), r.val = if s.val[0]? = t.val[0]? ∨ (2 ≤ s.leng ∧ s.val[1]? = t.val[0]?)
          then (1 : ℤ) else 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if s[0] != t[0] and (len(s) = 1 or (len(s) >= 2 and s[1] != t[0])).
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_12 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r) :
      (r.val = 0 ↔
        s.val[0]? ≠ t.val[0]? ∧ (s.leng = 1 ∨ (2 ≤ s.leng ∧ s.val[1]? ≠ t.val[0]?))) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r), (r.val = 0 ↔
          s.val[0]? ≠ t.val[0]? ∧ (s.leng = 1 ∨ (2 ≤ s.leng ∧ s.val[1]? ≠ t.val[0]?)))) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) <= len(t), then r = len(s) if and only if s[j] = t[j] for every 0 <= j < len(s).
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_13 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hle : s.leng ≤ t.leng) :
      (r.val = ((s.leng : ℕ) : ℤ) ↔ ∀ j : ℕ, j < s.leng → s.val[j]? = t.val[j]?) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hle : s.leng ≤ t.leng), (r.val = ((s.leng : ℕ) : ℤ) ↔ ∀ j : ℕ, j < s.leng → s.val[j]? = t.val[j]?)) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) > len(t), then there exists a deletion choice D that is either no deletion or deletion of an index d with 0 <= d <= len(t), such that, writing s_D for s with D applied, r <= len(s_D), r <= len(t), and s_D[j] = t[j] for every 0 <= j < r.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_14 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hgt : t.leng < s.leng) :
      ∃ D : Option ℕ,
        DelValidLe t.leng D ∧
          r.val ≤ (((applyDel s.val D).length : ℕ) : ℤ) ∧
            r.val ≤ ((t.leng : ℕ) : ℤ) ∧
              ∀ j : ℕ, (j : ℤ) < r.val → (applyDel s.val D)[j]? = t.val[j]? := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hgt : t.leng < s.leng), ∃ D : Option ℕ,
          DelValidLe t.leng D ∧
            r.val ≤ (((applyDel s.val D).length : ℕ) : ℤ) ∧
              r.val ≤ ((t.leng : ℕ) : ℤ) ∧
                ∀ j : ℕ, (j : ℤ) < r.val → (applyDel s.val D)[j]? = t.val[j]?) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) > len(t), then for every byte slice s' of the same length as s that also satisfies the preconditions and agrees with s on every index j with 0 <= j <= len(t), if the function returns r' on input (s', t), then r' = r.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_15 (s t s' : Slice U8) (hpre : Pre s t) (hpre' : Pre s' t)
      (hlen : s'.leng = s.leng)
      (hagree : ∀ j : ℕ, j ≤ t.leng → s.val[j]? = s'.val[j]?)
      (hgt : t.leng < s.leng) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (r' : I64)
      (hr' : Aegis.LongestCommonPrefix.longest_common_prefix s' t = Result.ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (s t s' : Slice U8) (hpre : Pre s t) (hpre' : Pre s' t)
        (hlen : s'.leng = s.leng)
        (hagree : ∀ j : ℕ, j ≤ t.leng → s.val[j]? = s'.val[j]?)
        (hgt : t.leng < s.leng) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (r' : I64)
        (hr' : Aegis.LongestCommonPrefix.longest_common_prefix s' t = Result.ok r'), r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, let p be the standard longest common prefix length of s and t: the largest L such that 0 <= L <= min(len(s), len(t)) and s[j] = t[j] for every 0 <= j < L. If p < min(len(s), len(t)), then r = p + L, where L is the largest integer such that 0 <= L <= len(s) - (p+1), 0 <= L <= len(t) - p, and s[p+1+j] = t[p+j] for every 0 <= j < L.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_16 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hp : lcpLen s.val t.val < min s.leng t.leng) :
      r.val = ((lcpLen s.val t.val + shiftLen s.val t.val (lcpLen s.val t.val) : ℕ) : ℤ) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hp : lcpLen s.val t.val < min s.leng t.leng), r.val = ((lcpLen s.val t.val + shiftLen s.val t.val (lcpLen s.val t.val) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) <= len(t), then for every byte slice t' of the same length as t that also satisfies the preconditions and agrees with t on every index j with 0 <= j < len(s), if the function returns r' on input (s, t'), then r' = r.
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_17 (s t t' : Slice U8) (hpre : Pre s t) (hpre' : Pre s t')
      (hlen : t'.leng = t.leng)
      (hagree : ∀ j : ℕ, j < s.leng → t.val[j]? = t'.val[j]?)
      (hle : s.leng ≤ t.leng) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (r' : I64)
      (hr' : Aegis.LongestCommonPrefix.longest_common_prefix s t' = Result.ok r') :
      r'.val = r.val := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (s t t' : Slice U8) (hpre : Pre s t) (hpre' : Pre s t')
        (hlen : t'.leng = t.leng)
        (hagree : ∀ j : ℕ, j < s.leng → t.val[j]? = t'.val[j]?)
        (hle : s.leng ≤ t.leng) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (r' : I64)
        (hr' : Aegis.LongestCommonPrefix.longest_common_prefix s t' = Result.ok r'), r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, if len(s) > len(t), then r = len(t) if and only if there exists a deletion choice D (no deletion or deletion of an index d with 0 <= d <= len(t)) such that, writing s_D for s with D applied, len(s_D) >= len(t) and s_D[j] = t[j] for every 0 <= j < len(t).
    Preconditions: len(s) >= 1, len(t) >= 1, len(s) <= 100000, len(t) <= 100000, and every byte of s and t is a lowercase English letter (97 <= byte <= 122). -/
  theorem spec_18 (s t : Slice U8) (hpre : Pre s t) (r : I64)
      (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
      (hgt : t.leng < s.leng) :
      (r.val = ((t.leng : ℕ) : ℤ) ↔
        ∃ D : Option ℕ,
          DelValidLe t.leng D ∧
            t.leng ≤ (applyDel s.val D).length ∧
              ∀ j : ℕ, j < t.leng → (applyDel s.val D)[j]? = t.val[j]?) := by
    sorry

  theorem spec_18_neg :
      ¬ (∀ (s t : Slice U8) (hpre : Pre s t) (r : I64)
        (hr : Aegis.LongestCommonPrefix.longest_common_prefix s t = Result.ok r)
        (hgt : t.leng < s.leng), (r.val = ((t.leng : ℕ) : ℤ) ↔
          ∃ D : Option ℕ,
            DelValidLe t.leng D ∧
              t.leng ≤ (applyDel s.val D).length ∧
                ∀ j : ℕ, j < t.leng → (applyDel s.val D)[j]? = t.val[j]?)) := by
    sorry

  end AegisSpec.LongestCommonPrefix
